use tptp::common::*;
use tptp::fof;
use tptp::top::*;
use tptp::visitor::*;
use tptp::TPTPIterator;

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::vec;

// 一階述語論理の項
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FOFTerm {
  Variable(String),
  Function(String, Vec<FOFTerm>),
}

impl std::fmt::Display for FOFTerm {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      FOFTerm::Variable(var) => write!(f, "{}", var),
      FOFTerm::Function(name, args) => {
        let args_str = args
          .iter()
          .map(|arg| format!("{}", arg))
          .collect::<Vec<_>>()
          .join(", ");
        write!(f, "{}({})", name, args_str)
      }
    }
  }
}

impl Ord for FOFTerm {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    use FOFTerm::*;
    match (self, other) {
      (Variable(a), Variable(b)) => a.cmp(b),
      (Variable(_), Function(_, _)) => std::cmp::Ordering::Less,
      (Function(_, _), Variable(_)) => std::cmp::Ordering::Greater,
      (Function(a, args_a), Function(b, args_b)) => match a.cmp(b) {
        std::cmp::Ordering::Equal => args_a.cmp(args_b),
        ord => ord,
      },
    }
  }
}

impl PartialOrd for FOFTerm {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    Some(self.cmp(other))
  }
}

impl FOFTerm {
  pub fn max_depth(&self) -> usize {
    match self {
      FOFTerm::Variable(_) => 1,
      FOFTerm::Function(_, args) => {
        let arg_depths: Vec<usize> = args.iter().map(|arg| arg.max_depth()).collect();
        1 + arg_depths.into_iter().max().unwrap_or(0)
      }
    }
  }

  pub fn count_symbols(&self) -> usize {
    match self {
      FOFTerm::Variable(_) => 1,
      FOFTerm::Function(_, args) => 1 + args.iter().map(|arg| arg.count_symbols()).sum::<usize>(),
    }
  }

  pub fn count_variables(&self) -> usize {
    match self {
      FOFTerm::Variable(_) => 1,
      FOFTerm::Function(_, args) => args.iter().map(|arg| arg.count_variables()).sum(),
    }
  }
}

// 一階述語論理の式
#[derive(Clone, Debug)]
enum FOFFormula {
  Or(Vec<FOFFormula>),
  And(Vec<FOFFormula>),
  Not(Box<FOFFormula>),
  Term(FOFTerm),
}

impl std::fmt::Display for FOFFormula {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use FOFFormula::*;
    match self {
      Or(formulas) => {
        let joined = formulas
          .iter()
          .map(|x| format!("{}", x))
          .collect::<Vec<_>>()
          .join(" ∨ ");
        write!(f, "({})", joined)
      }
      And(formulas) => {
        let joined = formulas
          .iter()
          .map(|x| format!("{}", x))
          .collect::<Vec<_>>()
          .join(" ∧ ");
        write!(f, "({})", joined)
      }
      Not(inner) => write!(f, "¬{}", inner),
      Term(term) => write!(f, "{}", term),
    }
  }
}

impl FOFFormula {
  fn to_nnf(&self) -> FOFFormula {
    use FOFFormula::*;
    match self {
      Not(formula) => match &**formula {
        Not(inner_formula) => inner_formula.to_nnf(),
        And(inner_formulas) => Or(
          inner_formulas
            .iter()
            .map(|f| Not(Box::new(f.clone())).to_nnf())
            .collect(),
        ),
        Or(inner_formulas) => And(
          inner_formulas
            .iter()
            .map(|f| Not(Box::new(f.clone())).to_nnf())
            .collect(),
        ),
        Term(_) => self.clone(),
      },
      And(formulas) => And(formulas.iter().map(|f| f.to_nnf()).collect()),
      Or(formulas) => Or(formulas.iter().map(|f| f.to_nnf()).collect()),
      Term(term) => Term(term.clone()),
    }
  }

  pub fn to_cnf(&self) -> FOFFormula {
    use FOFFormula::*;
    let nnf = self.to_nnf();
    match nnf {
      And(formulas) => {
        let cnf_formulas = formulas.iter().map(|f| f.to_cnf()).collect();
        And(FOFFormula::flatten_and(cnf_formulas))
      }
      Or(formulas) => {
        let mut cnf_formulas = formulas.iter().map(|f| f.to_cnf()).collect();
        FOFFormula::distribute_or(&mut cnf_formulas)
      }
      _ => nnf,
    }
  }

  fn distribute_or(formulas: &mut Vec<FOFFormula>) -> FOFFormula {
    use FOFFormula::*;
    if formulas.is_empty() {
      return Or(vec![]);
    } else if formulas.len() == 1 {
      return formulas[0].clone();
    }

    let first = formulas[0].clone();
    let rest = FOFFormula::distribute_or(&mut formulas[1..].to_vec());

    match (first, rest) {
      (And(first), And(rest)) => {
        let mut new_formulas = vec![];
        for f1 in &first {
          for f2 in &rest {
            new_formulas.push(Or(vec![f1.clone(), f2.clone()]));
          }
        }
        And(new_formulas.into_iter().map(|f| f.to_cnf()).collect())
      }
      (And(first), rest) => {
        let mut new_formulas = vec![];
        for f1 in first {
          new_formulas.push(Or(vec![f1, rest.clone()]));
        }
        And(new_formulas)
      }
      (first, And(rest)) => {
        let mut new_formulas = vec![];
        for f2 in rest {
          new_formulas.push(Or(vec![first.clone(), f2]));
        }
        And(new_formulas)
      }
      (first, rest) => Or(FOFFormula::flatten_or(vec![first, rest])),
    }
  }

  fn flatten_and(formulas: Vec<FOFFormula>) -> Vec<FOFFormula> {
    let mut result = vec![];
    for formula in formulas {
      match formula {
        FOFFormula::And(inner_formulas) => result.extend(inner_formulas),
        _ => result.push(formula),
      }
    }
    result
  }

  fn flatten_or(formulas: Vec<FOFFormula>) -> Vec<FOFFormula> {
    let mut result = vec![];
    for formula in formulas {
      match formula {
        FOFFormula::Or(inner_formulas) => result.extend(inner_formulas),
        _ => result.push(formula),
      }
    }
    result
  }

  fn insert_set_cnf(&self, cnf: &mut FOFCNF) {
    let cnf_formula = self.to_cnf();
    match cnf_formula {
      FOFFormula::And(formulas) => {
        for formula in formulas {
          FOFFormula::insert_set_cnf(&formula, cnf);
        }
      }
      FOFFormula::Or(terms) => {
        let mut pos = BTreeSet::new();
        let mut neg = BTreeSet::new();
        for term in terms {
          match term {
            FOFFormula::Term(term) => {
              pos.insert(term.clone());
            }
            FOFFormula::Not(inner) => match &*inner {
              FOFFormula::Term(term) => {
                neg.insert(term.clone());
              }
              _ => {
                eprintln!("Unexpected term in CNF: {:?}", inner);
              }
            },
            _ => eprintln!("Unexpected formula in CNF literal: {}", term),
          };
        }
        cnf.clauses.insert(CNFClause { pos, neg });
      }
      FOFFormula::Not(inner) => {
        if let FOFFormula::Term(term) = *inner {
          let mut neg = BTreeSet::new();
          neg.insert(term);
          cnf.clauses.insert(CNFClause {
            pos: BTreeSet::new(),
            neg,
          });
        } else {
          eprintln!("Unexpected formula in CNF Not: {}", inner);
        }
      }
      FOFFormula::Term(term) => {
        let mut pos = BTreeSet::new();
        pos.insert(term);
        cnf.clauses.insert(CNFClause {
          pos,
          neg: BTreeSet::new(),
        });
      }
    }
  }
}

// TPTPを解析しながら，冠頭標準形かつスコーレム標準形に変換する
#[derive(Default)]
pub struct SkolemNormalForm {
  var_map: BTreeMap<String, String>,
  var_count: u64,
  skolem_map: BTreeMap<String, FOFTerm>,
  skolem_count: u64,
  formulas: Vec<(String, FOFFormula)>,
  formula_name: String,
  node_stack: Vec<FOFFormula>,
  term_stack: Vec<FOFTerm>,
  term_count_stack: Vec<usize>,
  not: bool,           // 現在の訪問位置が否定の中かどうか
  recent_name: String, // 最近訪問した名前を保存する
}

impl std::fmt::Display for SkolemNormalForm {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for (name, formula) in &self.formulas {
      writeln!(f, "{}: {}", name, formula)?;
    }
    Ok(())
  }
}

impl SkolemNormalForm {
  pub fn new() -> Self {
    Self::default()
  }

  pub fn to_set_cnf(&self) -> FOFCNF {
    let mut cnf = FOFCNF::new();
    for (_, formula) in &self.formulas {
      formula.insert_set_cnf(&mut cnf);
    }
    cnf
  }
}

// TPTPの解析と同時にスコーレム標準形に変換する
impl<'a> Visitor<'a> for SkolemNormalForm {
  // 小文字の単語を訪問
  // 単語名をrecent_nameに保存
  fn visit_lower_word(&mut self, lower_word: &LowerWord<'a>) {
    self.recent_name = lower_word.0.to_string();
  }

  // 名前を訪問
  fn visit_atomic_word(&mut self, atomic_word: &AtomicWord<'a>) {
    match atomic_word {
      AtomicWord::Lower(lower_word) => self.visit_lower_word(lower_word),
      AtomicWord::SingleQuoted(_single_quoted) => {
        eprintln!("Single quoted words are not supported");
      }
    }
  }

  // 論理式の名前を訪問
  fn visit_name(&mut self, name: &Name<'a>) {
    match name {
      Name::AtomicWord(atomic_word) => self.visit_atomic_word(atomic_word),
      Name::Integer(_integer) => {
        eprintln!("Integer names are not supported");
      }
    }
  }

  // 論理式の注釈を訪問
  fn visit_annotations(&mut self, annotations: &Annotations<'a>) {
    if let Some(_boxed) = &annotations.0 {
      println!("Not supported annotations");
      // self.visit_source(&boxed.0);
      // self.visit_optional_info(&boxed.1);
    }
  }

  // FOFの処理
  fn visit_fof_annotated(&mut self, fof_annotated: &FofAnnotated<'a>) {
    // 構造確認用
    // println!("{:?}", fof_annotated);
    self.visit_name(&fof_annotated.0.name);
    self.formula_name = self.recent_name.clone();
    self.visit_formula_role(&fof_annotated.0.role);
    let role = self.recent_name.clone();

    if role == "axiom" {
      // axiomならそのまま訪問
      self.visit_fof_formula(&fof_annotated.0.formula)
    } else if role == "conjecture" {
      // conjectureなら否定を訪問
      self.not ^= true;
      self.visit_fof_formula(&fof_annotated.0.formula);
      if let Some(formula) = self.node_stack.pop() {
        self.node_stack.push(FOFFormula::Not(Box::new(formula)));
      } else {
        eprintln!("Stack underflow while processing conjecture");
        return;
      }
      self.not ^= true;
    } else {
      eprintln!("Unsupported role: {}", fof_annotated.0.role.0 .0);
    }
    self.visit_annotations(&fof_annotated.0.annotations);
  }

  // 量化子を訪問
  fn visit_fof_quantifier(&mut self, fof_quantifier: fof::Quantifier) {
    match fof_quantifier {
      fof::Quantifier::Exists => {
        self.not ^= true;
      }
      fof::Quantifier::Forall => (),
    }
  }

  // 量化式を訪問
  fn visit_fof_quantified_formula(&mut self, fof_quantified_formula: &fof::QuantifiedFormula<'a>) {
    self.visit_fof_quantifier(fof_quantified_formula.quantifier);

    for variable in &*fof_quantified_formula.bound.0 {
      // 各変数について
      let UpperWord(var) = variable.0;
      let key = var.to_string();
      if self.not {
        // 冠頭時にExistsになる場合
        self.skolem_count += 1;
        let skolem_var = format!("f{}", self.skolem_count);
        let vars_in_scope = self
          .var_map
          .values()
          .cloned()
          .map(FOFTerm::Variable)
          .collect();
        self
          .skolem_map
          .insert(key.clone(), FOFTerm::Function(skolem_var, vars_in_scope));
      } else {
        // 冠頭時にForallになる場合
        self.var_count += 1;
        let var = format!("x{}", self.var_count);
        self.var_map.insert(key, var);
      }
    }
    self.visit_fof_unit_formula(&fof_quantified_formula.formula);
    if self.not {
      println!("skolem: {:?}", self.skolem_map);
      for var in &*fof_quantified_formula.bound.0 {
        let key = var.0.to_string();
        self.skolem_map.remove(&key);
      }
    } else {
      println!("vars: {:?}", self.var_map);
      for var in &*fof_quantified_formula.bound.0 {
        let key = var.0.to_string();
        self.var_map.remove(&key);
      }
    }
    self.visit_fof_quantifier(fof_quantified_formula.quantifier);
  }

  // ORを訪問
  fn visit_fof_or_formula(&mut self, fof_or_formula: &fof::OrFormula<'a>) {
    for fof_unit_formula in &*fof_or_formula.0 {
      self.visit_fof_unit_formula(fof_unit_formula);
    }
    let or_formulas = self
      .node_stack
      .split_off(self.node_stack.len() - fof_or_formula.0.len());
    self.node_stack.push(FOFFormula::Or(or_formulas));
  }

  // ANDを訪問
  fn visit_fof_and_formula(&mut self, fof_and_formula: &fof::AndFormula<'a>) {
    for fof_unit_formula in &*fof_and_formula.0 {
      self.visit_fof_unit_formula(fof_unit_formula);
    }
    let and_formulas = self
      .node_stack
      .split_off(self.node_stack.len() - fof_and_formula.0.len());
    self.node_stack.push(FOFFormula::And(and_formulas));
  }

  // NOTを訪問
  fn visit_fof_unary_formula(&mut self, fof_unary_formula: &fof::UnaryFormula<'a>) {
    match fof_unary_formula {
      fof::UnaryFormula::Unary(_, fof_unit_formula) => {
        self.not ^= true;
        self.visit_fof_unit_formula(fof_unit_formula);
        self.not ^= true;
        if let Some(node) = self.node_stack.pop() {
          self.node_stack.push(FOFFormula::Not(Box::new(node)));
        } else {
          eprintln!("Stack underflow while processing UnaryFormula");
        }
      }
      fof::UnaryFormula::InfixUnary(ref fof_infix_unary) => {
        self.visit_fof_infix_unary(fof_infix_unary)
      }
    }
  }

  // 変換すべき2項真理関数を訪問
  fn visit_fof_binary_nonassoc(&mut self, fof_binary_nonassoc: &fof::BinaryNonassoc<'a>) {
    use FOFFormula::*;
    use NonassocConnective::*;

    let node = match fof_binary_nonassoc.op {
      LRImplies => {
        self.not ^= true;
        self.visit_fof_unit_formula(&fof_binary_nonassoc.left);
        self.not ^= true;
        self.visit_fof_unit_formula(&fof_binary_nonassoc.right);
        let (Some(right), Some(nleft)) = (self.node_stack.pop(), self.node_stack.pop()) else {
          eprintln!("Stack underflow while processing LRImplies");
          return;
        };
        Or(vec![Not(Box::new(nleft)), right])
      }
      RLImplies => {
        self.visit_fof_unit_formula(&fof_binary_nonassoc.left);
        self.not ^= true;
        self.visit_fof_unit_formula(&fof_binary_nonassoc.right);
        self.not ^= true;
        let (Some(left), Some(nright)) = (self.node_stack.pop(), self.node_stack.pop()) else {
          eprintln!("Stack underflow while processing RLImplies");
          return;
        };
        Or(vec![left, Not(Box::new(nright))])
      }
      Equivalent | NotEquivalent => {
        self.visit_fof_unit_formula(&fof_binary_nonassoc.left);
        self.visit_fof_unit_formula(&fof_binary_nonassoc.right);
        self.not ^= true;
        self.visit_fof_unit_formula(&fof_binary_nonassoc.left);
        self.visit_fof_unit_formula(&fof_binary_nonassoc.right);
        self.not ^= true;
        let (Some(nright), Some(nleft), Some(right), Some(left)) = (
          self.node_stack.pop(),
          self.node_stack.pop(),
          self.node_stack.pop(),
          self.node_stack.pop(),
        ) else {
          eprintln!("Stack underflow while processing Equivalent or NotEquivalent");
          return;
        };
        match fof_binary_nonassoc.op {
          Equivalent => {
            let a = Or(vec![Not(Box::new(nleft)), right]);
            let b = Or(vec![left, Not(Box::new(nright))]);
            And(vec![a, b])
          }
          NotEquivalent => {
            let a = Or(vec![Not(Box::new(left)), nright]);
            let b = Or(vec![nleft, Not(Box::new(right))]);
            Not(Box::new(And(vec![a, b])))
          }
          _ => unreachable!(),
        }
      }
      NotOr | NotAnd => {
        self.not ^= true;
        self.visit_fof_unit_formula(&fof_binary_nonassoc.left);
        self.visit_fof_unit_formula(&fof_binary_nonassoc.right);
        self.not ^= true;
        let (Some(nright), Some(nleft)) = (self.node_stack.pop(), self.node_stack.pop()) else {
          eprintln!("Stack underflow while processing NotOr or NotAnd");
          return;
        };
        match fof_binary_nonassoc.op {
          NotOr => Not(Box::new(Or(vec![nleft, nright]))),
          NotAnd => Not(Box::new(And(vec![nleft, nright]))),
          _ => unreachable!(),
        }
      }
    };

    self.node_stack.push(node);
  }

  // 関数or述語を訪問
  fn visit_fof_plain_term(&mut self, fof_plain_term: &fof::PlainTerm<'a>) {
    match fof_plain_term {
      fof::PlainTerm::Constant(constant) => self.visit_constant(constant),
      fof::PlainTerm::Function(functor, fof_arguments) => {
        // 順番を入れ替えてはいけない
        self.visit_fof_arguments(fof_arguments);
        self.visit_functor(functor);
      }
    }
  }

  // 関数or述語の引数を訪問
  fn visit_fof_arguments(&mut self, fof_arguments: &fof::Arguments<'a>) {
    self.term_count_stack.push(fof_arguments.0.len());
    for fof_term in &*fof_arguments.0 {
      self.visit_fof_term(fof_term);
    }
  }

  // 変数を訪問
  fn visit_variable(&mut self, variable: &Variable<'a>) {
    let key = variable.0 .0.to_string();
    if let Some(var) = self.var_map.get(&key) {
      self.term_stack.push(FOFTerm::Variable(var.clone()));
    } else if let Some(skolem_term) = self.skolem_map.get(&key) {
      self.term_stack.push(skolem_term.clone());
    } else {
      eprintln!("Variable {} not found in vars_map or skolem_map", key);
      self.term_stack.push(FOFTerm::Variable(key));
    }
  }

  // 定数を訪問
  fn visit_constant(&mut self, constant: &Constant<'a>) {
    let key = constant.0.to_string();
    if let Some(skolem_term) = self.skolem_map.get(&key) {
      self.term_stack.push(skolem_term.clone());
    } else {
      self.skolem_count += 1;
      let skolem_var = format!("c{}", self.skolem_count);
      let skolem_term = FOFTerm::Function(skolem_var.clone(), vec![]);
      self.skolem_map.insert(key, skolem_term.clone());
      self.term_stack.push(skolem_term);
    }
  }

  // 関数名を訪問
  fn visit_functor(&mut self, functor: &Functor<'a>) {
    let functor_name = match &functor.0 {
      AtomicWord::Lower(lower_word) => lower_word.0,
      AtomicWord::SingleQuoted(single_quoted) => single_quoted.0,
    };

    let args_count = self.term_count_stack.pop().unwrap_or(0);
    let args = self
      .term_stack
      .split_off(self.term_stack.len() - args_count);
    if self.term_count_stack.is_empty() {
      self.node_stack.push(FOFFormula::Term(FOFTerm::Function(
        functor_name.to_string(),
        args,
      )));
    } else {
      self
        .term_stack
        .push(FOFTerm::Function(functor_name.to_string(), args));
    }
  }

  // =を訪問
  fn visit_fof_defined_infix_formula(
    &mut self,
    fof_defined_infix_formula: &fof::DefinedInfixFormula<'a>,
  ) {
    self.term_count_stack.push(2);
    self.visit_fof_term(&fof_defined_infix_formula.left);
    self.visit_fof_term(&fof_defined_infix_formula.right);
    let (Some(right), Some(left)) = (self.term_stack.pop(), self.term_stack.pop()) else {
      eprintln!("Stack underflow while processing defined infix formula");
      return;
    };
    self.term_count_stack.pop();
    self.node_stack.push(FOFFormula::Term(FOFTerm::Function(
      "=".to_string(),
      vec![left, right],
    )));
  }

  // 論理式の種類
  fn visit_annotated_formula(&mut self, annotated: &AnnotatedFormula<'a>) {
    match annotated {
      AnnotatedFormula::Tfx(_tfx_annotated) => {
        eprintln!("Not supported TfxAnnotated");
      }
      AnnotatedFormula::Fof(fof_annotated) => self.visit_fof_annotated(fof_annotated),
      AnnotatedFormula::Cnf(_cnf_annotated) => {
        eprintln!("Not supported CnfAnnotated");
      }
    }
  }

  fn visit_single_quoted(&mut self, _single_quoted: &SingleQuoted<'a>) {
    self.recent_name = _single_quoted.0.to_string();
  }

  // Includeのリンク先を訪問
  fn visit_include(&mut self, include: &Include<'a>) {
    self.visit_file_name(&include.file_name);
    let file_name = format!("TPTP-v9.0.0/{}", self.recent_name.clone());
    self.visit_tptp_file(&file_name);
    if include.selection.0.is_some() {
      eprintln!("Not supported include selection");
    }
  }
}

impl SkolemNormalForm {
  fn visit_tptp_file(&mut self, tptp_file: &String) {
    let bytes = std::fs::read(tptp_file).expect("failed to read file");
    let mut parser = TPTPIterator::<()>::new(&bytes);
    for result in &mut parser {
      let input = result.expect("syntax error");
      // println!("Processing: {:?}", input);
      self.visit_tptp_input(&input);
      if let TPTPInput::Include(_) = &input {
        continue;
      }
      if let Some(formula) = self.node_stack.pop() {
        println!("{}: {}", self.formula_name, formula);
        self.formulas.push((self.formula_name.clone(), formula));
      } else {
        eprintln!("Stack underflow while processing TPTP input");
      }
    }
    assert!(parser.remaining.is_empty());
  }
}

#[derive(Default)]
pub struct FOFCNF {
  pub clauses: BTreeSet<CNFClause>,
}

impl std::fmt::Display for FOFCNF {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut cnt = 0;
    for clause in &self.clauses {
      write!(f, "CNFClause {}: {}\n", cnt, clause)?;
      cnt += 1;
    }
    Ok(())
  }
}

impl FOFCNF {
  pub fn new() -> Self {
    Self::default()
  }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct CNFClause {
  pub pos: BTreeSet<FOFTerm>,
  pub neg: BTreeSet<FOFTerm>,
}

impl std::fmt::Display for CNFClause {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let pos_terms = self.pos.iter().map(|term| format!("{}", term));
    let neg_terms = self.neg.iter().map(|term| format!("¬{}", term));
    let literals = pos_terms.chain(neg_terms).collect::<Vec<_>>().join(", ");
    write!(f, "{}", literals)
  }
}

impl Ord for CNFClause {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    let left = self.pos.len() + self.neg.len();
    let right = other.pos.len() + other.neg.len();
    if left.cmp(&right) != std::cmp::Ordering::Equal {
      return left.cmp(&right);
    }
    match self.pos.cmp(&other.pos) {
      std::cmp::Ordering::Equal => self.neg.cmp(&other.neg),
      ord => ord,
    }
  }
}

impl PartialOrd for CNFClause {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    Some(self.cmp(other))
  }
}

// TPTPのバイト列を受け取り、スコーレム標準形に変換してCNFに変換したものを返す
pub fn skolem_normal_form(tptp_file: &String) -> FOFCNF {
  let mut visitor = SkolemNormalForm::new();
  visitor.visit_tptp_file(tptp_file);
  visitor.to_set_cnf()
}
