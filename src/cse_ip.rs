use crate::skolem_normal_form::*;
use good_lp::solvers::coin_cbc::coin_cbc;
use good_lp::{constraint, variable, variables, Expression, Solution, SolverModel};
use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;

#[derive(Clone, PartialEq, Eq, Debug)]
struct CSEIPLiteral {
  literal: FOFTerm,
  positive: bool,      // 肯定リテラルか
  depth: usize,        // 最大項深度
  symbol_count: usize, // リテラル内の記号数
}

impl From<FOFTerm> for CSEIPLiteral {
  fn from(value: FOFTerm) -> Self {
    let depth = value.max_depth();
    let symbol_count = value.count_symbols();
    CSEIPLiteral {
      literal: value,
      positive: false,
      depth,
      symbol_count,
    }
  }
}

impl std::fmt::Display for CSEIPLiteral {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if !self.positive {
      write!(f, "¬")?;
    }
    write!(f, "{}", self.literal)?;
    Ok(())
  }
}

impl Ord for CSEIPLiteral {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    let self_weight = self.calculate_weight();
    let other_weight = other.calculate_weight();
    match self_weight.cmp(&other_weight) {
      std::cmp::Ordering::Equal => self.literal.cmp(&other.literal),
      ord => return ord,
    }
  }
}
impl PartialOrd for CSEIPLiteral {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    Some(self.cmp(other))
  }
}

impl CSEIPLiteral {
  fn calculate_weight(&self) -> usize {
    self.depth + self.symbol_count
  }
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct CSEIPClause {
  clause: BTreeSet<CSEIPLiteral>,
  literal_count: usize,
  deduction_count: usize,
}

impl From<CNFClause> for CSEIPClause {
  fn from(value: CNFClause) -> Self {
    let mut literals = BTreeSet::new();
    for lit in value.pos {
      let mut cse_lit = CSEIPLiteral::from(lit);
      cse_lit.positive = true;
      literals.insert(cse_lit);
    }
    for lit in value.neg {
      let cse_lit = CSEIPLiteral::from(lit);
      literals.insert(cse_lit);
    }
    let literal_count = literals.len();
    CSEIPClause {
      clause: literals,
      literal_count,
      deduction_count: 0,
    }
  }
}

impl std::fmt::Display for CSEIPClause {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{{")?;
    let mut iter = self.clause.iter().peekable();
    while let Some(literal) = iter.next() {
      write!(f, "{}", literal)?;
      if iter.peek().is_some() {
        write!(f, ", ")?;
      }
    }
    write!(f, "}}")?;
    Ok(())
  }
}

impl Ord for CSEIPClause {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    let self_weight = self.calculate_weight();
    let other_weight = other.calculate_weight();
    match self_weight.cmp(&other_weight) {
      std::cmp::Ordering::Equal => self.clause.cmp(&other.clause),
      ord => ord,
    }
  }
}
impl PartialOrd for CSEIPClause {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    Some(self.cmp(other))
  }
}
impl CSEIPClause {
  // fn substitute(&self, substitutions: &BTreeMap<FOFTerm, FOFTerm>) -> Self {
  //   let mut clause = BTreeSet::new();
  //   for lit in &self.clause {
  //     let new_literal = lit.literal.new_literal(substitutions);
  //     let mut cse_lit = CSEIPLiteral::from(new_literal);
  //     cse_lit.positive = lit.positive;
  //     clause.insert(cse_lit);
  //   }
  //   let literal_count = clause.len();
  //   CSEIPClause {
  //     clause,
  //     literal_count,
  //     deduction_count: 0,
  //   }
  // }

  fn calculate_weight(&self) -> usize {
    self.literal_count * 5
  }
}

struct CSEIP {
  clauses: Vec<CSEIPClause>,
  rel_count: Vec<Vec<(usize, usize)>>,
  next_clause_ids: Vec<usize>,
}

impl From<&FOFCNF> for CSEIP {
  fn from(value: &FOFCNF) -> Self {
    let mut clauses = CSEIP::new();
    for clause in &value.clauses {
      let cse_clause = CSEIPClause::from(clause.clone());
      clauses.clauses.push(cse_clause);
    }
    clauses
  }
}

impl std::fmt::Display for CSEIP {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut iter = self.clauses.iter().peekable();
    while let Some(clause) = iter.next() {
      write!(f, "{}", clause)?;
      if iter.peek().is_some() {
        write!(f, ", ")?;
      }
    }
    Ok(())
  }
}

impl CSEIP {
  fn new() -> Self {
    CSEIP {
      clauses: Vec::new(),
      rel_count: Vec::new(),
      next_clause_ids: Vec::new(),
    }
  }

  fn solve(&mut self) -> String {
    // 各節で置換後に，矛盾するリテラル，包含関係のリテラルの個数を数える
    for i in 0..self.clauses.len() {
      self.rel_count.push(Vec::new());
      for j in i + 1..self.clauses.len() {
        if i == j {
          continue;
        }
        let mut same_count = 0;
        let mut conj_count = 0;
        for lit_i in &self.clauses[i].clause {
          for lit_j in &self.clauses[j].clause {
            if lit_i
              .literal
              .unification(&lit_j.literal, &mut BTreeMap::new())
            {
              if lit_i.positive == lit_j.positive {
                same_count += 1;
              } else {
                conj_count += 1;
              }
            }
          }
        }
        self.rel_count[i].push((same_count, conj_count));
      }
    }
    // 導出
    match self.solve_lp() {
      Ok(_) => (),
      Err(e) => eprintln!("Error solving LP: {}", e),
    }

    "Solved".to_string()
  }

  fn solve_lp(&mut self) -> Result<(), Box<dyn Error>> {
    // IP問題を構築
    // 変数の定義
    let alpha: f64 = 0.0;
    let beta: f64 = 2.0;
    let mut vars = variables!();
    let x: Vec<_> = (0..self.clauses.len())
      .map(|i| vars.add(variable().binary().name(format!("x{}", i))))
      .collect();
    let mut y: Vec<Vec<Option<_>>> = (0..self.clauses.len())
      .map(|_| (0..self.clauses.len()).map(|_| None).collect())
      .collect();
    for i in 0..self.clauses.len() {
      for j in (i + 1)..self.clauses.len() {
        let var = vars.add(variable().binary().name(format!("y_{}_{}", i, j)));
        y[i][j] = Some(var);
      }
    }
    // 目的関数
    let mut objective = Expression::from(0.0);
    for i in 0..self.clauses.len() {
      for j in (i + 1)..self.clauses.len() {
        let y_ij = y[i][j].unwrap();
        let coeff = alpha * (self.rel_count[i][j - i - 1].0 as f64)
          + beta * (self.rel_count[i][j - i - 1].1 as f64);
        objective = objective + coeff * y_ij;
      }
    }
    for i in 0..self.clauses.len() {
      objective = objective - self.clauses[i].calculate_weight() as f64 * x[i];
    }
    let mut model = vars.maximise(objective).using(coin_cbc);
    model.set_parameter("log", "0");
    // 制約条件1
    for i in 0..self.clauses.len() {
      for j in (i + 1)..self.clauses.len() {
        let y_ij = y[i][j].unwrap();
        model = model.with(constraint!(y_ij <= x[i]));
        model = model.with(constraint!(y_ij <= x[j]));
        model = model.with(constraint!(y_ij >= x[i] + x[j] - 1));
      }
    }
    // 制約条件2
    let mut sum_x = Expression::from(0.0);
    for i in 0..self.clauses.len() {
      sum_x = sum_x + x[i];
    }
    model = model.with(constraint!(sum_x >= 2));
    // 制約条件3
    for i in 0..self.clauses.len() {
      for j in (i + 1)..self.clauses.len() {
        let y_ij = y[i][j].unwrap();
        let cij = self.rel_count[i][j - i - 1].1 as f64;
        model = model.with(constraint!(cij >= y_ij));
      }
    }
    // 解く
    let solution = model.solve()?;
    println!("objective = {}", solution.model().obj_value());

    let mut solution_clauses = Vec::new();
    for i in 0..self.clauses.len() {
      println!("x[{}] = {}", i, solution.value(x[i]));
      if solution.value(x[i]) > 0.5 {
        solution_clauses.push(i);
      }
    }
    self.next_clause_ids = solution_clauses;
    for i in 0..self.clauses.len() {
      for j in (i + 1)..self.clauses.len() {
        let y_ij = y[i][j].unwrap();
        println!("y[{},{}] = {}", i, j, solution.value(y_ij));
      }
    }
    Ok(())
  }
}

#[allow(dead_code)]
pub fn solve(cnf: &FOFCNF) -> String {
  let mut cseip_clauses = CSEIP::from(cnf);
  // println!("CSE Initial Clauses: {}", cse_clauses);
  cseip_clauses.solve()
}
