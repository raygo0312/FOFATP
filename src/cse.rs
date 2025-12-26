use crate::skolem_normal_form::*;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, PartialEq, Eq, Debug)]
struct CSELiteral {
  literal: FOFTerm,
  positive: bool,            // 肯定リテラルか
  acceptable_count: usize,   // 許容推論重み
  unacceptable_count: usize, // 非許容推論重み
  depth: usize,              // 最大項深度
  symbol_count: usize,       // リテラル内の記号数
}

impl From<FOFTerm> for CSELiteral {
  fn from(value: FOFTerm) -> Self {
    let depth = value.max_depth();
    let symbol_count = value.count_symbols();
    CSELiteral {
      literal: value,
      positive: false,
      acceptable_count: 0,
      unacceptable_count: 0,
      depth,
      symbol_count,
    }
  }
}

impl std::fmt::Display for CSELiteral {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if !self.positive {
      write!(f, "¬")?;
    }
    write!(f, "{}", self.literal)?;
    Ok(())
  }
}

impl Ord for CSELiteral {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    let self_weight = self.calculate_weight();
    let other_weight = other.calculate_weight();
    match self_weight.cmp(&other_weight) {
      std::cmp::Ordering::Equal => self.literal.cmp(&other.literal),
      ord => return ord,
    }
  }
}
impl PartialOrd for CSELiteral {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    Some(self.cmp(other))
  }
}

impl CSELiteral {
  fn calculate_weight(&self) -> usize {
    self.acceptable_count + self.unacceptable_count + self.depth + self.symbol_count
  }
}

#[derive(Clone, PartialEq, Eq)]
struct CSEUnitClause {
  clause: CSELiteral,
  deduction_count: usize, // 推論に参加した回数
  symbol_count: usize,    // 節内の記号数
  depth: usize,           // 最大項深度
  variable_count: usize,  // 節内の変数数
}

impl TryFrom<CNFClause> for CSEUnitClause {
  type Error = &'static str;

  fn try_from(value: CNFClause) -> Result<Self, Self::Error> {
    if value.pos.len() + value.neg.len() != 1 {
      return Err("The clause is not a unit clause.");
    }
    let literal = if !value.pos.is_empty() {
      let literal = value.pos.into_iter().next().unwrap();
      let mut literal = CSELiteral::from(literal);
      literal.positive = true;
      literal
    } else {
      let literal = value.neg.into_iter().next().unwrap();
      CSELiteral::from(literal)
    };
    let symbol_count = literal.symbol_count;
    let depth = literal.depth;
    let variable_count = literal.literal.count_variables();
    Ok(CSEUnitClause {
      clause: literal,
      deduction_count: 0,
      symbol_count,
      depth,
      variable_count,
    })
  }
}

impl TryFrom<CSENonUnitClause> for CSEUnitClause {
  type Error = &'static str;

  fn try_from(value: CSENonUnitClause) -> Result<Self, Self::Error> {
    if value.clause.len() != 1 {
      return Err("The clause is not a unit clause.");
    }
    let literal = value.clause.first().unwrap().clone();
    let symbol_count = literal.symbol_count;
    let depth = literal.depth;
    let variable_count = literal.literal.count_variables();
    Ok(CSEUnitClause {
      clause: literal,
      deduction_count: 0,
      symbol_count,
      depth,
      variable_count,
    })
  }
}

impl std::fmt::Display for CSEUnitClause {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", self.clause)?;
    Ok(())
  }
}

impl Ord for CSEUnitClause {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    let self_weight = self.calculate_weight();
    let other_weight = other.calculate_weight();
    match self_weight.cmp(&other_weight) {
      std::cmp::Ordering::Equal => self.clause.literal.cmp(&other.clause.literal),
      ord => ord,
    }
  }
}
impl PartialOrd for CSEUnitClause {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    Some(self.cmp(other))
  }
}

impl CSEUnitClause {
  fn calculate_weight(&self) -> usize {
    self.deduction_count + (self.symbol_count - self.variable_count) + self.depth
  }
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct CSENonUnitClause {
  clause: BTreeSet<CSELiteral>,
  acceptable_count: usize,   // 許容推論重み
  unacceptable_count: usize, // 非許容推論重み
  literal_count: usize,      // リテラル数
}

impl From<CNFClause> for CSENonUnitClause {
  fn from(value: CNFClause) -> Self {
    let mut literals = BTreeSet::new();
    for lit in value.pos {
      let mut cse_lit = CSELiteral::from(lit);
      cse_lit.positive = true;
      literals.insert(cse_lit);
    }
    for lit in value.neg {
      let cse_lit = CSELiteral::from(lit);
      literals.insert(cse_lit);
    }
    let literal_count = literals.len();
    CSENonUnitClause {
      clause: literals,
      acceptable_count: 0,
      unacceptable_count: 0,
      literal_count,
    }
  }
}

impl std::fmt::Display for CSENonUnitClause {
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

impl Ord for CSENonUnitClause {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    let self_weight = self.calculate_weight();
    let other_weight = other.calculate_weight();
    match self_weight.cmp(&other_weight) {
      std::cmp::Ordering::Equal => self.clause.cmp(&other.clause),
      ord => ord,
    }
  }
}
impl PartialOrd for CSENonUnitClause {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    Some(self.cmp(other))
  }
}
impl CSENonUnitClause {
  fn substitute(&self, substitutions: &BTreeMap<FOFTerm, FOFTerm>) -> Self {
    let mut clause = BTreeSet::new();
    for lit in &self.clause {
      let new_literal = lit.literal.new_literal(substitutions);
      let mut cse_lit = CSELiteral::from(new_literal);
      cse_lit.positive = lit.positive;
      clause.insert(cse_lit);
    }
    let literal_count = clause.len();
    CSENonUnitClause {
      clause,
      acceptable_count: 0,
      unacceptable_count: 0,
      literal_count,
    }
  }

  fn calculate_weight(&self) -> usize {
    self.acceptable_count + self.unacceptable_count + self.literal_count * 5
  }

  fn check_unacceptable(&self) -> bool {
    let max_depth = self.clause.iter().map(|lit| lit.depth).max().unwrap_or(0);
    self.literal_count > 10 || max_depth > 5
  }
}

struct CSEClauses {
  unit_clauses: BTreeSet<CSEUnitClause>,
  non_unit_clauses: BTreeSet<CSENonUnitClause>,
}

impl From<&FOFCNF> for CSEClauses {
  fn from(value: &FOFCNF) -> Self {
    let mut clauses = CSEClauses::new();
    for clause in &value.clauses {
      if clause.pos.len() + clause.neg.len() == 1 {
        if let Ok(cse_clause) = CSEUnitClause::try_from(clause.clone()) {
          clauses.unit_clauses.insert(cse_clause);
        }
      } else {
        let cse_clause = CSENonUnitClause::from(clause.clone());
        clauses.non_unit_clauses.insert(cse_clause);
      }
    }
    clauses
  }
}

impl std::fmt::Display for CSEClauses {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "CSEUnitClause: ")?;
    let mut unit_iter = self.unit_clauses.iter();
    while let Some(unit_clause) = unit_iter.next() {
      write!(f, "{}, ", unit_clause)?;
    }
    write!(f, "CSENonUnitClause: ")?;
    let mut non_unit_iter = self.non_unit_clauses.iter().peekable();
    while let Some(non_unit_clause) = non_unit_iter.next() {
      write!(f, "{}", non_unit_clause)?;
      if non_unit_iter.peek().is_some() {
        write!(f, ", ")?;
      }
    }
    Ok(())
  }
}

impl CSEClauses {
  fn new() -> Self {
    CSEClauses {
      unit_clauses: BTreeSet::new(),
      non_unit_clauses: BTreeSet::new(),
    }
  }

  fn solve(&mut self) -> String {
    let copy_unit_clauses = self.unit_clauses.clone();
    for unit_clause in copy_unit_clauses {
      for unit_clause2 in &self.unit_clauses {
        if unit_clause.clause.literal == unit_clause2.clause.literal
          && unit_clause.clause.positive != unit_clause2.clause.positive
        {
          return "UNSAT".into();
        }
      }
    }
    while let Some(mut p) = self.non_unit_clauses.first().cloned() {
      // println!("CSE Selected Non-Unit Clause: {}", p);
      self.non_unit_clauses.remove(&p);
      let q = self.scs_rule(&p);
      // println!("CSE Resulting Clause: {}", q);
      if q.literal_count == 0 {
        return "UNSAT".into();
      }
      if q.check_unacceptable() {
        p.unacceptable_count += 1;
        self.non_unit_clauses.insert(p);
        continue;
      }
      p.acceptable_count += 1;
      self.non_unit_clauses.insert(p);
      if q.literal_count == 1 {
        if let Ok(unit_clause) = CSEUnitClause::try_from(q) {
          self.unit_clauses.insert(unit_clause);
        }
        // println!("CSE Current Clauses: {}", self);

        continue;
      } else {
        self.non_unit_clauses.insert(q);
      }
      if self.check_exit_condition() {
        return "TIMEOUT".into();
      }
      // println!("CSE Current Clauses: {}", self);
    }
    "NONE".into()
  }

  fn scs_rule(&mut self, clause: &CSENonUnitClause) -> CSENonUnitClause {
    let mut new_clause = clause.clone();
    let mut once = false;
    loop {
      let mut updated_unit_clause = None;
      let mut delete_literal = None;
      let mut substitutions = BTreeMap::new();
      let mut finish = true;
      'outer: for search_clause in new_clause.clause.clone() {
        for unit_clause in &self.unit_clauses {
          let literal = unit_clause.clause.clone();
          if literal.positive != search_clause.positive
            && literal
              .literal
              .unification(&search_clause.literal, &mut substitutions)
          {
            // println!("CSE Hit Unit Clause: {}", unit_clause);
            updated_unit_clause = Some(unit_clause.clone());
            delete_literal = Some(search_clause);
            once = true;
            finish = false;
            break 'outer;
          }
        }
      }
      if let Some(unit_clause) = updated_unit_clause {
        self.unit_clauses.remove(&unit_clause);
        let mut updated_unit_clause = unit_clause.clone();
        updated_unit_clause.deduction_count += 1;
        self.unit_clauses.insert(updated_unit_clause);
      }
      if let Some(literal) = delete_literal {
        new_clause.clause.remove(&literal);
      }
      new_clause = new_clause.substitute(&substitutions);
      if finish {
        break;
      }
    }
    if !once {
      new_clause.unacceptable_count += 1;
    }
    new_clause
  }

  // 終了条件のチェック
  fn check_exit_condition(&self) -> bool {
    if self.unit_clauses.len() + self.non_unit_clauses.len() > 20 {
      return true;
    }
    false
  }
}

#[allow(dead_code)]
pub fn solve(cnf: &FOFCNF) -> String {
  let mut cse_clauses = CSEClauses::from(cnf);
  // println!("CSE Initial Clauses: {}", cse_clauses);
  cse_clauses.solve()
}
