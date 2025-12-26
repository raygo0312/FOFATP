use crate::skolem_normal_form::*;
use std::collections::BTreeMap;

impl FOFTerm {
  pub fn unification(
    &self,
    other: &FOFTerm,
    substitutions: &mut BTreeMap<FOFTerm, FOFTerm>,
  ) -> bool {
    if self == other {
      return true;
    }

    match (self, other) {
      (FOFTerm::Variable(s), t) => {
        if let Some(existing) = substitutions.get(&FOFTerm::Variable(s.clone())).cloned() {
          return existing.unification(t, substitutions);
        }
        substitutions.insert(FOFTerm::Variable(s.clone()), t.clone());
        true
      }
      (s, FOFTerm::Variable(t)) => {
        if let Some(existing) = substitutions.get(&FOFTerm::Variable(t.clone())).cloned() {
          return s.unification(&existing, substitutions);
        }
        substitutions.insert(FOFTerm::Variable(t.clone()), s.clone());
        true
      }
      (FOFTerm::Function(func1, args1), FOFTerm::Function(func2, args2)) => {
        if func1 != func2 || args1.len() != args2.len() {
          return false;
        }
        for (arg1, arg2) in args1.iter().zip(args2.iter()) {
          if arg1.unification(arg2, substitutions) == false {
            return false;
          }
        }
        true
      }
    }
  }

  pub fn new_literal(&self, substitutions: &BTreeMap<FOFTerm, FOFTerm>) -> FOFTerm {
    match self {
      FOFTerm::Variable(_) => substitutions
        .get(self)
        .cloned()
        .unwrap_or_else(|| self.clone()),
      FOFTerm::Function(name, args) => {
        let new_args = args.iter().map(|a| a.new_literal(substitutions)).collect();
        FOFTerm::Function(name.clone(), new_args)
      }
    }
  }
}
