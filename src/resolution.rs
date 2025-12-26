use crate::skolem_normal_form::*;

impl FOFCNF {
  #[allow(dead_code)]
  /// 解決法（resolution）を実行する。空節が導出できればtrue。
  pub fn resolution(&self) -> bool {
    // 最初の節を取得
    let mut c_now = self.clauses.first().unwrap().clone();
    for _ in 0..10 {
      // println!("Current Clause: {}", c_now);
      // 節集合から1つずつ節を選び、解決を試みる
      'resolution: for clause in &self.clauses {
        // c_nowの正リテラルとclauseの負リテラルで解決
        for pos in &c_now.pos {
          for neg in &clause.neg {
            let mut substitutions = std::collections::BTreeMap::new();
            // posとnegが単一化可能なら
            if pos.unification(neg, &mut substitutions) {
              // println!("Hit: {}", clause);
              // 新しい節を生成
              let mut new_clause = Self::make_resolvent(&c_now, clause, &substitutions);
              // 単純化（同じリテラルの削除）
              Self::simplify_clause(&mut new_clause);
              // 空節なら証明成功
              if new_clause.pos.is_empty() && new_clause.neg.is_empty() {
                return true;
              }
              // 新しい節を次のc_nowに
              c_now = new_clause;
              break 'resolution;
            }
          }
        }
        // c_nowの負リテラルとclauseの正リテラルで解決
        for neg in &c_now.neg {
          for pos in &clause.pos {
            let mut substitutions = std::collections::BTreeMap::new();
            if neg.unification(pos, &mut substitutions) {
              // println!("Hit: {}", clause);
              let mut new_clause = Self::make_resolvent(&c_now, clause, &substitutions);
              Self::simplify_clause(&mut new_clause);
              if new_clause.pos.is_empty() && new_clause.neg.is_empty() {
                return true;
              }
              c_now = new_clause;
              break 'resolution;
            }
          }
        }
      }
    }
    // 1000回繰り返しても空節が出なければ失敗
    false
  }

  /// 2つの節と代入から新しい節（解決節）を作る
  fn make_resolvent(
    c1: &CNFClause,
    c2: &CNFClause,
    substitutions: &std::collections::BTreeMap<FOFTerm, FOFTerm>,
  ) -> CNFClause {
    // 正リテラル・負リテラルを合体
    let mut new_clause = CNFClause {
      pos: c1.pos.union(&c2.pos).cloned().collect(),
      neg: c2.neg.union(&c1.neg).cloned().collect(),
    };
    // 代入を適用
    new_clause.pos = new_clause
      .pos
      .iter()
      .map(|term| term.new_literal(substitutions))
      .collect();
    new_clause.neg = new_clause
      .neg
      .iter()
      .map(|term| term.new_literal(substitutions))
      .collect();
    new_clause
  }

  /// 節から同じリテラル（正負一致）を削除
  fn simplify_clause(clause: &mut CNFClause) {
    let mut to_remove = vec![];
    for pos in &clause.pos {
      for neg in &clause.neg {
        if pos == neg {
          to_remove.push((pos.clone(), neg.clone()));
        }
      }
    }
    for (p, n) in to_remove {
      clause.pos.remove(&p);
      clause.neg.remove(&n);
    }
  }
}
