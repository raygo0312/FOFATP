fof(subset_union,axiom,
    ! [B,C] :
      ( subset(B,C)
      <=> ! [D]:
        ( member(D, B) => member(D, C) ) ) ) .

fof(prove_idempotency_of_union,conjecture,
    ! [B,C,D] :
      ( ( subset(B, C)
      & subset(C, D) )
      => subset(B, D) ) ).
