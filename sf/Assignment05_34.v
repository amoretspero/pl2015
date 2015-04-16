Require Export Assignment05_33.

(* problem #34: 10 points *)

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
    unfold lt.
    destruct m.
    split.
    inversion H.
    inversion H.
    split.
    apply n_le_m__Sn_le_Sm.
    apply Sn_le_Sm__n_le_m in H.
    apply le_trans with (m := n1) (n := (n1 + n2)) (o := m).
    apply le_plus_l.
    apply H.
    apply n_le_m__Sn_le_Sm.
    apply Sn_le_Sm__n_le_m in H.
    apply le_trans with (m := n2) (n := (n1 + n2)) (o := m).
    rewrite plus_comm with (n := n1) (m := n2).
    apply le_plus_l.
    apply H.
    
Qed.

