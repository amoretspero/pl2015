Require Export Assignment05_35.

(* problem #36: 10 points *)

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
    intros.
    generalize dependent m.
    induction n.
    intros m.
    intros H0.
    apply O_le_n.
    intros.
    induction m.
    inversion H.
    apply n_le_m__Sn_le_Sm.
    apply IHn.
    simpl in H.
    apply H.
    
Qed.

