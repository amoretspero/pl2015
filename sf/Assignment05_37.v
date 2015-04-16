Require Export Assignment05_36.

(* problem #37: 10 points *)

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
    (* Hint: This may be easiest to prove by induction on [m]. *)
    intros n m.
    generalize dependent n.
    induction m.
    (*generalize dependent n.*)
    intros n.
    intros H0.
    inversion H0.
    simpl.
    reflexivity.
    intros n.
    intros H1.
    induction n.
    simpl.
    reflexivity.
    simpl.
    apply Sn_le_Sm__n_le_m in H1.
    apply IHm.
    apply H1.
Qed.

