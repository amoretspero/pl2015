Require Export Assignment08_03.

(* problem #04: 10 points *)

(** **** Exercise: 4 stars (no_whiles_terminating)  *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this. *)

(* Hint *)
Check andb_true_iff.

Theorem no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.
Proof.
    intros.
    generalize dependent st.
    induction c; intros.
    apply ex_intro with (x := st).
    apply E_Skip.
    apply ex_intro with (x := (update st i (aeval st a))).
    apply E_Ass.
    reflexivity.
    inversion NOWHL.
    apply andb_true_iff in H0.
    inversion H0.
    apply IHc1 with (st := st) in H.
    inversion H.
    apply IHc2 with (st := x) in H1.
    inversion H1.
    apply ex_intro with (x := x0).
    apply E_Seq with (st' := x); assumption.
    inversion NOWHL.
    apply andb_true_iff in H0.
    inversion H0.
    apply IHc1 with (st := st) in H.
    inversion H.
    destruct (beval st b) eqn:b_dest.
    apply ex_intro with (x := x).
    apply E_IfTrue.
    apply b_dest.
    apply H2.
    apply IHc2 with (st := st) in H1.
    inversion H1.
    apply ex_intro with (x := x0).
    apply E_IfFalse.
    apply b_dest.
    apply H3.
    destruct (beval st b) eqn:b_dest.
    inversion NOWHL.
    inversion NOWHL.
Qed.

(*-- Check --*)
Check no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.

