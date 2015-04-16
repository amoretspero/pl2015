Require Export Assignment05_16.

(* problem #17: 10 points *)





(** 3 stars (b_timesm)  *)
(*Fixpoint mult (n : nat) (m : nat) :=
    match m with
    | O => O
    | S m' => n + (mult n (m' - 1))
    end.
Lemma mult_changer : forall n m, m * n = (mult n m).
Proof.
    intros n m.
    induction m.
    simpl.
    reflexivity.
    simpl.
    rewrite IHm.
    simpl.*)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
    intros n m.
    intros H0.
    induction m.
    simpl.
    apply b_0.
    simpl.
    apply b_sum with (n := n) (m := m * n).
    apply H0.
    apply IHm.
Qed.
(** [] *)




