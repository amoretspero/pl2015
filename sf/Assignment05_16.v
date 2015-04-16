Require Export Assignment05_15.

(* problem #16: 10 points *)







(** 2 stars (b_times2)  *)
Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
    intros n.
    intros H0.
    simpl.
    induction n.
    simpl.
    apply H0.
    apply (b_sum (S n) (S n + 0)).
    apply H0.
    apply (b_sum (S n) 0).
    apply H0.
    apply b_0. 
Qed.
(** [] *)



