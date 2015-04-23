Require Export Assignment06_02.

(* problem #03: 10 points *)

(** **** Exercise: 2 stars (dist_exists_or)  *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
    intros.
    split.
    intros.
    destruct H.
    destruct proof.
    left.
    apply ex_intro with (witness := witness).
    apply H.
    right.
    apply ex_intro with (witness := witness).
    apply H.
    intros H0.
    inversion H0.
    inversion H.
    apply ex_intro with (witness := witness).
    left.
    apply proof.
    inversion H.
    apply ex_intro with (witness := witness).
    right.
    apply proof.
Qed.
(** [] *)


