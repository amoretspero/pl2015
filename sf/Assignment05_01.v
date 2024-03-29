Require Export Assignment05_00.

(* problem #01: 10 points *)




(** 1 star, optional (proj2)  *)
Theorem proj2 : forall P Q : Prop, 
  P /\ Q -> Q.
Proof.
  intros P Q.
  intros H0.
  inversion H0.
  apply H1.
Qed.
(** [] *)




