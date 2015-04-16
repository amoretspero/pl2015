Require Export Assignment05_08.

(* problem #09: 10 points *)



(** 2 stars (contrapositive)  *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q.
  intros H0.
  intros H1.
  unfold not in H1.
  unfold not.
  intros H2.
  apply H1.
  apply H0 in H2.
  apply H2.
Qed.
(** [] *)



