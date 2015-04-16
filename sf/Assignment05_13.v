Require Export Assignment05_12.

(* problem #13: 10 points *)



(** 2 stars, optional (beq_nat_false)  *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  intros n m.
  intros H0.
  unfold not.
  intros H1.
  generalize dependent m.
  induction n.
  intros m.
  intros H0.
  induction m.
  intros H1.
  simpl in H0.
  inversion H0.
  intros H1.
  simpl in H0.
  apply IHm.
  simpl.
  induction m.
  inversion H1.
  reflexivity.
  inversion H1.
  intros m.
  intros H0.
  destruct m.
  intros.
  inversion H1.
  intros.
  simpl in H0.
  apply IHn in H0.
  apply H0.
  inversion H1.
  reflexivity.
Qed.

(** [] *)



