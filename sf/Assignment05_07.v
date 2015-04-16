Require Export Assignment05_06.

(* problem #07: 10 points *)



(** 2 stars, optional (orb_false_elim)  *)
Theorem orb_false_elim : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof. 
  intros b c.
  intros H0.
  destruct b.
  destruct c.
  split.
  destruct H0.
  simpl.
  reflexivity.
  destruct H0.
  simpl.
  reflexivity.
  split.
  destruct H0.
  destruct b.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  reflexivity.
  destruct c.
  split.
  reflexivity.
  destruct H0.
  destruct b.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  split.
  reflexivity.
  reflexivity.
Qed.
(** [] *)



