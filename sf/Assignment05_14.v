Require Export Assignment05_13.

(* problem #14: 10 points *)




(** 2 star (ev__even)  *)
Theorem ev__even: forall n : nat,
  ev n -> even n.
Proof.
  intros n.
  intros H0.
  induction H0.
  unfold even.
  simpl.
  reflexivity.
  unfold even.
  unfold even in IHev.
  simpl.
  rewrite IHev.
  reflexivity.
Qed.
(** [] *)


