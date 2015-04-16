Require Export Assignment05_05.

(* problem #06: 10 points *)


(** 2 stars, optional (orb_false)  *)
Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros b c.
  intros H0.
  destruct b.
  destruct c.
  apply or_intror.
  reflexivity.
  apply or_introl.
  reflexivity.
  destruct c.
  apply or_intror.
  reflexivity.
  destruct H0.
  simpl.
  apply or_intror.
  reflexivity.
Qed.


