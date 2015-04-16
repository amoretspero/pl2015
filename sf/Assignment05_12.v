Require Export Assignment05_11.

(* problem #12: 10 points *)




(** 2 stars (false_beq_nat)  *)

Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
  intros.
  unfold not in H.
  generalize dependent m.
  induction n as [| n'].
  intros.
  destruct m.
  simpl.
  destruct H.
  reflexivity.
  simpl.
  reflexivity.
  intros.
  destruct m as [| m'].
  reflexivity.
  apply IHn'.
  intros.
  apply H.
  rewrite H0.
  reflexivity.
Qed.
  

(** [] *)




