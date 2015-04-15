Require Export Assignment05_04.

(* problem #05: 10 points *)


(** 1 star, optional (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  intros.
  destruct H as [HP | HQ'].
  split.
  apply or_introl.
  apply HP.
  apply or_introl.
  apply HP.
  destruct HQ' as [HQ HR].
  split.
  apply or_intror.
  apply HQ.
  apply or_intror.
  apply HR.
  intros.
  destruct H as [HPQ HPR].
  destruct HPQ as [HP | HQ].
  destruct HPR as [HP' | HR].
  apply or_introl.
  apply HP.
  apply or_introl.
  apply HP.
  destruct HPR as [HP | HR].
  apply or_introl.
  apply HP.
  apply or_intror.
  split.
  apply HQ.
  apply HR.
Qed.
(** [] *)


