Require Export Assignment05_03.

(* problem #04: 10 points *)



Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R.
  split.
  destruct H as [HP HQ0].
  destruct H0 as [HQ1 HR].
  intros.
  apply HQ1 in HP.
  apply HP.
  apply H.
  intros.
  destruct H as [HP HQ].
  destruct H0 as [HQ1 HR].
  apply HQ in HR.
  apply HR.
  apply H1.
Qed.


