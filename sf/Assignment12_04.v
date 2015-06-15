Require Export Assignment12_03.

(* problem #04: 10 points *)

Corollary soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof.
    intros.
    unfold stuck.
    unfold not.
    intros.
    unfold normal_form in H1.
    unfold not in H1.
    inversion H1.
    apply H3.
    induction H0.
    apply progress in H.
    inversion H.
    apply H0.
    apply H2 in H0.
    inversion H0.
    apply IHmulti.
    apply preservation with (t' := y) in H.
    apply H.
    apply H0.
    apply H1.
    apply H2.
    apply H3.
Qed.
(*-- Check --*)
Check soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').

