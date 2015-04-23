Require Export Assignment06_01.

(* problem #02: 10 points *)

(** **** Exercise: 3 stars, optional (not_exists_dist)  *)
(** (The other direction of this theorem requires the classical "law
    of the excluded middle".) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
    intros H0.
    intros X.
    intros P0.
    intros H1.
    intros x0.
    unfold not in H1.
    unfold excluded_middle in H0.
    destruct (H0 (P0 x0)).
    apply H.
    destruct H1.
    unfold not in H.
    apply ex_intro with (witness := x0).
    apply H.
Qed.
(** [] *)

