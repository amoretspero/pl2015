Require Export Assignment06_00.

(* problem #01: 10 points *)


(** **** Exercise: 1 star (dist_not_exists)  *)
(** Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold." *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. 
    intros X.
    intros P0.
    intros H0.
    unfold not.
    intros H1.
    inversion H1.
    apply proof in H0.
    apply H0.
Qed.
(** [] *)


