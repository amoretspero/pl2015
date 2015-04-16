Require Export Assignment05_20.

(* problem #21: 10 points *)





(** 2 stars (ev_sum)  *)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
    intros n m.
    intros H0.
    intros H1.
    induction H0.
    simpl.
    apply H1.
    simpl.
    apply ev_SS with (n := (n + m)).
    apply IHev.
Qed.
(** [] *)





