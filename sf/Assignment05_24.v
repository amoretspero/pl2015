Require Export Assignment05_23.

(* problem #24: 10 points *)







(** 3 stars, advanced (ev_ev__ev)  *)
(** Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
    intros n m.
    intros H0.
    intros H1.
    induction H1.
    simpl in H0.
    apply H0.
    simpl in H0.
    inversion H0.
    apply IHev.
    apply pf_evn.
    
Qed.
(** [] *)



