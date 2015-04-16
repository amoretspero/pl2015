Require Export Assignment05_25.

(* problem #26: 10 points *)











(** 3 star (even__ev)  
    Note that proving [even__ev] directly is hard.
    You might find it easier to prove [even__ev_strong] first
    and then prove [even__ev] using it.
*)

Lemma even__ev_strong: forall n : nat, 
  (even (pred n) -> ev (pred n)) /\ (even n -> ev n).
Proof.
    intros n.
    induction n.
    split.
    intros H1.
    simpl.
    apply ev_0.
    intros H2.
    apply ev_0.
    split.
    intros H3.
    simpl in H3.
    simpl.
    apply IHn.
    apply H3.
    inversion IHn.
    induction n.
    intros H4.
    inversion H4.
    intros H5.
    apply ev_SS.
    unfold even in H5.
    simpl in H5.
    simpl in H.
    apply H.
    unfold even.
    apply H5.
    
Qed.
(** [] *)


