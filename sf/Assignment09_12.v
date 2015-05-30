Require Export Assignment09_11.

(* problem #12: 10 points *)

(** **** Exercise: 2 stars, advanced (hoare_asgn_weakest)  *)
(** Show that the precondition in the rule [hoare_asgn] is in fact the
    weakest precondition. *)

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
Proof.
    intros.
    unfold is_wp.
    split.
    apply hoare_asgn.
    intros.
    unfold assert_implies.
    intros.
    unfold hoare_triple in H.
    assert ((X ::= a) / st || (update st X (aeval st a))).
    apply E_Ass.
    auto.
    apply H in H1.
    unfold assn_sub.
    apply H1.
    apply H0.
    
Qed.

(*-- Check --*)
Check hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
