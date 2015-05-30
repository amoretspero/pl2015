Require Export Assignment09_10.

(* problem #11: 10 points *)

(** **** Exercise: 3 stars, advanced, optional (is_wp_formal)  *)
(** Prove formally using the definition of [hoare_triple] that [Y <= 4]
   is indeed the weakest precondition of [X ::= Y + 1] with respect to
   postcondition [X <= 5]. *)

Theorem is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).
Proof.
    unfold is_wp.
    split.
    unfold hoare_triple.
    intros.
    inversion H.
    subst.
    unfold update.
    simpl.
    omega.
    intros.
    unfold hoare_triple in H.
    unfold assert_implies.
    intros.
    assert ((X ::= APlus (AId Y) (ANum 1)) / st || (update st X (st Y + 1))).
    apply E_Ass.
    auto.
    apply H in H1.
    unfold update in H1.
    simpl in H1.
    omega.
    apply H0.
    
Qed.

(*-- Check --*)
Check is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).

