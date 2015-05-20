Require Export Assignment08_10.

(* problem #11: 10 points *)

(** **** Exercise: 2 stars (assign_aequiv)  *)
Lemma update_same : forall st X n,
    (update st X (st X)) n = st n.
Proof.
    intros.
    unfold update.
    destruct (eq_id_dec X n).
    rewrite e.
    auto.
    auto.
Qed.

(*Lemma update_same_2 : forall st X,
    update st X (st X) = st.
Proof.
    intros.*)
    
    

Theorem assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).
Proof.
    intros.
    split.
    intros.
    inversion H0.
    subst.
    unfold aequiv in H.
    assert (st' = update st' X (aeval st' e)).
        apply functional_extensionality.
        intros.
        rewrite <- H.
        simpl.
        symmetry.
        rewrite update_same.
        auto.
    rewrite H1 at 2.
    apply E_Ass.
    auto.
    intros.
    assert (st = st').
        apply functional_extensionality.
        inversion H0;
        subst.
        rewrite <- H.
        intros.
        symmetry.
        apply update_same.
    rewrite H1.
    apply E_Skip.
Qed.
       

(*-- Check --*)
Check assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).

