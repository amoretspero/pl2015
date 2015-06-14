Require Export Assignment10_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars, optional  *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
    intros.
    inversion H.
    induction n.
    exists st.
        unfold par_loop.
        split.
        apply multi_refl.
        auto.
    destruct IHn as [st' [A B]].
    inversion B.
    exists (update st' X (S n)).
        split.
        apply par_body_n__Sn in B.
        eapply multi_trans.
        apply A.
        apply B.
        split.
        unfold update.
        auto.
        unfold update.
        auto.
Qed.

(*-- Check --*)
Check par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.

