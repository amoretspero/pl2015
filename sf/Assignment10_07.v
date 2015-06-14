Require Export Assignment10_06.

(* problem #07: 10 points *)

(** **** Exercise: 2 stars (multistep_congr_2)  *)
Lemma multistep_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 ==>* t2' ->
     P t1 t2 ==>* P t1 t2'.
Proof.
    intros.
    induction H0.
    subst.
    inversion H.
    subst.
    apply multi_refl.
    subst.
    eapply multi_step.
    apply ST_Plus2.
    apply H.
    apply H0.
    apply IHmulti.
Qed.

(*-- Check --*)
Check multistep_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 ==>* t2' ->
     P t1 t2 ==>* P t1 t2'.

