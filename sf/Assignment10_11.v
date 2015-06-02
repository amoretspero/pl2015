Require Export Assignment10_10.

(* problem #11: 10 points *)

(** **** Exercise: 3 stars, optional (interp_tm)  *)
(** Remember that we also defined big-step evaluation of [tm]s as a
    function [evalF].  Prove that it is equivalent to the existing
    semantics.
 
    Hint: we just proved that [eval] and [multistep] are
    equivalent, so logically it doesn't matter which you choose.
    One will be easier than the other, though!  *)

Theorem evalF_eval : forall t n,
  evalF t = n <-> t || n.
Proof.
    intro t.
    induction t.
    split.
    intros.
    simpl in H.
    rewrite H.
    apply E_Const.
    intros.
    inversion H.
    subst.
    auto.
    intros.
    split.
    intros.
    rewrite <- H.
    simpl.
    constructor.
    apply IHt1.
    auto.
    apply IHt2.
    auto.
    intros.
    simpl.
    inversion H.
    subst.
    apply IHt1 in H2.
    apply IHt2 in H4.
    auto.
Qed.

(*-- Check --*)
Check evalF_eval : forall t n,
  evalF t = n <-> t || n.

