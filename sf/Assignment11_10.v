Require Export Assignment11_09.

(* problem #10: 30 points *)

(** Write a type checking function [tyeq: tm -> ty -> bool].
**)

Fixpoint tycheck (t: tm) (T: ty) : bool :=
    match t with
    | ttrue => 
        match T with
        | TBool => true
        | _ => false
        end
    | tfalse =>
        match T with
        | TBool => true
        | _ => false
        end
    | tif t1 t2 t3 =>
        (andb (tycheck t1 TBool) (andb (tycheck t2 T) (tycheck t3 T)))
    | tzero =>
        match T with
        | TNat => true
        | _ => false
        end
    | tsucc t1 =>
        match T with
        | TNat => (tycheck t1 TNat)
        | _ => false
        end
    | tpred t1 =>
        match T with
        | TNat => (tycheck t1 TNat)
        | _ => false
        end
    | tiszero t1 =>
        match T with
        | TBool => (tycheck t1 TNat)
        | _ => false
        end
    end.

Example tycheck_ex1:
  tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
    TBool 
  = true.
Proof. 
    auto.
Qed.

Example tycheck_ex2:
  tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
    TBool 
  = false.
Proof.
    auto.
Qed.

(** Prove that the type checking function [tyeq: tm -> ty -> bool] is correct.

    Hint: use the lemma [andb_prop].
**)

Check andb_prop.

Theorem tycheck_correct1: forall t T
    (TYCHK: tycheck t T = true),
  |- t \in T.
Proof.
    intros.
    generalize dependent T.
    induction t.
    intros.
    induction T.
    auto.
    inversion TYCHK.
    intros.
    induction T.
    auto.
    inversion TYCHK.
    intros.
    induction T.
    inversion TYCHK.
    apply andb_prop in H0.
    inversion H0.
    apply andb_prop in H1.
    inversion H1.
    clear H1.
    constructor.
    apply IHt1.
    apply H.
    apply IHt2.
    apply H2.
    apply IHt3.
    apply H3.
    inversion TYCHK.
    apply andb_prop in H0.
    inversion H0.
    apply andb_prop in H1.
    inversion H1.
    clear H1.
    constructor.
    apply IHt1.
    apply H.
    apply IHt2.
    apply H2.
    apply IHt3.
    apply H3.
    intros.
    induction T.
    inversion TYCHK.
    auto.
    intros.
    induction T.
    inversion TYCHK.
    auto.
    intros.
    induction T.
    inversion TYCHK.
    auto.
    intros.
    induction T.
    auto.
    inversion TYCHK.
Qed.

Theorem tycheck_correct2: forall t T
    (HASTY: |- t \in T),
  tycheck t T = true.
Proof.
    intros.
    generalize dependent T.
    induction t.
    intros.
    induction T.
    auto.
    inversion HASTY.
    intros.
    induction T.
    auto.
    inversion HASTY.
    intros.
    induction T.
    inversion HASTY.
    subst.
    apply IHt1 in H2.
    apply IHt2 in H4.
    apply IHt3 in H5.
    simpl.
    rewrite H2.
    rewrite H4.
    rewrite H5.
    auto.
    inversion HASTY.
    subst.
    apply IHt1 in H2.
    apply IHt2 in H4.
    apply IHt3 in H5.
    simpl.
    rewrite H2.
    rewrite H4.
    rewrite H5.
    auto.
    intros.
    induction T.
    inversion HASTY.
    auto.
    intros.
    induction T.
    inversion HASTY.
    inversion HASTY.
    subst.
    apply IHt in H0.
    auto.
    intros.
    induction T.
    inversion HASTY.
    inversion HASTY.
    subst.
    apply IHt in H0.
    auto.
    intros.
    induction T.
    inversion HASTY.
    subst.
    apply IHt in H0.
    auto.
    inversion HASTY.
Qed.
(*-- Check --*)

Check (conj tycheck_ex1 tycheck_ex2 :
 (tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
    TBool 
  = true)
 /\
 (tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
    TBool 
  = false)).

Check tycheck_correct1: forall t T
    (TYCHK: tycheck t T = true),
  |- t \in T.

Check tycheck_correct2: forall t T
    (HASTY: |- t \in T),
  tycheck t T = true.
