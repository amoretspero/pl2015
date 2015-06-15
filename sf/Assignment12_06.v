Require Export Assignment12_05.

(* problem #06: 10 points *)

Notation Loop_step1 := (tapp tloop (tnat 0)).
Notation Loop_step2 := (tapp
  (tapp
     (tabs Loop (TArrow TNat TNat) (tabs X TNat (tapp (tvar Loop) (tvar X))))
     (tfix
        (tabs Loop (TArrow TNat TNat)
           (tabs X TNat (tapp (tvar Loop) (tvar X)))))) (tnat 0)).
Notation Loop_step3 := (tapp
  ([Loop
   := tfix
        (tabs Loop (TArrow TNat TNat)
           (tabs X TNat (tapp (tvar Loop) (tvar X))))]
   tabs X TNat (tapp (tvar Loop) (tvar X))) (tnat 0)).

Inductive multi_n_step : tm -> nat -> tm -> Prop :=
    | zero_step : forall t, multi_n_step t 0 t
    | succ_step : forall n t0 t1 t2, 
        t0 ==> t1 -> multi_n_step t1 n t2 -> multi_n_step t0 (S n) t2.

Lemma multi_n_step_exists : forall t1 t2,
    t1 ==>* t2 -> exists n, (multi_n_step t1 n t2).
Proof.
    intros.
    induction H.
    exists 0.
    constructor.
    inversion IHmulti.
    exists (S x0).
    apply succ_step with (t1 := y).
    apply H.
    apply H1.
Qed.
    

Lemma loop_three : forall x n,
    multi_n_step Loop_step1 n x \/ multi_n_step Loop_step2 n x \/ multi_n_step Loop_step3 n x
        -> x = Loop_step1 \/ x = Loop_step2 \/ x = Loop_step3.
Proof.
    intros.
    generalize dependent x.
    induction n.
    intros.
    inversion H.
    inversion H0.
    left; auto.
    inversion H0.
    inversion H1.
    subst.
    auto.
    inversion H1.
    subst.
    auto.
    intros.
    inversion H.
    inversion H0.
    subst.
    assert (t1 = Loop_step2).
        inversion H2.
        subst.
        inversion H6.
        subst.
        inversion H3.
        subst.
        inversion H5.
        subst.
        inversion H7.
        subst.
        auto.
    rewrite H1 in H4.
    assert (multi_n_step Loop_step1 n x \/ multi_n_step Loop_step2 n x \/ multi_n_step Loop_step3 n x).
        auto.
    apply IHn in H3.
    apply H3.
    inversion H0.
    inversion H1.
    subst.
    assert (t1 = Loop_step3).
        inversion H3.
        subst.
        inversion H7.
        subst.
        inversion H10.
        subst.
        auto.
        inversion H8.
        subst.
        inversion H9.
        subst.
        inversion H4.
        subst.
        inversion H8.
    rewrite H2 in H5.
    assert (multi_n_step Loop_step1 n x \/ multi_n_step Loop_step2 n x \/ multi_n_step Loop_step3 n x).
        auto.
    apply IHn in H4.
    apply H4.
    inversion H1.
    subst.
    assert (t1 = Loop_step1).
        inversion H3.
        subst.
        auto.
        subst.
        inversion H7.
        subst.
        inversion H8.
    rewrite H2 in H5.
    assert (multi_n_step Loop_step1 n x \/ multi_n_step Loop_step2 n x \/ multi_n_step Loop_step3 n x).
        auto.
    apply IHn in H4.
    auto.
Qed.

Lemma loop_one : forall x,
    Loop_step1 ==>* x -> x = Loop_step1 \/ x = Loop_step2 \/ x = Loop_step3.
Proof.
    intros.
    apply multi_n_step_exists in H.
    inversion H.
    inversion H0.
    subst.
    left; auto.
    subst.
    apply loop_three with (n := (S n)).
    left; auto.
Qed.

Theorem tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.
Proof.
    unfold not.
    intros.
    inversion H.
    unfold normal_form in H0.
    inversion H0.
    unfold not in H2.
    apply H2.
    apply loop_one in H1.
    inversion H1.
    exists Loop_step2.
    rewrite H3.
    eapply ST_AppFix.
    constructor.
    constructor.
    inversion H3.
    exists Loop_step3.
    rewrite H4.
    eapply ST_App1.
    auto.
    rewrite H4.
    exists Loop_step1.
    apply ST_AppAbs.
    constructor.
Qed.

(*-- Check --*)
Check tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.

