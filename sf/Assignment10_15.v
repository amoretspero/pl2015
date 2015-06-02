Require Export Assignment10_14.

(* problem #15: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 7 lines thanks to:. 
     Hint Constructors bstep.

   You can use the following intro pattern:
     destruct ... as [[? | ?] | [? ?]].
*)

Theorem bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.
Proof.
    intros.
    induction b.
    auto.
    auto.
    assert ((exists n, a = ANum n) \/ (exists a', a / st ==>a a')).
        apply aexp_strong_progress.
    assert ((exists n0, a0 = ANum n0) \/ (exists a0', a0 / st ==>a a0')).
        apply aexp_strong_progress.
    right.
    inversion H.
    inversion H0.
    inversion H1.
    inversion H2.
    rewrite H3.
    rewrite H4.
    exists ((if (beq_nat x x0) then BTrue else BFalse)).
    apply BS_Eq.
    inversion H1.
    inversion H2.
    rewrite H3.
    exists (BEq (ANum x) x0).
    apply BS_Eq2.
    auto.
    auto.
    inversion H0.
    inversion H1.
    inversion H2.
    rewrite H4.
    exists (BEq x (ANum x0)).
    apply BS_Eq1.
    apply H3.
    inversion H1.
    inversion H2.
    exists (BEq x a0).
    apply BS_Eq1.
    auto.

    assert ((exists n, a = ANum n) \/ (exists a', a / st ==>a a')).
        apply aexp_strong_progress.
    assert ((exists n0, a0 = ANum n0) \/ (exists a0', a0 / st ==>a a0')).
        apply aexp_strong_progress.
    right.
    inversion H.
    inversion H0.
    inversion H1.
    inversion H2.
    rewrite H3.
    rewrite H4.
    exists ((if (ble_nat x x0) then BTrue else BFalse)).
    apply BS_LtEq.
    inversion H1.
    inversion H2.
    rewrite H3.
    exists (BLe (ANum x) x0).
    apply BS_LtEq2.
    auto.
    auto.
    inversion H0.
    inversion H1.
    inversion H2.
    rewrite H4.
    exists (BLe x (ANum x0)).
    apply BS_LtEq1.
    apply H3.
    inversion H1.
    inversion H2.
    exists (BLe x a0).
    apply BS_LtEq1.
    auto.
    
    inversion IHb.
    inversion H.
    rewrite H0.
    right.
    exists BFalse.
    apply BS_NotTrue.
    right.
    exists BTrue.
    rewrite H0.
    apply BS_NotFalse.
    inversion H.
    right.
    exists (BNot x).
    apply BS_NotStep.
    apply H0.
    
    right.
    inversion IHb1.
    inversion IHb2.
    inversion H.
    inversion H0.
    rewrite H1.
    rewrite H2.
    exists BTrue.
    apply BS_AndTrueTrue.
    rewrite H1.
    rewrite H2.
    exists BFalse.
    apply BS_AndTrueFalse.
    rewrite H1.
    exists BFalse.
    apply BS_AndFalse.
    inversion H.
    inversion H0.
    rewrite H1.
    exists (BAnd BTrue x).
    apply BS_AndTrueStep.
    apply H2.
    rewrite H1.
    exists BFalse.
    apply BS_AndFalse.
    inversion IHb2.
    inversion H.  
    exists (BAnd x b2).
    apply BS_AndStep.
    apply H1.
    inversion H.
    exists (BAnd x b2).
    apply BS_AndStep.
    apply H1.
Qed.

(*-- Check --*)
Check bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.

