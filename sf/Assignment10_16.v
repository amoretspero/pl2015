Require Export Assignment10_15.

(* problem #16: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 6 lines thanks to:
     Hint Constructors cstep.
 
   You can use the following intro pattern:
     destruct ... as [ | [? [? ?]]].
*)

Theorem cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==>c c' / st'.
Proof.
    intros.
    induction c.
    left.
    auto.

    right.
    assert ((exists n, a = ANum n) \/ (exists a', a / st ==>a a')).
        apply aexp_strong_progress.
    inversion H.
    inversion H0.
    rewrite H1.
    exists SKIP.
    exists (update st i x).
    apply CS_Ass.
    inversion H0.
    exists (i ::= x).
    exists st.
    apply CS_AssStep.
    apply H1.

    inversion IHc1.
    inversion IHc2.
    right.
    rewrite H.
    exists c2.
    exists st.
    apply CS_SeqFinish.
    right.
    rewrite H.
    exists c2.
    exists st.
    apply CS_SeqFinish.
    inversion IHc2.
    inversion H.
    inversion H1.
    right.
    exists (x ;; c2).
    exists x0.
    apply CS_SeqStep.
    apply H2.
    inversion H.
    inversion H1.
    right.
    exists (x ;; c2).
    exists x0.
    apply CS_SeqStep.
    apply H2.

    assert (forall st b, ((b = BTrue) \/ (b = BFalse)) \/ (exists b', b / st ==>b b')).
        apply bexp_strong_progress.
    assert (((b = BTrue) \/ (b = BFalse)) \/ (exists b' : bexp, b / st ==>b b')).
        apply H.
    inversion IHc1.
    inversion IHc2.
    right.
    inversion H0.
    inversion H3.
    rewrite H4.
    exists c1.
    exists st.
    apply CS_IfTrue.
    rewrite H4.
    exists c2.
    exists st.
    apply CS_IfFalse.
    inversion H3.
    exists (IFB x THEN c1 ELSE c2 FI).
    exists st.
    apply CS_IfStep.
    apply H4.
    right.
    inversion H0.
    inversion H3.
    rewrite H4.
    exists c1.
    exists st.
    apply CS_IfTrue.
    rewrite H4.
    exists c2.
    exists st.
    apply CS_IfFalse.
    inversion H3.
    exists (IFB x THEN c1 ELSE c2 FI).
    exists st.
    apply CS_IfStep.
    apply H4.
    inversion IHc2.
    right.
    inversion H0.
    inversion H3.
    rewrite H4.
    exists c1.
    exists st.
    apply CS_IfTrue.
    rewrite H4.
    exists c2.
    exists st.
    apply CS_IfFalse.
    inversion H3.
    exists (IFB x THEN c1 ELSE c2 FI).
    exists st.
    apply CS_IfStep.
    apply H4.
    right.
    inversion H0.
    inversion H3.
    rewrite H4.
    exists c1.
    exists st.
    apply CS_IfTrue.
    rewrite H4.
    exists c2.
    exists st.
    apply CS_IfFalse.
    inversion H3.
    exists (IFB x THEN c1 ELSE c2 FI).
    exists st.
    apply CS_IfStep.
    apply H4.

    inversion IHc.
    right.
    exists (IFB b THEN (c;; (WHILE b DO c END)) ELSE SKIP FI).
    exists st.
    apply CS_While.
    right.
    exists (IFB b THEN (c;; (WHILE b DO c END)) ELSE SKIP FI).
    exists st.
    apply CS_While.

    inversion IHc1.
    inversion IHc2.
    right.
    rewrite H.
    rewrite H0.
    exists SKIP.
    exists st.
    apply CS_ParDone.
    right.
    inversion H0.
    inversion H1.
    exists (PAR c1 WITH x END).
    exists x0.
    apply CS_Par2.
    apply H2.
    inversion IHc2.
    right.
    inversion H.
    inversion H1.
    exists (PAR x WITH c2 END).
    exists x0.
    apply CS_Par1.
    apply H2.
    right.
    inversion H.
    inversion H1.
    exists (PAR x WITH c2 END).
    exists x0.
    apply CS_Par1.
    apply H2.   
Qed.

(*-- Check --*)
Check cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==>c c' / st'.

