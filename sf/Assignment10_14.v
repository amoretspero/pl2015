Require Export Assignment10_13.

(* problem #14: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 4 lines thanks to: 
     Hint Constructors aval
     Hint Constructors astep.
  
   You can use the following intro pattern:
     destruct ... as [[? ?] | [? ?]].
*)

Theorem aexp_strong_progress: forall st a,
  (exists n, a = ANum n) \/
  exists a', a / st ==>a a'.
Proof.
    intros.
    induction a.
    left.
    exists n.
    auto.
    right.
    exists (ANum (st i)).
    apply AS_Id.
    right.
    inversion IHa1.
    inversion H.
    rewrite H0.
    inversion IHa2.
    inversion H1.
    rewrite H2.
    exists (ANum (x + x0)).
    apply AS_Plus.
    inversion H1.
    exists (APlus (ANum x) x0).
    apply AS_Plus2.
    auto.
    apply H2.
    inversion H.
    inversion IHa2.
    inversion H1.
    rewrite H2.
    exists (APlus x (ANum x0)).
    apply AS_Plus1.
    apply H0.
    inversion H1.
    exists (APlus x a2).
    apply AS_Plus1.
    apply H0.
    
    right.
    inversion IHa1.
    inversion H.
    rewrite H0.
    inversion IHa2.
    inversion H1.
    rewrite H2.
    exists (ANum (x - x0)).
    apply AS_Minus.
    inversion H1.
    exists (AMinus (ANum x) x0).
    apply AS_Minus2.
    auto.
    apply H2.
    inversion H.
    inversion IHa2.
    inversion H1.
    rewrite H2.
    exists (AMinus x (ANum x0)).
    apply AS_Minus1.
    apply H0.
    inversion H1.
    exists (AMinus x a2).
    apply AS_Minus1.
    apply H0.

    right.
    inversion IHa1.
    inversion H.
    rewrite H0.
    inversion IHa2.
    inversion H1.
    rewrite H2.
    exists (ANum (mult x x0)).
    apply AS_Mult.
    inversion H1.
    exists (AMult (ANum x) x0).
    apply AS_Mult2.
    auto.
    apply H2.
    inversion H.
    inversion IHa2.
    inversion H1.
    rewrite H2.
    exists (AMult x (ANum x0)).
    apply AS_Mult1.
    apply H0.
    inversion H1.
    exists (AMult x a2).
    apply AS_Mult1.
    apply H0.
Qed.
(*-- Check --*)
Check aexp_strong_progress: forall st a,
  (exists n, a = ANum n) \/
  exists a', a / st ==>a a'.

