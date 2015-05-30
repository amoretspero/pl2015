Require Export Assignment09_08.

(* problem #09: 10 points *)

(** **** Exercise: 4 stars (factorial)  *)
(** Recall that [n!] denotes the factorial of [n] (i.e. [n! =
    1*2*...*n]).  Here is an Imp program that calculates the factorial
    of the number initially stored in the variable [X] and puts it in
    the variable [Y]:
    {{ X = m }} 
  Y ::= 1 ;;
  WHILE X <> 0
  DO
     Y ::= Y * X ;;
     X ::= X - 1
  END
    {{ Y = m! }}

    Fill in the blanks in following decorated program:
    {{ X = m }} ->>
    {{                                      }}
  Y ::= 1;;
    {{                                      }}
  WHILE X <> 0
  DO   {{                                      }} ->>
       {{                                      }}
     Y ::= Y * X;;
       {{                                      }}
     X ::= X - 1
       {{                                      }}
  END
    {{                                      }} ->>
    {{ Y = m! }}
*)

Print fact.

Theorem factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.
Proof.
    intros.
    (*apply hoare_consequence_pre with (P' := (fun st : state => ble_nat 1 (st X) = true)).
    remember (fun st : state => ble_nat 1 (st X) = true) as p.*)
    remember (fun st : state => st X = m) as p.
    remember (fun st : state => st Y = fact m) as q.
    remember (Y ::= ANum 1) as c1.
    remember (BNot (BEq (AId X) (ANum 0))) as b.
    remember (Y ::= AMult (AId Y) (AId X);; X ::= AMinus (AId X) (ANum 1)) as c2.
    apply hoare_seq with (Q := (fun st => p st /\ st Y = 1)).
    remember (fun st : state => p st /\ st Y = 1) as p'.
    apply hoare_consequence_pre with (P' := (fun st : state => (fact (st X)) * (st Y) = fact m)).
    apply hoare_consequence_post with (Q' := (fun st => (fun st : state => (fact (st X) * (st Y) = fact m)) st /\ beval st b = false)).
    apply hoare_while.
    unfold hoare_triple.
    intros.
    subst.
    inversion H.
    subst.
    inversion H3.
    subst.
    inversion H6.
    subst.
    unfold update.
    simpl.
    inversion H0.
    unfold beval in H2.
    apply negb_true in H2.
    apply beq_nat_false in H2.
    rewrite <- H1.
    simpl in H2.
    rewrite mult_comm.
    symmetry.
    rewrite mult_comm.
    SearchAbout fact.
    assert (forall n, n <> 0 -> fact n = n * fact(n - 1)).
        intros.
        induction n.
        unfold not in H4.
        apply ex_falso_quodlibet.
        apply H4.
        auto.
        induction n.
        simpl.
        auto.
        auto.
    assert (H5 := H4 (st X)).
    apply H5 in H2.
    rewrite H2.
    rewrite mult_assoc.
    auto.
    unfold assert_implies.
    intros.
    subst.
    induction H.
    unfold beval in H0.
    apply negb_false in H0.
    apply beq_nat_true in H0.
    simpl in H0.
    rewrite H0 in H.
    simpl in H.
    rewrite plus_0_r in H.
    apply H.
    unfold assert_implies.
    intros.
    subst.
    inversion H.
    rewrite H0.
    rewrite H1.
    rewrite mult_comm.
    simpl.
    auto.
    unfold hoare_triple.
    intros.
    subst.
    split.
    inversion H.
    subst.
    unfold update.
    auto.
    inversion H.
    subst.
    unfold update.
    auto.
Qed.

(*-- Check --*)
Check factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.

