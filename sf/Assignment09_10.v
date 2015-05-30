Require Export Assignment09_09.

(* problem #10: 10 points *)

(** **** Exercise: 3 stars (two_loops)  *)
(** Here is a very inefficient way of adding 3 numbers:
  X ::= 0;;
  Y ::= 0;;
  Z ::= c;;
  WHILE X <> a DO
    X ::= X + 1;;
    Z ::= Z + 1
  END;;
  WHILE Y <> b DO
    Y ::= Y + 1;;
    Z ::= Z + 1
  END

    Show that it does what it should by filling in the blanks in the
    following decorated program.

    {{ True }} ->>
    {{                                        }}
  X ::= 0;;
    {{                                        }}
  Y ::= 0;;
    {{                                        }}
  Z ::= c;;
    {{                                        }}
  WHILE X <> a DO
      {{                                        }} ->>
      {{                                        }}
    X ::= X + 1;;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END;;
    {{                                        }} ->>
    {{                                        }}
  WHILE Y <> b DO
      {{                                        }} ->>
      {{                                        }}
    Y ::= Y + 1;;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END
    {{                                        }} ->>
    {{ Z = a + b + c }}
*)

Theorem add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.
Proof.
    intros.
    remember (X ::= ANum 0) as a1.
    remember (Y ::= ANum 0) as a2.
    remember (Z ::= ANum c) as a3.
    remember (BNot (BEq (AId X) (ANum a))) as b1.
    remember (BNot (BEq (AId Y) (ANum b))) as b2.
    remember (X ::= APlus (AId X) (ANum 1) ;; Z ::= APlus (AId Z) (ANum 1)) as c1.
    remember (Y ::= APlus (AId Y) (ANum 1) ;; Z ::= APlus (AId Z) (ANum 1)) as c2.
    apply hoare_seq with (Q := (fun st : state => (st X) = 0)).
    apply hoare_seq with (Q := (fun st : state => (st Y) = 0 /\ (st X) = 0)).
    apply hoare_seq with (Q := (fun st : state => (st Z) = c /\ (st Y) = 0 /\ (st X) = 0)).
    apply hoare_seq with (Q := (fun st : state => (st Z) = a + c /\ (st X) = a /\ (st Y) = 0)).
    apply hoare_consequence_pre with (P' := (fun st : state => (st Z) = a + (st Y) + c)).
    apply hoare_consequence_post with (Q' := (fun st : state => (fun st : state => st Z = a + (st Y) + c) st /\ beval st b2 = false)).
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
    omega.
    unfold assert_implies.
    intros.
    subst.
    inversion H.
    unfold beval in H1.
    apply negb_false in H1.
    apply beq_nat_true in H1.
    simpl in H1.
    omega.
    unfold assert_implies.
    intros.
    subst.
    inversion H.
    inversion H1.
    omega.
    apply hoare_consequence_pre with (P' := (fun st : state => (st Z) = c + (st X) /\ (st Y) = 0)).
    apply hoare_consequence_post with (Q' := (fun st : state => (fun st : state => st Z = c + st X /\ (st Y) = 0) st /\ beval st b1 = false)).
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
    omega.
    unfold assert_implies.
    intros.
    subst.
    inversion H.
    inversion H0.
    unfold beval in H1.
    apply negb_false in H1.
    apply beq_nat_true in H1.
    simpl in H1.
    omega.
    unfold assert_implies.
    intros.
    subst.
    inversion H.
    inversion H1.
    omega.
    unfold hoare_triple.
    intros.
    subst.
    inversion H.
    subst.
    unfold update.
    simpl.
    omega.
    unfold hoare_triple.
    intros.
    subst.
    inversion H.
    subst.
    unfold update.
    simpl.
    omega.
    unfold hoare_triple.
    intros.
    subst.
    inversion H.
    subst.
    unfold update.
    simpl.
    auto.
Qed.

(*-- Check --*)
Check add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.

