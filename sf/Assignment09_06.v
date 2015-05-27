Require Export Assignment09_05.

(* problem #06: 10 points *)

(** **** Exercise: 2 stars (slow_assignment)  *)
(** A roundabout way of assigning a number currently stored in [X] to
    the variable [Y] is to start [Y] at [0], then decrement [X] until
    it hits [0], incrementing [Y] at each step. Here is a program that
    implements this idea:
      {{ X = m }}
    Y ::= 0;;
    WHILE X <> 0 DO
      X ::= X - 1;;
      Y ::= Y + 1
    END
      {{ Y = m }} 
    Write an informal decorated program showing that this is correct. *)

Theorem slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
Proof.
    intros.
    remember (fun st : state => st X = m) as p.
    remember (fun st : state => st Y = m) as q.
    remember (Y ::= ANum 0) as c1.
    remember (BNot (BEq (AId X) (ANum 0))) as b.
    remember ((X ::= AMinus (AId X) (ANum 1));; (Y ::= APlus (AId Y) (ANum 1))) as c2.
    apply hoare_seq with (Q := (fun st : state => st X + st Y = m)).
    apply hoare_consequence_post with (Q' := (fun st => (fun st : state => st X + st Y = m) st /\ beval st b = false)).
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
    inversion H2.
    apply negb_true in H5.
    apply beq_nat_false in H5.
    omega.
    unfold assert_implies.
    intros.
    subst.
    inversion H.
    inversion H1.
    apply negb_false in H3.
    apply beq_nat_true in H3.
    rewrite H3 in H0.
    auto.
    unfold hoare_triple.
    intros.
    subst.
    inversion H.
    unfold update.
    simpl.
    subst.
    auto.
Qed.

(*-- Check --*)
Check slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
  
