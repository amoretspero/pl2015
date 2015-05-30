Require Export Assignment09_04.

(* problem #05: 10 points *)

(** **** Exercise: 2 stars (if_minus_plus)  *)
(** Prove the following hoare triple using [hoare_if]: *)

Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 
Proof.
    remember (BLe (AId X) (AId Y)) as b.
    remember (fun st : state => st Y = st X + st Z) as q.
    remember (Z ::= AMinus (AId Y) (AId X)) as c1.
    remember (Y ::= APlus (AId X) (AId Z)) as c2.
    apply hoare_consequence_pre with (P' := fun st => (beval st b = true -> (q [Z |-> (AMinus (AId Y) (AId X))]) st) /\ (beval st b = false -> (q [Y |-> APlus (AId X) (AId Z)]) st)).
    apply hoare_if.
    subst.
    apply hoare_asgn.
    subst.
    apply hoare_asgn.
    unfold assert_implies.
    intros.
    split.
    intros.
    subst.
    unfold assn_sub.
    unfold update.
    simpl.
    symmetry.
    rewrite plus_comm.
    
    inversion H0.
    apply ble_nat_true in H2.
    omega.
    intros.
    subst.
    unfold assn_sub.
    unfold update.
    auto.
Qed.

(*-- Check --*)
Check if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 

