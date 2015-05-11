Require Export Assignment07_02.

(* problem #03: 20 points *)

(** **** Exercise: 3 stars  (bevalR)  *)
(** Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval].*)


Inductive bevalR: bexp -> bool -> Prop :=
    | E_BTrue : (bevalR BTrue true)
    | E_BFalse : (bevalR BFalse false)
    | E_BEq : forall (aexp1 aexp2 : aexp) (n1 n2 : nat),
        (aexp1 || n1) -> (aexp2 || n2) -> (bevalR (BEq aexp1 aexp2) (beq_nat n1 n2))
    | E_BLe : forall (aexp1 aexp2 : aexp) (n1 n2 : nat),
        (aexp1 || n1) -> (aexp2 || n2) -> (bevalR (BLe aexp1 aexp2) (ble_nat n1 n2))
    | E_BNot : forall (bexp1 : bexp) (b1 : bool),
        ((beval bexp1) = b1) -> (bevalR (BNot bexp1) (negb b1))
    | E_BAnd : forall (bexp1 bexp2 : bexp) (b1 b2 : bool),
        ((beval bexp1) = b1) -> ((beval bexp2) = b2) -> (bevalR (BAnd bexp1 bexp2) (andb b1 b2))
.

Theorem beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
    intros.
    split.
    induction b;
        (*try simpl;*)
        try intros;
        try inversion H;
        try reflexivity.
        subst;
        apply aeval_iff_aevalR in H2;
        apply aeval_iff_aevalR in H4;
        simpl;
        rewrite <- H2 in *;
        rewrite <- H4 in *;
        reflexivity;
        inversion H.
        subst.
        apply aeval_iff_aevalR in H2.
        apply aeval_iff_aevalR in H4.
        simpl.
        auto.
        subst.
        simpl.
        reflexivity.
        subst.
        simpl.
        reflexivity.
    induction b.
        try intros;
        try simpl in H;
        try rewrite <- H;
        try apply E_BTrue.
        intros.
        simpl in H.
        rewrite <- H.
        apply E_BFalse.
        intros.
        simpl in H.
        rewrite <- H.
        apply E_BEq.
        apply aeval_iff_aevalR.
        reflexivity.
        apply aeval_iff_aevalR.
        reflexivity.
        intros.
        simpl in H.
        rewrite <- H.
        apply E_BLe.
        apply aeval_iff_aevalR.
        reflexivity.
        apply aeval_iff_aevalR.
        reflexivity.
        intros.
        simpl in H.
        rewrite <- H.
        apply E_BNot.
        reflexivity.
        intros.
        simpl in H.
        rewrite <- H.
        apply E_BAnd.
        reflexivity.
        reflexivity.
Qed.

(** [] *)

