Require Export Assignment07_00.

(* problem #01: 20 points *)


(** **** Exercise: 3 stars (optimize_0plus_b)  *)
(** Since the [optimize_0plus] tranformation doesn't change the value
    of [aexp]s, we should be able to apply it to all the [aexp]s that
    appear in a [bexp] without changing the [bexp]'s value.  Write a
    function which performs that transformation on [bexp]s, and prove
    it is sound.  Use the tacticals we've just seen to make the proof
    as elegant as possible. *)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
    match b with
    | BTrue => BTrue
    | BFalse => BFalse
    | BEq a1 a2 => BEq a1 a2
    | BLe a1 a2 => BLe a1 a2
    | BNot b1 => BNot (optimize_0plus_b b1)
        (*match b1 with
        | BTrue => BFalse
        | BFalse => BTrue
        | BNot b2 => (optimize_0plus_b b2)
        | BEq a1 a2 => BNot (BEq a1 a2)
        | BLe a1 a2 => BNot (BLe a1 a2)
        | BAnd b2 b3 => BNot (BAnd (optimize_0plus_b b2) (optimize_0plus_b b3))
        end*)
    | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
    end.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
    intros b.
    induction b.
    Case "BTrue".
        simpl.
        reflexivity.
    Case "BFalse".
        simpl.
        reflexivity.
    Case "BEq".
        simpl.
        reflexivity.
    Case "BLe".
        simpl.
        reflexivity.
    Case "BNot".
        simpl.
        rewrite IHb.
        reflexivity.
    Case "BAnd".
        simpl.
        rewrite IHb1.
        rewrite IHb2.
        reflexivity.
Qed.
(** [] *)

