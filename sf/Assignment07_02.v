Require Export Assignment07_01.

(* problem #02: 10 points *)

Fixpoint optimize_1mult (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus e1 e2 =>
      APlus (optimize_1mult e1) (optimize_1mult e2)
  | AMinus e1 e2 =>
      AMinus (optimize_1mult e1) (optimize_1mult e2)
  | AMult (ANum 1) e2 =>
      optimize_1mult e2
  | AMult e1 (ANum 1) =>
      optimize_1mult e1
  | AMult e1 e2 =>
      AMult (optimize_1mult e1) (optimize_1mult e2)
  end.

(** Hint:
    If you use the tacticals [;], [try] and [omega] well,
    you can prove the following theorem in 5 lines.
 **)

Theorem optimize_1mult_sound: forall a,
  aeval (optimize_1mult a) = aeval a.
Proof.
    intros a.
    induction a.
    Case "ANum".
        simpl.
        reflexivity.
    Case "APlus".
        simpl.
        rewrite IHa1.
        rewrite IHa2.
        reflexivity.
    Case "AMinus".
        simpl.
        rewrite IHa1.
        rewrite IHa2.
        reflexivity.
    Case "AMult".
        destruct a1.
        destruct a2.
        destruct n.
        simpl.
        destruct n0.
        reflexivity.
        destruct n0.
        reflexivity.
        reflexivity.
        destruct n.
        simpl.
        rewrite plus_0_r.
        reflexivity.
        simpl.
        destruct n0.
        simpl.
        reflexivity.
        destruct n0.
        simpl.
        omega.
        simpl.
        reflexivity.
        simpl.
        destruct n.
        simpl.
        reflexivity.
        destruct n.
        simpl.
        rewrite plus_0_r.
            simpl in IHa2.
            rewrite IHa2.
            reflexivity.
            simpl.
            simpl in IHa2.
            rewrite IHa2.
            reflexivity.
        simpl.
        destruct n.
        simpl.
        reflexivity.
        destruct n.
        simpl.
        rewrite plus_0_r.
            simpl in IHa2.
            rewrite IHa2.
            reflexivity.
            simpl.
            simpl in IHa2.
            rewrite IHa2.
            reflexivity.
        destruct n.
        simpl.
        reflexivity.
        destruct n.
        simpl in *.
        rewrite IHa2.
        omega.
        simpl in *.
        rewrite IHa2.
        omega.
        destruct a2.
        destruct n.
        simpl.
        omega.
        destruct n.
        simpl in *.
        rewrite IHa1.
        omega.
        simpl.
        simpl in *.
        rewrite IHa1.
        omega.
        simpl in *.
        auto.
        simpl in *.
        auto.
        simpl in *.
        auto.
        destruct a2.
        destruct n.
        simpl.
        omega.
        destruct n.
        simpl in *.
        rewrite IHa1.
        omega.
        simpl.
        simpl in *.
        rewrite IHa1.
        omega.
        simpl in *.
        auto.
        simpl in *.
        auto.
        simpl in *.
        auto.
        destruct a2.
        destruct n.
        simpl.
        auto.
        destruct n.
        simpl in *.
        rewrite IHa1.
        omega.
        simpl.
        auto.
        simpl in *.
        auto.
        simpl in *.
        auto.
        simpl in *.
        auto.
Qed.

