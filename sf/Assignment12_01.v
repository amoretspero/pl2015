Require Export Assignment12_00.

(* problem #01: 10 points *)

(** **** Exercise: 3 stars, optional (typing_nonexample_3)  *)
(** Another nonexample:
    ~ (exists S, exists T,
          empty |- \x:S. x x : T).
*)

Example typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).
Proof.
    unfold not.
    intros.
    inversion H.
    inversion H0.
    inversion H1.
    subst.
    inversion H7.
    subst.
    inversion H5.
    subst.
    inversion H8.
    subst.
    rewrite H4 in H6.
    inversion H6.
    induction T1.
    inversion H3.
    apply IHT1_1.
    rewrite H10 in *.
    apply H8.
    rewrite H9 in H8.
    apply H8.
    rewrite H9 in H4.
    apply H4.
    rewrite H9 in H6.
    apply H6.
    rewrite <- H10 in H9.
    apply H9.
    inversion H3.
    inversion H3.
    inversion H3.
    inversion H3.
    inversion H3.
Qed.

(*-- Check --*)
Check typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).

