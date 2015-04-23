Require Export Assignment06_04.

(* problem #05: 20 points *)

(** **** Exercise: 3 stars (all_forallb)  *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all {X : Type} (P : X -> Prop) : list X -> Prop :=
    | all_nil : all P []
    | all_cons x lst : P x -> all P lst -> all P (x :: lst)
.

(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)

Theorem forallb_correct: forall X (P: X -> bool) l,
  forallb P l = true <-> all (fun x => P x = true) l.
Proof.
    intros.
    split.
    intros H0.
    induction l.
    apply all_nil.
    apply all_cons.
    inversion H0.
    destruct (P x).
    rewrite H1.
    reflexivity.
    simpl.
    reflexivity.
    apply IHl.
    simpl in H0.
    assert (forall (b1 b2 : bool), andb b1 b2 = andb b2 b1).
        intros b1 b2.
        induction b1.
        simpl.
        induction b2.
        simpl.
        reflexivity.
        simpl.
        reflexivity.
        simpl.
        induction b2.
        simpl.
        reflexivity.
        simpl.
        reflexivity.
    assert (forall (b1 b2 : bool), andb b1 b2 = true -> b2 = true).
        intros.
        destruct b2.
        reflexivity.
        rewrite <- H1.
        symmetry.
        apply H.
    apply H1 in H0.
    apply H0.
    intros.
    induction H.
    simpl.
    reflexivity.
    simpl.
    rewrite H.
    rewrite IHall.
    simpl.
    reflexivity.
Qed.

(** [] *)

