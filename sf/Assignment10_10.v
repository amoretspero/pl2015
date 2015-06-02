Require Export Assignment10_09.

(* problem #10: 10 points *)

(** The fact that small-step reduction implies big-step is now
    straightforward to prove, once it is stated correctly. 

    The proof proceeds by induction on the multi-step reduction
    sequence that is buried in the hypothesis [normal_form_of t t']. *)
(** Make sure you understand the statement before you start to
    work on the proof.  *)

(** **** Exercise: 3 stars (multistep__eval)  *)

Lemma multistep_const : forall t1 n, C n ==>* t1 -> t1 = C n.
Proof.
    intros.
    inversion H.
    subst.
    auto.
    subst.
    inversion H0.
Qed.

(*Lemma evalf_plus : forall t1 t2, *)

(*Lemma evalf_same : forall t1 t2, t1 ==>* t2 -> t2 = C (evalF t1).
Proof.
    intros.
    SearchAbout 
    induction t1.
    simpl.
    apply multistep_const.
    apply H.
    simpl.    
    inversion H.
    subst.
    induction H.*)

Theorem strong_progress : forall t,
  value t \/ (exists t', t ==> t').
Proof.  
  tm_cases (induction t) Case.
    Case "C". left. apply v_const.
    Case "P". right. inversion IHt1.
      SCase "l". inversion IHt2.
        SSCase "l". inversion H. inversion H0.
          exists (C (n + n0)).
          apply ST_PlusConstConst.
        SSCase "r". inversion H0 as [t' H1].
          exists (P t1 t').
          apply ST_Plus2. apply H. apply H1.
      SCase "r". inversion H as [t' H0]. 
          exists (P t' t2).
          apply ST_Plus1. apply H0.  Qed.


Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof. (* a corollary of [strong_progress]... *)
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t ==> t').
    SCase "Proof of assertion". apply strong_progress.
  inversion G.
    SCase "l". apply H0.
    SCase "r". apply ex_falso_quodlibet. apply H. assumption.  Qed.

Lemma value_is_nf : forall t,
  value t -> normal_form step t.
Proof.
  unfold normal_form. intros t H. inversion H.
  intros contra. inversion contra. inversion H1.
Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split. apply nf_is_value. apply value_is_nf. Qed.
    



Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t || n.
Proof.
    unfold normal_form_of.
    intros t v [ms nf].
    induction ms.
    apply nf_is_value in nf.
    inversion nf.
    apply ex_intro with (x := n).
    split.
    reflexivity.
    constructor.
    apply IHms in nf.
    destruct nf as [n [A B]].
    apply ex_intro with (x := n).
    split.
    assumption.
    eapply step__eval.
    apply H.
    apply B.
    
Qed.

(*-- Check --*)
Check multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t || n.

