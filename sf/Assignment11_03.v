Require Export Assignment11_02.

(* problem #03: 10 points *)

(** **** Exercise: 3 stars, optional (step_deterministic)  *)
(** Using [value_is_nf], we can show that the [step] relation is
    also deterministic... *)

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
    unfold deterministic.
    intros.
    generalize dependent y2.
    induction H.
    intros.
    inversion H0.
    subst.
    auto.
    subst.
    inversion H4.
    intros.
    inversion H0.
    subst.
    auto.
    subst.
    inversion H4.
    intros.
    inversion H0.
    subst.
    inversion H.
    subst.
    inversion H.
    subst.
    apply IHstep in H5.
    rewrite H5.
    auto.
    intros.
    inversion H0.
    subst.
    apply IHstep in H2.
    rewrite H2.
    auto.
    intros.
    inversion H0.
    auto.
    subst.
    inversion H1.
    intros.
    assert (value t1).
        right.
        apply H.
    apply value_is_nf in H1.
    unfold normal_form in H1.
    unfold not in H1.
    inversion H0.
    auto.
    subst.
    assert (value (tsucc t1)).
        right.
        auto.
    apply value_is_nf in H2.
    unfold normal_form in H2.
    unfold not in H2.
    apply ex_falso_quodlibet.
    apply H2.
    exists (t1').
    apply H3.
    intros.
    inversion H0.
    subst.
    inversion H.
    subst.
    assert (value (tsucc y2)).
        right.
        auto.
    apply value_is_nf in H1.
    unfold normal_form in H1.
    unfold not in H1.
    apply ex_falso_quodlibet.
    apply H1.
    exists t1'.
    apply H.
    subst.
    apply IHstep in H2.
    rewrite H2.
    auto.
    intros.
    inversion H0.
    auto.
    subst.
    inversion H1.
    intros.
    inversion H0.
    auto.
    subst.
    assert (value (tsucc t1)).
        right.
        auto.
    apply value_is_nf in H1.
    unfold normal_form in H1.
    unfold not in H1.
    apply ex_falso_quodlibet.
    apply H1.
    exists t1'.
    apply H2.
    intros.
    inversion H0.
    subst.
    inversion H.
    subst.
    assert (value (tsucc t0)).
        right.
        auto.
    apply value_is_nf in H1.
    unfold normal_form in H1.
    unfold not in H1.
    apply ex_falso_quodlibet.
    apply H1.
    exists t1'.
    apply H.
    subst.
    apply IHstep in H2.
    rewrite H2.
    auto.
Qed.
(*-- Check --*)
Check step_deterministic:
  deterministic step.

