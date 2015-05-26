Require Export Assignment08_17.

(* problem #18: 10 points *)

Lemma optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.
Proof.
    unfold ctrans_sound.
    intros.
    induction c.
    simpl.
    apply refl_cequiv.
    apply CAss_congruence.
    apply optimize_0plus_aexp_sound.
    simpl.
    apply CSeq_congruence.
    apply IHc1.
    apply IHc2.
    apply CIf_congruence.
    apply optimize_0plus_bexp_sound.
    auto.
    auto.
    apply CWhile_congruence.
    apply optimize_0plus_bexp_sound.
    auto.
Qed.

(*-- Check --*)
Check optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.

