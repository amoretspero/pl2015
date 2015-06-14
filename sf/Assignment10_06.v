Require Export Assignment10_05.

(* problem #06: 10 points *)

Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  unfold deterministic. unfold normal_form_of.  intros x y1 y2 P1 P2.
  inversion P1 as [P11 P12]; clear P1. inversion P2 as [P21 P22]; clear P2. 
  generalize dependent y2. 
  (* We recommend using this initial setup as-is! *)
  induction P11.
  intros.
  inversion P21.
  subst.
  auto.
  subst.
  apply ex_falso_quodlibet.
  apply P12.
  apply ex_intro with (x := y).
  apply H.
  intros.
  inversion P21.
  subst.
  apply ex_falso_quodlibet.
  apply P22.
  apply ex_intro with (x := y).
  apply H.
  subst.
  assert (y = y0) as eq.
    eapply step_deterministic_alt.
    apply H.
    apply H0.
  rewrite eq in *.
  inversion P21.
  subst.
  apply ex_falso_quodlibet.
  apply P22.
  apply ex_intro with (x := y0).
  apply H0.
  subst.
  assert (y0 = y1) as eq1.
    eapply step_deterministic_alt.
    apply H0.
    apply H2.
  rewrite eq1 in *.
  apply IHP11.
  apply P12.
  apply H1.
  apply P22.
Qed.
(*-- Check --*)
Check normal_forms_unique:
  deterministic normal_form_of.

