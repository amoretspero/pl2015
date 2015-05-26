Require Export Assignment08_16.

(* problem #17: 10 points *)

Lemma optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.
Proof.
    unfold btrans_sound.
    intros.
    unfold bequiv.
    intros.
    induction b;
    simpl;
    try reflexivity;
    simpl;
    try rewrite <- optimize_0plus_aexp_sound;
    try rewrite <- optimize_0plus_aexp_sound;
    try rewrite <- IHb;
    try rewrite <- IHb1;
    try rewrite <- IHb2;
    auto.
Qed.

(*-- Check --*)
Check optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.

