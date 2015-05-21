Require Export Assignment08_15.

(* problem #16: 10 points *)
    

Lemma optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.

    unfold atrans_sound.
    intros.
    unfold aequiv.
    intros.
    induction a;
        try (
        simpl;
        auto).
        destruct a1;
        try destruct n; try auto;
        destruct a2;
        try destruct n0; try auto;
        try rewrite IHa1;
        try rewrite IHa2;
        auto;
        destruct n;
        try rewrite <- IHa1;
        try rewrite <- IHa2;
        auto;
        rewrite IHa1;
        rewrite IHa2;
        auto.
Qed.

(*-- Check --*)
Check optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.

