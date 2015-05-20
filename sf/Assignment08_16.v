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
        simpl;
        try (
        reflexivity;
        apply refl_aequiv;
        destruct (optimize_0plus_aexp a1);
        destruct (optimize_0plus_aexp a2);
        rewrite IHa1;
        rewrite IHa2;
        reflexivity).
        destruct n.
        destruct n0.
        auto.
        auto.
        destruct n0.
        auto.
        auto.
        simpl.
        destruct n.
        auto.
        auto.
        
        simpl.
        try (
        rewrite <- IHa1;
        simpl;
        rewrite <- IHa2;
        reflexivity).
        rewrite <- IHa1.
        simpl.
        auto;
        rewrite <- IHa1;
        rewrite <- IHa2;
        auto).
        
        remember (optimize_0plus_aexp a1) as oa_a1.
        remember (optimize_0plus_aexp a2) as oa_a2.
        
        
Qed.

(*-- Check --*)
Check optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.

