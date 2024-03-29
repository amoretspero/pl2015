Require Export Assignment07_09.

(* problem #10: 10 points *)

(** **** Exercise: 3 stars (update_permute)  *)
Theorem update_permute : forall n1 n2 x1 x2 x3 st,
  x2 <> x1 -> 
  (update (update st x2 n1) x1 n2) x3 = (update (update st x1 n2) x2 n1) x3.
Proof.
    intros.
    unfold update at 1.
    unfold update at 2.
    destruct eq_id_dec.
    destruct eq_id_dec.
    rewrite <- e0 in e.
    unfold not in H.
    symmetry in e.
    apply H in e.
    inversion e.
    unfold update.
    destruct eq_id_dec.
    reflexivity.
    unfold not in n0.
    apply n0 in e.
    inversion e.
    unfold update at 1.
    destruct eq_id_dec.
    reflexivity.
    unfold update.
    destruct eq_id_dec.
    unfold not in n.
    apply n in e.
    inversion e.
    reflexivity.
Qed.
(** [] *)

