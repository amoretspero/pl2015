Require Export Assignment07_04.

(* problem #05: 10 points *)

(** **** Exercise: 1 star (update_eq)  *)
Theorem update_eq : forall n x st,
  (update st x n) x = n.
Proof.
    intros.
    unfold update.
    destruct eq_id_dec.
    reflexivity.
    unfold not in n0.
    induction x.
    induction st.
    apply ex_falso_quodlibet.
    apply n0.
    reflexivity.
    rewrite IHst.
    apply ex_falso_quodlibet.
    apply n0.
    reflexivity.
    
Qed.
(** [] *)

