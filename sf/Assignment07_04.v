Require Export Assignment07_03.

(* problem #04: 10 points *)

(** **** Exercise: 1 star, optional (neq_id)  *)
Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> 
               (if eq_id_dec x y then p else q) = q. 
Proof.
    intros.
    unfold not in H.
    destruct eq_id_dec.
    apply H in e.
    inversion e.
    reflexivity.
Qed.
(** [] *)


