Require Export Assignment05_17.

(* problem #18: 10 points *)





(** 1 star (gorgeous_plus13)  *)
Theorem gorgeous_plus13: forall n, 
  gorgeous n -> gorgeous (13+n).
Proof.
   intros n.
   intros H0.
   apply g_plus3 with (n := n) in H0.
   apply g_plus5 with (n := 3+n) in H0.
   apply g_plus5 with (n := (5 + (3 + n))) in H0.
   assert ((5 + (3 + n)) = (8 + n)).
       apply plus_assoc.
   rewrite H in H0.
   assert ((5 + (8 + n)) = (13 + n)).
       apply plus_assoc.
   rewrite H1 in H0.
   apply H0.
Qed.
(** [] *)




