Require Export Assignment05_19.

(* problem #20: 10 points *)








(** 3 stars, advanced (beautiful__gorgeous)  *)
Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
    intros.
    induction H.
    apply g_0.
    apply g_plus3 with (n := 0).
    apply g_0.
    apply g_plus5 with (n := 0).
    apply g_0.
    apply gorgeous_sum with (n := n) (m := m).
    apply IHbeautiful1.
    apply IHbeautiful2.
Qed.
(** [] *)




