Require Export Assignment05_37.

(* problem #38: 10 points *)

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.                               
Proof.
    (* Hint: This theorem can be easily proved without using [induction]. *)
    intros.
    apply ble_nat_true with (n := m) (m := o) in H0.
    apply ble_nat_true with (n := n) (m := m) in H.
    apply le_ble_nat with (n := n) (m := o).
    apply le_trans with (n := m) (m := n) (o := o).
    apply H.
    apply H0.
Qed.

