Require Export Assignment12_04.

(* problem #05: 20 points *)

(** Translate this informal recursive definition into one using [fix]:
<<
   halve = 
     \x:Nat. 
        if x=0 then 0 
        else if (pred x)=0 then 0
        else 1 + (halve (pred (pred x))))
>>
*)

Definition halve : tm :=
    tfix (tabs Halve (TArrow TNat TNat) 
        (tabs X TNat (tif0 (tvar X) (tnat 0) 
            (tif0 (tpred (tvar X)) (tnat 0) (tsucc (tapp (tvar Halve) (tpred (tpred (tvar X))))))))).

Example halve_type: empty |- halve \in TArrow TNat TNat.
Proof.
  unfold halve; eauto 10.
  (* unfold halve; eauto 10. *)
Qed.

Example halve_10: tapp halve (tnat 10) ==>* tnat 5.
Proof.
  unfold halve; normalize.
  (* unfold halve; normalize. *)
Qed.

Example halve_11: tapp halve (tnat 11) ==>* tnat 5.
Proof.
  unfold halve; normalize.
  (* unfold halve; normalize. *)
Qed.

Lemma lem_f1 : forall t1 t2,
    t1 ==>* t2 -> tsucc t1 ==>* tsucc t2.
Proof.
    intros.
    induction H.
    constructor.
    eapply multi_step.
    constructor.
    apply H.
    apply IHmulti.
Qed.


Theorem halve_correct: forall n,
   tapp halve (tnat (n+n)) ==>* tnat n.
Proof.
    intros.
    induction n.
    simpl.
    unfold halve; normalize.
    unfold halve.
    eapply multi_step.
    eapply ST_AppFix.
    eauto.
    eauto.
    eapply multi_step.
    eapply ST_App1.
    eauto.
    simpl.
    eapply multi_step.
    eapply ST_AppAbs.
    eauto.
    simpl.
    eapply multi_step.
    eapply ST_If0Nonzero.
    eapply multi_step.
    eapply ST_If01.
    eapply ST_PredNat.
    simpl.
    eapply multi_step.
    rewrite <- plus_n_Sm.
    eapply ST_If0Nonzero.
    eapply multi_step.
    eapply ST_Succ1.
    eapply ST_App2.
    eauto.
    eauto.
    eapply multi_step.
    eapply ST_Succ1.
    eapply ST_App2.
    eauto.
    eauto.
    apply lem_f1 in IHn.
    apply multi_trans with (y := tsucc (tnat n)).
    apply IHn.
    eapply multi_step.
    eapply ST_SuccNat.
    constructor.
Qed.

(*-- Check --*)

Check conj halve_type (conj halve_10 halve_11) :
  empty |- halve \in TArrow TNat TNat /\
  tapp halve (tnat 10) ==>* tnat 5 /\ 
  tapp halve (tnat 11) ==>* tnat 5.

Check halve_correct: forall n,
   tapp halve (tnat (n + n)) ==>* tnat n.

