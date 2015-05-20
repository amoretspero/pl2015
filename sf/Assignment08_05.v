Require Export Assignment08_04.

(* problem #05: 20 points *)

(** Write a function which compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : aexp) : list sinstr :=
    match e with
    | ANum n => [ SPush n ]
    | AId aid => [ SLoad aid ]
    | APlus e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [ SPlus ]
    | AMinus e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [ SMinus ]
    | AMult e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [ SMult ]
    end.

(** After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof.
    auto.
Qed.

(** **** Exercise: 3 stars, advanced (stack_compiler_correct)  *)
(** The task of this exercise is to prove the correctness of the
    compiler implemented in the previous exercise.  Remember that
    the specification left unspecified what to do when encountering an
    [SPlus], [SMinus], or [SMult] instruction if the stack contains
    less than two elements.  (In order to make your correctness proof
    easier you may find it useful to go back and change your
    implementation!)

    Prove the following theorem, stating that the [compile] function
    behaves correctly.  You will need to start by stating a more
    general lemma to get a usable induction hypothesis; the main
    theorem will then be a simple corollary of this lemma. *)

Lemma s_compile_app : forall (st : state) (n1 : list nat) (s1 s2 : list sinstr),
    s_execute st n1 (s1 ++ s2) = s_execute st (s_execute st n1 s1) s2.
Proof.
    intros.
    generalize dependent n1.
    induction s1 as [| hd tl].
    reflexivity.
    destruct hd;
    simpl;
    intros n1;
    try apply IHtl;
    destruct n1;
    try apply IHtl;
    destruct n1;
    try apply IHtl.
Qed.
    
    
Lemma s_execute_to_app : forall (st : state) (n1 : list nat) (e : aexp),
    s_execute st n1 (s_compile e) = (aeval st e) :: n1.
Proof.
    intros.
    generalize dependent n1.
    induction e;
    try reflexivity;
    simpl;
    intros n1;
    rewrite s_compile_app;
    rewrite IHe1;
    rewrite s_compile_app;
    rewrite IHe2;
    reflexivity.
Qed.


Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
    intros.
    apply s_execute_to_app.
Qed.

(*-- Check --*)
Check s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].

Check s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].

