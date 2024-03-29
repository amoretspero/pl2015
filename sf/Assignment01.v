(** **** SNU 4190.310, 2015 Spring *)

(** Assignment 01 *)
(** Due: 2015/03/19 14:00 *)

Definition admit {T: Type} : T.  Admitted.

(** **** Problem #1 : 1 star (andb3) *)
(** Do the same for the [andb3] function below. This function should
    return [true] when all of its inputs are [true], and [false]
    otherwise. *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
    match b1 with
    | true => 
        match b2 with
        | true => b3
        | false => false
        end
    | false => false
    end.


Example test_andb31 :                 (andb3 true true true) = true.
reflexivity. Qed.
Example test_andb32 :                 (andb3 false true true) = false.
reflexivity. Qed.
Example test_andb33 :                 (andb3 true false true) = false.
reflexivity. Qed.
Example test_andb34 :                 (andb3 true true false) = false.
reflexivity. Qed.
(** [] *)



(** **** Problem #2: 1 star (factorial) *)
(** Recall the standard factorial function:
<<
    factorial(0)  =  1 
    factorial(n)  =  n * factorial(n-1)     (if n>0)
>>
    Translate this into Coq. 

    Note that plus and multiplication are already defined in Coq.
    use "+" for plus and "*" for multiplication.
*)

Eval compute in 3 * 5.
Eval compute in 3+5*6.

Fixpoint factorial (n:nat) : nat := 
    match n with
    | O => 1
    | S p => n * (factorial p)
    end.

Example test_factorial1:          (factorial 3) = 6.
reflexivity. Qed.
Example test_factorial2:          (factorial 5) = 10 * 12.
reflexivity. Qed.
(** [] *)



(** **** Problem #3: 2 stars (blt_nat) *)
(** The [blt_nat] function tests [nat]ural numbers for [l]ess-[t]han,
    yielding a [b]oolean.  Use [Fixpoint] to define it. *)

Fixpoint blt_nat (n m : nat) : bool := 
    match n with
    | O => 
        match m with
        | O => false
        | S p => true
        end
    | S q =>
        match m with
        | O => false
        | S r => (blt_nat q r)
        end
    end.

Example test_blt_nat1:             (blt_nat 2 2) = false.
reflexivity. Qed.
Example test_blt_nat2:             (blt_nat 2 4) = true.
reflexivity. Qed.
Example test_blt_nat3:             (blt_nat 4 2) = false.
reflexivity. Qed.
(** [] *)
