(* Chapter 4 - Page 96 *)

(* Section 4.1 *)

Require Import Arith.
(* Require Import ZArith. *)
(* Require Import Bool. *)

Parameters
  (prime_divisor : nat -> nat)
  (prime : nat -> Prop)
  (divides : nat -> nat -> Prop).

Open Scope nat_scope.

Check (prime (prime_divisor 220)).
Check (divides (prime_divisor 220) 220).
Check (divides 3).

Parameter binary_word : nat -> Set.

Definition short := binary_word 32.
Definition long  := binary_word 64.

Check (not (divides 3 81)).

Check (let d := prime_divisor 220 in prime d /\ divides d 220).

Require Import List.

Parameters
  (decomp  : nat -> list nat)
  (decomp2 : nat -> nat * nat).

Check (decomp 220).
Check (decomp2 284).

Parameters
  (prime_divisor_correct :
     forall n:nat, 2 <= n -> 
       let d := prime_divisor n in prime d /\ divides d n)

  (binary_word_concat :
     forall n p:nat,
       binary_word n -> binary_word p -> binary_word (n+p)).

Check prime_divisor_correct.

Check cons.
Check pair.
Check (forall A B : Set, A -> B -> A * B).
Check fst.

(* Section 4.2 *)

Check le_n.
Check le_S.
Check (le_n 36).

Definition le_36_37 := le_S 36 36 (le_n 36).
Check le_36_37.
Definition le_36_38 := le_S 36 37 (le_36_37).
Check le_36_38.

Check (le_S _ _ (le_S _ _ (le_n 36))).

Check (prime_divisor_correct 220).
