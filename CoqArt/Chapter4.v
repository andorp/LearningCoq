(* http://www.cse.chalmers.se/research/group/logic/TypesSS05/resources/coq/CoqArt/contents.html *)

(* Chapter 4 - Page 96 *)
(* Section 4.1 *)

Require Import Arith.
Require Import ZArith.
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

Parameters
  (iterate : forall A : Set, (A -> A) -> nat -> A -> A).

Check (iterate nat).
Check (iterate _ (mult 2)).
Check (iterate _ (mult 2) 10).
Check (iterate _ (mult 2) 10 1).

Eval compute in (iterate _ (mult 2) 10 1).

(* Check (iterate Z (Zmult 2) 5 36). *)
(* The term "36" has type "nat" while it is expected to have type "Z". *)

Check (binary_word_concat 32).
Check (binary_word_concat 32 32).

Definition twice
  : forall A : Set, (A -> A) -> A -> A
  := fun A f a => f (f a).

Check (twice Z).
Check (twice Z (fun z => (z * z) % Z)).
Check (twice _ S 56).
Check (twice (nat -> nat) (fun f x => f (f x)) (mult 3)).

Eval compute in
  (twice (nat -> nat) (fun f x => f (f x)) (mult 3) 1).

Definition binary_word_duplicates (n : nat) (w : binary_word n)
  : binary_word (n + n)
  := binary_word_concat _ _ w w.

Theorem le_i_SSi : forall i : nat, i <= S (S i).
Proof (fun i => le_S _ _ (le_S _ _ (le_n i))).

Definition compose
  : forall A B C : Set, (A -> B) -> (B -> C) -> A -> C
  := fun A B C f g x => g (f x).

(* Implicit Arguments compose [A B C]*)
Arguments compose [A B C].

Print compose.

Check (fun (A : Set) (f : Z -> A) => compose _ _ _ Z.of_nat f).
Check (compose _ _ _ Z.abs_nat (plus 78) 45%Z).

Check (le_i_SSi 1515).

Check (iterate _ (fun x => x) 23).

(* Implicit Arguments le_S *)
Arguments le_S [n m].

Check (compose Z.abs_nat (plus 78)).
Check (le_S (le_i_SSi 1515)).

Check (compose (C := Z) S).
Check (le_S (n := 45)).

(* Set Implicit Arguments. *)
(* Unset Implicit Arguments. *)

Reset compose.
Set Implicit Arguments.

Definition compose (A B C : Set) (f : A -> B) (g : B -> C) (a : A) := g (f a).
Definition thrice (A : Set) (f : A -> A) := compose f (compose f f).
Unset Implicit Arguments.

Print compose.
Print thrice.

Eval cbv beta delta in (thrice (thrice (A := nat)) S 0).

Definition short_concat
  : short -> short -> long
  := binary_word_concat 32 32.

(* Section 4.3 *)

Check (forall n : nat , 0 < n -> nat).
Check ((forall n : nat , 0 < n) -> nat).

Definition my_plus : nat -> nat -> nat := iterate nat S.

Definition my_mult (n p : nat) : nat := iterate nat (my_plus n) p 0.

Definition my_expo (x n : nat) : nat := iterate nat (my_mult x) n 1.

Definition ackermann (n : nat) : nat -> nat :=
  iterate
    (nat -> nat)
    (fun (f : nat -> nat) (p : nat) => iterate nat f (S p) 1)
    n
    S.

(* Exercise 4.4 *)

Definition id
  : forall A : Set , A -> A
  := fun A x => x.

Definition diag
  : forall A B : Set , (A -> A -> B) -> A -> B
  := fun A B f a => f a a.

Definition permute
  : forall A B C : Set , (A -> B -> C) -> B -> A -> C
  := fun A B C f b a => f a b.

Search (Z -> nat).

Definition f_nat_Z
  : forall A : Set , (nat -> A) -> Z -> A
  := fun A f z => f (Z.to_nat z).

Check (forall P : Prop, P -> P).
Check (fun (P : Prop) (p : P) => p).

(* Exercise 4.5 *)

Theorem all_perm
  : forall (A : Type) (P : A -> A -> Prop) , (forall x y : A, P x y) -> (forall x y : A, P y x).
Proof.
  intros A P Hxy x y.
  apply Hxy.
Qed.

Theorem resolution
  : forall (A : Type) (P Q R S : A -> Prop)
   , (forall a : A , Q a -> R a -> S a)
  -> (forall b : A , P b -> Q b)
  -> (forall c : A , P c -> R c -> S c).
Proof.
  intros A P Q R S Hqrs Hpq c Hpc Hrc.
  apply Hqrs.
  - apply Hpq.
    apply Hpc.
  - apply Hrc.
Qed.

Check False_ind.
Check False_rec.
Check False_rect.

Theorem ThirtySix : 9*4 = 6*6.
Proof (refl_equal 36).

Check eq_ind.
Check eq_rec.
Check eq_rect.

Definition eq_sym (A : Type) (x y : A) (h : x=y) : y=x
  := eq_ind x (fun z => z=x) (refl_equal x) y h.

Check (eq_sym _ _ _ ThirtySix).

Definition not (P : Prop) : Prop := P -> False.

Check conj.
Check or_introl.
Check or_intror.

Check and_ind.

Theorem conj3 : forall P Q R : Prop , P -> Q -> R -> P /\ Q /\ R.
Proof (fun P Q R p q r => conj p (conj q r)).

Theorem conj3' : forall P Q R : Prop , P -> Q -> R -> P /\ Q /\ R.
Proof.
  intros P Q R p q r.
  exact (conj p (conj q r)).
Qed.

Theorem disj4_3 : forall P Q R S : Prop , R -> P \/ Q \/ R \/ S.
Proof (fun P Q R S r => or_intror _ (or_intror _ (or_introl _ r))).

Theorem disj4_3' : forall P Q R S : Prop , R -> P \/ Q \/ R \/ S.
Proof.
  intros P Q R S r.
  auto.
Qed.

Check (ex (fun z:Z => (z*z <= 37 /\ 37 <= (z + 1)*(z + 1)) % Z)).

Check ex_intro.
Check ex_ind.



