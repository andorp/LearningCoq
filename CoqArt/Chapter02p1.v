Require Import Arith.
Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Locate "_ * _".

Print Scope Z_scope.

Check 33%nat.

Open Scope nat_scope.
Check 33.
Check 33%Z.
Check (-12)%Z.
Open Scope Z_scope.
Check (-12).
Check 33%nat.
Check true.
Check false.

Check plus.
Check Zplus.
Check negb.
(* Check zero. *)

Check negb.
Check (negb true).
Check (negb (negb true)).

Open Scope nat_scope.
Check S (S(S(O))).

Unset Printing Notations.
Check 4. (* This did not work *)
Set Printing Notations.
Check 4.

Check (fun n:nat => (n*n*n)%nat).

Check
    (fun n p : nat => 
        (let diff := n-p in
        let square := diff * diff in
            square * (square + n))%nat
    ).

Parameter max_int : Z.

Open Scope Z_scope.

Definition min_int := 1-max_int.
Print min_int.
Definition  cube := fun z:Z  => z*z*z.
Definition cube1 (z:Z) := z*z*z.
Definition cube2 z := z*z*z .
Definition Z_thrice (f : Z -> Z) (z:Z) := f (f (f z)).
Definition plus9 := Z_thrice (Z_thrice (fun n => n + 1)).

Section binomial_def.
  Variables a b : Z.
  Definition binomial z:Z := a*z + b.
  Print binomial.
  Section trinomial_def.
    Variable c : Z.
    Definition trinomial z:Z := (binomial z)*z + c.
    Print trinomial.
  End trinomial_def.
  Print trinomial.
End binomial_def.
Print binomial.
Print trinomial.

Section h_def.
  Variables a b : Z.
  Let s:Z := (a+b).
  Let d:Z := a-b.
  Definition h : Z := s*s + d * d.
End h_def.
Print h.

(* Exercise 2.7 *)
Open Scope Z_scope.
Definition funE2_7 (x : Z) : Z
  := 2 * (x*x) + 3 * x + 3.

Eval cbv iota beta zeta delta in (funE2_7 2).
Eval cbv iota beta zeta delta in (funE2_7 3).
Eval cbv iota beta zeta delta in (funE2_7 4).

Check Z.
Check ((Z -> Z) -> nat -> nat).
Check Set.
Check Type.

Definition Z_bin : Set := Z -> Z -> Z.
Check (fun z0 z1 : Z => let d := z0 - z1 in d * d).
Definition Zdist2 : Z_bin := fun z z0 => let d := z - z0 in d * d.

Check (nat -> nat).
Check (nat -> nat:Type).

Section domain.
  Variables (D:Set) (op:D -> D -> D) (sym : D -> D) (e : D).
  Let diff : D -> D -> D :=
    fun (x y : D) => op x (sym y).
End domain.

Section realization.
  Variable (A B : Set).
  Let spec : Set := (((A -> B) -> B) -> B) -> A -> B.
  Let realization : spec
        := fun (f:((A -> B)->B)->B) a => f (fun g => g a).
2
