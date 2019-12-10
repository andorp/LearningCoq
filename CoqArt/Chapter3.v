(* Chapter3 *)

Require Import Arith.
Require Import ZArith.
Require Import Bool.

Section Minimal_propositional_logic.

  (* Section 3.1 *)

  Variables P Q R T : Prop.

  Theorem imp_trans_auto : (P -> Q) -> (Q -> R) -> P -> R.
  Proof.
    auto.
  Qed.

  Theorem imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
  Proof.
    intros H H' p.
    apply H'.
    apply H.
    exact p.
  Qed.

  Print imp_trans_auto.
  Print imp_trans.

  (* Section 3.2 *)

  Section example_of_assumption.
    Hypothesis H : P -> Q -> R.

    Lemma L1 : P -> Q -> R.
    Proof.
      assumption.
    Qed.
  End example_of_assumption.

  Theorem delta : (P -> P -> Q) -> P -> Q.
  Proof.
    exact (fun (H : P -> P -> Q) (p:P) => H p p).
  Qed.

  Theorem delta2 : (P -> P -> Q) -> P -> Q.
  Proof (fun (H : P -> P -> Q) (p:P) => H p p).

  Theorem apply_example : (Q -> R -> T) -> (P -> Q) -> P -> R -> T.
  Proof.
    intros H H0 p.
    apply H.
    exact (H0 p).
  Qed.

  Theorem imp_dist_auto : (P -> Q -> R) -> (P -> Q) -> (P -> R).
  Proof.
    auto.
  Qed.
  Print imp_dist_auto.

  Theorem imp_dist : (P -> Q -> R) -> (P -> Q) -> (P -> R).
  Proof.
    intros H H' p.
    apply H.
    - exact p.
    - exact (H' p).
  Qed.
  
  Theorem K : P -> Q -> P.
  Proof.
    intros p q.
    exact p.
  Qed.

(* Section 3.3 *)

End Minimal_propositional_logic.
