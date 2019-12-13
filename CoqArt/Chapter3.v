(* Chapter 3 *)

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

(* Exercise 3.2 *)

  Lemma id_P : P -> P.
  Proof.
    intro p.
    exact p.
  Qed.
  
  Lemma id_PP : (P -> P) -> (P -> P).
  Proof.
    intro p.
    exact p.
  Qed.

  Lemma imp_trans' : (P -> Q) -> (Q -> R) -> P -> R.
  Proof.
    intros Hpq Hqr p.
    apply Hqr.
    apply Hpq.
    exact p.
  Qed.

  Lemma imp_perm : (P -> Q -> R) -> (Q -> P -> R).
  Proof.
    intros Hpqr q p.
    apply Hpqr.
    - exact p.
    - exact q.
  Qed.

  Lemma ignore_Q : (P -> R) -> P -> Q -> R.
  Proof.
    intros Hpr p q.
    apply Hpr.
    exact p.
  Qed.

  Lemma delta_imp : (P -> P -> Q) -> P -> Q.
  Proof.
    intros Hppq p.
    apply Hppq.
    - exact p.
    - exact p.
  Qed.

  Lemma delta_impR : (P -> Q) -> (P -> P -> Q).
  Proof.
    intros Hpq p1 p2.
    apply Hpq.
    exact p1.
  Qed.

  Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
  Proof.
    intros Hpq Hpr Hqrt p.
    apply Hqrt.
    - apply Hpq.
      exact p.
    - apply Hpr.
      exact p.
  Qed.

  Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
  Proof.
    intro H0.
    apply H0.
    intro H1.
    apply H1.
    intro p.
    apply H0.
    intro H2.
    exact p.
  Qed.
    

(* Section 3.4*)

  Definition unreliable : (nat -> bool) -> (nat -> bool) -> nat -> bool.
    intros f1 f2.
    assumption.
  Defined.
  Print unreliable.
  Eval compute in (unreliable (fun n => true) (fun n => false) 45).
  Opaque unreliable.
  Eval compute in (unreliable (fun n => true) (fun n => false) 45).

(* Section 3.5 *)

  Section proof_of_triple_impl.
    Hypothesis H : ((P -> Q) -> Q) -> Q.
    Hypothesis p : P.

    Lemma Rem : (P -> Q) -> Q.
    Proof (fun H0 : P -> Q => H0 p).

    Theorem triple_impl : Q.
    Proof (H Rem).
  End proof_of_triple_impl.
  Print Rem.
  Print triple_impl.

(* Section 3.6 *)

  Theorem then_example : P -> Q -> (P -> Q -> R) -> R.
  Proof.
    intros p q Hpq.
    apply Hpq; assumption.
  Qed.

  Theorem triple_impl_one_go : (((P -> Q) -> Q) -> Q) -> P -> Q.
  Proof.
    intros H p; apply H; intro H0; apply H0; assumption.
  Qed.

  Theorem compose_example : (P -> Q -> R) -> (P -> Q) -> P -> R.
  Proof.
    intros Hpqr Hpq p.
    apply Hpqr; [assumption | apply Hpq; assumption].
  Qed.

  Theorem orelse_example : (P -> Q) -> R -> ((P -> Q) -> R -> (T -> Q) -> T) -> T.
  Proof.
    intros Hpq r H.
    apply H;(assumption || intro H1).
  Abort.

(* Exercise 3.3 - TODO *)

Lemma id_P_1 : P -> P.
Proof.
  intros p; assumption.
Qed.

Lemma id_PP_1 : (P -> P) -> (P -> P).
Proof.
  intros Hpp p; assumption.
Qed.

Lemma imp_trans_1 : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros Hpq Hqr p; apply Hqr; apply Hpq; assumption.
Qed.

Lemma imp_perm_1 : (P -> Q -> R) -> (Q -> P -> R).
Proof.
  intros Hpqr q p; apply Hpqr; assumption.
Qed.

Lemma ignore_Q_1 : (P -> R) -> P -> Q -> R.
Proof.
  intros Hpr p q; apply Hpr; assumption.
Abort.

Lemma delta_imp_1 : (P -> P -> Q) -> P -> Q.
Proof.
  intros Hppq p; apply Hppq; assumption.
Qed.

Lemma delta_impR_1 : (P -> Q) -> (P -> P -> Q).
Proof.
  intros Hpq p0 p1; apply Hpq; assumption.
Qed.

Lemma diamond_1 : (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
Proof.
  intros Hpq Hpr Hqrt p; apply Hqrt; (apply Hpr || apply Hpq); assumption.
Qed.

Lemma weak_peirce_1 : ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
  auto. (*TODO*)
Qed.

(* Section 3.7 *)

  Section section_for_cut_example.
    Hypotheses
      (H : P -> Q)
      (H0 : Q -> R)
      (H1 : (P -> R) -> T -> Q)
      (H2 : (P -> R) -> T).
    Theorem cut_example : Q.
    Proof.
      cut (P -> R).
      intro H3.
      - apply H1; [assumption | apply H2; assumption ].
      - intro p.
        apply H0.
        apply H.
        exact p.
    Qed. 
    Print cut_example.
  End section_for_cut_example.

(* Exercise 3.5 *)

End Minimal_propositional_logic.

(* Section 3.9 *)

Print imp_dist.

Section using_imp_dict.
  Variables (P1 P2 P3 : Prop).
  Check (imp_dist P1 P2 P3).
End using_imp_dict.

