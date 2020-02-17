Class ordered (T : Type) :=
  { eq  : T -> T -> bool
  ; lt  : T -> T -> bool
  ; leq : T -> T -> bool

  ; eq_sym
      : forall (t1 t2 : T)
      , eq t1 t2 = eq t2 t1
  ; lt_asym
      : forall (t1 t2 : T) (b : bool)
      , lt t1 t2 = true -> lt t2 t1 = false
  ; eq_implies_leq
      : forall (t1 t2 : T)
      , eq t1 t2 = true -> leq t1 t2 = true
  ; lt_implies_leq
      : forall (t1 t2 : T)
      , lt t1 t2 = true -> leq t1 t2 = true
  ; lt_not_eq
      : forall (t1 t2 : T)
      , lt t1 t2 = true -> eq t1 t2 = false
  }.

Class heap (H : Type) (E : Type) `{o : ordered E} : Type :=
  { empty     : H
  ; isEmpty   : H -> bool
  ; insert    : E -> H -> H
  ; merge     : H -> H -> H
  ; findMin   : H -> option E
  ; deleteMin : H -> option H

  ; empty_is_empty
      : isEmpty empty = true
  ; non_empty_is_not_empty
      : forall (h : H) (e : E)
      , isEmpty (insert e h) = true
  ; merge_empty_left
      : forall (h : H)
      , merge empty h = h
  ; merge_empty_right
      : forall (h : H)
      , merge h empty = h
  ; empty_findMin
      : findMin empty = None
  ; empty_deleteMin
      : deleteMin empty = None
  ; insert_min
      : forall (h : H) (e1 e2 : E)
      , findMin h = Some e1 -> lt e2 e1 = true -> findMin (insert e2 h) = Some e2
  ; insert_non_min
      : forall (h : H) (e1 e2 : E)
      , findMin h = Some e1 -> lt e2 e1 = false -> findMin (insert e2 h) = Some e1
  ; merge_min_left
      : forall (h1 h2 : H) (e1 e2 : E)
      , findMin h1 = Some e1 -> findMin h2 = Some e2 -> lt e1 e2 = true -> findMin (merge h1 h2) = Some e1
  ; merge_min_right
      : forall (h1 h2 : H) (e1 e2 : E)
      , findMin h1 = Some e1 -> findMin h2 = Some e2 -> lt e2 e1 = true -> findMin (merge h1 h2) = Some e2
  ; delete_min
      : forall (h1 h2 : H) (e1 e2 : E)
      , findMin h1 = Some e1 -> lt e2 e1 = true -> deleteMin (insert e2 h1) = Some h2 -> findMin h2 = Some e1
  }.

Require Import Arith.

Inductive leftish_heap (E : Type) : Type :=
  | Empty : leftish_heap E
  | Node  : nat -> E -> leftish_heap E -> leftish_heap E -> leftish_heap E
  .

Definition lh_empty {E : Type} : leftish_heap E :=
  Empty E.

Definition lh_isEmpty {E : Type} (h : leftish_heap E) : bool :=
  match h with
    | Empty _         => true
    | Node  _ _ _ _ _ => false
  end.

Definition lh_findMin {E : Type} `{o : ordered E} (h : leftish_heap E) : option E :=
  match h with
    | Empty _ => None
    | Node _ _ x _ _ => Some x
  end.

Definition rank {E : Type} (e : leftish_heap E) : nat :=
  match e with
    | Empty _         => 0
    | Node  _ r _ _ _ => r
  end.

(* Cannot guess decreasing argument of fix. *)
(* Definition makeT {E : Type} (x : E) (a : leftish_heap E) (b : leftish_heap E) : leftish_heap E :=
  if (rank b) <? (rank a)
    then Node E (rank b + 1) x a b
    else Node E (rank a + 1) x b a.

Fixpoint merge {E : Type} `{o : ordered E} (e1 : leftish_heap E) (e2 : leftish_heap E) : leftish_heap E :=
  match e1, e2 with
    | h, Empty _ => h
    | Empty _, h => h
    | Node _ _ x a1 b1 as h1, Node _ _ y a2 b2 as h2 =>
        if leq x y
          then makeT x a1 (merge b1 h2)
          else makeT y a2 (merge h1 b2)
  end. *)

Fixpoint lh_merge {E : Type} `{o : ordered E} (e1 : leftish_heap E) (e2 : leftish_heap E) : leftish_heap E :=
  match e1, e2 with
    | h, Empty _ => h
    | Empty _, h => h
    | Node _ _ x a1 b1 as h1, Node _ _ y a2 b2 as h2 =>
        if leq x y
          then (let a := a1 in
                let b := lh_merge b1 h2 in
                let ra := rank a in
                let rb := rank b
                in if rank b <? rank a
                    then Node E (rb + 1) x a b
                    else Node E (ra + 1) x b a)
          else (let a := a1 in
                let b := lh_merge b1 h2 in
                let ra := rank a in
                let rb := rank b
                in if rank b <? rank a
                    then Node E (rb + 1) x a b
                    else Node E (ra + 1) x b a)
  end.

Definition lh_insert {E : Type} `{o : ordered E} (x : E) (h : leftish_heap E) : leftish_heap E :=
  lh_merge (Node E 1 x (Empty E) (Empty E)) h.

Definition lh_deleteMin {E : Type} `{o : ordered E} (h : leftish_heap E) : option (leftish_heap E) :=
  match h with
    | Empty _         => None
    | Node  _ _ x a b => Some (lh_merge a b)
  end.

Theorem lh_empty_is_empty
  : forall (E : Type)
  , @lh_isEmpty E lh_empty = true.
Proof.
Admitted.

Theorem lh_non_empty_is_not_empty
  : forall (E : Type) (o : ordered E) (h : leftish_heap E) (e : E)
  , lh_isEmpty (lh_insert e h) = true.
Proof.
Admitted.

Theorem lh_merge_empty_left
  : forall (E : Type) (o : ordered E) (h : leftish_heap E)
  , lh_merge lh_empty h = h.
Proof.
Admitted.

Theorem lh_merge_empty_right
  : forall (E : Type) (o : ordered E) (h : leftish_heap E)
  , lh_merge h lh_empty = h.
Proof.
Admitted.

Theorem lh_empty_findMin
  : forall (E : Type) (o : ordered E)
  , lh_findMin lh_empty = None.
Proof.
Admitted.

Theorem lh_empty_deleteMin
  : forall (E : Type) (o : ordered E)
  , lh_deleteMin lh_empty = None.
Proof.
Admitted.

Theorem lh_insert_min
  : forall (E : Type) (o : ordered E) (h : leftish_heap E) (e1 e2 : E)
  , lh_findMin h = Some e1 -> lt e2 e1 = true -> lh_findMin (lh_insert e2 h) = Some e2.
Proof.
Admitted.

Theorem lh_insert_non_min
  : forall (E : Type) (o : ordered E) (h : leftish_heap E) (e1 e2 : E)
  , lh_findMin h = Some e1 -> lt e2 e1 = false -> lh_findMin (lh_insert e2 h) = Some e1.
Proof.
Admitted.

Theorem lh_merge_min_left
  : forall (E : Type) (o : ordered E) (h1 h2 : leftish_heap E) (e1 e2 : E)
  , lh_findMin h1 = Some e1 -> lh_findMin h2 = Some e2 -> lt e1 e2 = true -> lh_findMin (lh_merge h1 h2) = Some e1.
Proof.
Admitted.

Theorem lh_merge_min_right
  : forall (E : Type) (o : ordered E) (h1 h2 : leftish_heap E) (e1 e2 : E)
  , lh_findMin h1 = Some e1 -> lh_findMin h2 = Some e2 -> lt e2 e1 = true -> lh_findMin (lh_merge h1 h2) = Some e2.
Proof.
Admitted.

Theorem lh_delete_min
  : forall (E : Type) (o : ordered E) (h1 h2 : leftish_heap E) (e1 e2 : E)
  , lh_findMin h1 = Some e1 -> lt e2 e1 = true -> lh_deleteMin (lh_insert e2 h1) = Some h2 -> lh_findMin h2 = Some e1.
Proof.
Admitted.

(* TODO: Figure out how to instanciate this *)
(* Instance leftish {E : Type} `{o : ordered E} : heap (leftish_heap E) E :=
  { empty     := lh_empty
  ; isEmpty   := lh_isEmpty
  ; insert    := lh_insert
  ; merge     := lh_merge
  ; findMin   := lh_findMin
  ; deleteMin := lh_deleteMin

  ; empty_is_empty          := lh_empty_is_empty
  ; non_empty_is_not_empty  := lh_non_empty_is_not_empty
  ; merge_empty_left        := lh_merge_empty_left
  ; merge_empty_right       := lh_merge_empty_right
  ; empty_findMin           := lh_empty_findMin
  ; empty_deleteMin         := lh_empty_deleteMin
  ; insert_min              := lh_insert_min
  ; insert_non_min          := lh_insert_non_min
  ; merge_min_left          := lh_merge_min_left
  ; merge_min_right         := lh_merge_min_right
  ; delete_min              := lh_delete_min
  }. *)
