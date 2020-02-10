
Class set (S : Type -> Type) : Type :=
  { empty  : forall (A : Type) , S A
  ; insert : forall {A : Type} , A -> S A -> S A
  ; member : forall {A : Type} , A -> S A -> bool

  ; empty_member
      : forall (A : Type) (a : A)
      , member a (empty A) = false
  ; insert_member
      : forall (A : Type) (a : A) (s : S A)
      , member a (insert a s) = true
  ; insert_member_idenpotent
      : forall (A : Type) (a : A) (s : S A)
      , member a (insert a s) = member a (insert a (insert a s))
  }.

Class ordered (T : Type) :=
  { eq  : T -> T -> bool
  ; lt  : T -> T -> bool
  ; leq : T -> T -> bool

  ; eq_refl
      : forall (t1 t2 : T)
      , eq t1 t2 = eq t2 t1
  ; lt_asym
      : forall (t1 t2 : T) (b : bool)
      , (lt t1 t2 = b) -> (lt t2 t1) <> b
  ; implies_leq
      : forall (t1 t2 : T)
      , eq t1 t2 = true -> lt t1 t2 = true -> leq t1 t2 = true
  ; lt_not_eq
      : forall (t1 t2 : T)
      , lt t1 t2 = true -> eq t1 t2 = false
  }.

Notation "x =? y"   := (eq x y) (at level 70).
Notation "x <? y"   := (lt x y) (at level 70).
Notation "x <=? y"  := (leq x y) (at level 70). 

Section OrderedNat.

  Fixpoint nat_eq (n0 n1 : nat) : bool :=
    match (n0, n1) with
      | (O, O)       => true
      | (S m0, S m1) => nat_eq m0 m1
      | _            => false
    end.
  
  Fixpoint nat_lt (n0 n1 : nat) : bool :=
    match (n0, n1) with
      | (O, O)   => false
      | (O, S _) => true
      | (S _, O) => false
      | (S m0, S m1) => nat_lt m0 m1
    end.

  Definition nat_leq (n0 n1 : nat) : bool :=
    nat_eq n0 n1 || nat_lt n0 n1.
    
  Theorem nat_eq_refl
    : forall (t1 t2 : nat)
    , nat_eq t1 t2 = nat_eq t2 t1.
  Proof.
  Admitted.

  Theorem nat_lt_asym
    : forall (t1 t2 : nat) (b : bool)
    , (nat_lt t1 t2 = b) -> (nat_lt t2 t1) <> b.
  Proof.
  Admitted.

  Theorem nat_implies_leq
    : forall (t1 t2 : nat)
    , nat_eq t1 t2 = true -> nat_lt t1 t2 = true -> nat_leq t1 t2 = true.
  Proof.
  Admitted.

  Theorem nat_lt_not_eq
    : forall (t1 t2 : nat)
    , nat_lt t1 t2 = true -> nat_eq t1 t2 = false.
  Proof.
  Admitted.

End OrderedNat.



Section BinaryTree.

  Inductive tree (A : Type) : Type :=
    | Leaf   : tree A
    | Branch : tree A -> A -> tree A -> tree A
    .
  
  (* How to represent the balanced tree property in for tree? *)
  
  Fixpoint tree_member {A : Type} `{ordered A} (x : A) (t : tree A) : bool :=
    match t with
      | Leaf _         => false
      | Branch _ l y r =>
          match (x <? y) with
            | true  => tree_member x l
            | false =>
                match (y <? x) with
                  | true  => tree_member x r
                  | false => true
                end
          end
    end.

  Fixpoint tree_insert {A : Type} `{o : ordered A} (x : A) (t : tree A) : tree A :=
    match t with
      | Leaf _         => Branch A (Leaf A) x (Leaf A)
      | Branch _ l y r =>
          match (x <? y) with
            | true  => Branch A (tree_insert x l) y r
            | false =>
                match (y <? x) with
                  | true  => Branch A l y (tree_insert x r)
                  | false => Branch A l y r
                end
          end
    end.

End BinaryTree.

Print tree_member.

Section UnbalancedSet.

(* Theorem tree_empty_member
  : forall (A : Type) (a : A)
  , tree_member a (Leaf A) = false.
Proof.
Admitted. *)

Theorem tree_insert_member
  : forall (A : Type) `{o : ordered A} (a : A) (s : tree A)
  , tree_member a (tree_insert a s) = true.
Proof.
Admitted.

Theorem tree_insert_member_idenpotent
  : forall (A : Type) `{o : ordered A} (a : A) (s : tree A)
  , tree_member a (tree_insert a s) = tree_member a (tree_insert a (tree_insert a s)).
Proof.
Admitted.

Instance unbalanced_set_tree : set tree :=
  { empty  := Leaf
  }.
Abort.
(* 
Class set (S : Type -> Type) : Type :=
  { empty  : forall (A : Type) , S A
  ; insert : forall {A : Type} , A -> S A -> S A
  ; member : forall {A : Type} , A -> S A -> bool

  ; empty_member
      : forall (A : Type) (a : A)
      , member a (empty A) = false
  ; insert_member
      : forall (A : Type) (a : A) (s : S A)
      , member a (insert a s) = true
  ; insert_member_idenpotent
      : forall (A : Type) (a : A) (s : S A)
      , member a (insert a s) = member a (insert a (insert a s))
  }. *)

End UnbalancedSet.
