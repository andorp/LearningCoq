Class ordered (T : Type) :=
  { eq  : T -> T -> bool
  ; lt  : T -> T -> bool
  ; leq : T -> T -> bool

  ; eq_sym
      : forall (t1 t2 : T)
      , eq t1 t2 = eq t2 t1
  ; lt_asym
      : forall (t1 t2 : T) (b : bool)
      , (lt t1 t2 = true) -> (lt t2 t1 = false)
  ; eq_implies_leq
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
    
  Theorem nat_eq_sym
    : forall (t1 t2 : nat)
    , nat_eq t1 t2 = nat_eq t2 t1.
  Proof.
  Admitted.

  Theorem nat_lt_asym
    : forall (t1 t2 : nat) (b : bool)
    , (nat_lt t1 t2 = true) -> (nat_lt t2 t1 = false).
  Proof.
  Admitted.

  Theorem nat_eq_implies_leq
    : forall (t1 t2 : nat)
    , nat_eq t1 t2 = true -> nat_lt t1 t2 = true -> nat_leq t1 t2 = true.
  Proof.
  Admitted.

  Theorem nat_lt_not_eq
    : forall (t1 t2 : nat)
    , nat_lt t1 t2 = true -> nat_eq t1 t2 = false.
  Proof.
  Admitted.

  Instance orderedNat : ordered nat :=
    { eq              := nat_eq
    ; lt              := nat_lt
    ; leq             := nat_leq
    ; eq_sym          := nat_eq_sym
    ; lt_asym         := nat_lt_asym
    ; eq_implies_leq  := nat_eq_implies_leq
    ; lt_not_eq       := nat_lt_not_eq
    }.

End OrderedNat.

Class set (S : Type) (A : Type) : Type :=
  { empty  : S
  ; insert : A -> S -> S
  ; member : A -> S -> bool

  ; empty_member
      : forall (a : A)
      , member a empty = false
  ; insert_non_member
      : forall (s : S) (a : A)
      , member a s = false -> member a (insert a s) = true
  ; insert_member_idenpotent
      : forall (s : S) (a : A)
      , member a (insert a s) = member a (insert a (insert a s))
  }.


Section BinarySearchTree.

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

End BinarySearchTree.

Section UnbalancedSet.

Theorem tree_empty_member
  : forall (A : Type) (o : ordered A) (a : A)
  , tree_member a (Leaf A) = false.
Proof.
Admitted.

Theorem tree_insert_member
  : forall (A : Type) (o : ordered A) (s : tree A) (a : A)
  , tree_member a (tree_insert a s) = true.
Proof.
Admitted.

Theorem tree_insert_non_member
  : forall (A : Type) (o : ordered A) (s : tree A) (a : A)
  , tree_member a s = false -> tree_member a (tree_insert a s) = true.
Proof.
Admitted.

Theorem tree_insert_member_idenpotent
  : forall (A : Type) (o : ordered A) (s : tree A) (a : A)
  , tree_member a (tree_insert a s) = tree_member a (tree_insert a (tree_insert a s)).
Proof.
Admitted.

Instance unbalanced_set_tree {A : Type} `{o : ordered A} : set (tree A) A :=
  { empty                     := Leaf A
  ; insert                    := tree_insert
  ; member                    := tree_member
  ; empty_member              := tree_empty_member _ _
  ; insert_non_member         := tree_insert_non_member _ _
  ; insert_member_idenpotent  := tree_insert_member_idenpotent _ _
  }.

End UnbalancedSet.

