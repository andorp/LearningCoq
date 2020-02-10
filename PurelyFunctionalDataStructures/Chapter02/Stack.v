Require Import Coq.Lists.List.

Set Implicit Arguments.

Class Stack (S : Type -> Type) : Type :=
  { empty    : forall (A : Type) , S A
  ; is_empty : forall {A : Type} , S A -> bool
  ; cons     : forall {A : Type} , A -> S A -> S A
  ; head     : forall {A : Type} , S A -> option A
  ; tail     : forall {A : Type} , S A -> option (S A)

  ; empty_is_empty  : forall (A : Type) , is_empty (empty A) = true
  ; empty_cons      : forall (A : Type) (a : A) (s : S A) , is_empty (cons a s) = false
  ; head_empty      : forall (A : Type) , head (empty A) = None
  ; head_cons       : forall (A : Type) (a : A) (s : S A) , head (cons a s) = Some a
  ; tail_empty      : forall (A : Type) , tail (empty A) = None
  ; tail_cons       : forall (A : Type) (a : A) (s : S A) , tail (cons a s) = Some s
  }.
  
Section list_stack_implementation.
  Definition list_empty (A : Type) : list A := nil.
  
  Definition list_is_empty {A : Type} (s : list A) : bool :=
    match s with
      | nil => true
      | _   => false
    end.
  
  Definition list_cons {A : Type} (a : A) (s : list A) : list A := a :: s.
  
  Definition list_head {A : Type} (s : list A) : option A :=
    match s with
      | nil     => None
      | a :: _  => Some a
    end.
  
  Definition list_tail {A : Type} (s : list A) : option (list A) :=
    match s with
      | nil     => None
      | _ :: s  => Some s
    end.
  
  Theorem list_empty_is_empty
    : forall (A : Type)
    , list_is_empty (list_empty A) = true.
  Proof.
    intros A.
    simpl.
    trivial.
  Qed.
  
  Theorem list_empty_cons
    : forall (A : Type) (a : A) (s : list A) , list_is_empty (list_cons a s) = false.
  Proof.
    intros A a s.
    simpl.
    trivial.
  Qed.
  
  Theorem list_head_empty
    : forall (A : Type) , list_head (list_empty A) = None.
  Proof.
    intros A.
    simpl.
    trivial.
  Qed.
  
  Theorem list_head_cons 
    : forall (A : Type) (a : A) (s : list A) , list_head (list_cons a s) = Some a.
  Proof.
    intros A a s.
    simpl.
    trivial.
  Qed.
  
  Theorem list_tail_empty
    : forall (A : Type) , list_tail (list_empty A) = None.
  Proof.
    intros A.
    simpl.
    trivial.
  Qed.
  
  Theorem list_tail_cons 
    : forall (A : Type) (a : A) (s : list A) , list_tail (list_cons a s) = Some s.
  Proof.
    intros A a s.
    simpl.
    trivial.
  Qed.
  
  Instance listStack : Stack list :=
    { empty     A     := list_empty A
    ; is_empty  A s   := list_is_empty s
    ; cons      A a s := list_cons a s
    ; head      A s   := list_head s
    ; tail      A s   := list_tail s
    ; empty_is_empty  := list_empty_is_empty
    ; empty_cons      := list_empty_cons
    ; head_empty      := list_head_empty
    ; head_cons       := list_head_cons
    ; tail_empty      := list_tail_empty
    ; tail_cons       := list_tail_cons
    }.

End list_stack_implementation.

