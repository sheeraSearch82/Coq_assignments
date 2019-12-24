(**********************************************LISTS*********************************************************)
Require Import List.
Import ListNotations.

Module MyList.

Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

End MyList.

Check list.

Definition is_empty (A : Type) (lst : list A) :=
  match lst with
  | nil => true
  | cons _ _ => false
  end.

Definition is_empty_sugar (A : Type) (lst : list A) :=
  match lst with
  | [] => true
  | _::_ => false
  end.

Compute is_empty nat [1].

Compute is_empty nat [].

Definition is_empty' {A : Type} (lst : list A) :=
  match lst with
  | [] => true
  | _::_ => false
  end.

Compute is_empty' [1].


Compute @is_empty' nat [1].

Module MyLength.

Fixpoint length {A : Type} (lst : list A) :=
  match lst with
  | nil => 0
  | _::t => 1 + length t
  end.

Compute length [1;2].

End MyLength.

(************************************************OPTIONS******************************************************)

Module MyOption.

Inductive option (A:Type) : Type :=
  | Some : A -> option A
  | None : option A.

End MyOption.

Definition hd_opt {A : Type} (lst : list A) : option A :=
  match lst with
  | nil => None 
  | x :: xs => Some x
  end.

Compute hd_opt [1].

Compute @hd_opt nat [].

Theorem length0_implies_hdopt_is_none :
  forall A : Type, forall lst : list A,
    length lst = 0 -> hd_opt lst = None.
Proof.
  intros A lst length_lst_is_0.
  destruct lst.
    trivial.
    discriminate.
Qed.

Theorem length0_implies_hdopt_is_none' :
forall A : Type, forall lst : list A,
  length lst = 0 -> hd_opt lst = None.
Proof.
  intros A lst length_lst_is_0.
  destruct lst.
    - trivial.
    - discriminate.
Qed.