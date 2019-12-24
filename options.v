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