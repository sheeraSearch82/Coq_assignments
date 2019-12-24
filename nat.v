Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | white
  | black
  | primary (p : rgb).

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Check S (S (S O)).

Definition minustwo (n : nat) : nat :=
   match n with
    | O => O
    | S O => O
    | S (S n') => n'
   end.

Check S.
Check pred.
Check minustwo.




End NatPlayground.

Definition minustwo (n : Datatypes.nat) : Datatypes.nat :=
   match n with
    | O => O
    | S O => O
    | S (S n') => n'
   end.

Compute (minustwo 4).


Fixpoint evenb (n : Datatypes.nat) : bool :=
 match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
 end.

Compute (evenb 4).

Compute (evenb 1).

Definition oddb (n : Datatypes.nat) : bool :=
 negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Fixpoint addn (n : Datatypes.nat) (m : Datatypes.nat) : Datatypes.nat :=
 match n with
 | O => m
 | S n' => S (addn n' m)
 end.

Compute (addn 5 6).

Fixpoint multn (n : Datatypes.nat) (m : Datatypes.nat) : Datatypes.nat :=
 match n with
 | O => O
 | S n' => addn m (multn n' m)
 end.

Compute (multn 5 6).

Example test_mult3 : (multn 3 3) = 9.
Proof.
 simpl.
 reflexivity.
Qed.





