(**
 * Functional Programming in Coq
 *)

(* Exercise: mult2 [1 star].  
   Define a function that multiplies its input by 2.
   What is the function's type?
   What is the result of computing the function on 0?  On 3110?
*)

(********************************************************************************************************)

Fixpoint addn (n : Datatypes.nat) (m : Datatypes.nat) : Datatypes.nat :=
 match n with
 | O => m
 | S n' => S (addn n' m)
end.

Fixpoint mult2 (n : Datatypes.nat) : Datatypes.nat :=
 match n with
 | O => O
 | S n' => addn 2 (mult2 n')
 end.
(*--------------------------------------------------------------------------------------------------------*)

Compute (mult2 3).

Compute (mult2 0).
Compute (mult2 3110).

(********************************************************************************************************)

(**
   What is the function's type?
    ----->   nat -> nat
   What is the result of computing the function on 0?  On 3110?
   ------>  0 : nat , 6220 : nat
*)

(* Exercise: xor [1 star].
   Define a function that computes the xor of two [bool] inputs.
   Do this by pattern matching on the inputs.
   What is the function's type?
   Compute all four possible combinations of inputs to test your function.
*)

Definition negb (n : bool) : bool :=
 match n with
 | false => true
 | true => false
 end.

(*--------------------------------------------------------------------------------------------------------*)

Compute (negb true).
Compute (negb false).

Definition xorb (n : bool ) (m : bool) : bool :=
 match n with
 | true => negb m
 | false => m
 end.

(*--------------------------------------------------------------------------------------------------------*)
Compute (xorb true true).
Compute (xorb true false).
Compute (xorb false true).
Compute (xorb false false).

(********************************************************************************************************)

(* Exercise: is_none [2 star].
   Define a function that returns [true] if its input is [None], and [false] otherwise.
   Your function's type should be [forall A : Type, option A -> bool].
   That means the function will actually need to take two inputs:
     the first has type [Type], and the second is an option.
   Hint:  model your solution on [is_empty] in the notes for this lecture.
*)

(********************************************************************************************************)



Module MyOption.

Inductive option (A : Type) : Type :=
 | Some  : A -> option A
 | None : option A.

End MyOption.

Definition is_none (A : Type) (opt : option A) : bool :=
 match opt with
 | None => true
 | Some x => false
 end.

Compute is_none nat (Some 5).

Compute is_none nat (None).

(* Exercise: double_all [2 star].
   There is a function [map] that was imported by the [Require Import List] command above.
   First, check its type with [Check map].  Explain that type in your own words.
   Second, print it with [Print map].  Note at the end of that which arguments are _implicit_.
   For a discussion of what implicit means, see the notes for this lecture.
   Third, use map to write your own function, which should double (i.e., multiply by 2) 
   every value of a list. 
   For example, [double_all [0;2;10]] should be [[0;4;20]].
*)

Require Import List.
Import ListNotations.

Check map.

Print map.

Definition double_all (A : Type) (lst : list nat) :=
 match lst with
 | [] => []
 | x :: t => map (mult2) (x :: t)
end.

Compute double_all nat ([0;2;10]).

(* Exercise: sum [2 star]. 
   Write a function that sums all the natural numbers in a list.
   Implement this two different ways:  
   - as a recursive function, using the [Fixpoint] syntax.
   - as a nonrecursive function, using [Definition] and an application of [fold_left].
*)

Fixpoint nat_sum (A : Type) (lst : list nat) :=
 match lst with
 | [] => 0
 | x :: xs => x + (nat_sum nat xs)
 end.

Compute nat_sum nat [1;2;3;4].
Compute nat_sum nat [].

Check fold_left.

Print fold_left.


Definition nat_sum' (A: Type) (lst : list nat) :=
 fold_left plus lst 0.

Compute nat_sum' nat [1;2;3;4].
Compute nat_sum' nat [].

Eval vm_compute in fold_left plus (1::2::3::nil) 0.

(** Usage of fold_left
https://fzn.fr/teaching/coq/ecole10/summer/lectures/lec2
Fixpoint fold_left A B (f:A->B->A)(l:list B)(init:A) : A :=
 match l with
 | nil => init
 | x :: l' => fold_left f l' (f init x)
 end.
Eval vm_compute in fold_left plus (1::2::3::nil) 0.
==> (((0+1)+2)+3) ==> 6
Eval vm_compute in
fold_left (fun l x => x::l) nil (1::2::3::nil).
==> 3::2::1::nil
*)
(* For an explanation about vm_compute, refer this:
https://coq.inria.fr/refman/proof-engine/tactics.html
*)

Inductive day : Type :=
  | sun : day
  | mon : day
  | tue : day
  | wed : day
  | thu : day
  | fri : day
  | sat : day.

Definition next_day d :=
  match d with
  | sun => mon
  | mon => tue
  | tue => wed
  | wed => thu
  | thu => fri
  | fri => sat
  | sat => sun
  end.

(* Exercise: thu after wed [2 star].
   State a theorem that says [thu] is the [next_day] after [wed].
   Write down in natural language how you would informally explain
   to a human why this theorem is true.
   ---> Don't skip this "natural language" part of the exercise;
        it's crucial to develop intuition before proceeding.
   Prove the theorem in Coq.
*)

Theorem next_day_wed_thu : next_day wed = thu.
Proof.
simpl.
trivial.
Qed.

(**
The theorem starts with the invokation of the function next_day.
When we invoke the function next_day with argument [wed] it will replace the argument part of the
function with [wed]. It wil substitute that in the function boday and checks what day is returned when [wed] 
is called.
It is [thu]. Then LHS = RHS. Hence the theorem is true.
Proof startegy. simpl => we are simplyfying the LHS by applying the function on the given argument.
After simplification, we get LHS = RHS. Then nothing is there to be proved, hence we call trivial which states that
now proof folows trivially. This completes the proof.
*)

(* Exercise: wed before thu [3 star].
   Below is a theorem that says if the day after [d] is [thu], then
   [d] must be [wed].  
   Write down in natural language how you would informally explain
   to a human why this theorem is true.
   ---> Don't skip this "natural language" part of the exercise;
        it's crucial to develop intuition before proceeding.
   Prove the theorem in Coq.  To do that, delete the [Abort]
   command, which tells Coq to discard the theorem,
   then fill in your own proof.
*)

Theorem wed_proceeds_thu : forall d : day, next_day d = thu -> d = wed.
Proof.
intros d next_day_thu.
destruct d.
all : discriminate || trivial.
Qed.

(**
The third line says to use discriminate || trivial on all the subgoals. 
That works like a short-circuit OR in OCaml: if discriminate fails to find a proof of the subgoal, 
then trivial will be used to find the proof instead.
discriminate || trivial is aplied on all the cases of d. discriminate will eliminate all the cases except
wed = wed. Itrivial will act on wed = wed and proves it trivially.
*)

(* Exercise: tl_opt [2 star].
   Define a function [tl_opt] such that [tl_opt lst] return [Some t] if [t] is the tail of [lst],
   or [None] if [lst] is empty.
   We have gotten you started by providing an obviously incorrect definition, below; you should
   replace the body of the function with a correct definition.
*)

Definition tl_opt {A : Type} (lst : list A) : option (list A) :=
  match lst with
  | nil => None 
  | _ :: t => Some t
  end.

Compute tl_opt [1;2;3;4].

Eval vm_compute in tl_opt [1;2;3;4].

Compute @tl_opt nat [].

(* In the second, we are forced to explicitly provide the type argument, 
because Coq can't infer from just the empty list what kind of option 
it should be: should it be option nat? option bool? or something else?*)

(*We put the A:Type parameter in braces instead of parentheses. This tells 
Coq that the argument should be inferred. 
If for some reason we really did need to explicitly provide an implicit argument, 
we could do that by prefixing the name of the function with @ *)

(* Here is a new tactic: [rewrite x].  If [x : e] is an assumption in the proof state, then 
   [rewrite x] replaces [x] with [e] in the subgoal being proved.  For example,
   here is a proof that incrementing 1 produces 2: *)

Theorem inc1_is_2 : forall n, n=1 -> (fun x => x+1) n = 2.
Proof.
  intros n n_is_1. rewrite n_is_1. trivial.
Qed.

(* Exercise: tl_opt correct [2 star].
   Using [rewrite], prove the following theorems. For both, first explain in natural language 
   why the theorem should hold, before moving on to prove it with Coq. *)

Theorem nil_implies_tlopt_none :
  forall A : Type, forall lst : list A,
  lst = nil -> tl_opt lst = None.
Proof.
 intros.
 rewrite H.
 trivial.
Qed.

Theorem cons_implies_tlopt_some : 
  forall {A : Type} (h:A) (t : list A) (lst : list A), 
  lst = h::t -> tl_opt lst = Some t.
Proof.
intros.
rewrite H.
trivial.
Qed.















