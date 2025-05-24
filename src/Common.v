From Coq Require Import Eqdep_dec.
From Coq Require Import Peano_dec.
(**)
(** printing SET $\mathbf{Set}$ *)
(** printing Empty $\varnothing$ *)
(** printing True %\coqdockw{True}% *)
(** printing False %\coqdockw{False}% *)
(** printing exists $\exists$ *)
(** printing exists2 $\exists$ *)
(** printing exists3 $\exists$ *)
(** printing & $\mathrel{\wedge}$ *)
(** printing nat $\N$ *)
(** printing bool $\B$ *)
(** printing fun $\lambda\!$ *)
(** printing => $\mapsto$ *)
(** printing IV $\isa{I}$ *)
(** printing EV $\iseq{I}$ *)
(** printing <: $<:$ *)
(** printing None $\mathit{None}$ *)
(** printing Some $\mathit{Some}$ *)
(** printing {| $\{\mathord{\mid}$ *)
(** printing |} $\mathord{\mid}\}$ *)


(** We use [SET] to ensure that a type belongs to the universe of sets rather than some larger universe.
    We cannot use the standard [Set] universe because we need [SET] to contain [Prop] to model impredicativity.*)

Definition SET : Type := Type.


Inductive Empty : SET :=.


(* begin hide *)
Inductive ex3 {A : Type} (P Q R : A -> Prop) : Prop
:= ex_intro3 : forall x:A, P x -> Q x -> R x -> ex3 P Q R.

Notation "'exists3' x , p & q & r" := (ex3 (fun x => p) (fun x => q) (fun x => r))
  (at level 200, x ident, p at level 200, right associativity) : type_scope.
Notation "'exists3' x : A , p & q & r" := (ex3 (A:=A) (fun x => p) (fun x => q) (fun x => r))
  (at level 200, x ident, A at level 200, p at level 200, right associativity,
    format "'[' 'exists3' '/ ' x : A , '/ ' '[' p & '/' q & '/' r ']' ']'")
  : type_scope.

Notation "'exists3' ' x , p & q & r" := (ex3 (fun x => p) (fun x => q) (fun x => r))
  (at level 200, x strict pattern, p at level 200, right associativity) : type_scope.
Notation "'exists3' ' x : A , p & q & r" := (ex3 (A:=A) (fun x => p) (fun x => q) (fun x => r))
  (at level 200, x strict pattern, A at level 200, p at level 200, right associativity,
    format "'[' 'exists3' '/ ' ' x : A , '/ ' '[' p & '/' q & '/' r ']' ']'")
  : type_scope.


Lemma inj_pair2_nat (T : nat -> Type) (n : nat) (t t' : T n) : existT T n t = existT T n t' -> t = t'.
  apply inj_pair2_eq_dec. exact eq_nat_dec.
Qed.

Ltac inj_pair2_nat := match goal with [ e : @existT nat _ ?n _ = @existT nat _ ?n _ |- _ ] => apply inj_pair2_nat in e end.

Create HintDb common_hints.

Hint Extern 4 => inj_pair2_nat : common_hints.


Ltac has_no_evar t := (has_evar t; fail 1) || idtac.
Ltac fresh_evar T t := let v := fresh "evar" in evar (v : T); let ev := eval unfold v in v in clear v; t ev.


Hint Extern 10 => match goal with [ H : _ /\ _ |- _ ] => destruct H end : common_hints.
Hint Resolve conj : common_hints.
Hint Extern 100 => match goal with [ H : ?P1 |- _ ] => match type of P1 with Prop => apply H end end : common_hints.
Hint Extern 5 ( exists n : nat, _ ) => exists 0 : common_hints.
Hint Extern 1 ( exists i : ?I, ?IV i ) => match goal with [ iv : IV ?i |- _ ] => exists i; exact iv end : common_hints.
(* end hide *)
