Require Import ProbCA.Common.
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
(**)
(** printing Code $C$ *)
(** printing CodeV $\isa{C}$ *)
(** printing EVar $V$ *)
(** printing ExprVar $E_?$ *)
(** printing evar $\mathit{evar}$ *)
(** printing eapp $\app$ *)
(** printing ecode $(\cdot)$ *)
(** printing EVarV $\isa{V}$ *)
(** printing ExprVarV $\isa{E}$ *)
(** printing esubst $\dot{e}[\cdot]$ *)
(**)
(** printing ef $e_f$ *)
(** printing ea $e_a$ *)

Create HintDb expr_hints.

(** *** Definition of Applicative Expressions *)

Module ApplicativeExpression.
  Fixpoint EVar (Code : SET) (n : nat) : Type :=
    match n with
      0 => Code
    | S n => option (EVar Code n)
    end.

  Fixpoint vcode {Code : SET} (c : Code) (n : nat) : EVar Code n :=
    match n with
      0 => c
    | S n => Some (vcode c n)
    end.

  Inductive ExprVar {Code : SET} {n : nat} : Type :=
      evar (c : EVar Code n)
    | eapp (ef ea : ExprVar).
  Arguments ExprVar : clear implicits.
  Arguments evar {Code} n c.
  Definition Expr (Code : SET) : Type := ExprVar Code 0.

  Fixpoint EVarV {Code : SET} (CodeV : Code -> Prop) {n : nat} : EVar Code n -> Prop :=
    match n with
      0 => CodeV
    | S n => fun v => match v with
        None => True
      | Some v => EVarV CodeV v
      end
    end.

  Inductive ExprVarV {Code : SET} (CodeV : Code -> Prop) {n : nat} : ExprVar Code n -> Prop
  := evarv (c : EVar Code n) : EVarV CodeV c -> ExprVarV CodeV (evar n c)
   | eappv (ef ea : ExprVar Code n) : ExprVarV CodeV ef -> ExprVarV CodeV ea -> ExprVarV CodeV (eapp ef ea).
  Hint Unfold EVarV : expr_hints.
  Hint Constructors ExprVarV : expr_hints.

  Fixpoint esubst {Code : SET} (c : Code) {n : nat} (e : ExprVar Code (S n)) : ExprVar Code n :=
    match e with
      evar _ v => evar n (match v with
                                    None => vcode c n
                                  | Some v => v
                          end)
    | eapp ef ea => eapp (esubst c ef) (esubst c ea)
    end.

  Lemma esubstv (Code : SET) (CodeV : Code -> Prop) (c : Code) (n : nat) (e : ExprVar Code (S n)) : CodeV c -> ExprVarV CodeV e -> ExprVarV CodeV (esubst c e).
    intros cv ev. induction ev; simpl; constructor; try auto. destruct c0; try assumption. induction n; auto.
  Qed.
  Hint Resolve esubstv : expr_hints.

  Definition ecode {Code : SET} (c : Code) {n : nat} : ExprVar Code n := evar n (vcode c n).
  Lemma ecodev (Code : SET) (CodeV : Code -> Prop) (c : Code) (n : nat) : CodeV c -> ExprVarV CodeV (n := n) (ecode c).
    intro. constructor. induction n; trivial.
  Qed.
  Hint Resolve ecodev : expr_hints.

End ApplicativeExpression.
