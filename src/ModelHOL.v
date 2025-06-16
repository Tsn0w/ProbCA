Require Import ProbCA.ProbCA.

From Coq Require Import Reals.
From Coq Require Import Lra.

Module ProbCAToHOL (Import PrCA : ProbCA.ProbabilityCombinatoryAlgebra).
  Import PrCA.

  (* Predicate is a set of codes indicate which codes holds the predicate *)
  Definition predicate := Code -> Prop.

  Definition entails (P Q : predicate) (e: Expr Code):= forall c, P c -> Probabil
End ProbCAToHOL.

(*
  Define predicate/entailemnt/Lemma/...
    (* TermRed tells wheter application of 2 "models" predicate with probability p *)
    Definition TermRed (cf ca : Code) (p : R) (Pr : Code -> Prop) : Prop :=
      VApp cf ca /\ Term cf ca /\ Probability.prob p /\ Probability.total_prob (Probability.Filter (App cf ca) Pr) > p.

    (* TermRedExpr tells whether expression "models" predicate with probability p *)
    Fixpoint TermRedExpr (e : Expr Code) (p : R) (Pr : Code -> Prop) : Prop :=
      match e with
        evar _ c => Pr c /\ Probability.prob p
      | eapp ef ea => exists p1: R, Probability.prob p1 /\ TermRedExpr ef p1
           (fun cf => exists p2: R, Probability.prob p2 /\ TermRedExpr ea p2
           (fun ca => exists p3, TermRed cf ca p3 Pr /\ (p1 * p2 * p3) < p))
      end.
 *)

Module ProbabilityCombinatoryAlgebraTools (ProbCA : ProbCA.ProbabilityCombinatoryAlgebra).
  Import ProbCA.
  Import ProbCA.ProbabilityApplicativeExpression.

  (* if forall codes Pr implies Pr', then if TermRed cf ca p Pr holds then TermRed cf ca p Pr' holds *)
  Lemma termred_mono (cf ca : Code) (p: R) (Pr Pr' : Code -> Prop) :
    (forall cr : Code, Pr cr -> Pr' cr) -> TermRed cf ca p Pr -> .TermRed cf ca p Pr'.
  Proof.
    intros cr. unfold TermRed. intros [Hvapp [Hterm [Hp Htp]]].
    split.
    - apply Hvapp.
    - split.
      + apply Hterm.
      + split.
        * apply Hp.
        * apply Htp.
  Qed.

End ProbabilityCombinatoryAlgebraTools.
