Require Import ProbCA.ProbCA.
Require Import ProbCA.Expressions.

From Coq Require Import Reals.
From Coq Require Import Lra.

Require Import List.
Import ListNotations.

Module ProbCAToHOL (Import PrCA : ProbCA.ProbabilityCombinatoryAlgebra).
  Import PrCA.
  Import Probability.
  Export ApplicativeExpression.

  (* Predicate is a set of codes indicate which codes holds the predicate *)
  Definition predicate := Code -> Prop.

  (* Top predicate where any code realize it *)
  Definition top : predicate := fun c => True.

  (* Bottom predicate where no code realize it *)
  Definition bottom : predicate := fun c => False.

  (* For Filter - assume can conver predicate to bool for simplicity, revisit later *)
  Parameter dec : predicate -> (Code -> bool).

  (* Is it legit to assume that?? *)
  Axiom dec_monotone :
  forall (P P' : predicate),
    (forall x, P x -> P' x) ->
    forall x, dec P x = true -> dec P' x = true.

  (* how to better call TermRed?? modality? *)
  (* TermRed tells wheter application of 2 "models" predicate with probability p *)
  Definition TermRed (cf ca : Code) (p : R) (Pr : predicate) : Prop :=
    VApp cf ca /\ Term cf ca /\ Probability.prob p
    /\ Probability.total_prob (Probability.filter_md (dec Pr) (App cf ca)) > p.

  (* TermRedExpr tells whether expression "models" predicate with probability p *)
  Fixpoint TermRedExpr (e : Expr Code) (p : R) (Pr : Code -> Prop) : Prop :=
    match e with
      evar _ c => Pr c /\ Probability.prob p
    | eapp ef ea => exists p1: R, Probability.prob p1 /\ TermRedExpr ef p1
         (fun cf => exists p2: R, Probability.prob p2 /\ TermRedExpr ea p2
         (fun ca => exists p3, TermRed cf ca p3 Pr /\ (p1 * p2 * p3) < p))
    end.

  (* if forall codes Pr implies Pr', then if TermRed cf ca p Pr holds then TermRed cf ca p Pr' holds *)
  Lemma termred_mono (cf ca : Code) (p: R) (Pr Pr' : predicate) :
    (forall cr : Code, Pr cr -> Pr' cr) -> TermRed cf ca p Pr -> TermRed cf ca p Pr'.
  Proof.
    intros cr. unfold TermRed. intros [Hvapp [Hterm [Hp Htp]]].
    split.
    - apply Hvapp.
    - split.
      + apply Hterm.
      + split.
        * apply Hp.
        * eapply Rlt_le_trans.
          -- apply Htp.
          -- apply Probability.filter_md_monotone. apply Hvapp.
             intros x Hpx. apply (dec_monotone Pr Pr'). auto. apply Hpx.
  Qed.

End ProbCAToHOL.
