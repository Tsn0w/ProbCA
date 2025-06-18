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

  (***********************************************************************************************)
  (*                                             Top                                             *)
  (***********************************************************************************************)
  Definition top : predicate := fun c => True.

  (***********************************************************************************************)
  (*                                            Bottom                                           *)
  (***********************************************************************************************)
  Definition bottom : predicate := fun c => False.

  (***********************************************************************************************)
  (*                                      Code Decidability                                      *)
  (***********************************************************************************************)
  (* These are the filter logic, for now assume, revisit later *)
  Parameter dec : predicate -> (Code -> bool).

  Axiom dec_monotone :
  forall (P P' : predicate),
    (forall x, P x -> P' x) ->
    forall x, dec P x = true -> dec P' x = true.


  (***********************************************************************************************)
  (*                                           TermRed                                           *)
  (***********************************************************************************************)
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

  (***********************************************************************************************)
  (*                                          Entailment                                         *)
  (***********************************************************************************************)
  (*
   * There are 2 options for entailment, given predicate P and Q we say P entails Q with probability
   * p and code c if:
   * 1. foreach realizer of P, say c', at least p-ratio codes from the application of c' and c are
   *    are realizers for Q.
   * 2. foreach realizer of P, say c', at least p codes from the application of c' and c are
   *    are realizers for Q.
   * Note the difference, in 1 we ask for total_prob (filter_md (App c' c) Q) >= p * total_prob (App c' c)
   * while in the 2.  we just need total_prob (filter_md (App c' c) Q) >= p.
   * When know better, see if should switch to the second one.
   *)
  Definition Entails (P Q: predicate) : Prop := exists (p: R) (c: Code), Probability.prob p ->
    (forall (c': Code), P c' ->
      Probability.total_prob (Probability.filter_md (dec Q) (App c' c)) >= p * Probability.total_prob (App c' c)).

End ProbCAToHOL.
