Require Import ProbCA.Probability.
Require Import ProbCA.Expressions.

From Coq Require Import List.
Import ListNotations.


Open Scope prob_scope.

Definition SET : Type := Type.
Inductive Empty : SET :=.


Module Type ProbabilityApplicativeStructure.
  (* set of Codes *)
  Parameter Code : SET.

  (* The Application - on 2 codes returns multi-distribution of codes *)
  Parameter App: Code -> Code -> Probability.MultiDist Code.

  (* Reduction relation, "infered" from the application *)
  Parameter Red : Code -> Code -> Probability.prob -> Code -> Prop.

  (* Application relation, "infered" from the application also but only care if there are any results *)
  Parameter Term : Code -> Code -> Prop.

  (* Progress: if terminates, exists a result *)
  Parameter progress : forall cf ca : Code, Term cf ca -> exists (p: Probability.prob) (cr : Code),
      Red cf ca p cr /\ Probability.gt p Probability.zero.

  (* Exsistence: iff reduces, can be "found" in the the md *)
  Parameter existence: forall (cf ca cr : Code) (p: Probability.prob),
  Red cf ca p cr <-> Probability.gt (Probability.prob_of (App cf ca) cr) p.

  (* define later! *)
  Parameter Filter : Probability.MultiDist Code -> (Code -> Prop) ->  Probability.MultiDist Code -> Prop.

  Module ProbabilityApplicativeExpression.
    Export ApplicativeExpression.

    (* RedExpr tells whether expression reduce to code c with probability p *)
    Inductive RedExpr : Expr Code -> Probability.prob -> Code -> Prop
    := revar (c : Code) : RedExpr (evar 0 c) Probability.one c
     | reapp (ef ea : Expr Code) (cf ca cr: Code) (p1 p2 p3: Probability.prob):
          RedExpr ef p1 cf -> RedExpr ea p2 ca -> Red cf ca p3 cr
          -> RedExpr (eapp ef ea) (Probability.mult (Probability.mult p1 p2) p3) cr.

    (* TermExpr tells whether expression reduce to a code *)
    Inductive TermExpr : Expr Code -> Prop
    := tevar (c : Code) : TermExpr (evar 0 c)
     | teapp (ef ea : Expr Code) : TermExpr ef ->
        (exists (cf : Code) (p1: Probability.prob), RedExpr ef p1 cf -> TermExpr ea /\
          (exists (ca : Code) (p2: Probability.prob), RedExpr ea p2 ca -> Term cf ca)) -> TermExpr (eapp ef ea).

    (* TermRed tells wheter application of 2 "models" predicate with probability p *)
    Definition TermRed (cf ca : Code) (p : Probability.prob) (Pr : Code -> Prop) : Prop :=
      Term cf ca /\ exists md : Probability.MultiDist Code, Filter (App cf ca) Pr md /\ Probability.ge (Probability.termination_probability md) p.

    (* TermRedExpr tells whether expression "models" predicate with probability p *)
    Fixpoint TermRedExpr (e : Expr Code) (p : Probability.prob) (Pr : Code -> Prop) : Prop :=
      match e with
        evar _ c => Pr c
      | eapp ef ea => exists p1: Probability.prob, TermRedExpr ef p1
           (fun cf => exists p2: Probability.prob, TermRedExpr ea p2
              (fun ca => exists p3, TermRed cf ca p3 Pr /\ Probability.eq (Probability.mult (Probability.mult p1 p2) p3) p))
      end.
  End ProbabilityApplicativeExpression.

End ProbabilityApplicativeStructure.

Module Type ProbabilityCombinatoryAlgebra.
  Include ProbabilityApplicativeStructure.
  Import ProbabilityApplicativeExpression.

  (* encode expression with n free variable with specific code (the assigment) *)
  Parameter cencode : forall n : nat, ExprVar Code (S n) -> Code.

  (* $ \forall e \in E_1. \forall c_a, c_r. \forall p. c_{\lambda^0.e} \cdot c_a \downarrow_p c_r  \Longleftrightarrow  e[c_a] \downarrow_p c_r $ *)
  Parameter red_encode_0 : forall e: ExprVar Code 1,
    forall (ca cr: Code) (p: Probability.prob), Red (cencode 0 e) ca p cr <-> RedExpr (esubst ca e) p cr.

  (* $ \forall n. \forall e \in E_{n+2}. \forall c_a, c_r . c_{\lambda^{n+1}.e} \cdot c_a \downarrow_1 c_r \Longrightarrow c_r =  c_{\lambda^{n}.e[c_a]} $ *)
  Parameter red_encode_S : forall n: nat,
    forall e : ExprVar Code (S (S n)), forall ca cr : Code,
    Red (cencode (S n) e) ca Probability.one cr  -> cr = (cencode n (esubst ca e)).

  (* $ \forall e \in E_1. \forall c_a. \forall p e[c_a] \downarrow \Longleftrightarrow c_{\lambda^0.e} \cdot c_a \downarrow $ *)
  Parameter term_encode_0 : forall e: ExprVar Code 1,
    forall (ca : Code), TermExpr (esubst ca e) -> Term (cencode 0 e) ca.

  (* $ \forall n. \forall e \in E_{n+2} . \forall c_a. c_{\lambda^{n+1}.e} \cdot c_a \downarrow $ *)
  Parameter term_encode_S : forall n: nat,
    forall e : ExprVar Code (S (S n)), forall ca: Code, Term (cencode (S n) e) ca.
End ProbabilityCombinatoryAlgebra.

Module ProbabilityCombinatoryAlgebraTools (ProbCA : ProbabilityCombinatoryAlgebra).
  Import ProbCA.
  Import ProbabilityApplicativeExpression.

  (* if forall codes Pr implies Pr', then if TermRed cf ca p Pr holds then TermRed cf ca p Pr' holds *)
  Lemma termred_mono (cf ca : Code) (p: Probability.prob) (Pr Pr' : Code -> Prop) : (forall cr : Code, Pr cr -> Pr' cr) -> TermRed cf ca p Pr -> TermRed cf ca p Pr'.
  Proof.
  Admitted.

End ProbabilityCombinatoryAlgebraTools.
