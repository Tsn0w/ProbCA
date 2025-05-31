Require Import ProbCA.Probability.
Require Import ProbCA.Expressions.
From Coq Require Import Reals.
From Coq Require Import Lra.

From Coq Require Import List.
Import ListNotations.

Open Scope R_scope.

Definition SET : Type := Type.
Inductive Empty : SET :=.

Module Type ProbabilityApplicativeStructure.
  (* set of Codes *)
  Parameter Code : SET.

  (*
   * The Application - on 2 codes returns multi-distribution of codes
   * applicaiton is valid is the result is indeed a multi-distribution
   *)
  Parameter App: Code -> Code -> list (Probability.md_elem Code).
  (* Validate App *)
  Definition VApp (cf ca: Code) : Prop := Probability.mult_dist (App cf ca).

  (* Paramter to compare codes, probably temporary till understand how to do this better! *)
  Parameter eq_dec : forall (c c' : Code), {c = c'} + {c <> c'}.

  (* Reduction relation, "infered" from the application
   * The > can not be => 0, because than we than can have termination without any outcomes
   * But this might be ok, since if we use p = 0, then we obviously want chaos.
   *)
  Definition Red (cf ca: Code) (p: R) (cr: Code) : Prop :=
    VApp cf ca /\ Probability.prob p /\ Probability.prob_of eq_dec cr (App cf ca) > p.

  (* Application relation, "infered" from the application also but only care if there are any results *)
  (* consider change to take p also *)
  Parameter Term : Code -> Code -> Prop.

  (* Progress: if terminates, exists a result *)
  Parameter progress : forall cf ca : Code, Term cf ca -> exists (p: R) (cr : Code),
      Red cf ca p cr /\ p >  0.

  (* Exsistence: iff reduces, can be "found" in the the md *)
  Lemma existence: forall (cf ca cr : Code) (p: R),
  Red cf ca p cr <-> VApp cf ca /\ Probability.prob p /\ Probability.prob_of eq_dec cr (App cf ca) > p.
  Proof.
    intros cf ca cr p. unfold Red. reflexivity.
  Qed.

  Lemma reduction_imply_lower: forall (p1 p2: R) (cf ca cr: Code),
    Probability.prob p2 -> p1 > p2 -> Red cf ca p1 cr -> Red cf ca p2 cr.
  Proof.
    intros p1 p2 cf ca cr Vp2 Hlt [Happ [Hp1 Hgt]].
    split; [assumption|]. split.
    - apply Vp2.
    - lra.
  Qed.
End ProbabilityApplicativeStructure.

Module ProbabilityApplicativeExpression.
  Include ProbabilityApplicativeStructure.
  Export ApplicativeExpression.

  (* RedExpr tells whether expression reduce to code c with probability p *)
  Inductive RedExpr : Expr Code -> R -> Code -> Prop
    :=
      (* Ideally its enough to write only 1, but do I need to enforce the nubmer to be a valid probability? *)
      revar (c : Code): RedExpr (evar 0 c) 1 c
    | reapp (ef ea : Expr Code) (cf ca cr: Code) (p: R):
        RedExpr ef p cf -> RedExpr ea p ca -> Red cf ca p cr
  -> RedExpr (eapp ef ea) (p * p * p) cr.

  (* TermExpr tells whether expression reduce to a code *)
  Inductive TermExpr : Expr Code -> Prop
  := tevar (c : Code) : TermExpr (evar 0 c)
    | teapp (ef ea : Expr Code) : TermExpr ef -> (exists (p: R), Probability.prob p ->
      (exists (cf : Code), RedExpr ef p cf -> TermExpr ea /\
        (exists (ca : Code), RedExpr ea p ca -> Term cf ca))) -> TermExpr (eapp ef ea).

End ProbabilityApplicativeExpression.

Module Type ProbabilityCombinatoryAlgebra.
  Include ProbabilityApplicativeStructure.
  Import ProbabilityApplicativeExpression.

  (* encode expression with n free variable with specific code (the assigment) *)
  Parameter cencode : forall n : nat, ExprVar Code (S n) -> Code.

  (* $ \forall e \in E_1. \forall c_a, c_r. \forall p. c_{\lambda^0.e} \cdot c_a \downarrow_p c_r  \Longleftrightarrow  e[c_a] \downarrow_p c_r $ *)
  Parameter red_encode_0 : forall e: ExprVar Code 1,
    forall (ca cr: Code) (p: R), Probability.prob p -> Red (cencode 0 e) ca p cr <-> RedExpr (esubst ca e) p cr.

  (* $ \forall n. \forall e \in E_{n+2}. \forall c_a, c_r . c_{\lambda^{n+1}.e} \cdot c_a \downarrow_1 c_r \Longrightarrow c_r =  c_{\lambda^{n}.e[c_a]} $ *)
  Parameter red_encode_S : forall n: nat,
    forall e : ExprVar Code (S (S n)), forall ca cr : Code,
    Red (cencode (S n) e) ca 1 cr  -> cr = (cencode n (esubst ca e)).

  (* $ \forall e \in E_1. \forall c_a. \forall p e[c_a] \downarrow \Longleftrightarrow c_{\lambda^0.e} \cdot c_a \downarrow $ *)
  Parameter term_encode_0 : forall e: ExprVar Code 1,
    forall (ca : Code), TermExpr (esubst ca e) -> Term (cencode 0 e) ca.

  (* $ \forall n. \forall e \in E_{n+2} . \forall c_a. c_{\lambda^{n+1}.e} \cdot c_a \downarrow $ *)
  Parameter term_encode_S : forall n: nat,
    forall e : ExprVar Code (S (S n)), forall ca: Code, Term (cencode (S n) e) ca.
End ProbabilityCombinatoryAlgebra.
