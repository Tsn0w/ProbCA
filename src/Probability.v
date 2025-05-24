
From Coq Require Import Reals.
From Coq Require Import List.
From Coq Require Import Lra.

Import ListNotations.

Open Scope R_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope prob_scope.

Module Probability.
  Definition prob := { p : R | 0 <= p <= 1 }.
  Definition prob_val (p : prob) : R := proj1_sig p.

  (* const probability values *)
  Definition one : prob := exist _ R1 (conj Rle_0_1 (Rle_refl 1)).
  Definition zero : prob := exist _ R0 (conj (Rle_refl 0) Rle_0_1).

  (* probability operators *)
  Definition mult (p1 p2 : prob) : prob.
  Proof.
    destruct p1 as [x1 [H1x H1x']].
    destruct p2 as [x2 [H2x H2x']].
    exists (x1 * x2).
    split.
    - apply Rmult_le_pos; assumption.
    - assert (H : 1 * 1 = 1). apply Rmult_1_r. rewrite <- H.
      apply (Rmult_le_compat x1 1 x2 1); try assumption.
  Defined.
  Notation "p1 * p2" := (mult p1 p2) : prob_scope.

  Definition ge (p1 p2 : prob) : Prop := (proj1_sig p1) >= (proj1_sig p2).
  Notation "p1 >= p2" := (ge p1 p2) : prob_scope.

  Definition gt (p1 p2: prob) :Prop := (proj1_sig p1) > (proj1_sig p2).
  Notation "p1 > p2" := (gt p1 p2) : prob_scope.

  Definition eq (p1 p2: prob) :Prop := (proj1_sig p1) = (proj1_sig p2).
  Notation "p1 = p2" := (eq p1 p2) : prob_scope.

  Delimit Scope prob_scope with prob.
  Bind Scope prob_scope with prob.
  Global Open Scope prob_scope.

  Record MultiDist (T: Type) := {
    support : list (T * prob);
    valid_distribution : fold_right Rplus 0%R
      (map (fun x => prob_val (snd x)) support) <= 1%R;
  }.

   Lemma support_prob_nonneg{T} (lst : list (T * prob)) :
      0 <= fold_right Rplus 0 (map (fun x => prob_val (snd x)) lst).
    Proof.
      induction lst as [| [t p] tl IH].
      - simpl; lra.
      - simpl.
        destruct p as [pval [Hp0 Hp1]].
        apply Rplus_le_le_0_compat; assumption.
    Qed.

      Definition termination_probability {T: Type} (md: MultiDist T) : prob.
  Proof.
    destruct md as [lst Hvalid].
    set (r := fold_right Rplus 0 (map (fun x => prob_val (snd x)) lst)).
    assert (Hnonneg: 0 <= r) by (apply support_prob_nonneg).
    exists r; split; [assumption | assumption].
  Defined.

  (* TODO: Add proof or definition? *)
  Parameter prob_of : forall {T : Type}, MultiDist T -> T -> prob.
End Probability.
