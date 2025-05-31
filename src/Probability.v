From Coq Require Import Reals.
From Coq Require Import List.
From Coq Require Import Lra.

Import ListNotations.

Open Scope R_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Probability.
  Definition prob (p: R) := 0 <= p <= 1.
  Check prob.

  Example prob_zero: prob 0.
    Proof. split. lra. lra. Qed.
  Example prob_one: prob 1.
    Proof. split. lra. lra. Qed.
  Lemma prob_mult: forall x y, prob x -> prob y -> prob (x * y).
  Proof.
    intros x y [Hx0 Hx1] [Hy0 Hy1]. split.
    - apply Rmult_le_pos. apply Hx0. apply Hy0.
    - replace 1 with (1 * 1) by lra. apply (Rmult_le_compat x 1 y 1).
      apply Hx0. apply Hy0. apply Hx1. apply Hy1.
  Qed.

  Record multi_dist (T: Type) := {
    support: list (T * R);

    (* Validate every element has valid probability *)
    valid_elem: Forall (fun x => prob (snd x) /\ (snd x) > 0) support;

    (* Validate total probability does not surpass 1 *)
    valid_distribution: fold_right Rplus 0%R
      (map (fun x => snd x) support) <= 1%R;
  }.

  (* Takes multi-distribution and return its total probability *)
  Definition total_probability {T: Type} (md: multi_dist T) : R :=
    fold_right Rplus 0%R (map (fun x => snd x) (support md)).

  Definition prob_of_elem {T: Type} (T_eq: T -> T -> bool) (md: multi_dist T) (e : T): R :=
    fold_right Rplus 0%R (map (fun x => if (T_eq (fst x) e) then (snd x) else 0) (support md)).

  Definition in_multi_dist {T: Type} (T_eq: T -> T -> bool) (md: multi_dist T) (e: T) : Prop := prob_of_elem T_eq md e > 0.


  (******************************************* Examples *******************************************)
  Program Definition flip {T:Type} (x y: T) : multi_dist T :=
    {| support := [(x, 0.5); (y, 0.5)];
    |}.
  Next Obligation. (* Proof valid_elem *)
    Proof.
       constructor.
       - simpl. unfold prob. lra.
       - constructor.
         + simpl. unfold prob. lra.
         + constructor.
    Qed.
  Next Obligation. (* Proof valid_distribution *)
    Proof. lra. Qed.




End Probability.
