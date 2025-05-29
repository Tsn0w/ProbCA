
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

  Definition MDElem (T: Type) : Type := (T * R)%type.
  Definition valid_MD_prob (p: R) := prob p /\ p > 0.
  Definition valid_MDElem {T: Type} (e: MDElem T) :=  valid_MD_prob (snd e).
  Definition total_prob (T: Type) (dist : list (MDElem T)) : R :=
  fold_right (fun e acc => snd e + acc) 0 dist.

  Definition mult_dist (T: Type) (dist: list (MDElem T)) : Prop :=
    total_prob dist <= 1 /\ Forall valid_MDElem dist.

  Definition flip_list := [(1, 0.5); (0, 0.5)].
  Example flip_multidist: mult_dist flip_list.
  Proof.
     unfold mult_dist. split.
     - simpl. lra.
     - unfold valid_MDElem. unfold valid_MD_prob. unfold prob.
       constructor.
       + simpl. lra.
       + constructor. simpl. lra. constructor.
  Qed.

  Definition multi_mult_dist {T U V: Type} (f : T -> U -> V) (dist1 : list (MDElem T)) (dist2 : list (MDElem U))
      : list (MDElem V) :=
    flat_map (fun e1: MDElem T =>
                let (x1, p1) := e1 in
                  map (fun e2 : MDElem U =>
                    let (x2, p2) := e2 in (f x1 x2, p1 * p2)
                  ) dist2
              ) dist1.

  Example flip_md_mult_flip_md_is_md: mult_dist (multi_mult_dist (fun x y => x + y) flip_list flip_list).
  Proof.
    unfold mult_dist. split.
    - simpl. lra.
    - simpl. unfold valid_MDElem. unfold valid_MD_prob. unfold prob. constructor.
      + simpl. lra.
      + constructor.
        -- simpl. lra.
        -- constructor.
           ++ simpl. lra.
           ++ constructor.
              * simpl. lra.
              * constructor.
  Qed.

End Probability.
