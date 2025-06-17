From Coq Require Import Reals.
From Coq Require Import List.
From Coq Require Import Lra.
Require Import Coq.Lists.ListSet.

Import ListNotations.

Open Scope R_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Probability.
  (***********************************************************************************************)
  (*                                 Probability definition                                      *)
  (***********************************************************************************************)
  Definition prob (p: R) := 0 <= p <= 1.

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


  (***********************************************************************************************)
  (*                                 multi-distribution definition                               *)
  (***********************************************************************************************)
  Definition md_elem (T: Type) : Type := (T * R)%type.
  Definition valid_md_prob (p: R) := prob p /\ p > 0.
  Definition valid_md_elem {T: Type} (e: md_elem T) :=  valid_md_prob (snd e).
  Fixpoint total_prob (T: Type) (l: list(md_elem T)) : R :=
    match l with
      | [] => 0
      | x :: l' => (snd x) + (total_prob l')
    end.

  Definition mult_dist (T: Type) (dist: list (md_elem T)) : Prop :=
    total_prob dist <= 1 /\ Forall valid_md_elem dist.

  Example empty_md: forall {T: Type}, mult_dist ([] : list (md_elem T)).
  Proof.
    intro T. simpl. unfold mult_dist. simpl. split.
    - lra.
    - constructor.
  Qed.

  Definition flip_list: list (md_elem nat):= [(1%nat, 0.5); (0%nat, 0.5)].
  Example flip_multidist: mult_dist flip_list.
  Proof.
     unfold mult_dist. split.
     - simpl. lra.
     - unfold valid_md_elem. unfold valid_md_prob. unfold prob.
       constructor.
       + simpl. lra.
       + constructor. simpl. lra. constructor.
  Qed.

  Lemma total_prob_geq_zero {T: Type} : forall (l: list (md_elem T)), mult_dist l -> 0 <= total_prob l.
  Proof.
  intros l Hdist.
  induction l as [| [x p] l' IH].
  - simpl. lra.
  - simpl in *. destruct Hdist as [Htotal Hforalls].
    inversion Hforalls as [| [x' p'] l'' Hvalid_elem Hrest_eq]; subst.
    unfold valid_md_elem, valid_md_prob, prob in Hvalid_elem.
    destruct Hvalid_elem as [[Hp0 _] Hp_pos]. apply Rplus_le_le_0_compat.
    simpl in Hp0.
    + apply Hp0.
    + apply IH. split.
      * simpl in Htotal. simpl in Hp0. lra.
      * apply Hrest_eq.
  Qed.


  (***********************************************************************************************)
  (*                                    Probability of Element                                   *)
  (***********************************************************************************************)
  Fixpoint prob_of {T: Type} (eq_dec : forall a b : T, {a = b} + {a <> b}) (t: T) (l: list (T * R)) : R :=
  match l with
    | [] => 0
    | (t', p) :: xs => if eq_dec t' t then p + prob_of eq_dec t xs else prob_of eq_dec t xs
  end.

  Example prob_of_1_at_flip_is_half: prob_of Nat.eq_dec 1%nat (flip_list) = 0.5.
  Proof.
    unfold prob_of. simpl. rewrite Rplus_0_r. reflexivity.
  Qed.

  (***********************************************************************************************)
  (*                                 Multiplication by scalar                                    *)
  (***********************************************************************************************)
  Fixpoint mult_md_by_scalar {T: Type} (p: R) (l: list (md_elem T)) : list (md_elem T) :=
    match l with
      | [] => []
      | (x1, p1) :: xs1 => (x1, p1 * p)::(mult_md_by_scalar p xs1)
    end.

  Lemma total_prob_scalar {T} (p: R) (l: list (md_elem T)) :
  total_prob (mult_md_by_scalar p l) = p * total_prob l.
Proof.
  induction l as [| [x q] l' IH]; simpl.
  - lra.
  - rewrite IH. lra.
Qed.

  Lemma scalar_multi_md {T: Type} : forall (p: R) (l: list (md_elem T)),
    prob p /\ p > 0 -> mult_dist l ->  mult_dist (mult_md_by_scalar p l).
  Proof.
    intros p l [[p0 p1] p0'] [Htotal Hvalid].
  split.
  - rewrite total_prob_scalar.
    replace 1 with (1 * 1) by lra.
    apply (Rmult_le_compat p 1 (total_prob l) 1); try lra.
    apply total_prob_geq_zero. split; assumption.
  - induction Hvalid as [| [x q] l' Hq_valid Hrest IH].
    + simpl. constructor.
    + simpl. constructor.
      * unfold valid_md_elem, valid_md_prob, prob in *.
        destruct Hq_valid as [[Hq0 Hq1] Hq_pos].
        split.
        -- simpl. simpl in Hq0, Hq1. split.
           ++ apply Rmult_le_pos; lra.
           ++ replace 1 with (1 * 1) by lra. apply Rmult_le_compat; lra.
        -- simpl. simpl in Hq_pos. apply Rmult_lt_0_compat. lra. apply p0'.
      * simpl in Htotal. unfold valid_md_elem in Hq_valid. simpl in Hq_valid.
        destruct Hq_valid as [q0 q1]. apply IH. lra.
Qed.


  (***********************************************************************************************)
  (*                                 Multiplication of mdists                                    *)
  (***********************************************************************************************)
  Fixpoint multi_list {T U V: Type} (f : T -> U -> V) (list1 : list (md_elem T)) (list2 : list (md_elem U))
      : list (md_elem V) :=
      match list1 with
        | [] => []
        | (x, p) :: t => (map (fun '(x', p') => (f x x', p * p')) list2) ++ multi_list f t list2
      end.

  Example flip_list_mult_flip_list_is_md: mult_dist (multi_list (fun x y => (x + y)%nat) flip_list flip_list).
  Proof.
    unfold mult_dist. split.
    - simpl. lra.
    - simpl. unfold valid_md_elem. unfold valid_md_prob. unfold prob. constructor.
      + simpl. lra.
      + constructor.
        -- simpl. lra.
        -- constructor.
           ++ simpl. lra.
           ++ constructor.
              * simpl. lra.
              * constructor.
  Qed.

  Lemma multi_list_app_split {T U V: Type}: forall (f: T -> U -> V) (x: md_elem T) (l1 : list (md_elem T)) (l2 : list (md_elem U)),
    multi_list f (x :: l1) l2 = (multi_list f [x] l2) ++ (multi_list f l1 l2).
  Proof.
    intros f x l1 l2.  destruct x as [xv xp]. simpl. rewrite app_nil_r. reflexivity.
  Qed.

  Lemma total_prob_split {T: Type}: forall (l1 l2: list (md_elem T)),
    total_prob l1 + total_prob l2 = total_prob (l1 ++ l2).
  Proof.
    intros l1 l2. induction l1 as [| [x p] l1' IHl1].
    - simpl. lra.
    - simpl. rewrite <- IHl1. lra.
  Qed.

Lemma total_prob_multi_list_nil : forall (T U V : Type) (f : T -> U -> V) (x : T) (p : R),
  total_prob (multi_list f [(x, p)] []) = p * (total_prob ([] : list (md_elem V))).
Proof.
  intros T U V f x p. simpl. lra.
Qed.

Lemma total_prob_mult_elem {T U V: Type}: forall  (f: T -> U -> V) (x: md_elem T) (l: list (md_elem U)),
    total_prob [x] * total_prob l = total_prob (multi_list f [x] l).
  Proof.
    intros f [xv xp] l. induction l as [| [x' p'] l' IHl'].
    - simpl. lra.
    - simpl. simpl in IHl'. rewrite <- IHl'. lra.
  Qed.


  Lemma total_prob_mult {T U V: Type}: forall  (f: T -> U -> V) (l1: list (md_elem T)) (l2: list (md_elem U)),
    total_prob l1 * total_prob l2 = total_prob (multi_list f l1 l2).
  Proof.
    intros f l1 l2. induction l1 as [| [x p] l1' IHl1'].
    - simpl. lra.
    - rewrite multi_list_app_split. rewrite <- total_prob_split. rewrite <- IHl1'.
      change (total_prob ((x, p) :: l1')) with (total_prob ([(x, p)] ++ l1')).
      assert (total_prob ([(x, p)] ++ l1') = total_prob [(x, p)] + total_prob l1').
        { simpl. lra. }
        rewrite H. rewrite <- total_prob_mult_elem. simpl. lra.
  Qed.

  Lemma valid_list_total_prob_geq_zero {T : Type} :
  forall (l : list (md_elem T)),
    Forall valid_md_elem l ->
    0 <= total_prob l.
  Proof.
    intros l Hvalid. induction Hvalid.
  - simpl. lra.
  - simpl. destruct x as [xv pval].
    assert (pval_ge_0: 0 <= pval).
      { unfold valid_md_elem, valid_md_prob in H. simpl in H. apply H. }
      simpl. lra.
  Qed.

  Lemma head_tail_md_is_md {T: Type}: forall (x: md_elem T) (l: list (md_elem T)),
    mult_dist (x :: l) -> mult_dist [x] /\ mult_dist l.
  Proof.
    intros [x0 p0] l Hmd.
    assert (pos_md: 0 <= total_prob ((x0, p0) :: l)).
      { apply total_prob_geq_zero.  apply Hmd. }
      destruct Hmd as [Ht Hv]. simpl in Ht.
      simpl in pos_md.
      inversion Hv as [|x l' Hfx Hfl Heq]; subst.
      unfold valid_md_elem, valid_md_prob in Hfx. simpl in Hfx.
      destruct Hfx as [Hpp0 Hg0p0].
      assert (total_prob_l_0: 0<= total_prob l).
        { apply valid_list_total_prob_geq_zero. apply Hfl. }
      assert (total_prob_l_1: total_prob l <= 1).
        { lra. }
      split.
      - split.
        + simpl. lra.
        + constructor.
          * unfold valid_md_elem, valid_md_prob. simpl. apply (conj Hpp0 Hg0p0).
          * constructor.
      - apply (conj total_prob_l_1 Hfl).
  Qed.

  Lemma multi_list_split_r {T U V: Type}:
    forall (f: T -> U -> V) (l1 : list (md_elem T)) (x: md_elem T) (l2 : list (md_elem U)),
    multi_list f (x::l1) l2 = multi_list f [x] l2 ++ multi_list f l1 l2.
  Proof.
    intros f l1 x l2.  destruct x as [tx px].
     simpl. rewrite app_nil_r. reflexivity.
  Qed.

  Lemma Forall_map :
    forall (A B : Type) (f : A -> B) (P : B -> Prop) (l : list A),
      Forall P (map f l) <-> Forall (fun x => P (f x)) l.
  Proof.
    intros A B f P l. split.
    - induction l; simpl.
      + constructor.
      + intros H. inversion H. constructor; auto.
    - induction l; simpl.
      + constructor.
      + intros H. inversion H. constructor; auto.
  Qed.

  Lemma valid_md_elem_map :
    forall (T U V : Type) (f : T -> U -> V) (x1 : T) (p1 : R) (x' : U) (p' : R),
      valid_md_elem (x1, p1) ->
      valid_md_elem (x', p') ->
      valid_md_elem (f x1 x', p1 * p').
  Proof.
    intros T U V f x1 p1 x' p' Hvalid1 Hvalid2.
    unfold valid_md_elem in *.
    destruct Hvalid1 as [Hle1 Hgt1].
    destruct Hvalid2 as [Hle2 Hgt2].
    simpl in *. unfold prob in *. destruct Hle1 as [Hle01 Hlg11].
    destruct Hle2 as [Hle02 Hlg12]. split.
    - unfold prob. split.
      + apply Rmult_le_pos; lra.
      + replace 1 with (1 * 1) by lra. apply Rmult_le_compat; lra.
    - apply Rmult_lt_0_compat; lra.
  Qed.

  Lemma multi_list_of_valid_elems_is_valid_elems {T U V: Type}:
      forall (f: T -> U -> V) (l1 : list (md_elem T)) (l2 : list (md_elem U)),
        Forall valid_md_elem l1 -> Forall valid_md_elem l2 ->
          Forall valid_md_elem (multi_list f l1 l2).
  Proof.
    intros f l1 l2 Hvalid1 Hvalid2.
    induction Hvalid1 as [| [x1 p1] l1' Hx1_valid Hl1' IH].
    - simpl. constructor.
    - rewrite multi_list_split_r. apply Forall_app. split.
      + simpl. rewrite app_nil_r.
        apply Forall_map. apply Forall_forall. intros [x' p'] Hin.
        apply valid_md_elem_map.
        * apply Hx1_valid.
        * apply Forall_forall with (x := (x', p')) in Hvalid2; auto.
      + apply IH.
  Qed.


  Lemma multi_md_md_is_md {T U V: Type} : forall (f: T -> U -> V) (l1 : list (md_elem T)) (l2 : list (md_elem U)),
    mult_dist l1 -> mult_dist l2 -> mult_dist (multi_list f l1 l2).
  Proof.
    intros f l1 l2 mdl1 mdl2.
    + induction l1 as [| [x p] l1' C].
      - simpl. apply empty_md.
      - destruct (@head_tail_md_is_md T (x, p) l1' mdl1) as [mdx mdl1'].
        assert (total_l1_pos : 0 <= total_prob l1').
          { apply total_prob_geq_zero. apply mdl1'. }
      destruct mdl1 as [l1total l1elems].
        simpl in l1total. rewrite multi_list_app_split. unfold mult_dist. split.
        * rewrite <- total_prob_split. rewrite <- total_prob_mult.
          assert (total_prob (multi_list f l1' l2) = total_prob l1' * total_prob l2).
            { rewrite <- total_prob_mult. reflexivity. }
          rewrite H. simpl.
          assert ((p + 0) * total_prob l2 + total_prob l1' * total_prob l2 = (p + total_prob l1') * total_prob l2).
            { lra. }
            rewrite H0. replace 1 with (1 *1) by lra. apply Rmult_le_compat.
            --  inversion l1elems as [| ?? Hhead Htail].
                apply Rplus_le_le_0_compat; try lra.
               ++ unfold valid_md_elem,valid_md_prob in Hhead. simpl in Hhead. lra.
            -- apply total_prob_geq_zero. apply mdl2.
            -- apply l1total.
            -- apply mdl2.
        * apply Forall_app. split.
            -- apply multi_list_of_valid_elems_is_valid_elems.
               ++ constructor. apply Forall_inv in l1elems. apply l1elems.
                  constructor.
               ++ apply mdl2.
            -- apply C. apply mdl1'.
  Qed.



  (***********************************************************************************************)
  (*                                     Filter of mdist                                         *)
  (***********************************************************************************************)
  Fixpoint filter_md {T : Type} (Pr : T -> bool) (l : list (md_elem T)) : list (md_elem T) :=
  match l with
  | [] => []
  | x :: xs => if Pr (fst x) then x :: filter_md Pr xs else filter_md Pr xs
  end.

  Lemma total_prob_filter_valid {T: Type}: forall (Pr: T-> bool) (l: list (md_elem T)),
    mult_dist l -> total_prob (filter_md Pr l) <= total_prob l.
  Proof.
    intros Pr l md. induction l as [| x xs IHxs].
    - simpl. lra.
    - simpl. destruct (@head_tail_md_is_md T x xs md) as [mdx mdxs].
      destruct (Pr (fst x)) eqn:Pr_vx.
      + simpl. apply Rplus_le_compat_l. apply IHxs. apply mdxs.
      + unfold mult_dist in mdx. destruct mdx as [totalx validx].
        apply Forall_inv in validx. unfold valid_md_elem, valid_md_prob in validx.
        destruct validx as [px g0x]. specialize (IHxs mdxs).
        apply Rle_trans with (r2 := total_prob xs).
        * apply IHxs.
        * lra.
  Qed.

  Lemma filter_md_is_md {T: Type}: forall (Pr: T -> bool) (l: list (md_elem T)),
    mult_dist l -> mult_dist (filter_md Pr l).
  Proof.
    intros Pr l md. induction l as [|x xs IH].
    - simpl. apply md.
    - destruct (@head_tail_md_is_md T x xs md) as [mdx mdxs].
      specialize (IH mdxs).
      destruct (Pr (fst x)) eqn:Pr_vx.
      + simpl. rewrite Pr_vx. unfold mult_dist. split.
        * simpl.
          assert (Hfilt: total_prob (filter_md Pr xs) <= total_prob xs)
            by (apply total_prob_filter_valid; exact mdxs).
          assert (H: snd x + total_prob (filter_md Pr xs) <= snd x + total_prob xs)
            by (apply Rplus_le_compat_l; exact Hfilt).
          assert (Hsum : snd x + total_prob xs <= 1)
            by (destruct md as [Hsum _]; exact Hsum).
            eapply Rle_trans; [apply H | apply Hsum].
        * constructor.
          -- destruct mdx as [totalx validx]. apply Forall_inv in validx. apply validx.
          -- apply IH.
      + simpl. rewrite Pr_vx. apply IH.
  Qed.

  Lemma filter_md_monotone {T} (l : list (md_elem T)) (Pr Pr' : T -> bool) :
    mult_dist l -> (forall x, Pr x = true -> Pr' x = true) ->
  total_prob (filter_md Pr l) <= total_prob (filter_md Pr' l).
  Proof.
    intros mdl mono_pred. induction l as [| x xs IHxs].
    - simpl. lra.
    - simpl. destruct (@head_tail_md_is_md T x xs mdl) as [mdx mdxs].
      destruct (Pr (fst x)) eqn:Pr_vx.
      + assert (Pr'_vxtrue : Pr' (fst x) = true) by now apply mono_pred.
        rewrite Pr'_vxtrue. simpl. apply Rplus_le_compat_l. apply IHxs.
        apply mdxs.
      + destruct (Pr' (fst x)) eqn:Pr'_vx.
        * simpl. eapply Rle_trans.
          -- apply IHxs. apply mdxs.
          -- unfold mult_dist in mdx. destruct mdx as [totalx validx].
             apply Forall_inv in validx. unfold valid_md_elem, valid_md_prob in validx.
             destruct validx as [px g0x].
             apply Rle_trans with (r2 := 0 + total_prob (filter_md Pr' xs)).
             ++ right. ring.
             ++ apply Rplus_le_compat_r. apply Rlt_le. exact g0x.
        * apply IHxs. apply mdxs.
  Qed.

End Probability.
