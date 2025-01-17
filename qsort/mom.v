Require Import SetsClass.SetsClass.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import PL.FixedPoint.
Require Import Coq.Lists.List.
Require Import PL.Monad.
Import SetsNotation
       KleeneFix Sets_CPO
       Monad
       MonadNotation.
Local Open Scope sets.
Local Open Scope Z.
Local Open Scope monad.

Module QSortExample2.
Import SetMonadHoare
       SetMonadOperator0
       SetMonadOperator1
       ListNotations.

Fixpoint insert (x : Z) (l : list Z) : list Z :=
  match l with
  | nil => x :: nil 
  | y :: l' => if x <=? y then x :: l else y :: insert x l'
  end.

Lemma insert_perm:
 forall x l, Permutation (x :: l) (insert x l).
Proof.
 intros x l.
 induction l; simpl.
 - apply Permutation_refl.
 - destruct (x <=? a) eqn:E.
   + apply Permutation_refl.
   + apply perm_trans with (a :: x :: l).
     * apply perm_swap.
     * apply perm_skip.
       apply IHl.
Qed.

Definition insertion_sort_body:
  list Z * list Z -> SetMonad.M (ContinueOrBreak (list Z * list Z) (list Z)) :=
  fun '(rest_list, current_ret) =>
    match rest_list with
    | nil => break current_ret
    | x :: rest_list' =>
      continue (rest_list', insert x current_ret)
    end.

Definition insertion_sort (l : (list Z)): SetMonad.M (list Z):=
  repeat_break insertion_sort_body (l, nil).

Lemma insertion_sort_perm:
 forall l,
  Hoare (insertion_sort l) (Permutation l).
Proof.
  intros.
  unfold insertion_sort.
  apply (Hoare_repeat_break _ 
    (fun '(rest, sorted) => Permutation l (rest ++ sorted))).
  
  intros [rest sorted] H.
  destruct rest.
  
  unfold insertion_sort_body.

  - apply Hoare_ret. 
    rewrite app_nil_l in H.
    exact H.
    
  - apply Hoare_ret.
    simpl in *.
    apply perm_trans with (z :: rest ++ sorted).
   * apply H.
   * apply perm_trans with (rest ++ z :: sorted).
   + apply Permutation_middle.
   + rewrite <- insert_perm.
    apply Permutation_refl.
    
  - rewrite app_nil_r.
    apply Permutation_refl.  
Qed.

Fixpoint get_nth (n: nat) (l: list Z) : Z :=
  match n, l with
  | O, x::_ => x
  | S n', _::l' => get_nth n' l'
  | _, nil => 0
end.

Definition In' (l: list Z) (x : Z): Prop :=
  In x l.

Lemma get_nth_in:
  forall (k: nat) (l: list Z),
    (k < length l)%nat -> In' l (get_nth k l).
Proof.
  induction k; intros l H; simpl.
  - destruct l; simpl in H.
   + lia.
   + left. reflexivity.
  - destruct l; simpl in H.
   + lia.
   + right. apply IHk. lia.
Qed.

Definition median (l : (list Z)): SetMonad.M Z:=
  sorted <- insertion_sort l;;
  let len := length sorted in
  ret (get_nth (len / 2) sorted).

Lemma median_correct: 
  forall l,
  l <> nil ->
  Hoare (median l) (In' l).
Proof.
  unfold Hoare, median.
  intros l Hnonempty x.
  eapply Hoare_bind.
  - apply insertion_sort_perm.
  - intros sorted Hperm.
    unfold ret, set_monad, SetMonad.ret.
    unfold Hoare.
    intros.
    sets_unfold in H.
    rewrite <- H.
    assert (Hin_sorted: In' sorted (get_nth (length sorted / 2) sorted)).
    {
      apply get_nth_in.
      apply Nat.div_lt.
      assert (Z.of_nat(length sorted) > 0) as Hlen.
      {
        apply Permutation_length in Hperm.
        rewrite <- Hperm.
        destruct l.
        - contradiction Hnonempty; reflexivity.
        - simpl; lia.
      }
       * lia.
       * lia.
    }
    apply Permutation_in with sorted; auto.
    rewrite <- Hperm.
    reflexivity.
Qed.

Definition get_medians_body:
((list Z) * (list Z)) -> SetMonad.M (ContinueOrBreak ((list Z) * (list Z)) (list Z)) :=
  fun '(rest , current_l) =>
    match rest with
    | a :: b :: c :: d :: e :: rest' =>
      m <- median [a; b; c; d; e];; continue (rest', m :: current_l)
    | nil => break current_l
    | _ => m <- median rest;; break (m :: current_l)
    end.

Definition get_medians (l: list Z): SetMonad.M (list Z):=
  repeat_break get_medians_body (l, nil).

Definition list_include_nonempty (l l': list Z):=
    (l' <> nil) /\ (forall x: Z, In x l' -> In x l).

Definition list_include (l l': list Z) :=
  forall x: Z, In x l' -> In x l.

Lemma get_medians_no_empty:
forall l: list Z,
  l <> nil -> Hoare (get_medians l)
    (fun l' => l' <> nil).
    Proof.
    intros l H.
    unfold get_medians.
    apply (Hoare_repeat_break _
      (fun '(rest, current) => rest = nil -> current <> nil)).
    intros [rest current] H_inv.
    unfold get_medians_body.
    destruct rest as [ | a [ | b [ | c [ | d [ | e rest']]]]].
    
    - apply Hoare_ret.
      apply H_inv; reflexivity.
      
    - eapply Hoare_bind.
      + apply median_correct.
        intros H1. discriminate H1.
      + intros m _.
        apply Hoare_ret.
        intros H1. discriminate H1.
        
    - eapply Hoare_bind.
      + apply median_correct.
        intros H1. discriminate H1.
      + intros m _.
        apply Hoare_ret.
        intros H1. discriminate H1.
        
    - eapply Hoare_bind.
      + apply median_correct.
        intros H1. discriminate H1.
      + intros m _.
        apply Hoare_ret.
        intros H1. discriminate H1.
        
    - eapply Hoare_bind.
      + apply median_correct.
        intros H1. discriminate H1.
      + intros m _.
        apply Hoare_ret.
        intros H1. discriminate H1.
        
    - eapply Hoare_bind.
      + apply median_correct.
        intros H1. discriminate H1.
      + intros m _.
        apply Hoare_ret.
        intros H_rest.
        intros H1. discriminate H1.
    
    - intros H_empty.
      contradiction H.
Qed.


Theorem get_medians_include:
forall l: list Z,
 Hoare (get_medians l) 
  (list_include l).
  Proof.
  intros l.
  unfold get_medians.
  apply (Hoare_repeat_break _ 
    (fun '(rest, curr) => 
      (forall x, In x curr -> In x l) /\ 
      (forall x, In x rest -> In x l))).
  
  intros [rest curr] [Hcurr Hrest].
  destruct rest as [|a [|b [|c [|d [|e rest']]]]].
  
  - unfold get_medians_body.
    apply Hoare_ret.
    intros x Hin. apply Hcurr, Hin.
    
  - unfold get_medians_body.
    eapply Hoare_bind.
    + apply median_correct.
      discriminate.
    + intros m Hm.
      apply Hoare_ret.
      intros x Hin.
      simpl in Hin.
      destruct Hin as [Heq | Hin].
      * subst x.
        unfold In' in Hm.
        apply Hrest.
        apply Hm.
      * apply Hcurr, Hin.
        
  - unfold get_medians_body.
    eapply Hoare_bind.
    + apply median_correct.
      discriminate.
    + intros m Hm.
      apply Hoare_ret.
      intros x Hin.
      simpl in Hin.
      destruct Hin as [Heq | Hin].
      * subst x.
        unfold In' in Hm.
        apply Hrest.
        apply Hm.
      * apply Hcurr, Hin.
        
  - unfold get_medians_body.
    eapply Hoare_bind.
    + apply median_correct.
      discriminate.
    + intros m Hm.
      apply Hoare_ret.
      intros x Hin.
      simpl in Hin.
      destruct Hin as [Heq | Hin].
      * subst x.
        unfold In' in Hm.
        apply Hrest.
        apply Hm.
      * apply Hcurr, Hin.
        
  - unfold get_medians_body.
    eapply Hoare_bind.
    + apply median_correct.
      discriminate.
    + intros m Hm.
      apply Hoare_ret.
      intros x Hin.
      simpl in Hin.
      destruct Hin as [Heq | Hin].
      * subst x.
        unfold In' in Hm.
        apply Hrest.
        apply Hm.
      * apply Hcurr, Hin.
        
  - unfold get_medians_body.
    eapply Hoare_bind.
    + apply median_correct.
      discriminate.
    + intros m Hm.
      simpl in Hm.
      apply Hoare_ret.
      split.
      * intros x Hin.
        simpl in Hin.
        destruct Hin as [Heq | Hin].
        -- assert (In m (a::b::c::d::e::rest')).
        {
          destruct Hm as [H1|[H2|[H3|[H4|[H5|F]]]]].
          - subst a. simpl. left. reflexivity.
          - subst b. simpl. right. left. reflexivity.
          - subst c. simpl. right. right. left. reflexivity.
          - subst d. simpl. right. right. right. left. reflexivity.
          - subst e. simpl. right. right. right. right. left. reflexivity.
          - contradiction.
        }
        specialize (Hrest m H).
        rewrite Heq in Hrest.
        apply Hrest.
        -- specialize (Hcurr x Hin).
        apply Hcurr.
      * intros x Hin.
        apply Hrest.
        right. right. right. right. right.
        exact Hin.
  - split.
    + intros x H; contradiction.
    + intros x H; assumption.
Qed.

Theorem get_medians_correct:
forall l: list Z,
  l <> nil -> Hoare (get_medians l)
    (list_include_nonempty l).
Proof.
  unfold list_include_nonempty.
  unfold Hoare.
  intros l.
  split.
  * apply (get_medians_no_empty l H a H0).
  * apply (get_medians_include l).
    exact H0.
Qed.
             
Definition partition (pivot: Z) (l: list Z): SetMonad.M (list Z * list Z * list Z) :=
  fun '(l1, l2, l3) =>
    Permutation l (l1 ++ l2 ++ l3)
    /\ (forall x, In x l1 -> x < pivot)
    /\ (forall x, In x l2 -> x = pivot)
    /\ (forall x, In x l3 -> x > pivot).

Lemma partition_correct:
  forall pivot l,
    Hoare (partition pivot l)
      (fun '(l1, l2, l3) =>
        Permutation l (l1 ++ l2 ++ l3)).
Proof.
  intros pivot l.
  unfold Hoare, partition.
  intros triple.
  destruct triple as [[l1 l2] l3].
  sets_unfold.
  intros [H_perm [H_l1 [H_l2 H_l3]]].
  exact H_perm.
Qed.

Definition MedianOfMedians_body
      (W: list Z -> nat -> SetMonad.M Z)
      (l: list Z)
      (k: nat)
  : SetMonad.M Z
  :=
  choice
    ((test (length l < 5)%nat);;
      sorted <- insertion_sort l;;
      ret (get_nth k sorted))
    ((test (length l >= 5)%nat);;
      medians <- get_medians l;;
      pivot <- W medians (length medians / 2)%nat;;
      '(lo, pivots, hi) <- partition pivot l;;
      choice
        ((test (k < length lo)%nat);;
          W lo k)
        (choice
          ((test (length lo <= k < length lo + length pivots)%nat);;
            ret pivot)
          ((test (length lo + length pivots <= k)%nat);;
            W hi (k - (length lo) - (length pivots))%nat))).

Definition MedianOfMedians: list Z -> nat -> SetMonad.M Z :=
  Kleene_LFix MedianOfMedians_body.

Lemma permutation_in:
  forall (p q: list Z) (x: Z),
    Permutation p q -> In' p x <-> In' q x.
Proof.
  intros p q x H.
  split; intros HIn.
  - apply Permutation_sym in H.
   induction H.
   + assumption.
   + simpl in *. destruct HIn; auto.
   + simpl in *. destruct HIn; auto.
     destruct H.
     * left; auto.
     * right; auto.
   + auto.

  - induction H.
   + assumption. 
   + simpl in *. destruct HIn; auto.
   + simpl in *. destruct HIn; auto.
     destruct H.
     * left; auto.
     * right; auto.
   + auto.
Qed.

Lemma not_nil_length_pos: forall (A: Type) (l: list A),
  l <> nil -> (length l > 0)%nat.
Proof.
  intros A l Hnil.
  destruct l as [|x l'].
  - contradiction.
  - simpl. 
    apply gt_Sn_O. 
Qed.

Lemma list_length_half_lt: forall (a: list Z),
  a <> nil -> (length a / 2 < length a)%nat.
Proof.
  intros.
  apply not_nil_length_pos in H.
  apply Nat.div_lt_upper_bound.
  - nia.
  - assert (H1: (length a + length a = 2 * length a)%nat).
  { lia. }
  rewrite <- H1.
  apply Nat.lt_add_pos_r.
  exact H.
Qed.

Lemma Kleene_list_include (l l': list Z):
  forall n k: nat, list_include l l' -> Hoare (Nat.iter n MedianOfMedians_body ∅ l' k) (In' l') -> Hoare (Nat.iter n MedianOfMedians_body ∅ l' k) (In' l).
Proof.
  intros.
  eapply Hoare_conseq; [| apply H0].
  intros.
  unfold list_include in H.
  pose proof H a H1.
  apply H2.
Qed.

Lemma list_partition_include (l l1 l2: list Z):
  Permutation l (l1 ++ l2) -> (list_include l l1 /\ list_include l l2).
Proof.
  unfold list_include.
  split.
  + intros x Hin.
    apply Permutation_in with (l1 ++ l2).
    - symmetry.
      exact H.
    - apply in_or_app.
    left.
    exact Hin.   
  + intros x Hin. 
    apply Permutation_in with (l1 ++ l2).
    - symmetry.
      exact H.
    - apply in_or_app.
    right.
    exact Hin.   
Qed.  

Lemma list_partition_length (l l1 l2: list Z):
  Permutation l (l1 ++ l2) -> (length l = length l1 + length l2)%nat.
Proof.
  intros.
  apply Permutation_length in H.
  rewrite H.
  apply app_length.
Qed.

Theorem MedianOfMedians_correct:
  forall l k,
    (k < length l)%nat ->
    Hoare (MedianOfMedians l k) (fun x => In' l x).
Proof.
  intros.
  unfold MedianOfMedians.
  unfold Kleene_LFix.
  unfold_CPO_defs.
  intros a [n ?].
  revert a H0.
  revert H.
  revert k.
  revert l.
  change (forall l k, (k < length l)%nat -> Hoare (Nat.iter n MedianOfMedians_body ∅ l k) (In' l)).
  induction n; simpl.
  + unfold Hoare; sets_unfold; tauto.
  + unfold MedianOfMedians_body at 1; intros.
    apply Hoare_choice.
    - apply Hoare_test_bind; intros.
      eapply Hoare_bind.
      * apply insertion_sort_perm.
      * intros; apply Hoare_ret.
        pose proof permutation_in l a (get_nth k a) H1.
        rewrite H2; apply get_nth_in.
        assert (length l = length a). {
          apply Permutation_length; exact H1.
        }
        lia.
    - apply Hoare_test_bind; intros.
      eapply Hoare_bind; [apply get_medians_correct |]. {
        unfold not.
        intros.
        rewrite H1 in H0.
        simpl in H0.
        lia.
      }
      intros a [? ?].
      eapply Hoare_bind. {
        pose proof list_length_half_lt a H1.
        pose proof IHn a (length a / 2)%nat H3.
        apply H4.
      }
      intros.
      eapply Hoare_bind; [apply partition_correct |].
      intros [[l1 l2] l3] ?.
      apply Hoare_choice. {
        apply Hoare_test_bind.
        intros.
        pose proof IHn l1 k H5.
        pose proof list_partition_include l l1 (l2 ++ l3) H4 as [? ?].
        pose proof Kleene_list_include l l1 n k H7 H6.
        exact H9.
      }
      apply Hoare_choice. {
        apply Hoare_test_bind.
        intros.
        apply Hoare_ret.
        pose proof H2 a0 H3.
        apply H6.
      }
      apply Hoare_test_bind.
      intros.
      eapply Hoare_conseq.
      2: {
        pose proof list_partition_length l l1 (l2 ++ l3) H4.
        pose proof app_length l2 l3.
        rewrite H7 in H6.
        assert((k - length l1 - length l2 < length l3)%nat). {
          lia.
        }
        pose proof IHn l3 (k - length l1 - length l2)%nat H8.
        apply H9.
      }
      intros.
      pose proof app_assoc l1 l2 l3.
      rewrite H7 in H4.
      pose proof list_partition_include l (l1 ++ l2) l3 H4 as [? ?].
      apply H9.
      apply H6.
Qed.

Fixpoint count_le (x : Z) (l : list Z) : nat :=
  match l with
  | nil => 0
  | y :: l' => if x >=? y then 1 + count_le x l' else count_le x l'
  end.

Fixpoint count_ge (x : Z) (l : list Z) : nat :=
  match l with
  | nil => 0
  | y :: l' => if x <=? y then 1 + count_ge x l' else count_ge x l'
  end.

Definition is_median: Prop :=
  forall l, Hoare (median l) (fun x => (count_le x l * 2 >= (length l))%nat /\ (count_ge x l * 2 >= (length l))%nat).

Definition calc_range_body:
  list (list Z) * Z * nat * nat * nat * nat -> SetMonad.M (ContinueOrBreak (list (list Z) * Z * nat * nat * nat * nat) (nat * nat * nat * nat)) :=
  fun '(lol, mid, Nle, nle, Nge, nge) =>
    match lol with
    | nil => break (Nle, nle, Nge, nge)
    | l :: rst =>
      nw <- median l;;
      choice
        (test (nw = mid);;
          continue (rst, mid, (Nle + count_le nw l)%nat, (nle + 1)%nat, (Nge + count_ge nw l)%nat, (nge + 1)%nat))
        (choice
          (test (nw < mid);;
            continue (rst, mid, (Nle + count_le nw l)%nat, (nle + 1)%nat, Nge, nge))
          (test (nw > mid);;
            continue (rst, mid, Nle, nle, (Nge + count_ge nw l)%nat, (nge + 1)%nat)))
    end.

Definition calc_range (lol: list (list Z)) (mid: Z): SetMonad.M (nat * nat * nat * nat) :=
  repeat_break calc_range_body (lol, mid, 0%nat, 0%nat, 0%nat, 0%nat).

Definition partitioned_lol (lol: list (list Z)): Prop :=
  forall l, In l lol -> (length l = 5)%nat.

Theorem range_correct :
  forall lol x, partitioned_lol lol -> is_median -> Hoare (calc_range lol x) (fun '(Nle, nle, Nge, nge) => (Nle >= 3 * nle)%nat /\ (Nge >= 3 * nge)%nat).
Proof.
  intros.
  unfold calc_range.
  apply (Hoare_repeat_break _ (fun '(lol, mid, Nle, nle, Nge, nge) => (partitioned_lol lol) /\ (Nle >= 3 * nle)%nat /\ (Nge >= 3 * nge)%nat)).
  intros.
  - destruct a; destruct p; destruct p; destruct p; destruct p.
    destruct H1.
    unfold calc_range_body.
    destruct l.
    + apply Hoare_ret.
      tauto.
    + eapply Hoare_bind.
      * apply H0.
      * intros.
        apply Hoare_choice.
        -- apply Hoare_test_bind.
           intros.
           apply Hoare_ret.
           split.
           unfold partitioned_lol in H1.
           ++ unfold partitioned_lol.
              intros.
              assert (In l1 (l :: l0)). { 
                right. exact H5. 
              }
              apply H1 in H6.
              lia.
           ++ simpl in H3.
              destruct H3.
              assert (In l (l :: l0)). { 
                left. reflexivity. 
              }
              apply H1 in H6.
              split.
              **  rewrite H6 in H3.
                  lia.
              **  rewrite H6 in H5.
                  lia.
        -- apply Hoare_choice.
           ++ apply Hoare_test_bind.
              intros.
              apply Hoare_ret.
              split.
              unfold partitioned_lol in H1.
              **  unfold partitioned_lol.
                  intros.
                  assert (In l1 (l :: l0)). { 
                    right. exact H5. 
                  }
                  apply H1 in H6.
                  lia.
              **  simpl in H3.
                  destruct H3.
                  assert (In l (l :: l0)). { 
                    left. reflexivity. 
                  }
                  apply H1 in H6.
                  split.
                  unfold partitioned_lol in H1.
                  +++ simpl in H3.
                      assert (In l (l :: l0)). { 
                        left. reflexivity. 
                      }
                      apply H1 in H7.
                      rewrite H7 in H3.
                      lia.
                  +++ destruct H2.
                      lia.
          ++ apply Hoare_test_bind.
              intros.
              apply Hoare_ret.
              split.
              unfold partitioned_lol in H1.
              **  unfold partitioned_lol.
                  intros.
                  assert (In l1 (l :: l0)). { 
                    right. exact H5. 
                  }
                  apply H1 in H6.
                  lia.
              **  simpl in H3.
                  destruct H3.
                  assert (In l (l :: l0)). { 
                    left. reflexivity. 
                  }
                  apply H1 in H6.
                  split.
                  unfold partitioned_lol in H1.
                  +++ simpl in H3.
                      assert (In l (l :: l0)). { 
                        left. reflexivity. 
                      }
                      apply H1 in H7.
                      rewrite H7 in H5.
                      lia.
                  +++ destruct H2.
                      lia.
  - split.
    tauto.
    split;lia.
Qed.
(*Finally, take x to be the median of medians of lol, we gain Nle >= 3 * nle >= 3 * length concat lol / 10 /\ Nge >= 3 * nge >= 3 * length concat lol / 10, which is what we want. *)

End QSortExample2.