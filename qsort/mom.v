Require Import SetsClass.SetsClass.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import PL.FixedPoint.
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

(* Definition group_of_five_body:
  list Z * list(list Z)   -> SetMonad.M (ContinueOrBreak (list Z * list(list Z) ) (list(list Z))) :=
  fun '(rest_list , current_ret) =>
      match rest_list with
      | a :: b :: c :: d :: e :: rest_list' =>
        continue (rest_list', [a; b; c; d; e] :: current_ret)
      | nil => break current_ret
      | _ => break (rest_list :: current_ret)
      end.

Definition group_of_five l:=
  repeat_break group_of_five_body (l, nil). *)

(* Lemma *)

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
   * apply H.  (* 使用假设 H *)
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
  l <> nil ->  (* Added non-empty condition *)
  Hoare (median l) (In' l).
Proof.
  unfold Hoare, median.
  intros l Hnonempty x.  (* Added Hnonempty hypothesis *)
  eapply Hoare_bind.
  - apply insertion_sort_perm.
  - intros sorted Hperm.
    unfold ret, set_monad, SetMonad.ret.
    unfold Hoare.
    intros.
    sets_unfold in H.
    rewrite <- H.
    (* First show it's in sorted *)
    assert (Hin_sorted: In' sorted (get_nth (length sorted / 2) sorted)).
    {
      apply get_nth_in.
      apply Nat.div_lt.
      (* 证明排序后的列表非空 *)
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
    (* Then use permutation to show it's in l *)
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

Theorem get_medians_correct:
forall l: list Z,
  Hoare (get_medians l)
    (list_include_nonempty l).
Admitted.
(* Proof.
  intros l.
  unfold get_medians.
  apply (Hoare_repeat_break _ 
    (fun '(rest, curr) => 
      (forall x, In x curr -> In x l) /\ 
      (forall x, In x rest -> In x l))).
  
  intros [rest curr] [Hcurr Hrest].
  destruct rest as [|a [|b [|c [|d [|e rest']]]]].
  
  - (* Empty case *)
    unfold get_medians_body.
    apply Hoare_ret.
    intros x Hin. apply Hcurr, Hin.
    
  - (* 1 element case *)
    unfold get_medians_body.
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
        
  - (* 2 elements case *)
    unfold get_medians_body.
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
        
  - (* 3 elements case *)
    unfold get_medians_body.
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
        
  - (* 4 elements case *)
    unfold get_medians_body.
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
        
  - (* 5+ elements case *)
    unfold get_medians_body.
    eapply Hoare_bind.
    + apply median_correct.
      discriminate.
    + intros m Hm.
      simpl in Hm.
      apply Hoare_ret.
      split.
      * (* Prove curr property *)
        intros x Hin.
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
      * (* Prove rest property *)
        intros x Hin.
        apply Hrest.
        right. right. right. right. right.
        exact Hin.
  - (* Initial case *)
    split.
    + intros x H; contradiction.
    + intros x H; assumption.
Qed. *)
             
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

(* Lemma list_include_length:
  forall (l l': list Z), 
    list_include l l' -> (length l' <= length l)%nat.
Admitted. *)

Lemma list_length_half_lt:
  forall (a: list Z),
    a <> nil -> (length a / 2 < length a)%nat.
Admitted.

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
Admitted.

Lemma list_partition_length (l l1 l2: list Z):
  Permutation l (l1 ++ l2) -> (length l = length l1 + length l2)%nat.
Admitted.

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
      eapply Hoare_bind; [apply get_medians_correct |].
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

End QSortExample2.
