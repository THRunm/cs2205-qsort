Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Psatz.
Import ListNotations.

Require Import SetsClass.SetsClass.
Require Import PL.FixedPoint.
Require Import PL.Monad.
Require Import PL.Monad2.
Import SetsNotation
       KleeneFix
       Sets_CPO
       Monad
       MonadNotation.
      

Local Open Scope sets.
Local Open Scope Z.
Local Open Scope monad.

Module QSortExamples.

  Import SetMonadHoare
         SetMonadOperator0
         SetMonadOperator1
         SetMonadProperties0.
         

  Fixpoint incr_aux (l: list Z) (x: Z): Prop :=
    match l with
    | nil => True
    | y :: t => x <= y /\ incr_aux t y
    end.

  Definition incr (l: list Z): Prop :=
    match l with
    | nil => True
    | x :: t => incr_aux t x
    end.

  Definition partition (pivot: Z) (l: list Z): SetMonad.M (list Z * list Z) :=
    fun '(l1, l2) =>
      Permutation l (l1 ++ l2)
      /\ (forall x, In x l1 -> x <= pivot)
      /\ (forall x, In x l2 -> x > pivot).


Definition body_qsort_f
      (W: list Z -> SetMonad.M (list Z))
      (l: list Z)
 : SetMonad.M (list Z)
 := 
 match l with
 | nil => ret nil 
 | pivot :: rest =>
   '(l1, l2) <- partition pivot rest;;
   sorted1 <- W l1;;
   sorted2 <- W l2;;
   ret (sorted1 ++ [pivot] ++ sorted2)
 end.

  Definition qsort: list Z -> SetMonad.M (list Z) :=
    Kleene_LFix body_qsort_f.


Lemma partition_correct:
    forall pivot l,
      Hoare (partition pivot l)
            (fun '(l1, l2) =>
               Permutation l (l1 ++ l2) /\
               (forall x, In x l1 -> x <= pivot) /\
               (forall x, In x l2 -> x > pivot)).
  Proof.
    intros pivot l.
    unfold Hoare, partition.
    sets_unfold.
    intros [l1 l2] [Hperm [Hle Hgt]].
    split.
    - exact Hperm.
    - split; assumption.
  Qed.
  Lemma qsort_perm_:
  forall l a (n :nat),
  Nat.iter n body_qsort_f ∅ l a -> Permutation l a.
  Proof.
  intros.
  revert l a H.
  change (forall l, 
      Hoare (Nat.iter n body_qsort_f ∅ l) (Permutation l)).
    induction n; simpl; intros.
    - unfold Hoare; sets_unfold; tauto.
    - destruct l as [| pivot rest]; simpl.
      + apply Hoare_ret. apply Permutation_refl.
      + eapply Hoare_bind.
        { apply partition_correct. }
        intros [l1 l2] [Hperm [_ _]].
        eapply Hoare_bind.
        { apply IHn. }
        intros sorted1 Hsorted1.
        eapply Hoare_bind.
        { apply IHn. }
        intros sorted2 Hsorted2.
        apply Hoare_ret.
        apply Permutation_trans with (pivot :: rest).
        { apply Permutation_refl. }
        apply Permutation_trans with (pivot :: l1 ++ l2).
        { apply Permutation_cons.  
          - reflexivity.
          - exact Hperm. }
        apply Permutation_trans with (l1 ++ pivot :: l2).
        { apply Permutation_middle. }
        apply Permutation_app.
        * assumption.
        * apply Permutation_cons.
          -- reflexivity.
          -- exact Hsorted2.
Qed.
  

Lemma qsort_perm:
  forall l,
    Hoare (qsort l) (Permutation l).
Proof.
  intros l.
  unfold qsort, Kleene_LFix; unfold_CPO_defs.
  intros a [n ?].
  revert  H.
  apply (qsort_perm_ l a n).
Qed.

Lemma incr_cons:
  forall x l,
    incr l ->
    (forall y, In y l -> x <= y) ->
    incr (x :: l).
Proof.
  intros x l Hincr H.
  unfold incr.
  destruct l as [| y t].
  - simpl. constructor.
  - simpl. split.
    + apply H. simpl. left. reflexivity.
    + apply Hincr.
Qed.

Lemma incr_cons_:
forall x l,
incr l ->
(forall y, In y l -> x >= y) ->
incr (l ++ [x]).
Proof.
  intros x l Hincr Hge.
  induction l as [| h t IH].
  - simpl. unfold incr. trivial.
  - simpl.
    destruct t as [| h' t'].
    + simpl. 
      unfold incr. simpl.
      split.
      * apply Z.ge_le. apply Hge. simpl. left. reflexivity.
      * simpl. trivial.
    + unfold incr in *. simpl in *.
      destruct Hincr as [Hhead Htail].
      split.
      * exact Hhead.
      * apply IH.
        -- exact Htail.
        -- intros y Hy.
           apply Hge.
           simpl. right. exact Hy.
Qed.

Lemma incr_inv : forall (l:list Z) (x:Z),
  incr (x :: l) -> incr l.
Proof.
intros l x H.
simpl in H.
unfold incr.  
destruct l as [|y t].
- tauto.
- simpl in H. tauto.
Qed.

Lemma incr_app_cons: forall l1 x l2,
 incr (l1 ++ [x]) ->
 incr (x :: l2) ->
 incr (l1 ++ x :: l2).
Proof.
 intros.
 simpl in H0.
 destruct l1 as [| a l1]; simpl in *.
 { tauto. }
 revert a H; induction l1; simpl; intros.
 + tauto.
 + split; [tauto |].
   apply IHl1.
   tauto.
Qed.

Definition correct (l: list Z) (sorted: list Z): Prop :=
  Permutation l sorted /\ incr sorted.
Lemma qsort_incr:
  forall l,
    Hoare (qsort l) incr.
Proof.
  intros l.
  unfold qsort, Kleene_LFix; unfold_CPO_defs.
  intros a [n ?].
  revert  l a H.
    change (forall l, 
    Hoare (Nat.iter n body_qsort_f ∅ l) incr).
  induction n; simpl; intros.
  - unfold Hoare; sets_unfold; tauto.
  - destruct l as [| pivot rest]; simpl.
    + apply Hoare_ret. constructor.
    + eapply Hoare_bind.
      { apply partition_correct. }
      intros [l1 l2] .
      intros [Hperm [Hle Hgt]].
      assert (HPerm1: forall sorted1, 
        (Nat.iter n body_qsort_f ∅) l1 sorted1 -> 
        Permutation  sorted1 l1).
        {
          pose proof (qsort_perm_ l1).
          intros sorted1 Hsorted1.
          apply H with (a:=sorted1) in Hsorted1.
          apply Permutation_sym.
          exact Hsorted1.
        }
        assert (HPerm2: forall sorted2, 
        (Nat.iter n body_qsort_f ∅) l2 sorted2 -> 
        Permutation  sorted2 l2 ).
        {
          pose proof (qsort_perm_ l2).
          intros sorted2 Hsorted2.
          apply H with (a:=sorted2) in Hsorted2.
          apply Permutation_sym.
          exact Hsorted2.
        }
        assert (Hk:forall l ,Hoare (Nat.iter n body_qsort_f ∅ l) (fun l' =>correct l l' )).
        {
            unfold correct.
            intros l0.
            apply Hoare_conjunct.
            {
              unfold Hoare.
              sets_unfold.
              intros a.
              apply ( qsort_perm_ l0 a n).
            }
            apply IHn.
        }
      eapply Hoare_bind.
      { apply  Hk . }
      intros sorted1 Hincr1.
      eapply Hoare_bind.
      { apply Hk . }
      intros sorted2 Hincr2.
      unfold correct in *.
      destruct Hincr1 as [Hperm1 Hincr1].
      apply Hoare_ret.
      assert (forall x, In x sorted1 -> In x l1).
      {         intros x Hx.
         apply Permutation_sym in Hperm1.
         pose proof (Permutation_in  x  Hperm1).
          apply H.
          apply Hx.
      }
      destruct Hincr2 as [Hperm2 Hincr2].
      assert (forall x, In x sorted2 -> In x l2).
     {
      intros x Hx.
      apply Permutation_sym in Hperm2.
      pose proof (Permutation_in  x Hperm2  ).
       apply H0.
       apply Hx.
      }
    assert (forall x , In x sorted1 -> x <= pivot).
    {
        intros x Hx.
        apply Hle.
        apply H.
        apply Hx.
    }
    assert (forall x , In x sorted2 -> x > pivot).
    {
        intros x Hx.
        apply Hgt.
        apply H0.
        apply Hx.
    }
    apply incr_app_cons.
    --apply incr_cons_.
        ++ apply Hincr1.
        ++ intros y.
            intros Hy.
            apply Z.le_ge.
            apply H1.
            apply Hy.
    --apply incr_cons.
        ++ apply Hincr2.
        ++ intros y.
            intros Hy.
            apply Z.lt_le_incl.
            apply Z.gt_lt.
            apply H2.
            apply Hy.     
Qed.

Theorem functional_correctness_quicksort:
    forall l,
      Hoare (qsort l) (fun l' => Permutation l l' /\ incr l').
Proof.
    intro l.
    apply Hoare_conjunct.
    - apply qsort_perm.
    - apply qsort_incr.
Qed.

End QSortExamples.
