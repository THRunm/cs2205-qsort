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

Definition group_of_five_body:
  list Z * list(list Z)   -> SetMonad.M (ContinueOrBreak (list Z * list(list Z) ) (list(list Z))) :=
  fun '(rest_list , current_ret) =>
      match rest_list with
      | a :: b :: c :: d :: e ::  rest_list' =>
        continue (rest_list', [a; b; c; d; e] :: current_ret)
      | nil => break current_ret
      | _ => break (rest_list :: current_ret)
      end.

Definition group_of_five l:=
  repeat_break group_of_five_body (l, nil).

(* Lemma *)

Definition insertion_sort_body:
  list Z * list Z -> SetMonad.M (ContinueOrBreak (list Z * list Z) (list Z)) :=
  fun '(rest_list, current_ret) =>
    match rest_list with
    | nil => break current_ret
    | x :: rest_list' =>
      let fix insert x l :=
          match l with
          | nil => x :: nil
          | y :: l' => if x <=? y then x :: l else y :: insert x l'
          end in
      continue (rest_list', insert x current_ret)
    end.

Definition insertion_sort (l : (list Z)): SetMonad.M (list Z):=
  repeat_break insertion_sort_body (l, nil).

Theorem insertion_sort_perm:
 forall l,
  Hoare (insertion_sort l) (Permutation l).
Admitted.

Fixpoint get_nth (n: nat) (l: list Z) : Z :=
  match n, l with
  | O, x::_ => x
  | S n', _::l' => get_nth n' l'
  | _, nil => 0
end.

Definition median (l : (list Z)): SetMonad.M Z:=
  sorted <- insertion_sort l;;
  let len := length sorted in
  ret (get_nth (len / 2) sorted).

Definition get_medians_body:
(list(list Z) * (list Z)) -> SetMonad.M (ContinueOrBreak (list(list Z) * (list Z)) (list Z)) :=
  fun '(l_of_ls , current_l) =>
    match l_of_ls with
    | nil => break current_l
    | h :: t => 
      match h with
      | nil => continue (t, current_l)  (* 处理空子列表的情况 *)
      | _ => 
        m <- median h;;
        continue (t, m :: current_l)
      end
    end.

Definition get_medians (l_of_ls: list (list Z)): SetMonad.M (list Z):=
  repeat_break get_medians_body (l_of_ls, nil).

Definition partition (pivot: Z) (l: list Z): SetMonad.M (list Z * list Z * list Z) :=
  fun '(l1, l2, l3) =>
    Permutation l (l1 ++ l2 ++ l3)
    /\ (forall x, In x l1 -> x < pivot)
    /\ (forall x, In x l2 -> x = pivot)
    /\ (forall x, In x l3 -> x > pivot).

Definition MedianOfMedians_body
      (W: list Z -> nat -> SetMonad.M Z)
      (l: list Z)
      (k: nat)
  : SetMonad.M Z
  :=
  match l with
  | a :: b :: c :: d :: e :: f :: l' => 
    l_of_ls <- group_of_five l;;
    medians <- get_medians l_of_ls;;
    let len := (length medians) in
    pivot <- W medians (Nat.div len 2);;
    '(lo, pivots, hi) <- partition pivot l;;
    (* match Nat.compare k (length lo) with
    | Lt => W lo k
    | _ => match Nat.compare k (length lo + length pivots) with
      | Lt => ret pivot
      | _ => W hi (Nat.sub k (length lo + length pivots))
      end
    end *)
    if Nat.ltb k (length lo) then
      W lo k
    else if Nat.ltb k (length lo + length pivots) then
      ret pivot
    else
      W hi (Nat.sub k (length lo + length pivots))
  | _ => 
    sorted_l <- insertion_sort l;;
    ret (get_nth k sorted_l)
  end.

Definition MedianOfMedians: list Z -> nat -> SetMonad.M Z :=
  Kleene_LFix MedianOfMedians_body.

Definition In' (l: list Z) (x : Z): Prop :=
  In x l.

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
  change (Hoare (Nat.iter n MedianOfMedians_body ∅ l k) (In' l)).
  induction n; simpl.
  + unfold Hoare; sets_unfold; tauto.
  +  
Qed.





End QSortExample2.