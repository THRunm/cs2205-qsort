Require Import SetsClass.SetsClass.
Require Import Coq.ZArith.ZArith.
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
  match sorted with
  | a :: [] => ret a  (* 单元素列表，返回该元素 *)
  | _ => 
      
      let len := Z.of_nat (length sorted) in
      ret (get_nth (Z.to_nat ((len - 1) / 2)) sorted)
  end.

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
(*TODO*)

Definition get_medians (l_of_ls: list (list Z)): SetMonad.M (list Z):=
  repeat_break get_medians_body (l_of_ls, nil).

Definition MedianOfMedians_body:
  list Z -> SetMonad.M (ContinueOrBreak (list Z) (Z)) :=
  fun '(l) =>
    match l with
    | a :: b :: c :: d :: e :: f::l' =>
      l_of_ls <- group_of_five l;;
      m <- get_medians l_of_ls;;
        continue (m)
    | _ =>
        m <- median l;;       (* 先计算 median *)
        break m 
    end.
    
Definition MedianOfMedians (l: (list Z)): SetMonad.M Z :=
  repeat_break MedianOfMedians_body (l).    

Theorem MedianOfMedians_correct:
  forall l,
    Hoare (MedianOfMedians l) (fun x => In x l).
Admitted.

End QSortExample2.