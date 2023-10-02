Set Warnings "-notation-overridden,-parsing".

From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From LF Require Import Maps.
From LF Require Import Lists.


Inductive tree X : Type :=
| empty : tree X
| node : tree X -> X -> tree X -> tree X.


Arguments empty {X}.
Arguments node {X} _ _ _.

(* Question 1 *)

Definition T : tree nat := 
(node
    (node
      (node (empty) 1 (empty)) 
                                3
      (node (empty) 2 (empty))
    ) 
                                      0 
    (node
      (node (empty) 4 (empty))
                                1 
      (node (empty) 5 (empty))
    )
).


(* Question 2 *)

Fixpoint in_order {X: Type} (t: tree X) : list X :=
  match t with
  | empty => nil
  | (node l t' r) => (in_order l) ++ [t'] ++ (in_order r)
  end.
  
  
Example test_in_order : [1; 3; 2; 0; 4; 1; 5] = (in_order T).
Proof.
  simpl. reflexivity. Qed.
  

(* Question 3 *)

Fixpoint tree_map {X Y} (f: X -> Y) (t: tree X) : tree Y :=
  match t with
  | empty => empty
  | (node lx tx rx) => (node (tree_map f lx) (f tx) (tree_map f rx))
  end.
  

Example test_tree_map1 : (tree_map (fun (x: nat) => S x) T) = 
          (node (node (node empty 2 empty) 4 (node empty 3 empty)) 1 
          (node (node empty 5 empty) 2 (node empty 6 empty))).
Proof.
  reflexivity. Qed.

Example test_tree_map2 : (tree_map (fun (x: nat) => (even x)) T) = 
          (node (node (node empty false empty) false (node empty true empty)) true 
          (node (node empty true empty) false (node empty false empty))).
Proof.
  reflexivity. Qed.

Example test_tree_map3 : (tree_map (fun (x: bool) => (negb x)) 
    (node (node (node empty false empty) true empty) true 
    (node empty true (node empty false empty)))  ) = 
    (node (node (node empty true empty) false empty) false 
    (node empty false (node empty true empty))).
Proof.
  reflexivity. Qed.


(* Question 4 *)

Lemma tree_map_app : forall X Y (f: X -> Y) (tl tr: tree X) (x: X),
    tree_map f (node tl x tr) = (node (tree_map f tl) (f x) (tree_map f tr)).
Proof.
 intros X Y f tl tr x. destruct tl; reflexivity.
Qed.

Lemma in_order_app : forall X (tr tl: tree X) (x: X),
    in_order (node tl x tr) = (in_order tl) ++ x :: (in_order tr).
Proof.
 intros X tr tl x. destruct tl; reflexivity.
Qed.

Lemma tree_map_in_order : forall X Y (f: X -> Y) (t: tree X),
    map f (in_order t) = in_order (tree_map f t).
Proof.
 intros X Y f t. induction t.
 - (* empty *) simpl. reflexivity.
 - (* node *) rewrite tree_map_app. rewrite in_order_app. rewrite map_app. rewrite map_cons.
   symmetry. rewrite in_order_app. rewrite IHt1. rewrite IHt2. reflexivity.
Qed.

(* Question 5 *)

Theorem tree_map_tree_map : forall X Y Z (f: X -> Y) (g: Y -> Z) (t: tree X),
    (tree_map g (tree_map f t)) = (tree_map (fun (x: X) => (g (f x))) t).
Proof.
 intros X Y Z f g t. induction t.
 - (* empty *) reflexivity.
 - (* node *) simpl. rewrite IHt1. rewrite IHt2. reflexivity.
Qed.


(* Question 6 *)

(* We define a new function [tree_size], witch takes a [tree X] as an argument,
  and returns the number of nodes in that tree.*)
Fixpoint tree_size (X: Type) (t: tree X) : nat :=
  match t with
  | empty => 0
  | (node l x r) => S ((tree_size X l) + (tree_size X r))
  end.
  
Example test_tree_size1 : (tree_size nat empty) = 0.
Proof.
  reflexivity. Qed.

Example test_tree_size2 : (tree_size nat (node (node (node empty 2 empty) 3 
    (node empty 4 (node empty 6 empty))) 5 (node empty 4 empty))) = 6.
Proof.
  reflexivity. Qed.

(* False specification  & Proof that it doesn't hold*)
Theorem tree_map_changes_tree_size : forall X Y (f: X -> Y) (t: tree X) (n: nat),
    (tree_size X t) <> (tree_size Y (tree_map f t)) -> False.
Proof.
 intros X Y f t n E.  unfold not in E. apply E. clear E.
 induction t.
 - (* empty *) simpl. reflexivity.
 - (* node *) simpl. rewrite IHt1. rewrite IHt2. reflexivity.
Qed.

  
  
  (*  *)
  