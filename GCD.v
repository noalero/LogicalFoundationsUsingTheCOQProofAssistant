Set Warnings "-notation-overridden,-parsing".

From Coq Require Import Lia.
From LF Require Import Maps.
From LF Require Import Lists.
From Coq Require Import Arith.Arith.
Import Nat.

Inductive euclid : nat -> nat -> nat -> Prop :=
| stop : forall z, euclid z z z
| step_a : forall a b z, a > b -> euclid (a - b) b z -> euclid a b z
| step_b : forall a b z, a < b -> euclid a (b - a) z -> euclid a b z.


Inductive gcd : nat -> nat -> nat -> Prop :=
| base : forall z, gcd z z z
| step_a' : forall a b z, gcd a b z -> gcd (a + b) b z
| step_b' : forall a b z, gcd a b z -> gcd a (a + b) z.


Theorem euclid_gcd : forall a b z, euclid a b z -> gcd a b z.
Proof.
  intros a b z Heuclid. induction Heuclid.
  - (* stop *) apply base.
  - (* step_a *) apply step_a' in IHHeuclid. rewrite <- add_comm in IHHeuclid.
    rewrite le_plus_minus_r in IHHeuclid.
    + assumption.
    + lia.
  - (* step_b *) apply step_b' in IHHeuclid. rewrite le_plus_minus_r in IHHeuclid.
    + assumption.
    + lia.
Qed.


Lemma noether_max P :
(forall a b, (forall a' b', max a' b' < max a b -> P a' b') -> P a b)
-> forall a b, P a b.
(* I have a truly remarkable proof of this theorem which this file
is too small to contain. *)
Admitted.

Lemma case_split_3way P : forall a b,
(a < b -> P a b) -> (a = b -> P a b) -> (a > b -> P a b) -> P a b.
Proof.
  intros a b Hlt Heq Hgt. destruct (lt_eq_lt_dec a b) as [[H1 | H2] | H3].
  - (* H1 *) apply Hlt. assumption.
  - (* H2 *) apply Heq. assumption.
  - (* H3 *) apply Hgt. assumption.
Qed.

Lemma gt_max_l : forall n m: nat, n < m -> max n m = m.
Proof.
  intros n m H. apply max_r. apply le_lteq. left. assumption.
Qed.

Lemma gt_max_r : forall n m: nat, n > m -> max n m = n.
Proof.
  intros n m H. apply max_l. apply le_lteq. left. assumption.
Qed.


Theorem euclid_terminates : forall a b,
    a > 0 -> b > 0 -> exists z, euclid a b z.
Proof.
  intros a b. apply noether_max with (a := a) (b := b). clear a b.
  intros a b Hmax H_a0 H_b0. apply case_split_3way with (a := a) (b := b).
  - (* a < b *) intros Hlt. induction Hmax with (a' := a) (b' := (b - a)).
    (* Here, since [a < b], the suitable constructor is [step_b].
      Since constructor [step_b] staites 
      [a < b -> euclid a (b - a) z -> euclid a b z],
      we assign [b' := (b - a)]. *)
    + exists x. apply step_b; assumption.
    + rewrite gt_max_l with (n := a) (m := b). apply max_lub_lt; try(assumption).
      apply sub_lt. rewrite le_lteq. left. assumption. assumption. assumption.
    + assumption.
    + lia.     
  - (* a = b *) intros Heq. exists a. rewrite Heq. apply stop.
  - (* a > b *) intros Hgt. induction Hmax with (a' := a - b) (b' := b).
    (* Here, since [a > b], the suitable constructor is [step_a].
      Since constructor [step_a] staites 
      [a > b -> euclid (a - b) b z -> euclid a b z],
      we assign [a' := a - b]. *)
    + exists x. apply step_a; assumption.
    + rewrite gt_max_r with (n := a) (m := b). apply max_lub_lt; try(assumption).
      apply sub_lt. rewrite le_lteq. left. assumption. assumption. assumption.
    + lia.
    + assumption.
Qed.
  

(*Lemma and_implies P : forall (a b c: Prop), 
    (a /\ b /\ c) -> P -> ((a -> P) -> (b -> P) -> (c -> P) -> P).
Proof.
  intros a b c Hand p. intros Ha Hb Hc. apply p.
Qed. *)


(* Lemma or_implies P : forall (a b c: Prop), 
    (a \/ b \/ c) -> P -> ((a -> P) -> (b -> P) -> (c -> P) -> P).
Proof.
  intros a b c Hand p. intros Ha Hb Hc. apply p.
Qed. *)


(* Lemma gt_iff_lt :  forall n m: nat, n > m <-> m < n.
Proof.
  intros n m. split; intros H; induction H as [| a IHa];
  try( apply lt_succ_diag_r);
  try(apply lt_succ_r; apply le_Sn_le in IHa; assumption).
Qed. *)

(* Lemma not_n_lt_n : forall n: nat, n < n -> False. 
Proof.
 intros n Hwrong. apply lt_neq in Hwrong. unfold not in Hwrong. apply Hwrong. 
  reflexivity.
Qed.

Lemma euclid_n_1_1 : forall n : nat, n > 0 -> euclid n 1 1.
Proof.
  intros n H. induction H as [| n'].
  - (* n = 1 *) apply stop.
  - (* n = S n' *) apply step_a.
    + (* S n' > 1 *) apply le_gt_S. assumption.
    + (* euclid (S n' - 1) 1 1 *) rewrite sub_1_r. rewrite <- pred_Sn. assumption.
Qed.

Lemma euclid_1_n_1 : forall n : nat, n > 0 -> euclid 1 n 1.
Proof.
  intros n H. induction H as [| n'].
  - (* n = 1 *) apply stop.
  - (* n = S n' *) apply step_b.
    + (* S n' > 1 *) apply le_gt_S. assumption.
    + (* euclid (S n' - 1) 1 1 *) rewrite sub_1_r. rewrite <- pred_Sn. assumption.
Qed. *)
