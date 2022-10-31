Require Import Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import compcert.lib.Integers.
Require Import PL.SetsDomain.
Require Import PL.DenotationalSemantics.
Local Open Scope bool.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets_scope.

(** **** Exercise **** *)
(** 请证明_[BinRel.id]_是二元关系连接运算的单位元。 *)

Lemma BinRel_concat_id_l:
  forall {A B} (R: A -> B -> Prop),
    BinRel.id ∘ R == R.
Proof.
  intros. unfold BinRel.concat. sets_unfold. intros. unfold iff.
  split.
  - intros [b [H0 H1]].
    unfold BinRel.id in H0.
    rewrite H0. apply H1.
  - intros.
    exists a. split; try tauto.
    unfold BinRel.id. reflexivity.
Qed.

Lemma BinRel_concat_id_r:
  forall {A B} (R: A -> B -> Prop),
    R ∘ BinRel.id == R.
Proof.
  intros. unfold BinRel.concat. sets_unfold. intros a b. unfold iff.
  split.
  - intros [b0 [H0 H1]].
    unfold BinRel.id in H1. rewrite H1 in H0. apply H0.
  - intros.
    exists b. split; try tauto.
    unfold BinRel.id. reflexivity.
Qed.

(** **** Exercise **** *)
(** 请证明空集是二元关系连接运算的零元。请注意：在数学中，只要一个集合中不包含任
    何元素，那么这个集合就是空集。然而，在Coq中，任何一个数学对象都应当有类型。
    因此，下面定理中，我们用_[∅: A -> B -> Prop]_以及_[∅: B -> C -> Prop]_表示在
    考虑_[A]_到_[B]_的二元关系时以及在考虑_[B]_到_[C]_的二元关系时的空集。 *)

Lemma BinRel_concat_empty_l:
  forall {A B C} (R: B -> C -> Prop),
    (∅: A -> B -> Prop) ∘ R == ∅.
Proof.
  intros. sets_unfold. intros a c. unfold iff. split.
  2: { contradiction. }
  unfold BinRel.concat. intros.
  destruct H as [b H].
  tauto.
Qed.

Lemma BinRel_concat_empty_r:
  forall {A B C} (R: A -> B -> Prop),
    R ∘ (∅: B -> C -> Prop) == ∅.
Proof.
  intros. sets_unfold. intros a c. unfold iff. split.
  2: { contradiction. }
  unfold BinRel.concat. intros.
  destruct H as [b H]. tauto.
Qed.

(** **** Exercise **** *)
(** 请证明二元关系连接运算对于并集运算的分配律。 *)

Lemma BinRel_concat_union_distr_r:
  forall
    {A B C}
    (R1 R2: A -> B -> Prop)
    (R3: B -> C -> Prop),
  (R1 ∪ R2) ∘ R3 == (R1 ∘ R3) ∪ (R2 ∘ R3).
Proof.
  intros A B C R1 R2 R3.
  sets_unfold. unfold BinRel.concat.
  intros a c. unfold iff.
  split; intros.
  - destruct H as [b H].
    destruct H as [H H0].
    destruct H as [H | H'].
    + left. exists b. split; tauto.
    + right. exists b. split; tauto.
  - destruct H as [H | H'].
    + destruct H as [b [H H']].
      exists b. split; tauto.
    + destruct H' as [b [H H']].
      exists b. split; tauto.
Qed.
  
Lemma BinRel_concat_union_distr_l:
  forall
    {A B C}
    (R1: A -> B -> Prop)
    (R2 R3: B -> C -> Prop),
  R1 ∘ (R2 ∪ R3) == (R1 ∘ R2) ∪ (R1 ∘ R3).
Proof.
  intros A B C R1 R2 R3.
  sets_unfold. unfold BinRel.concat.
  intros a c. unfold iff.
  split; intros.
  - destruct H as [b [H H']]. destruct H' as [H0 | H1].
    + left. exists b. tauto.
    + right. exists b. tauto.
  - destruct H as [H | H'].
    + destruct H as [b H].
      exists b. tauto.
    + destruct H' as [b H].
      exists b. tauto.
Qed.

Lemma BinRel_concat_omega_union_distr_r:
  forall
    {A B C}
    (R1: nat -> A -> B -> Prop)
    (R2: B -> C -> Prop),
  (⋃ R1) ∘ R2 == ⋃ (fun n => R1 n ∘ R2).
Proof.
  intros A B C R1 R2.
  sets_unfold. unfold BinRel.concat.
  intros a c. unfold iff.
  split; intros.
  - destruct H as [b [H H']].
    destruct H as [n H].
    exists n. exists b. tauto.
  - destruct H as [n [b [H H']]].
    exists b. split.
    + exists n. tauto.
    + tauto.
Qed.
  
Lemma BinRel_concat_omega_union_distr_l:
  forall
    {A B C}
    (R1: A -> B -> Prop)
    (R2: nat -> B -> C -> Prop),
  R1 ∘ (⋃ R2) == ⋃ (fun n => R1 ∘ R2 n).
Proof.
  intros A B C R1 R2.
  sets_unfold. unfold BinRel.concat.
  intros a c. unfold iff.
  split; intros.
  - destruct H as [b [H [n H']]].
    exists n. exists b. tauto.
  - destruct H as [n [b [H H']]].
    exists b. split; try tauto.
    exists n. tauto.
Qed.

