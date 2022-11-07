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
(** 请证明下面结论 *)

(** 自反函数的单调性：*)
Lemma id_mono:
  forall {A: Type}
         `{POA: PartialOrder_Setoid A},
  mono (fun x => x).
Proof.
  intros A RA EA POA. unfold mono. unfold order_rel.
  intros a1 a2 H. tauto.
Qed.

(** 复合函数保持单调性：*)
Lemma compose_mono:
  forall {A B C: Type}
         `{POA: PartialOrder_Setoid A}
         `{POB: PartialOrder_Setoid B}
         `{POC: PartialOrder_Setoid C}
         (f: A -> B)
         (g: B -> C),
  mono f -> mono g -> mono (fun x => g (f x)).
Proof.
  intros A B C RA EA POA RB EB POB RC EC POC f g.
  unfold mono. unfold order_rel. intros.
  apply H0. apply H. apply H1.
Qed.

(** 自反函数的连续性：*)
Lemma id_continuous:
  forall {A: Type}
         `{oCPOA: OmegaCompletePartialOrder_Setoid A}
         {EquivA: Equivalence equiv},
  continuous (fun x => x).
Proof.
  intros. unfold continuous. intros.
  pose proof oCPO_completeness l H.
  assert (is_omega_ub l == is_omega_ub (fun n => l n)).
  { unfold is_omega_ub. reflexivity. }
  pose proof same_omega_ub_same_omega_lub l (fun n => l n).
  specialize (H2 (omega_lub l) (omega_lub (fun n => l n))).
  specialize (H2 H1 H0). apply H2. tauto.
Qed.

(** 一个单调函数作用在一个单调不减序列的每一项后还会得到一个单调不减序列 *)
Lemma increasing_mono_increasing:
  forall {A B: Type}
         `{POA: PartialOrder_Setoid A}
         `{POB: PartialOrder_Setoid B}
         (f: A -> B)
         (l: nat -> A),
  increasing l -> mono f -> increasing (fun n => f (l n)).
Proof.
  intros A B RA EA POA RB EB POB f l Hi Hm.
  unfold increasing. intros n.
  apply Hm. apply Hi.
Qed.

(** 单调函数能保持相等关系 *)
Lemma mono_equiv_congr:
  forall {A B: Type}
         `{POA: PartialOrder_Setoid A}
         `{POB: PartialOrder_Setoid B}
          {EquivA: Equivalence (equiv: A -> A -> Prop)}
         (f: A -> B),
  mono f -> Proper (equiv ==> equiv) f.
Proof.
  intros A B RA EA POA PB EB POB. intros.
  unfold Proper, respectful. intros x y He.
  apply antisymmetricity_setoid.
  - apply reflexivity_setoid.
    apply mono_equiv_congr. apply H. apply He.
  - apply reflexivity_setoid.
    apply mono_equiv_congr. apply H.
    symmetry. apply He.
Qed.

(** 复合函数的连续性 *)
Lemma compose_continuous:
  forall {A B C: Type}
         `{oCPOA: OmegaCompletePartialOrder_Setoid A}
         `{oCPOB: OmegaCompletePartialOrder_Setoid B}
         `{oCPOC: OmegaCompletePartialOrder_Setoid C}
          {EquivB: Equivalence (equiv: B -> B -> Prop)}
          {EquivC: Equivalence (equiv: C -> C -> Prop)}
         (f: A -> B)
         (g: B -> C),
  mono f ->
  mono g ->
  continuous f ->
  continuous g ->
  continuous (fun x => g (f x)).
Proof.
  intros A B C RA EA oLubA BotA oCPOA RB EB oLubB BotB oCPOB.
  intros RC EC oLubC BotC oCPOC. intros EquivB EquivC f g.
  unfold continuous. intros Hmf Hmg Hcf Hcg.
  intros l Hil.
  specialize (Hcf l Hil). specialize (Hcg (fun n => f (l n))).
  assert (increasing (fun n => f (l n))).
  { apply increasing_mono_increasing. apply Hil. apply Hmf. }
  specialize (Hcg H).
  pose proof mono_equiv_congr g Hmg. unfold Proper, respectful in H0.
  apply H0 in Hcf.
  pose proof transitivity Hcf Hcg.
  tauto.
Qed.

(** 二元关系连接保持集合包含关系 *)
#[export] Instance BinRel_concat_included_congr:
  forall A B C: Type,
    Proper
      (Sets.included ==> Sets.included ==> Sets.included)
      (@BinRel.concat A B C).
Proof.
  intros. unfold Proper, respectful. sets_unfold. unfold BinRel.concat.
  intros.
  destruct H1 as [b [? ?]].
  exists b. split.
  - apply H in H1. tauto.
  - apply H0 in H2. tauto.
Qed.
