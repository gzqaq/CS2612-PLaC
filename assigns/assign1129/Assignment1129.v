Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
Require Import PL.DenotationalSemantics.
Require Import PL.SmallStepSemantics.
Require Import compcert.lib.Integers.
Import WhileD_Expr WhileD_Cmd.
Local Open Scope Z.
Local Open Scope sets_scope.

(** 请完成下面证明 *)
Lemma estep_sound: forall s el1 el2 n,
  estep s el1 el2 ->
  el_eval el2 s n ->
  el_eval el1 s n.
Proof.
  intros.
  revert n H0; induction H; simpl in *; intros.
  + unfold var_denote.
    tauto.
  + unfold const_denote.
    tauto.
  + destruct H0 as [n1 [? ?]].
    eapply binop_compute_step1_binop_denote; eauto.
  + destruct op; simpl in *; try contradiction.
    - exists n1; subst n.
      tauto.
    - exists n1; subst n.
      tauto.
  + destruct H0 as [n2 [? ?]].
    exists n1. split; try tauto.
    destruct op; simpl in *; unfold bool_compute in H1.
    destruct H1 as [[? ?] | [? ?]].
    - right; right. repeat split; auto.
      subst n2. tauto.
    - right; left. exists n2.
      repeat split; auto.
    - destruct H1 as [[? ?] | [? ?]].
      * right; left. repeat split; auto.
        congruence.
      * right; right. exists n2.
        tauto.
    - exists n2; tauto.
    - exists n2; tauto.
    - exists n2; tauto.
    - exists n2; tauto.
    - exists n2; tauto.
    - exists n2; tauto.
    - exists n2; tauto.
    - exists n2; tauto.
    - exists n2; tauto.
    - exists n2; tauto.
    - exists n2; tauto.
  + exists n2; split; congruence.
  + destruct H0 as [n0 [? ?]].
    destruct op; simpl in *.
    - unfold not_denote; unfold not_compute in H0.
      destruct H0 as [[? ?] | [? ?]].
      * left; exists n0; tauto.
      * right; split; congruence.
    - unfold neg_denote; unfold neg_compute in H0.
      exists n0; tauto.
  + exists n0; split; congruence.
  + destruct H0 as [n0 [? ?]].
    unfold deref_denote.
    exists n0; tauto.
  + exists n0; split; congruence.
  + destruct H0 as [n0 [? ?]].
    specialize (IHestep n0 H0).
    exists n0; split; congruence.
Qed.
