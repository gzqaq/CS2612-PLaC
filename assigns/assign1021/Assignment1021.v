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

Module ExerciseLang4.
Import Lang1 Lang4.

(** 在本次作业中，程序表达式的语义是程序状态与64位整数之间的二元关系。*)

(** **** Exercise **** *)
(** 下面定义的_[subst_const]_描述了表达式之间的变量/常数替换关系：_[x]_是一个程
    序变量，其在表达式_[e1]_中出现了若干次（也可能是0次），将其中出现的一部分次
    数替换成常数_[n]_之后可以得到表达式_[e2]_。 *)

Fixpoint subst_const (e1 e2: expr) (x: var_name) (n: Z): Prop :=
  match e1, e2 with
  | ENum n1, ENum n2 => n1 = n2
  | EVar x1, EVar x2 => x1 = x2
  | EVar x1, ENum n2 => x1 = x /\ n2 = n
  | EPlus e11 e12, EPlus e21 e22 =>
    subst_const e11 e21 x n /\ subst_const e12 e22 x n
  | EMinus e11 e12, EMinus e21 e22 =>
    subst_const e11 e21 x n /\ subst_const e12 e22 x n
  | EMult e11 e12, EMult e21 e22 =>
    subst_const e11 e21 x n /\ subst_const e12 e22 x n
  | _, _ => False
  end.

(** 例如，如果_[n]_的值为_[0]_，那么_[x + x]_可以被替换为_[x + 0]_，_[0 + x]_，
    _[0 + 0]_，或_[x + x]_。下面，你的任务是证明（下面定理_[subst_const_sound]_）：
    对于任意程序状态_[st]_，如果该程序状态上程序变量_[x]_的值是_[n]_，那么上述变
    换前后的表达式_[e1]_与_[e2]_在程序状态_[st]_上的求值结果相同。为了证明这一结
    果，你很有可能会有用到下面引理。请先证明下面引理。*)

Lemma arith_denote_congr: forall Zfun int64fun D1 D2 D3 D4 st1 st2,
  (forall v, D1 st1 v <-> D2 st2 v) ->
  (forall v, D3 st1 v <-> D4 st2 v) ->
  (forall v, arith_denote Zfun int64fun D1 D3 st1 v <->
             arith_denote Zfun int64fun D2 D4 st2 v).
Proof.
  intros.
  unfold iff.
  split.
  - unfold arith_denote.
    intros.
    destruct H1 as [n1 ?].
    destruct H1 as [n2 ?].
    destruct H1 as [H11 ?].
    destruct H1 as [H12 ?].
    destruct H1 as [H13 ?].
    destruct H1 as [H14 H15].
    exists n1. exists n2.
    split; try tauto.
    + apply H. apply H11.
    + split; try tauto.
      apply H0. apply H12.
  - unfold arith_denote.
    intros.
    destruct H1 as [n1 ?].
    destruct H1 as [n2 ?].
    destruct H1 as [H11 ?].
    destruct H1 as [H12 ?].
    destruct H1 as [H13 ?].
    destruct H1 as [H14 H15].
    exists n1. exists n2.
    split; try tauto.
    + apply H. apply H11.
    + split; try tauto.
      apply H0. apply H12.
Qed.

(** 下面请你完成_[subst_const_sound]_的证明。该证明可以通过先对_[e1]_归纳，后对
    _[e2]_分类讨论完成证明。其中_[e1]_为常量部分的证明已经替你完成了。请你完成其
    它部分的证明。*)

Theorem subst_const_sound: forall st e1 e2 (x: var_name) n,
  n <= Int64.max_signed ->
  n >= Int64.min_signed ->
  st x = Int64.repr n ->
  subst_const e1 e2 x n ->
  forall v, eeval e1 st v <-> eeval e2 st v.
Proof.
  intros st e1 e2 x n H H0 H1.
  revert e2; induction e1; intros.
  + destruct e2; simpl in H2; try tauto.
    rewrite H2.
    tauto.
  + destruct e2; simpl in H2; try tauto; destruct H2; simpl; try tauto.
    unfold var_denote. unfold const_denote. unfold iff.
    split.
    - intros.
      split.
      * rewrite H3. rewrite <- H1. rewrite H2 in H4. apply H4.
      * split; rewrite H3; tauto.
    - intros. destruct H4. destruct H5.
      rewrite H4. rewrite H3. rewrite <- H1. rewrite H2. reflexivity.
  + destruct e2; simpl in H2; simpl; try tauto.
    apply arith_denote_congr; destruct H2; intros.
    - apply IHe1_1. apply H2.
    - apply IHe1_2. apply H3.
  + destruct e2; simpl in H2; simpl; try tauto.
    apply arith_denote_congr; destruct H2; intros.
    - apply IHe1_1. apply H2.
    - apply IHe1_2. apply H3.
  + destruct e2; simpl in H2; simpl; try tauto.
    apply arith_denote_congr; destruct H2; intros.
    - apply IHe1_1. apply H2.
    - apply IHe1_2. apply H3.
Qed.

(** **** Exercise **** *)
(** 下面定义的_[appears_in_expr]_是一个关于表达式_[e]_与程序变量_[x]_的命题：
    _[x]_在_[e]_中至少出现一次。*)

Fixpoint appears_in_expr (e: expr) (x: var_name): Prop :=
  match e with
  | ENum _ => False
  | EVar y => x = y
  | EPlus e1 e2 => appears_in_expr e1 x \/ appears_in_expr e2 x
  | EMinus e1 e2 => appears_in_expr e1 x \/ appears_in_expr e2 x
  | EMult e1 e2 => appears_in_expr e1 x \/ appears_in_expr e2 x
  end.

(** 请你证明，如果所有在_[e]_出现过至少一次的变量在_[st1]_与_[st2]_这两个程序状
    态之间的值都相同，那么_[e]_在这两个程序状态上的值就相同。提示：你的证明中也
    可能会用到你前面证明的引理_[arith_denote_congr]_。*)

Theorem eeval_appears: forall st1 st2 e,
  (forall x: var_name, appears_in_expr e x -> st1 x = st2 x) ->
  (forall v, eeval e st1 v <-> eeval e st2 v).
Proof.
  intros st1 st2 e H.
  induction e; simpl in H; simpl; try tauto.
  - unfold iff. unfold var_denote.
    split; intros.
    + assert (st1 x = st2 x). { apply H. reflexivity. }
      rewrite H0. apply H1.
    + assert (st1 x = st2 x). { apply H. reflexivity. }
      rewrite H1. apply H0.
  - apply arith_denote_congr.
    + apply IHe1. intros.
      apply H. left. tauto.
    + apply IHe2. intros.
      apply H. right. tauto.
  - apply arith_denote_congr.
    + apply IHe1. intros.
      apply H. left. tauto.
    + apply IHe2. intros.
      apply H. right. tauto.
  - apply arith_denote_congr.
    + apply IHe1. intros.
      apply H. left. tauto.
    + apply IHe2. intros.
      apply H. right. tauto.
Qed.

End ExerciseLang4.
