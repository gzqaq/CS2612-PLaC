Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
Require Import PL.DenotationalSemantics.
Require Import PL.HoareLogic.
Require Import compcert.lib.Integers.

Local Open Scope Z.

Import WhileD_Expr WhileD_Cmd AssertionLang
       SimpleSymbEval AssertionSem.

(** 请证明下述关于指称语义以及符号执行关系的结论。*)


(** 提示：相关定义与证明中可能要用到标准库中提供的有关_[Forall]_以及_[String.eqb]_
    的性质。*)

(** _[Forall]_有如下四条重要性质：*)

Check Forall_nil.
Check Forall_cons.
Check Forall_cons_iff.
Check Forall_app.

(** 我们在HoareLogic中引入了两条自定义证明指令，其中_[Forall_decomp H]_用于拆分
    证明前提_[H]_中的_[Forall]_，_[Forall_split]_用于拆分证明结论中的_[Forall]_。

    _[String.eqb]_是标准库中定义的字符串相等比较，它有两条重要性质：*)

Check String.eqb_eq.
Check String.eqb_neq.

(** 我们在HoareLogic中引入了_[string_eqb_case_analysis str1 str2]_这一证明指令，
    可以对_[str1]_与_[str2]_是否相等进行分类讨论。*)

(** **** Exercise **** *)
(** 请证明While+D语言表达式行为的确定性 *)

Definition deterministic (D: prog_state -> int64 -> Prop): Prop :=
  forall (s: prog_state) (i1 i2: int64),
    D s i1 -> D s i2 -> i1 = i2.

(** 下面证明中，我们使用了Coq标准库提供的_[congruence]_指令。_[congruence]_能够
    用于解决可以利用反复_[rewrite]_证明（但其中不能化简）的结论。*)
Lemma const_denote_det: forall n, deterministic (const_denote n).
Proof.
  unfold deterministic, const_denote.
  intros.
  destruct H as [H _], H0 as [H0 _].
  congruence.
Qed.

Lemma var_denote_det: forall x, deterministic (var_denote x).
Proof.
  unfold deterministic, var_denote.
  intros x s i1 i2 Hi1 Hi2.
  congruence.
Qed.

(** 提示：在下面几个引理的证明中，我们使用_[specialize]_证明指令可以大大简化证明。*)
Lemma arith_denote1_det: forall D1 D2 Zfun ifun,
  deterministic D1 ->
  deterministic D2 ->
  deterministic (arith_denote1 Zfun ifun D1 D2).
Proof.
  unfold deterministic, arith_denote1.
  intros.
  destruct H1 as [n1 [n2 [H1n1 [H1n2 [H1i1 _]]]]].
  destruct H2 as [n1' [n2' [H2n1 [H2n2 [H2i2 _]]]]].
  specialize (H s n1 n1' H1n1 H2n1).
  specialize (H0 s n2 n2' H1n2 H2n2).
  congruence.
Qed.

Lemma arith_denote2_det: forall D1 D2 ifun,
  deterministic D1 ->
  deterministic D2 ->
  deterministic (arith_denote2 ifun D1 D2).
Proof.
  unfold deterministic, arith_denote2.
  intros.
  destruct H1 as [n1 [n1' [H1n1 [H1n1' [H1i1 _]]]]].
  destruct H2 as [n2 [n2' [H2n2 [H2n2' [H2i2 _]]]]].
  specialize (H s n1 n2 H1n1 H2n2).
  specialize (H0 s n1' n2' H1n1' H2n2').
  congruence.
Qed.

Lemma cmp_denote_det: forall D1 D2 c,
  deterministic D1 ->
  deterministic D2 ->
  deterministic (cmp_denote c D1 D2).
Proof.
  unfold deterministic, cmp_denote.
  intros.
  destruct H1 as [n1 [n1' [H1n1 [H1n1' H1i1]]]].
  destruct H2 as [n2 [n2' [H2n2 [H2n2' H2i2]]]].
  specialize (H s n1 n2 H1n1 H2n2).
  specialize (H0 s n1' n2' H1n1' H2n2').
  rewrite H in H1i1; rewrite H0 in H1i1.
  congruence.
Qed.

(** 在后续几个关于布尔运算的证明中，经常需要用到零与非零是不相等的这条性质。*)
Lemma sign_zero_not_zero_contradiction: forall i (P: Prop),
  i = Int64.repr 0 ->
  Int64.signed i <> 0 ->
  P.
Proof.
  intros.
  subst i.
  rewrite Int64.signed_repr in H0 by int64_lia.
  congruence.
Qed.

(** 下面这个关于_[and_denote]_的证明就反复使用了上述引理。*)
Lemma and_denote_det: forall D1 D2,
  deterministic D1 ->
  deterministic D2 ->
  deterministic (and_denote D1 D2).
Proof.
  unfold deterministic, and_denote; intros.
  destruct H1 as [ [? ?] | [ [n1 [? [? [? ?] ] ] ] | [n1 [n2 [? [? [? [? ?] ] ] ] ] ] ] ],
           H2 as [ [? ?] | [ [n1' [? [? [? ?] ] ] ] | [n1' [n2' [? [? [? [? ?] ] ] ] ] ] ] ].
  + congruence.
  + congruence.
  + specialize (H _ _ _ H1 H2).
    apply (sign_zero_not_zero_contradiction n1'); auto.
  + congruence.
  + congruence.
  + specialize (H0 _ _ _ H3 H6).
    apply (sign_zero_not_zero_contradiction n2'); auto.
  + specialize (H _ _ _ H1 H2).
    apply (sign_zero_not_zero_contradiction n1); auto.
  + specialize (H0 _ _ _ H3 H7).
    apply (sign_zero_not_zero_contradiction n2); auto.
  + congruence.
Qed.

Lemma or_denote_det: forall D1 D2,
  deterministic D1 ->
  deterministic D2 ->
  deterministic (or_denote D1 D2).
Proof.
  unfold deterministic, or_denote; intros.
  destruct H1 as [[n1 [H1n11 [H1n12 H1n13]]] | [[n1' [H1n1'1 [H1n1'2 [H1n1'3 H1n1'4]]]] | [H11 [H12 H13]]]],
           H2 as [[n2 [H2n21 [H2n22 H2n23]]] | [[n2' [H2n2'1 [H2n2'2 [H2n2'3 H2n2'4]]]] | [H21 [H22 H23]]]].
  - congruence.
  - congruence.
  - specialize (H _ _ _ H1n11 H21).
    apply (sign_zero_not_zero_contradiction n1); auto.
  - congruence.
  - congruence.
  - specialize (H0 _ _ _ H1n1'2 H22).
    apply (sign_zero_not_zero_contradiction n1'); auto.
  - specialize (H _ _ _ H2n21 H11).
    apply (sign_zero_not_zero_contradiction n2); auto.
  - specialize (H0 _ _ _ H2n2'2 H12).
    apply (sign_zero_not_zero_contradiction n2'); auto.
  - congruence.
Qed.

Lemma not_denote_det: forall D,
  deterministic D ->
  deterministic (not_denote D).
Proof.
  unfold deterministic, not_denote; intros.
  destruct H0 as [[n0 [H0n01 [H0n02 H0n03]]] | [H01 H02]],
           H1 as [[n1 [H1n11 [H1n12 H1n13]]] | [H11 H12]].
  - congruence.
  - specialize (H _ _ _ H0n01 H11).
    apply (sign_zero_not_zero_contradiction n0); auto.
  - specialize (H _ _ _ H1n11 H01).
    apply (sign_zero_not_zero_contradiction n1); auto.
  - congruence.
Qed.

Lemma neg_denote_det: forall D,
  deterministic D ->
  deterministic (neg_denote D).
Proof.
  unfold deterministic, neg_denote; intros.
  destruct H0 as [n0 [Hn01 [Hn02 _]]],
           H1 as [n1 [Hn11 [Hn12 _]]].
  specialize (H _ _ _ Hn01 Hn11).
  congruence.
Qed.

Lemma deref_denote_det: forall D,
  deterministic D ->
  deterministic (deref_denote D).
Proof.
  unfold deterministic, deref_denote; intros.
  destruct H0 as [p0 [Hp01 Hp02]],
           H1 as [p1 [Hp11 Hp12]].
  specialize (H _ _ _ Hp01 Hp11).
  rewrite H in Hp02.
  congruence.
Qed.

Lemma eeval_det: forall e, deterministic (eeval e).
Proof.
  intros.
  induction e; simpl.
  + apply const_denote_det.
  + apply var_denote_det.
  + destruct op; simpl.
    - apply or_denote_det; tauto.
    - apply and_denote_det; tauto.
    - apply cmp_denote_det; tauto.
    - apply cmp_denote_det; tauto.
    - apply cmp_denote_det; tauto.
    - apply cmp_denote_det; tauto.
    - apply cmp_denote_det; tauto.
    - apply cmp_denote_det; tauto.
    - apply arith_denote1_det; tauto.
    - apply arith_denote1_det; tauto.
    - apply arith_denote1_det; tauto.
    - apply arith_denote2_det; tauto.
    - apply arith_denote2_det; tauto.
  + destruct op; simpl.
    - apply not_denote_det; tauto.
    - apply neg_denote_det; tauto.
  + apply deref_denote_det; tauto.
Qed.

(** **** Exercise **** *)
(** 请证明我们符号执行中所计算的最强后条件的正确性。*)

(** _[remove_var_lit]_函数表示删除标准形式断言的_[var_part]_中所有关于程序变量
    _[x]_的子句（如果有的话）。*)
Fixpoint remove_var_lit
           (Ps: list vars_literal)
           (x: var_name): list vars_literal :=
  match Ps with
  | nil => nil
  | P :: Ps0 =>
      if String.eqb x P.(lit_var_name)
      then remove_var_lit Ps0 x
      else P :: remove_var_lit Ps0 x
  end.

(** _[insert_var_lit]_函数表示插入一下关于程序变量_[x]_的子句，并删除原有的关于
    _[x]_的子句（如果有的话）。插入的子句会被插入到原先_[x]_第一次出现的位置，如
    果原先的断言与_[x]_无关，那就插入到子句列表尾。*)
Fixpoint insert_var_lit
           (Ps: list vars_literal)
           (x: var_name)
           (a: aexpr): list vars_literal :=
  match Ps with
  | nil =>
      {| lit_var_name := x; lit_var_value := a |} :: nil
  | P :: Ps0 =>
      if String.eqb x P.(lit_var_name)
      then {| lit_var_name := x; lit_var_value := a |} ::
           remove_var_lit Ps0 x
      else P :: insert_var_lit Ps0 x a
  end.

(** 首先证明：如果程序状态_[s]_是对变量_[x]_进行赋值后得到的新程序状态，那么对应
    的新的_[vars_literal]_在程序状态_[s]_上成立。*)
Lemma vars_literal_sat_pos: forall J x a n s,
  aexpr_denote J a = Some n ->
  s x = Int64.repr n ->
  n <= Int64.max_signed ->
  n >= Int64.min_signed ->
  vars_literal_sat
    s
    J
    {| lit_var_name := x; lit_var_value := a |}.
Proof.
  unfold vars_literal_sat; intros; simpl.
  exists n.
  split. tauto.
  split. tauto.
  split. tauto.
  congruence.
Qed.

(** 其次证明：如果程序状态_[s2]_是自程序状态_[s1]_对变量_[x]_进行赋值后得到的新
    程序状态，那么除了与_[x]_有关的情况之外，所有的_[vars_literal]_只要在_[s1]_
    上为真就会在_[s2]_上为真。*)
Lemma vars_literal_sat_unchanged: forall J x (P: vars_literal) s1 s2,
  vars_literal_sat s1 J P ->
  (forall y, x <> y -> s1 y = s2 y) ->
  x <> P.(lit_var_name) ->
  vars_literal_sat s2 J P.
Proof.
  unfold vars_literal_sat; intros.
  destruct H as [n [Hn1 [Hn2 [Hn3 Hn4]]]].
  exists n.
  split. tauto.
  split. tauto.
  split. tauto.
  specialize (H0 P.(lit_var_name) H1).
  congruence.
Qed.

(** 进一步，可以证明_[remove_var_lit]_是正确的。*)
Lemma remove_var_lit_sound: forall Ps x (s1 s2: var_name -> int64) J,
  Forall (vars_literal_sat s1 J) Ps ->
  (forall y, x <> y -> s1 y = s2 y) ->
  Forall (vars_literal_sat s2 J) (remove_var_lit Ps x).
Proof.
  intros.
  induction Ps as [| P Ps0 ?]; simpl.
  - apply Forall_nil.
  - apply Forall_cons_iff in H; destruct H as [? ?].
    string_eqb_case_analysis x P.(lit_var_name).
    + apply IHPs.
      apply H1.
    + apply Forall_cons.
      * revert H H0 H2. apply vars_literal_sat_unchanged.
      * specialize (IHPs H1). tauto.
Qed.

(** 再进一步，可以证明_[insert_var_lit]_是正确的。*)
Lemma insert_var_lit_sound: forall Ps x a n s1 s2 J,
  Forall (vars_literal_sat s1 J) Ps ->
  aexpr_denote J a = Some n ->
  s2 x = Int64.repr n ->
  (forall y, x <> y -> s1 y = s2 y) ->
  n <= Int64.max_signed ->
  n >= Int64.min_signed ->
  Forall (vars_literal_sat s2 J) (insert_var_lit Ps x a).
Proof.
  intros.
  induction Ps as [| P Ps0 ?]; simpl.
  - apply Forall_cons.
    + revert H0 H1 H3 H4. apply vars_literal_sat_pos.
    + apply Forall_nil.
  - apply Forall_cons_iff in H; destruct H as [? ?].
    string_eqb_case_analysis x P.(lit_var_name).
    + apply Forall_cons.
      * revert H0 H1 H3 H4. apply vars_literal_sat_pos.
      * revert H5 H2. apply remove_var_lit_sound.
    + apply Forall_cons.
      * revert H H2 H6. apply vars_literal_sat_unchanged.
      * apply IHPs. apply H5.
Qed.
