

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
Require Import PL.DenotationalSemantics.
Require Import compcert.lib.Integers.

Local Open Scope Z.

(** * 在Coq中定义标准形式断言 *)

Module AssertionLang.

Import WhileD_Expr WhileD_Cmd.

Definition logic_var_name := string.

(** _[aexpr]_定义了断言语言的项。在当前这个极简的断言语言中，我们只考虑了基本的
    算数运算。*)
Inductive aexpr: Type :=
| AConst (n: Z)
| AVar (v: logic_var_name)
| ANeg (e: aexpr)
| APlus (e1 e2: aexpr)
| AMinus (e1 e2: aexpr)
| AMul (e1 e2: aexpr)
| ADiv (e1 e2: aexpr)
| AMod (e1 e2: aexpr).

(** 我们可以在Coq中定义表达式的语法树相等判定函数。*)
Fixpoint aexpr_eqb (e1 e2: aexpr): bool :=
  match e1, e2 with
  | AConst n1, AConst n2 => Z.eqb n1 n2
  | AVar v1, AVar v2 => String.eqb v1 v2
  | ANeg e1, ANeg e2 => aexpr_eqb e1 e2
  | APlus e11 e12, APlus e21 e22 =>
      (aexpr_eqb e11 e21 && aexpr_eqb e12 e22)%bool
  | AMinus e11 e12, AMinus e21 e22 =>
      (aexpr_eqb e11 e21 && aexpr_eqb e12 e22)%bool
  | AMul e11 e12, AMul e21 e22 =>
      (aexpr_eqb e11 e21 && aexpr_eqb e12 e22)%bool
  | ADiv e11 e12, ADiv e21 e22 =>
      (aexpr_eqb e11 e21 && aexpr_eqb e12 e22)%bool
  | AMod e11 e12, AMod e21 e22 =>
    (aexpr_eqb e11 e21 && aexpr_eqb e12 e22)%bool
  | _, _ => false
  end.

(** 并证明它确实判定了相等。*)
Lemma aexpr_eqb_eq: forall e1 e2, aexpr_eqb e1 e2 = true <-> e1 = e2.
Proof.
  intros e1.
  induction e1; destruct e2; try (split; intros HH; discriminate HH); simpl.
  + rewrite Z.eqb_eq.
    split; intros; congruence.
  + rewrite String.eqb_eq.
    split; intros; congruence.
  + rewrite IHe1.
    split; intros; congruence.
  + rewrite Bool.andb_true_iff.
    rewrite IHe1_1, IHe1_2.
    split; [intros [? ?]; congruence | intros; split; congruence].
  + rewrite Bool.andb_true_iff.
    rewrite IHe1_1, IHe1_2.
    split; [intros [? ?]; congruence | intros; split; congruence].
  + rewrite Bool.andb_true_iff.
    rewrite IHe1_1, IHe1_2.
    split; [intros [? ?]; congruence | intros; split; congruence].
  + rewrite Bool.andb_true_iff.
    rewrite IHe1_1, IHe1_2.
    split; [intros [? ?]; congruence | intros; split; congruence].
  + rewrite Bool.andb_true_iff.
    rewrite IHe1_1, IHe1_2.
    split; [intros [? ?]; congruence | intros; split; congruence].
Qed.

(** _[aprop_pure]_是内存无关断言。同样为了简单起见，我们只考虑了整数间的大小比
    较。*)
Inductive aprop_pure: Type :=
| AGe (e1 e2: aexpr)
| AGt (e1 e2: aexpr)
| ALe (e1 e2: aexpr)
| ALt (e1 e2: aexpr)
| AEq (e1 e2: aexpr)
| ANe (e1 e2: aexpr)
.

(** _[aprop_sep]_是与内存有关的断言。*)
Inductive aprop_sep: Type :=
| AStore (e1 e2: aexpr)
| AListRep (e: aexpr)
| AListSeg (e1 e2: aexpr)
.

(** 下面先定义标准形式断言的变量部分。*)
Record vars_literal: Type := {
  lit_var_name: var_name;
  lit_var_value: aexpr;
}.

(** 接下去我们可以分三步定义标准形式断言。首先定义各个变量性质、内存性质的合取。
    这里，_[list]_是Coq标准库定义的类型，_[list A]_表示一列_[A]_集合的元素。在
    Coq中，_[nil]_表示空的_[list]_，_[cons a l]_表示由头元素_[a]_和剩余部分_[l]_
    组成的_[list]_，也可以用_[a :: l]_表示。例如，_[1 :: 2 :: 3 :: 1 :: nil]_就
    是一个_[list Z]_的元素。*)
Record conj_assertion: Type := {
  var_part: list vars_literal;
  pure_part: list aprop_pure;
  mem_part: list aprop_sep
}.

(** 下面定义带存在量词的断言，其中_[ex_vars]_域表示的是被存在量词约束的变量名。*)
Record ex_assertion: Type := {
  ex_vars: list logic_var_name;
  property: conj_assertion
}.

(** 最后我们允许把带存在量词的断言析取起来。*)
Definition assertion: Type := list ex_assertion.

End AssertionLang.

(** 下面我们将在Coq中定义符号执行过程，并证明其可靠性。我们将从简单的表达式符号
    求值开始。具体而言，我们将先定义一个表达式符号求值函数：

      - _[eval: conj_assertion -> expr -> option aexpr]_

    表示程序表达式的符号求值。要证明这个求值过程的正确性，就是要证明：对于任意断
    言_[P]_、程序表达式_[e]_以及数学表达式_[a]_，如果_[eval P e = Some a]_，那么
    在任意满足断言_[P]_的程序状态_[s]_与逻辑变量的指派_[J]_上，_[e]_的值与_[a]_
    的值相同。当然，这其中的许多语义定义都需要考虑程序表达式与数学表达式是否有定
    义的问题，因此这里首先引入一系列关于_[option]_的运算。*)

Definition option_map_xx
             {A B}
             (f: A -> B)
             (x: option A): option B :=
  match x with
  | Some x' => Some (f x')
  | _ => None
  end.

Definition option_map_xo
             {A B}
             (f: A -> option B)
             (x: option A): option B :=
  match x with
  | Some x' => f x'
  | _ => None
  end.

Definition option_map_xxx
             {A B C}
             (f: A -> B -> C)
             (x: option A)
             (y: option B): option C :=
  match x, y with
  | Some x', Some y' => Some (f x' y')
  | _, _ => None
  end.

Definition option_pred_xx
             {A B}
             (P: A -> B -> Prop)
             (x: option A)
             (y: option B): Prop :=
  match x, y with
  | Some x', Some y' => P x' y'
  | _, _ => False
  end.

(** * 在Coq中定义符号执行过程 *)

Module SimpleSymbEval.

Import WhileD_Expr WhileD_Cmd AssertionLang.

(** 下面首先定义表达式的符号求值过程。*)

(** 表达式的符号求值结果分为两部分，其一是一个数学表达式，表示求值结果；其二是求
    值安全的附加条件。*)
Record eval_result: Type := {
  value_of_result: aexpr;
  safe_cond: list aprop_pure
}.

(** _[eval_var]_函数定义了如何从标准形式断言的_[var_part]_部分找到程序变量_[x]_
    的符号求值结果。该定义中使用了Coq字符串标准库中的_[String.eqb]_函数用于判定
    两个字符串是否相等。*)
Fixpoint eval_var
           (lits: list vars_literal)
           (x: var_name): option eval_result :=
  match lits with
  | nil => None
  | lit :: lits0 =>
      if String.eqb x lit.(lit_var_name)
      then Some {| value_of_result := lit.(lit_var_value);
                   safe_cond := nil |}
      else eval_var lits0 x
  end.

(** _[eval_var]_函数定义了如何从标准形式断言的_[mem_part]_部分找到地址解引用表达
    式的符号求值结果。这一定义中使用了先前定义的_[aexpr_eqb]_函数用于判断两个数
    学表达式是否是相同的表达式。*)
Fixpoint eval_deref
           (Ps: list aprop_sep)
           (res: eval_result): option eval_result :=
  match Ps with
  | nil => None
  | P :: Ps0 =>
    match P with
    | AStore e1 e2 =>
        if aexpr_eqb res.(value_of_result) e1
        then Some {| value_of_result := e2;
                     safe_cond := res.(safe_cond) |}
        else eval_deref Ps0 res
    | _ => eval_deref Ps0 res
    end
  end.

(** 接下去定义常数、算术运算的符号求值，它们都是较为直观的。*)
Definition eval_const (n: Z): eval_result :=
  {| value_of_result := AConst n;
     safe_cond :=
       ALe (AConst n) (AConst Int64.max_signed) ::
       AGe (AConst n) (AConst Int64.min_signed) :: nil |}.

(** 在下面二元运算的符号求值定义中，使用了_[++]_连接_[res1]_与_[res2]_的安全求值
    附加条件。这个符号_[++]_表示Coq中两个_[list]_的连接，其定义为_[app]_。这里说
    明，如果_[EBinop op e1 e2]_的求值是安全的，首先要求_[e1]_与_[e2]_的求值是安
    全的。 *)
Definition eval_binop1
             (f: aexpr -> aexpr -> aexpr)
             (res1 res2: eval_result): eval_result :=
  {| value_of_result :=
       f res1.(value_of_result) res2.(value_of_result);
     safe_cond :=
       ALe
         (f res1.(value_of_result) res2.(value_of_result))
         (AConst Int64.max_signed) ::
       AGe
         (f res1.(value_of_result) res2.(value_of_result))
         (AConst Int64.min_signed) ::
       res1.(safe_cond) ++ res2.(safe_cond)
  |}.

Definition eval_binop2
             (f: aexpr -> aexpr -> aexpr)
             (res1 res2: eval_result): eval_result :=
  {| value_of_result :=
       f res1.(value_of_result) res2.(value_of_result);
     safe_cond :=
       ALe
         (ADiv res1.(value_of_result) res2.(value_of_result))
         (AConst Int64.max_signed) ::
       AGe
         (ADiv res1.(value_of_result) res2.(value_of_result))
         (AConst Int64.min_signed) ::
       ANe res2.(value_of_result) (AConst 0) ::
       res1.(safe_cond) ++ res2.(safe_cond)
  |}.

Definition eval_neg (res: eval_result): eval_result :=
  {| value_of_result :=
       ANeg res.(value_of_result);
     safe_cond :=
       ANe
         res.(value_of_result)
         (AConst Int64.min_signed) ::
       res.(safe_cond)
  |}.

(** 将上面这些定义汇总起来，可以对程序表达式_[e]_递归定义其符号求值的结果。*)
Fixpoint eval
           (P: conj_assertion)
           (e: expr): option eval_result :=
  match e with
  | ENum n => Some (eval_const n)
  | EVar x => eval_var P.(var_part) x
  | EBinop op e1 e2 =>
      match op with
      | OPlus =>
          option_map_xxx
            (eval_binop1 APlus) (eval P e1) (eval P e2)
      | OMinus =>
          option_map_xxx
            (eval_binop1 AMinus) (eval P e1) (eval P e2)
      | OMul =>
          option_map_xxx
            (eval_binop1 AMul) (eval P e1) (eval P e2)
      | ODiv =>
          option_map_xxx
            (eval_binop2 ADiv) (eval P e1) (eval P e2)
      | OMod =>
          option_map_xxx
            (eval_binop2 AMod) (eval P e1) (eval P e2)
      | _ => None
      end
  | EUnop op e1 =>
      match op with
      | ONeg => option_map_xx eval_neg (eval P e1)
      | _ => None
      end
  | EDeref e1 =>
      option_map_xo (eval_deref P.(mem_part)) (eval P e1)
  end.

(** 在表达式符号求值的基础上，我们可以定义赋值语句的符号执行结果。*)

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

(** 与上面定义的_[var_part]_变换类似，_[replace_aprop_sep]_定义了对标准形式断言
    中_[mem_part]_进行的变换。*)
Fixpoint replace_aprop_sep
           (Ps: list aprop_sep)
           (a b: aexpr): option (list aprop_sep) :=
  match Ps with
  | nil => None
  | P :: Ps0 =>
      match P with
      | AStore a0 b0 =>
          if aexpr_eqb a a0
          then Some (AStore a b :: Ps0)
          else option_map_xx (cons P) (replace_aprop_sep Ps0 a b)
      | _ => option_map_xx (cons P) (replace_aprop_sep Ps0 a b)
      end
  end.

(** 基于上面的辅助函数，可以定义变量赋值语句与内存地址赋值语句的最强后条件。*)
Record sp_result: Type := {
  sp_assrt: conj_assertion;
  side_cond: list aprop_pure
}.

Definition sp_asgn_var
             (P: conj_assertion)
             (x: var_name)
             (e: expr): option sp_result :=
  match eval P e with
  | Some a =>
      Some
        {| sp_assrt := {|
             var_part :=
               insert_var_lit P.(var_part) x a.(value_of_result);
             pure_part := P.(pure_part);
             mem_part := P.(mem_part) |};
           side_cond := a.(safe_cond) |}
  | None => None
  end.

Definition sp_asgn_mem
             (P: conj_assertion)
             (e1 e2: expr): option sp_result :=
  match eval P e1, eval P e2 with
  | Some a, Some b =>
      match replace_aprop_sep
              P.(mem_part)
              a.(value_of_result)
              b.(value_of_result) with
      | Some Ps =>
          Some {| sp_assrt :=
                    {| var_part := P.(var_part);
                       pure_part := P.(pure_part);
                       mem_part := Ps |};
                  side_cond :=
                    a.(safe_cond) ++ b.(safe_cond) |}
      | None => None
      end
  | _, _ => None
  end.

End SimpleSymbEval.

(** * 断言的语义 *)

Module AssertionSem.

Import WhileD_Expr WhileD_Cmd AssertionLang.

Definition var_assignment: Type :=
  logic_var_name -> Z.

Definition option_partial_Zfunc2
             (valid: Z -> Z -> bool)
             (f: Z -> Z -> Z)
             (x y: option Z): option Z :=
  match x, y with
  | Some x', Some y' =>
      if valid x' y' then None else Some (f x' y')
  | _, _ => None
  end.

(** _[aexpr_denote]_定义了数学表达式的语义 *)
Fixpoint aexpr_denote
           (J: var_assignment)
           (e: aexpr): option Z :=
  match e with
  | AConst n =>
      Some n
  | AVar v =>
      Some (J v)
  | ANeg e1 =>
      option_map_xx Z.opp (aexpr_denote J e1)
  | APlus e1 e2 =>
      option_map_xxx
        Z.add (aexpr_denote J e1) (aexpr_denote J e2)
  | AMinus e1 e2 =>
      option_map_xxx
        Z.sub (aexpr_denote J e1) (aexpr_denote J e2)
  | AMul e1 e2 =>
      option_map_xxx
        Z.mul (aexpr_denote J e1) (aexpr_denote J e2)
  | ADiv e1 e2 =>
      option_partial_Zfunc2 (fun _ z => Z.eqb z 0)
        Z.quot (aexpr_denote J e1) (aexpr_denote J e2)
  | AMod e1 e2 =>
      option_partial_Zfunc2 (fun _ z => Z.eqb z 0)
        Z.rem (aexpr_denote J e1) (aexpr_denote J e2)
  end.

(** 下面定义三类原子命题的语义 *)
Definition aprop_pure_sat
             (J: var_assignment)
             (P: aprop_pure): Prop :=
  match P with
  | AGe e1 e2 =>
      option_pred_xx
        Z.ge (aexpr_denote J e1) (aexpr_denote J e2)
  | AGt e1 e2 =>
      option_pred_xx
        Z.gt (aexpr_denote J e1) (aexpr_denote J e2)
  | ALe e1 e2 =>
      option_pred_xx
        Z.le (aexpr_denote J e1) (aexpr_denote J e2)
  | ALt e1 e2 =>
      option_pred_xx
        Z.lt (aexpr_denote J e1) (aexpr_denote J e2)
  | AEq e1 e2 =>
      option_pred_xx
        eq (aexpr_denote J e1) (aexpr_denote J e2)
  | ANe e1 e2 =>
      option_pred_xx
        (fun x y => x <> y)
        (aexpr_denote J e1) (aexpr_denote J e2)
  end.

Definition store_sat
             (m: int64 -> option int64)
             (n1 n2: Z): Prop :=
  n1 <= Int64.max_signed /\
  n1 >= Int64.min_signed /\
  n2 <= Int64.max_signed /\
  n2 >= Int64.min_signed /\
  m (Int64.repr n1) = Some (Int64.repr n2).

Fixpoint listseg_sat
           (m: int64 -> option int64)
           (n1: Z)
           (l: list Z)
           (n2: Z): Prop :=
  Int64.min_signed <= n1 <= Int64.max_signed /\
  match l with
  | nil =>
      n1 = n2
  | n1' :: l0 =>
      m (Int64.repr n1) = Some (Int64.repr n1') /\
      listseg_sat m n1' l0 n2
  end.

Definition aprop_sep_sat
             (m: int64 -> option int64)
             (J: var_assignment)
             (P: aprop_sep): Prop :=
  match P with
  | AStore e1 e2 =>
      match aexpr_denote J e1, aexpr_denote J e2 with
      | Some n1, Some n2 =>
          store_sat m n1 n2
      | _, _ => False
      end
  | AListRep e =>
      match aexpr_denote J e with
      | Some n =>
          exists l, listseg_sat m n l 0
      | _ => False
      end
  | AListSeg e1 e2 =>
      match aexpr_denote J e1, aexpr_denote J e2 with
      | Some n1, Some n2 =>
          exists l, listseg_sat m n1 l n2
      | _, _ => False
      end
  end.

Definition vars_literal_sat
             (s: var_name -> int64)
             (J: var_assignment)
             (l: vars_literal): Prop :=
  exists n,
    aexpr_denote J l.(lit_var_value) = Some n /\
    n <= Int64.max_signed /\
    n >= Int64.min_signed /\
    Int64.repr n = s l.(lit_var_name).

(** 可以证明，如果做程序状态上的等价变化，不影响上面这些命题满足与否。*)
Lemma vars_literal_sat_congr:
  forall s1 s2 J l,
    (forall x, s1 x = s2 x) ->
    (vars_literal_sat s1 J l <-> vars_literal_sat s2 J l).
Proof.
  intros.
  unfold vars_literal_sat.
  apply Morphisms_Prop.ex_iff_morphism; intros n.
  rewrite H.
  tauto.
Qed.

Lemma store_sat_congr:
  forall m1 m2 n1 n2,
    (forall p, m1 p = m2 p) ->
    (store_sat m1 n1 n2 <-> store_sat m2 n1 n2).
Proof.
  intros.
  unfold store_sat.
  rewrite H.
  tauto.
Qed.

Lemma listseg_sat_congr:
  forall m1 m2 n1 l n2,
    (forall p, m1 p = m2 p) ->
    (listseg_sat m1 n1 l n2 <-> listseg_sat m2 n1 l n2).
Proof.
  intros.
  revert n1; induction l; intros; simpl.
  + tauto.
  + rewrite H, IHl; tauto.
Qed.

Lemma aprop_sep_sat_congr:
  forall m1 m2 J P,
    (forall p, m1 p = m2 p) ->
    (aprop_sep_sat m1 J P <-> aprop_sep_sat m2 J P).
Proof.
  intros.
  destruct P; simpl.
  + destruct (aexpr_denote J e1), (aexpr_denote J e2);
      try tauto.
    apply store_sat_congr; tauto.
  + destruct (aexpr_denote J e); try tauto.
    apply Morphisms_Prop.ex_iff_morphism; intros l.
    apply listseg_sat_congr; tauto.
  + destruct (aexpr_denote J e1), (aexpr_denote J e2);
      try tauto.
    apply Morphisms_Prop.ex_iff_morphism; intros l.
    apply listseg_sat_congr; tauto.
Qed.

(** 基于上述所有不同子句的语义定义，可以定义完整断言的语义。其中最重要的是要利用
    分离逻辑定义标准形式断言中_[mem_part]_的语义。下面首先定义内存的不交并。*)
Definition mem_join (m1 m2 m: int64 -> option int64): Prop :=
  forall i,
    (m1 i = None /\ m2 i = None /\ m i = None) \/
    (exists i', m1 i = None /\ m2 i = Some i' /\ m i = Some i') \/
    (exists i', m1 i = Some i' /\ m2 i = None /\ m i = Some i').

(** 下面列出它的四条基本性质。*)
Lemma mem_join_unit: forall m,
  mem_join (fun _ => None) m m.
Proof.
  intros m i.
  destruct (m i).
  + right; left.
    exists i0; tauto.
  + tauto.
Qed.

Lemma mem_join_assoc: forall m1 m2 m3 m23 m123,
  mem_join m2 m3 m23 ->
  mem_join m1 m23 m123 ->
  exists m12,
    mem_join m1 m2 m12 /\
    mem_join m12 m3 m123.
Proof.
  intros.
  exists (fun i => match m1 i, m2 i with
                   | Some i0, None => Some i0
                   | None, Some i0 => Some i0
                   | _, _ => None
                   end);
  split; intros i; specialize (H i); specialize (H0 i);
  destruct H as [ [? [? ?] ] | [ [? [? [? ?] ] ] | [? [? [? ?] ] ] ] ];
    destruct H0 as [ [? [? ?] ] | [ [? [? [? ?] ] ] | [? [? [? ?] ] ] ] ];
    rewrite H2 in H3;
    try congruence;
    rewrite H, H0, ?H1, ?H4;
  try (left; split; [| split]; tauto);
  try (solve [right; left; eexists; split; [| split]; eauto]);
  try (solve [right; right; eexists; split; [| split]; eauto]).
Qed.

Lemma mem_join_Some_left: forall m1 m2 m i i',
  mem_join m1 m2 m ->
  m1 i = Some i' ->
  m i = Some i'.
Proof.
  intros.
  specialize (H i).
  destruct H as [ [? [? ?] ] | [ [? [? [? ?] ] ] | [? [? [? ?] ] ] ] ];
  congruence.
Qed.

Lemma mem_join_Some_right: forall m1 m2 m i i',
  mem_join m1 m2 m ->
  m2 i = Some i' ->
  m i = Some i'.
Proof.
  intros.
  specialize (H i).
  destruct H as [ [? [? ?] ] | [ [? [? [? ?] ] ] | [? [? [? ?] ] ] ] ];
  congruence.
Qed.

(** 利用内存的不交并，我们可以定义_[mem_part]_部分的语义。*)
Fixpoint sep_conj_sat
           (m: int64 -> option int64)
           (J: var_assignment)
           (Ps: list aprop_sep): Prop :=
  match Ps with
  | nil => True
  | P :: Ps0 =>
      exists m1 m2,
        mem_join m1 m2 m /\
        aprop_sep_sat m1 J P /\
        sep_conj_sat m2 J Ps0
  end.

(** 基于上面的定义，我们可以如下刻画整个断言的语义，该定义分为3个部分，其中，前
    两个部分的定义中使用了_[Forall]_这个Coq标准库中提供的关于_[list]_的高阶谓
    词。假如_[X: A -> Prop]_表示一个集合并且_[l: list A]_是一列_[A]_集合中的元
    素，那么_[Forall X l]_就表示_[l]_中的每一项都是_[X]_中的元素。在下面
    _[conj_assertion_sat]_的定义中：

      - _[Forall (vars_literal_sat s.(vars) J) P.(var_part)]_要求程序状态_[s]_与
        逻辑变量的指派_[J]_满足_[P.(var_part)]_中的每一项；

      - _[Forall (aprop_pure_sat J) P.(pure_part)]_则要求指派_[J]_能够满足
        _[P.(pure_part)]_中的每一项。*)

Definition conj_assertion_sat
             (s: prog_state)
             (J: var_assignment)
             (P: conj_assertion): Prop :=
  Forall (vars_literal_sat s.(vars) J) P.(var_part) /\
  Forall (aprop_pure_sat J) P.(pure_part) /\
  sep_conj_sat s.(mem) J P.(mem_part).

(** 最后，我们可以定义霍尔三元组的有效性（valid）。*)
Definition hoare_triple_valid
             (P: conj_assertion)
             (c: com)
             (Q: conj_assertion): Prop :=
  forall s1 J,
    conj_assertion_sat s1 J P ->
    (~ (ceval c).(err) s1 /\
     forall s2,
       (ceval c).(fin) s1 s2 ->
       conj_assertion_sat s2 J Q).

End AssertionSem.

(** * 符号执行的正确性 *)

(** 在开始证明之前，我们先介绍关于标准库中提供的_[Forall]_以及_[String.eqb]_的证
    明方法。*)

(** _[Forall]_有如下四条重要性质：*)

Check Forall_nil.
Check Forall_cons.
Check Forall_cons_iff.
Check Forall_app.

(** 我们在此处引入两条自定义证明指令，其中_[Forall_decomp H]_用于拆分证明前提
    _[H]_中的_[Forall]_，_[Forall_split]_用于拆分证明结论中的_[Forall]_。*)

Ltac Forall_decomp H :=
  repeat first [rewrite !Forall_cons_iff in H |
                rewrite !Forall_app in H].

Ltac Forall_split :=
  repeat first [simple apply Forall_app |
                simple apply Forall_cons |
                simple apply Forall_nil].

(** _[String.eqb]_是标准库中定义的字符串相等比较，它有两条重要性质：*)

Check String.eqb_eq.
Check String.eqb_neq.

(** 我们在先前的定义中，反复使用了_[String.eqb]_用于判断字符串相等与否，因此，我
    们在后续的证明中就难免要对这一判定结果为真还是为假进行分类讨论。下面我们也提
    供一条自定义证明指令用于这类分类讨论。*)

Ltac string_eqb_case_analysis str1 str2 :=
  let H := fresh "H" in
  destruct (String.eqb str1 str2) eqn:H;
  [apply String.eqb_eq in H | apply String.eqb_neq in H].

Module SimpleSymbEvalSound.

Import WhileD_Expr WhileD_Cmd AssertionLang
       SimpleSymbEval AssertionSem.

(** 下面先证明用于证明程序表达式的值是某整数_[n]_的几个引理。*)
Lemma build_neg_denote:
  forall (D: prog_state -> int64 -> Prop) s n,
    D s (Int64.repr n) ->
    n <= Int64.max_signed ->
    n >= Int64.min_signed ->
    n <> Int64.min_signed ->
    neg_denote D s (Int64.repr (- n)).
Proof.
  intros.
  unfold neg_denote.
  exists (Int64.repr n).
  rewrite Int64.neg_repr.
  rewrite !Int64.signed_repr by int64_lia.
  tauto.
Qed.

Lemma build_deref_denote:
  forall (D: prog_state -> int64 -> Prop) s n1 n2,
    D s (Int64.repr n1) ->
    mem s (Int64.repr n1) = Some (Int64.repr n2) ->
    deref_denote D s (Int64.repr n2).
Proof.
  intros.
  unfold deref_denote.
  exists (Int64.repr n1).
  tauto.
Qed.

Lemma build_arith_denote1_add:
  forall (D1 D2: prog_state -> int64 -> Prop) s n1 n2,
    D1 s (Int64.repr n1) ->
    D2 s (Int64.repr n2) ->
    n1 <= Int64.max_signed ->
    n1 >= Int64.min_signed ->
    n2 <= Int64.max_signed ->
    n2 >= Int64.min_signed ->
    n1 + n2 <= Int64.max_signed ->
    n1 + n2 >= Int64.min_signed ->
    arith_denote1
      Z.add Int64.add D1 D2 s (Int64.repr (n1 + n2)).
Proof.
  unfold arith_denote1.
  intros.
  exists (Int64.repr n1), (Int64.repr n2).
  rewrite Int64.add_signed.
  rewrite !Int64.signed_repr by lia.
  tauto.
Qed.

Lemma build_arith_denote1_sub:
  forall (D1 D2: prog_state -> int64 -> Prop) s n1 n2,
    D1 s (Int64.repr n1) ->
    D2 s (Int64.repr n2) ->
    n1 <= Int64.max_signed ->
    n1 >= Int64.min_signed ->
    n2 <= Int64.max_signed ->
    n2 >= Int64.min_signed ->
    n1 - n2 <= Int64.max_signed ->
    n1 - n2 >= Int64.min_signed ->
    arith_denote1
      Z.sub Int64.sub D1 D2 s (Int64.repr (n1 - n2)).
Proof.
  unfold arith_denote1.
  intros.
  exists (Int64.repr n1), (Int64.repr n2).
  rewrite Int64.sub_signed.
  rewrite !Int64.signed_repr by lia.
  tauto.
Qed.

Lemma build_arith_denote1_mul:
  forall (D1 D2: prog_state -> int64 -> Prop) s n1 n2,
    D1 s (Int64.repr n1) ->
    D2 s (Int64.repr n2) ->
    n1 <= Int64.max_signed ->
    n1 >= Int64.min_signed ->
    n2 <= Int64.max_signed ->
    n2 >= Int64.min_signed ->
    n1 * n2 <= Int64.max_signed ->
    n1 * n2 >= Int64.min_signed ->
    arith_denote1
      Z.mul Int64.mul D1 D2 s (Int64.repr (n1 * n2)).
Proof.
  unfold arith_denote1.
  intros.
  exists (Int64.repr n1), (Int64.repr n2).
  rewrite Int64.mul_signed.
  rewrite !Int64.signed_repr by lia.
  tauto.
Qed.

Lemma build_arith_denote2_div:
  forall (D1 D2: prog_state -> int64 -> Prop) s n1 n2,
    D1 s (Int64.repr n1) ->
    D2 s (Int64.repr n2) ->
    n1 <= Int64.max_signed ->
    n1 >= Int64.min_signed ->
    n2 <= Int64.max_signed ->
    n2 >= Int64.min_signed ->
    n2 <> 0 ->
    n1 ÷ n2 <= Int64.max_signed ->
    n1 ÷ n2 >= Int64.min_signed ->
    arith_denote2
      Int64.divs D1 D2 s (Int64.repr (n1 ÷ n2)).
Proof.
  unfold arith_denote2.
  intros.
  exists (Int64.repr n1), (Int64.repr n2).
  unfold Int64.divs.
  rewrite !Int64.signed_repr by lia.
  assert (n1 <> Int64.min_signed \/ n2 <> -1). {
    destruct (Z.eq_dec n2 (-1)); [| tauto].
    rewrite Z.quot_div in H6 by tauto.
    subst n2.
    simpl in H6.
    rewrite Z.div_1_r in H6.
    pose proof Z.abs_sgn n1.
    assert (Int64.max_signed = - Int64.min_signed - 1) by int64_lia.
    nia.
  }
  tauto.
Qed.

Lemma build_arith_denote2_mod:
  forall (D1 D2: prog_state -> int64 -> Prop) s n1 n2,
    D1 s (Int64.repr n1) ->
    D2 s (Int64.repr n2) ->
    n1 <= Int64.max_signed ->
    n1 >= Int64.min_signed ->
    n2 <= Int64.max_signed ->
    n2 >= Int64.min_signed ->
    n2 <> 0 ->
    n1 ÷ n2 <= Int64.max_signed ->
    n1 ÷ n2 >= Int64.min_signed ->
    arith_denote2
      Int64.mods D1 D2 s (Int64.repr (Z.rem n1 n2)).
Proof.
  unfold arith_denote2.
  intros.
  exists (Int64.repr n1), (Int64.repr n2).
  unfold Int64.mods.
  rewrite !Int64.signed_repr by lia.
  assert (n1 <> Int64.min_signed \/ n2 <> -1). {
    destruct (Z.eq_dec n2 (-1)); [| tauto].
    rewrite Z.quot_div in H6 by tauto.
    subst n2.
    simpl in H6.
    rewrite Z.div_1_r in H6.
    pose proof Z.abs_sgn n1.
    assert (Int64.max_signed = - Int64.min_signed - 1) by int64_lia.
    nia.
  }
  tauto.
Qed.

Lemma Z_rem_range: forall n1 n2,
  n1 <= Int64.max_signed ->
  n1 >= Int64.min_signed ->
  n2 <= Int64.max_signed ->
  n2 >= Int64.min_signed ->
  n2 <> 0 ->
  n1 ÷ n2 <= Int64.max_signed ->
  n1 ÷ n2 >= Int64.min_signed ->
  Z.rem n1 n2 <= Int64.max_signed /\
  Z.rem n1 n2 >= Int64.min_signed.
Proof.
  intros.
  pose proof Z.rem_bound_neg_pos n1 n2.
  pose proof Z.rem_bound_pos_neg n1 n2.
  pose proof Z.rem_bound_pos_pos n1 n2.
  pose proof Z.rem_bound_neg_neg n1 n2.
  assert (Int64.max_signed = - Int64.min_signed - 1) by int64_lia.
  lia.
Qed.

(** 下面证明我们的While-D语言的表达式语义是确定性的。*)
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
Admitted. (* 留作习题 *)

(** 在下面几个引理的证明中，我们使用_[specialize]_证明指令可以大大简化证明。*)
Lemma arith_denote1_det: forall D1 D2 Zfun ifun,
  deterministic D1 ->
  deterministic D2 ->
  deterministic (arith_denote1 Zfun ifun D1 D2).
Proof.
Admitted. (* 留作习题 *)


Lemma arith_denote2_det: forall D1 D2 ifun,
  deterministic D1 ->
  deterministic D2 ->
  deterministic (arith_denote2 ifun D1 D2).
Proof.
Admitted. (* 留作习题 *)

Lemma cmp_denote_det: forall D1 D2 c,
  deterministic D1 ->
  deterministic D2 ->
  deterministic (cmp_denote c D1 D2).
Proof.
Admitted. (* 留作习题 *)

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
Admitted. (* 留作习题 *)

Lemma not_denote_det: forall D,
  deterministic D ->
  deterministic (not_denote D).
Proof.
Admitted. (* 留作习题 *)

Lemma neg_denote_det: forall D,
  deterministic D ->
  deterministic (neg_denote D).
Proof.
Admitted. (* 留作习题 *)

Lemma deref_denote_det: forall D,
  deterministic D ->
  deterministic (deref_denote D).
Proof.
Admitted. (* 留作习题 *)

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

(** 下面证明几个关于表达式符号求值的引理，它们都证明了，如果符合表达式符号求值成
    功，那么其中的子表达式都能符号执行成果。*)
Lemma eval_EBinop_OPlus_fact: forall P e1 e2 res,
  eval P (EBinop OPlus e1 e2) = Some res ->
  exists res1 res2,
    eval P e1 = Some res1 /\
    eval P e2 = Some res2 /\
    eval_binop1 APlus res1 res2 = res.
Proof.
  intros.
  simpl in H; unfold option_map_xxx in H.
  destruct (eval P e1) as [res1 |]; [| discriminate H].
  destruct (eval P e2) as [res2 |]; [| discriminate H].
  injection H as H.
  exists res1, res2.
  tauto.
Qed.

Lemma eval_EBinop_OMinus_fact: forall P e1 e2 res,
  eval P (EBinop OMinus e1 e2) = Some res ->
  exists res1 res2,
    eval P e1 = Some res1 /\
    eval P e2 = Some res2 /\
    eval_binop1 AMinus res1 res2 = res.
Proof.
  intros.
  simpl in H; unfold option_map_xxx in H.
  destruct (eval P e1) as [res1 |]; [| discriminate H].
  destruct (eval P e2) as [res2 |]; [| discriminate H].
  injection H as H.
  exists res1, res2.
  tauto.
Qed.

Lemma eval_EBinop_OMul_fact: forall P e1 e2 res,
  eval P (EBinop OMul e1 e2) = Some res ->
  exists res1 res2,
    eval P e1 = Some res1 /\
    eval P e2 = Some res2 /\
    eval_binop1 AMul res1 res2 = res.
Proof.
  intros.
  simpl in H; unfold option_map_xxx in H.
  destruct (eval P e1) as [res1 |]; [| discriminate H].
  destruct (eval P e2) as [res2 |]; [| discriminate H].
  injection H as H.
  exists res1, res2.
  tauto.
Qed.

Lemma eval_EBinop_ODiv_fact: forall P e1 e2 res,
  eval P (EBinop ODiv e1 e2) = Some res ->
  exists res1 res2,
    eval P e1 = Some res1 /\
    eval P e2 = Some res2 /\
    eval_binop2 ADiv res1 res2 = res.
Proof.
  intros.
  simpl in H; unfold option_map_xxx in H.
  destruct (eval P e1) as [res1 |]; [| discriminate H].
  destruct (eval P e2) as [res2 |]; [| discriminate H].
  injection H as H.
  exists res1, res2.
  tauto.
Qed.

Lemma eval_EBinop_OMod_fact: forall P e1 e2 res,
  eval P (EBinop OMod e1 e2) = Some res ->
  exists res1 res2,
    eval P e1 = Some res1 /\
    eval P e2 = Some res2 /\
    eval_binop2 AMod res1 res2 = res.
Proof.
  intros.
  simpl in H; unfold option_map_xxx in H.
  destruct (eval P e1) as [res1 |]; [| discriminate H].
  destruct (eval P e2) as [res2 |]; [| discriminate H].
  injection H as H.
  exists res1, res2.
  tauto.
Qed.

Lemma eval_EUnop_ONeg_fact: forall P e res,
  eval P (EUnop ONeg e) = Some res ->
  exists res0,
    eval P e = Some res0 /\
    eval_neg res0 = res.
Proof.
  intros.
  simpl in H.
  destruct (eval P e) as [res0 |]; [injection H as H | discriminate H].
  exists res0.
  tauto.
Qed.

Lemma eval_EDeref_fact: forall P e res,
  eval P (EDeref e) = Some res ->
  exists res0,
    eval P e = Some res0 /\
    eval_deref P.(mem_part) res0 = Some res.
Proof.
  intros.
  simpl in H.
  destruct (eval P e) as [res0 |]; [| discriminate H].
  exists res0.
  tauto.
Qed.

(** 下面依次证明表达式求值正确性的各个情况。 *)
Lemma eval_sound_var: forall s J P x res,
  conj_assertion_sat s J P ->
  eval_var P.(var_part) x = Some res ->
  exists n,
    aexpr_denote J res.(value_of_result) = Some n /\
    n <= Int64.max_signed /\
    n >= Int64.min_signed /\
    eeval (EVar x) s (Int64.repr n).
Proof.
  intros.
  destruct H as [? _].
  set (lits := var_part P) in *; clearbody lits; clear P.
  induction lits as [| lit lits0 ?].
  + simpl in H0.
    discriminate H0.
  + simpl in H0.
    string_eqb_case_analysis x (lit_var_name lit).
    - subst x.
      injection H0 as H0.
      clear IHlits.
      Forall_decomp H.
      unfold vars_literal_sat in H.
      rewrite <- H0; simpl.
      apply H.
    - Forall_decomp H.
      apply IHlits; tauto.
Qed.

Lemma eval_sound_plus: forall s J P D1 D2 res1 res2 res,
  conj_assertion_sat s J P ->
  eval_binop1 APlus res1 res2 = res ->
  (exists n,
     aexpr_denote J res1.(value_of_result) = Some n /\
     n <= Int64.max_signed /\
     n >= Int64.min_signed /\
     D1 s (Int64.repr n)) ->
  (exists n,
     aexpr_denote J res2.(value_of_result) = Some n /\
     n <= Int64.max_signed /\
     n >= Int64.min_signed /\
     D2 s (Int64.repr n)) ->
  aprop_pure_sat J
    (ALe (APlus res1.(value_of_result) res2.(value_of_result))
       (AConst Int64.max_signed)) ->
  aprop_pure_sat J
    (AGe (APlus res1.(value_of_result) res2.(value_of_result))
        (AConst Int64.min_signed)) ->
  exists n : Z,
    aexpr_denote J res.(value_of_result) = Some n /\
    n <= Int64.max_signed /\
    n >= Int64.min_signed /\
    arith_denote1 Z.add Int64.add D1 D2 s (Int64.repr n).
Proof.
  intros.
  destruct H1 as [n1 [? ?] ], H2 as [n2 [? ?] ].
  exists (n1 + n2).
  rewrite <- H0.
  simpl in H3, H4 |- *.
  rewrite H1, H2 in H3, H4 |- *.
  simpl in H3, H4 |- *.
  pose proof build_arith_denote1_add D1 D2 s n1 n2.
  tauto.
Qed.

Lemma eval_sound_minus: forall s J P D1 D2 res1 res2 res,
  conj_assertion_sat s J P ->
  eval_binop1 AMinus res1 res2 = res ->
  (exists n,
     aexpr_denote J res1.(value_of_result) = Some n /\
     n <= Int64.max_signed /\
     n >= Int64.min_signed /\
     D1 s (Int64.repr n)) ->
  (exists n,
     aexpr_denote J res2.(value_of_result) = Some n /\
     n <= Int64.max_signed /\
     n >= Int64.min_signed /\
     D2 s (Int64.repr n)) ->
  aprop_pure_sat J
    (ALe (AMinus res1.(value_of_result) res2.(value_of_result))
       (AConst Int64.max_signed)) ->
  aprop_pure_sat J
    (AGe (AMinus res1.(value_of_result) res2.(value_of_result))
        (AConst Int64.min_signed)) ->
  exists n : Z,
    aexpr_denote J res.(value_of_result) = Some n /\
    n <= Int64.max_signed /\
    n >= Int64.min_signed /\
    arith_denote1 Z.sub Int64.sub D1 D2 s (Int64.repr n).
Proof.
  intros.
  destruct H1 as [n1 [? ?] ], H2 as [n2 [? ?] ].
  exists (n1 - n2).
  rewrite <- H0.
  simpl in H3, H4 |- *.
  rewrite H1, H2 in H3, H4 |- *.
  simpl in H3, H4 |- *.
  pose proof build_arith_denote1_sub D1 D2 s n1 n2.
  tauto.
Qed.

Lemma eval_sound_mul: forall s J P D1 D2 res1 res2 res,
  conj_assertion_sat s J P ->
  eval_binop1 AMul res1 res2 = res ->
  (exists n,
     aexpr_denote J res1.(value_of_result) = Some n /\
     n <= Int64.max_signed /\
     n >= Int64.min_signed /\
     D1 s (Int64.repr n)) ->
  (exists n,
     aexpr_denote J res2.(value_of_result) = Some n /\
     n <= Int64.max_signed /\
     n >= Int64.min_signed /\
     D2 s (Int64.repr n)) ->
  aprop_pure_sat J
    (ALe (AMul res1.(value_of_result) res2.(value_of_result))
       (AConst Int64.max_signed)) ->
  aprop_pure_sat J
    (AGe (AMul res1.(value_of_result) res2.(value_of_result))
        (AConst Int64.min_signed)) ->
  exists n : Z,
    aexpr_denote J res.(value_of_result) = Some n /\
    n <= Int64.max_signed /\
    n >= Int64.min_signed /\
    arith_denote1 Z.mul Int64.mul D1 D2 s (Int64.repr n).
Proof.
  intros.
  destruct H1 as [n1 [? ?] ], H2 as [n2 [? ?] ].
  exists (n1 * n2).
  rewrite <- H0.
  simpl in H3, H4 |- *.
  rewrite H1, H2 in H3, H4 |- *.
  simpl in H3, H4 |- *.
  pose proof build_arith_denote1_mul D1 D2 s n1 n2.
  tauto.
Qed.

Lemma eval_sound_div: forall s J P D1 D2 res1 res2 res,
  conj_assertion_sat s J P ->
  eval_binop2 ADiv res1 res2 = res ->
  (exists n,
     aexpr_denote J res1.(value_of_result) = Some n /\
     n <= Int64.max_signed /\
     n >= Int64.min_signed /\
     D1 s (Int64.repr n)) ->
  (exists n,
     aexpr_denote J res2.(value_of_result) = Some n /\
     n <= Int64.max_signed /\
     n >= Int64.min_signed /\
     D2 s (Int64.repr n)) ->
  aprop_pure_sat J
    (ALe (ADiv res1.(value_of_result) res2.(value_of_result))
       (AConst Int64.max_signed)) ->
  aprop_pure_sat J
    (AGe (ADiv res1.(value_of_result) res2.(value_of_result))
        (AConst Int64.min_signed)) ->
  aprop_pure_sat J
    (ANe res2.(value_of_result) (AConst 0)) ->
  exists n : Z,
    aexpr_denote J res.(value_of_result) = Some n /\
    n <= Int64.max_signed /\
    n >= Int64.min_signed /\
    arith_denote2 Int64.divs D1 D2 s (Int64.repr n).
Proof.
  intros.
  destruct H1 as [n1 [? ?] ], H2 as [n2 [? ?] ].
  exists (Z.quot n1 n2).
  rewrite <- H0.
  simpl in H3, H4, H5 |- *.
  rewrite H1, H2 in H3, H4 |- *; rewrite H2 in H5.
  simpl in H3, H4, H5 |- *.
  rewrite (proj2 (Z.eqb_neq n2 0)) in H3, H4 |- * by tauto.
  simpl in H3, H4.
  pose proof build_arith_denote2_div D1 D2 s n1 n2.
  tauto.
Qed.

Lemma eval_sound_mod: forall s J P D1 D2 res1 res2 res,
  conj_assertion_sat s J P ->
  eval_binop2 AMod res1 res2 = res ->
  (exists n,
     aexpr_denote J res1.(value_of_result) = Some n /\
     n <= Int64.max_signed /\
     n >= Int64.min_signed /\
     D1 s (Int64.repr n)) ->
  (exists n,
     aexpr_denote J res2.(value_of_result) = Some n /\
     n <= Int64.max_signed /\
     n >= Int64.min_signed /\
     D2 s (Int64.repr n)) ->
  aprop_pure_sat J
    (ALe (ADiv res1.(value_of_result) res2.(value_of_result))
       (AConst Int64.max_signed)) ->
  aprop_pure_sat J
    (AGe (ADiv res1.(value_of_result) res2.(value_of_result))
        (AConst Int64.min_signed)) ->
  aprop_pure_sat J
    (ANe res2.(value_of_result) (AConst 0)) ->
  exists n : Z,
    aexpr_denote J res.(value_of_result) = Some n /\
    n <= Int64.max_signed /\
    n >= Int64.min_signed /\
    arith_denote2 Int64.mods D1 D2 s (Int64.repr n).
Proof.
  intros.
  destruct H1 as [n1 [? ?] ], H2 as [n2 [? ?] ].
  exists (Z.rem n1 n2).
  rewrite <- H0.
  simpl in H3, H4, H5 |- *.
  rewrite H1, H2 in H3, H4 |- *; rewrite H2 in H5.
  simpl in H3, H4, H5 |- *.
  rewrite (proj2 (Z.eqb_neq n2 0)) in H3, H4 |- * by tauto.
  simpl in H3, H4.
  pose proof build_arith_denote2_mod D1 D2 s n1 n2.
  pose proof Z_rem_range n1 n2.
  tauto.
Qed.

Lemma eval_sound_neg_aux: forall s J P res1 n1 res2,
  conj_assertion_sat s J P ->
  eval_neg res1 = res2 ->
  aexpr_denote J res1.(value_of_result) = Some n1 ->
  aexpr_denote J res2.(value_of_result) = Some (- n1).
Proof.
  intros.
  rewrite <- H0.
  simpl.
  rewrite H1.
  reflexivity.
Qed.

Lemma eval_sound_neg: forall s J P D res1 res2,
  conj_assertion_sat s J P ->
  eval_neg res1 = res2 ->
  (exists n,
     aexpr_denote J res1.(value_of_result) = Some n /\
     n <= Int64.max_signed /\
     n >= Int64.min_signed /\
     D s (Int64.repr n)) ->
  aprop_pure_sat J (ANe res1.(value_of_result) (AConst Int64.min_signed)) ->
  (exists n,
    aexpr_denote J res2.(value_of_result) = Some n /\
    n <= Int64.max_signed /\
    n >= Int64.min_signed /\
    neg_denote D s (Int64.repr n)).
Proof.
  intros.
  destruct H1 as [n [? ?] ].
  pose proof eval_sound_neg_aux _ _ _ _ _ _ H H0 H1.
  exists (- n).
  simpl in H2.
  rewrite H1 in H2.
  simpl in H2.
  pose proof build_neg_denote D s n.
  assert (- n <= Int64.max_signed /\ - n >= Int64.min_signed) by int64_lia.
  tauto.
Qed.

Lemma eval_deref_safe_cond: forall Ps res1 res2,
  eval_deref Ps res1 = Some res2 ->
  res2.(safe_cond) = res1.(safe_cond).
Proof.
  intros.
  induction Ps as [| P Ps0 ?].
  + discriminate H.
  + destruct P.
    - simpl in H.
      destruct (aexpr_eqb res1.(value_of_result) e1).
      * injection H as H.
        rewrite <- H.
        simpl.
        reflexivity.
      * apply IHPs, H.
    - apply IHPs, H.
    - apply IHPs, H.
Qed.

Lemma eval_sound_deref_aux: forall s J P res1 res2 n1,
  conj_assertion_sat s J P ->
  eval_deref P.(mem_part) res1 = Some res2 ->
  aexpr_denote J res1.(value_of_result) = Some n1 ->
  exists n2,
  aexpr_denote J res2.(value_of_result) = Some n2 /\
  n2 <= Int64.max_signed /\
  n2 >= Int64.min_signed /\
  s.(mem) (Int64.repr n1) = Some (Int64.repr n2).
Proof.
  intros.
  destruct H as [_ [_ ?] ].
  set (m := s.(mem)) in *.
  set (Ps := P.(mem_part)) in *.
  clearbody m Ps; clear P s.
  assert (exists m1 m2, mem_join m1 m2 m /\ sep_conj_sat m2 J Ps).
  {
    exists (fun _ => None), m.
    split; [apply mem_join_unit | apply H].
  }
  clear H; destruct H2 as [m1 [m2 [JOIN_m SAT] ] ].
  revert m1 m2 SAT JOIN_m; induction Ps as [| P Ps0 ?]; intros.
  + simpl in H0.
    discriminate H0.
  + simpl in SAT.
    destruct SAT as [m2a [m2b [JOIN_m2 [SAT_P SAT] ] ] ].
    pose proof mem_join_assoc _ _ _ _ _ JOIN_m2 JOIN_m.
    destruct H as [m12a [JOIN_m12a JOIN_m'] ].
    simpl in H0.
    destruct P; [destruct (aexpr_eqb res1.(value_of_result) e1) eqn:?H | |].
    - apply aexpr_eqb_eq in H.
      injection H0 as ?.
      subst e1 res2.
      clear IHPs.
      simpl in SAT_P.
      rewrite H1 in SAT_P.
      destruct (aexpr_denote J e2) as [n2 |] eqn:?H; [| contradiction].
      exists n2.
      simpl.
      unfold store_sat in SAT_P.
      destruct SAT_P as [? [? [? [? ? ] ] ] ].
      pose proof mem_join_Some_left _ _ _ _ _ JOIN_m2 H5.
      pose proof mem_join_Some_right _ _ _ _ _ JOIN_m H6.
      tauto.
    - specialize (IHPs H0 m12a m2b SAT JOIN_m').
      tauto.
    - specialize (IHPs H0 m12a m2b SAT JOIN_m').
      tauto.
    - specialize (IHPs H0 m12a m2b SAT JOIN_m').
      tauto.
Qed.

Lemma eval_sound_deref: forall s J P D res1 res2,
  conj_assertion_sat s J P ->
  eval_deref P.(mem_part) res1 = Some res2 ->
  (exists n,
     aexpr_denote J res1.(value_of_result) = Some n /\
     n <= Int64.max_signed /\
     n >= Int64.min_signed /\
     D s (Int64.repr n)) ->
  (exists n,
    aexpr_denote J res2.(value_of_result) = Some n /\
    n <= Int64.max_signed /\
    n >= Int64.min_signed /\
    deref_denote D s (Int64.repr n)).
Proof.
  intros.
  destruct H1 as [n1 [? ?] ].
  pose proof eval_sound_deref_aux _ _ _ _ _ _ H H0 H1.
  destruct H3 as [n2 ?].
  pose proof build_deref_denote D s n1 n2.
  exists n2; tauto.
Qed.

(** 最后，可以对表达式_[e]_归纳，证明表达式求值函数_[eval]_是正确的。*)
Lemma eval_soundness: forall s J P e res,
  conj_assertion_sat s J P ->
  eval P e = Some res ->
  Forall (aprop_pure_sat J) res.(safe_cond) ->
  exists n,
    aexpr_denote J res.(value_of_result) = Some n /\
    n <= Int64.max_signed /\
    n >= Int64.min_signed /\
    eeval e s (Int64.repr n).
Proof.
  intros.
  revert res H0 H1; induction e; intros.
  + simpl in H0.
    injection H0 as ?; subst res.
    simpl in H1.
    Forall_decomp H1.
    destruct H1 as [? [? ?] ].
    simpl in H0, H1.
    exists n; simpl.
    unfold const_denote.
    tauto.
  + simpl eeval.
    unfold var_denote.
    apply (eval_sound_var s J P); tauto.
  + destruct op; try discriminate H0.
    - apply eval_EBinop_OPlus_fact in H0.
      destruct H0 as [res1 [res2 [Hres1 [Hres2 Heval] ] ] ].
      rewrite <- Heval in H1; simpl in H1.
      Forall_decomp H1; destruct H1 as [? [? [Hsafe1 Hsafe2] ] ].
      specialize (IHe1 _ Hres1 Hsafe1); specialize (IHe2 _ Hres2 Hsafe2).
      eapply (eval_sound_plus); eauto.
    - apply eval_EBinop_OMinus_fact in H0.
      destruct H0 as [res1 [res2 [Hres1 [Hres2 Heval] ] ] ].
      rewrite <- Heval in H1; simpl in H1.
      Forall_decomp H1; destruct H1 as [? [? [Hsafe1 Hsafe2] ] ].
      specialize (IHe1 _ Hres1 Hsafe1); specialize (IHe2 _ Hres2 Hsafe2).
      eapply (eval_sound_minus); eauto.
    - apply eval_EBinop_OMul_fact in H0.
      destruct H0 as [res1 [res2 [Hres1 [Hres2 Heval] ] ] ].
      rewrite <- Heval in H1; simpl in H1.
      Forall_decomp H1; destruct H1 as [? [? [Hsafe1 Hsafe2] ] ].
      specialize (IHe1 _ Hres1 Hsafe1); specialize (IHe2 _ Hres2 Hsafe2).
      eapply (eval_sound_mul); eauto.
    - apply eval_EBinop_ODiv_fact in H0.
      destruct H0 as [res1 [res2 [Hres1 [Hres2 Heval] ] ] ].
      rewrite <- Heval in H1; simpl in H1.
      Forall_decomp H1; destruct H1 as [? [? [? [Hsafe1 Hsafe2] ] ] ].
      specialize (IHe1 _ Hres1 Hsafe1); specialize (IHe2 _ Hres2 Hsafe2).
      eapply (eval_sound_div); eauto.
    - apply eval_EBinop_OMod_fact in H0.
      destruct H0 as [res1 [res2 [Hres1 [Hres2 Heval] ] ] ].
      rewrite <- Heval in H1; simpl in H1.
      Forall_decomp H1; destruct H1 as [? [? [? [Hsafe1 Hsafe2] ] ] ].
      specialize (IHe1 _ Hres1 Hsafe1); specialize (IHe2 _ Hres2 Hsafe2).
      eapply (eval_sound_mod); eauto.
  + destruct op; try discriminate H0.
    apply eval_EUnop_ONeg_fact in H0.
    destruct H0 as [res1 [? ?] ].
    rewrite <- H2 in H1; simpl in H1.
    Forall_decomp H1; destruct H1 as [? ?].
    specialize (IHe _ H0 H3).
    eapply eval_sound_neg; eauto.
  + apply eval_EDeref_fact in H0.
    destruct H0 as [res1 [? ?] ].
    rewrite (eval_deref_safe_cond _ _ _ H2) in H1.
    specialize (IHe _ H0 H1).
    eapply eval_sound_deref; eauto.
Qed.

(** 接下去我们考虑符号执行中所计算的最强后条件的正确性。*)

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
Admitted. (* 留作习题 *)

(** 其次证明：如果程序状态_[s2]_是自程序状态_[s1]_对变量_[x]_进行赋值后得到的新
    程序状态，那么除了与_[x]_有关的情况之外，所有的_[vars_literal]_只要在_[s1]_
    上为真就会在_[s2]_上为真。*)
Lemma vars_literal_sat_unchanged: forall J x (P: vars_literal) s1 s2,
  vars_literal_sat s1 J P ->
  (forall y, x <> y -> s1 y = s2 y) ->
  x <> P.(lit_var_name) ->
  vars_literal_sat s2 J P.
Proof.
Admitted. (* 留作习题 *)

(** 进一步，可以证明_[remove_var_lit]_是正确的。*)
Lemma remove_var_lit_sound: forall Ps x (s1 s2: var_name -> int64) J,
  Forall (vars_literal_sat s1 J) Ps ->
  (forall y, x <> y -> s1 y = s2 y) ->
  Forall (vars_literal_sat s2 J) (remove_var_lit Ps x).
Proof.
Admitted. (* 留作习题 *)

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
Admitted. (* 留作习题 *)


End SimpleSymbEvalSound.









































