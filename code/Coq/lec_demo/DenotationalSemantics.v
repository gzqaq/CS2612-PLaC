Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.

(** 这次课程中，我们将引用_[compcert.lib.Integers]_中的定义与证明。CompCert是一
    个经过Coq验证的C编译器，我们课程中要用到其中对32位整数、64位整数及其运算的定
    义以及相关性质的证明。要引用这一Coq库有两种方法。其一，在安装Coq时勾选安装
    CompCert包。其二，从课程网站下载附件，将compcert_lib文件夹放在与平时课程文件
    所在文件夹并列的位置，依次编译Coqlib.v、Zbits.v与Integers.v这三个文件，再在
    本课程之前使用的_CoqProject文件中加入一行：-R compcert.lib ../compcert_lib。*)

Require Import compcert.lib.Integers.
Require Import PL.SetsDomain.
Local Open Scope bool.
Local Open Scope string.
Local Open Scope Z.

Ltac int64_lia :=
  change Int64.min_signed with (-9223372036854775808) in *;
  change Int64.max_signed with 9223372036854775807 in *;
  lia.


(** 我们一般将描述程序行为的理论成为程序语义理论。在之前我们实现解释器的过程中，
    实际已经使用了两种程序语义理论。其一是在描述程序表达式的行为时，我们在简单解
    释器中对表达式的树结构进行递归，从而求出了其在特定程序状态下的值。其二是在描
    述程序语句行为，特别是复合语句行为时，引入了『单步』执行这一概念。今天，我们
    将介绍前者的理论基础：指称语义。*)

(** 其实我们在学习正则表达式的时候，已经接触过指称语义。我们将一个正则表达式的语
    义定义为一个字符串的集合，每一个正则表达式的语义又可以有其语法上的子表达式递
    归定义得到。*)


(** 下面我们也试图使用类似的方式定义程序表达式以及程序语句的语义。*)

(** * 表达式的指称语义 *)

(** ** 方案一 *)

(** 依据解释器的C代码实现，很容易设想，将While+DB语言的表达式语义规定为程序状态
    到整数值的映射。例如，以下考虑一种极简的程序语言。*)


Module Lang1.

(** 下面依次在Coq中定义该语言变量名、表达式与语句。*)

Definition var_name: Type := string.


Inductive expr : Type :=
  | ENum (n: Z): expr
  | EVar (x: var_name): expr
  | EPlus (e1 e2: expr): expr
  | EMinus (e1 e2: expr): expr
  | EMult (e1 e2: expr): expr.


Definition EVar': string -> expr := EVar.
Declare Custom Entry expr_entry.
Coercion ENum: Z >-> expr.
Coercion EVar: var_name >-> expr.
Coercion EVar': string >-> expr.
Notation "[[ e ]]" := e
  (at level 0, e custom expr_entry at level 99).
Notation "( x )" := x
  (in custom expr_entry, x custom expr_entry at level 99).
Notation "x" := x
  (in custom expr_entry at level 0, x constr at level 0).
Notation "x * y" := (EMult x y)
  (in custom expr_entry at level 11, left associativity).
Notation "x + y" := (EPlus x y)
  (in custom expr_entry at level 12, left associativity).
Notation "x - y" := (EMinus x y)
  (in custom expr_entry at level 12, left associativity).

Check [[1 + "x"]].
Check [["x" * ("a" + "b" + 1)]].

Inductive com : Type :=
  | CAss (x: var_name) (e: expr): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com.

(** 这一程序语言中，只有程序变量，没有内存地址相关的读写操作。因此，其程序状态可
    以简单定义为变量名到整数的映射。*)

Definition prog_state: Type := var_name -> Z.

(** 那么，程序表达式的语义可以如下定义：*)

Fixpoint eeval (e : expr) (st : prog_state) : Z :=
  match e with
  | ENum n => n
  | EVar X => st X
  | EPlus a1 a2 => (eeval a1 st) + (eeval a2 st)
  | EMinus a1 a2  => (eeval a1 st) - (eeval a2 st)
  | EMult a1 a2 => (eeval a1 st) * (eeval a2 st)
  end.

(** 再次提醒大家，这里的_[eeval]_既可以看做从表达式与程序状态到整数的二元函数，
    又可以看做从表达式到其语义的一元函数。*)


(** 当然，这个极简程序语言与我们可以实用的程序语言有着很多不同。我们研究这个极简
    语言表达式的基本性质，之后我们再研究如何把类似理论拓展到我们这门课之前使用的
    While+DB语言中去。*)

(** ** 语义等价表达式 *)

(** 在上面的语义定义基础上，我们可以定义表达式之间的语义等价关系。*)



Definition eequiv (e1 e2: expr): Prop :=
  forall s: prog_state, eeval e1 s = eeval e2 s.

Declare Scope expr_scope.
Delimit Scope expr_scope with expr.
Notation "e1 == e2" := (eequiv e1 e2)
  (at level 70, no associativity): expr_scope.
Local Open Scope expr.

(** 我们在Coq中也用_[==]_表示表达式的语义等价。*)


(** 下面是一些语义等价的简单例子：*)


Lemma EPlus_comm: forall e1 e2,
  [[e1 + e2]] == [[e2 + e1]].
Proof.
(* WORK IN CLASS *)
  intros.
  unfold eequiv.
  intros.
  simpl.
  lia.
Qed.


Lemma EPlus_0_r: forall e,
  [[e + 0]] == [[e]].
Proof.
(* WORK IN CLASS *)
  intros.
  unfold eequiv.
  intros.
  simpl.
  lia.
Qed.






(** 接下去，我们介绍语义等价的两条重要性质。其一：语义等价是一种等价关系。*)


(** 在Coq标准库中，_[Reflexive]_、_[Symmetric]_、_[Transitive]_以及
    _[Equivalence]_定义了自反性、对称性、传递性以及等价关系。下面证明中，我们统
    一使用了_[Instance]_关键字，而非之前证明中常用的_[Theorem]_与_[Lemma]_，我们
    将稍后再解释_[Instance]_关键字的特殊作用。*)

#[export] Instance eequiv_refl: Reflexive eequiv.
Proof.
(* WORK IN CLASS *)
  unfold Reflexive, eequiv.
  intros.
  reflexivity.
Qed.

#[export] Instance eequiv_sym: Symmetric eequiv.
Proof.
(* WORK IN CLASS *)
  unfold Symmetric, eequiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

#[export] Instance eequiv_trans: Transitive eequiv.
Proof.
(* WORK IN CLASS *)
  unfold Transitive, eequiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

#[export] Instance eequiv_equiv: Equivalence eequiv.
Proof.
  split.
  + apply eequiv_refl.
  + apply eequiv_sym.
  + apply eequiv_trans.
Qed.

(** 两条重要性质之二是：三种语法连接词能保持语义等价关系（congruence）。*)


(** 在Coq中，这一性质可以表示为下面_[EPlus_eequiv_congr]_性质。这条性质说的是：
    _[EPlus]_是一个二元函数（因为_[Proper]_后_[EPlus]_前的括号中有两个_[==>]_箭
    头），并且，如果对其第一个参数做_[eequiv]_变换，对其第二个参数也做_[eequiv]_
    变换，那么_[EPlus]_的运算结果也做了_[eequiv]_变换。即：加号能保持语义等价关
    系。*)

#[export] Instance EPlus_eequiv_congr:
  Proper (eequiv ==> eequiv ==> eequiv) EPlus.
Proof.
  unfold Proper, respectful.
  (** 上述指令可以将_[Proper]_这一定义展开。可以看到，定义展开后，这条性质说的就
      是：加号能保持语义等价关系。*)
  unfold eequiv.
  (* WORK IN CLASS *)
  intros.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.



(** 减号与乘号保持语义等价关系的证明是类似的。*)

#[export] Instance EMinus_eequiv_congr:
  Proper (eequiv ==> eequiv ==> eequiv) EMinus.
Proof.
(* WORK IN CLASS *)
  unfold Proper, respectful.
  unfold eequiv.
  intros.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

#[export] Instance EMult_eequiv_congr:
  Proper (eequiv ==> eequiv ==> eequiv) EMult.
Proof.
(* WORK IN CLASS *)
  unfold Proper, respectful.
  unfold eequiv.
  intros.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

(** 下面我们证明一条简单表达式变换的正确性：其变换前后表达式语义不变。*)


(** 下面是常量折叠变换（constant folding）在Coq中的定义： *)

Fixpoint CF (e: expr): expr :=
  match e with
  | ENum n => ENum n
  | EVar x => EVar x
  | EPlus e1 e2 =>
      match CF e1, CF e2 with
      | ENum n1, ENum n2 => ENum (n1 + n2)
      | _, _ => EPlus (CF e1) (CF e2)
      end
  | EMinus e1 e2 =>
      match CF e1, CF e2 with
      | ENum n1, ENum n2 => ENum (n1 - n2)
      | _, _ => EMinus (CF e1) (CF e2)
      end
  | EMult e1 e2 =>
      match CF e1, CF e2 with
      | ENum n1, ENum n2 => ENum (n1 * n2)
      | _, _ => EMult (CF e1) (CF e2)
      end
  end.

(** 我们需要证明：*)


Lemma CF_sound: forall e,
  CF(e) == e.
Proof.
  intros.
  induction e; simpl.
  + reflexivity.
  + reflexivity.
  + destruct (CF e1), (CF e2); rewrite <- IHe1, <- IHe2; try reflexivity.
    unfold eequiv; intros; simpl.
    reflexivity.
  + destruct (CF e1), (CF e2); rewrite <- IHe1, <- IHe2; try reflexivity.
    unfold eequiv; intros; simpl.
    reflexivity.
  + destruct (CF e1), (CF e2); rewrite <- IHe1, <- IHe2; try reflexivity.
    unfold eequiv; intros; simpl.
    reflexivity.
Qed.


End Lang1.

(** ** 方案二 *)

(** 然而上面方案并没有考虑我们对于while语言只处理64位有符号整数运算的约定。上述
    定义事实上假设了程序能够表达的整数范围是无限的。这并不合理。为此，我们可以对
    上面定义的指称语义稍作修改。*)


(** 在运算符的语义定义中，也应当把整数运算改为相应的64位整数运算。*)

(** 在Coq定义方面，下面我们将引用CompCert工具中对于64位整数及其运算的代码库。该
    代码库定义了_[int64]_类型以及相关算术运算（例如_[Int64.add]_）以及位运算（例
    如_[Int64.and]_），其中算术运算都表示保留运算的最后64位。*)


(** _[Int64.add]_表示64位整数的加法：*)

Check Int64.add.

(** Coq返回：_[Int64.add : int64 -> int64 -> int64]_ *)
(** _[Int64.and]_表示64位整数的按位合取：*)

Check Int64.and.

(** Coq返回：_[Int64.and : int64 -> int64 -> int64]_ *)


(** 在Coq中，用户可以用_[Search]_指令搜索已经证明过的结果。例如，使用

      _[Search Int64.add.]_

    指令可以搜索所有关于_[Int64.add]_的性质。除此之外，_[Search]_指令允许在搜索
    中对包含命题的形式做更细化的描述。例如：

      _[Search (Int64.add _ _ = Int64.add _ _).]_
*)


(** 利用类似的方法，还可以搜索64位整数上的所有二元函数。*)

Search (int64 -> int64 -> int64).

(** 除了上述表达算术运算、位运算的函数外，还有3个64位整数相关的函数十分常用，分
    别是：_[Int64.repr]_, _[Int64.signed]_, _[Int64.unsigned]_。另外，下面几个常
    数定义了有符号64位整数与无符号64位整数的大小边界：_[Int64.max_unsigned]_,
    _[Int64.max_signed]_, _[Int64.min_signed]_*)

(** 利用64位整数代码库，我们如下改进上面程序语言的语义定义。*)

Module Lang2.

Import Lang1.

(** 首先，程序状态不再是变量名到整数的映射，而是变量名到64位整数的映射。*)

Definition prog_state: Type := var_name -> int64.

(** 其次，程序表达式的值也改为64位整数：*)

Fixpoint eeval (e : expr) (st : prog_state) : int64 :=
  match e with
  | ENum n => Int64.repr n
  | EVar X => st X
  | EPlus a1 a2 => Int64.add (eeval a1 st) (eeval a2 st)
  | EMinus a1 a2  => Int64.sub (eeval a1 st) (eeval a2 st)
  | EMult a1 a2 => Int64.mul (eeval a1 st) (eeval a2 st)
  end.

End Lang2.


(** ** 方案三 *)

(** 在讲解并实现简单解释器之前，我们曾经约定while语言的算术运算语义基本遵循C标准
    的规定。特别的，有符号64位整数的运算越界应当被视为程序错误（C11标准6.5章节第
    5段落）。然而，这一点并未在上面定义中得到体现。*)

(** 为了解决这一问题，我们需要能够在定义中表达『程序表达式求值出错』这一概念。这
    在数学上有两种常见方案。其一是将求值结果由64位整数集合改为64位整数或求值失
    败。*)




(** 在Coq中可以使用_[option]_类型描述相关概念。*)


Print option.

(** 具体而言，对于任意Coq类型_[A]_，_[option A]_的元素要么是_[Some a]_（其中
    _[a]_是_[A]_的元素）要么是_[None]_。可以看到_[option]_也是一个Coq归纳类型，
    只不过其定义中并不需要对自身归纳。我们可以像处理先前其他归纳类型一样使用Coq
    中的_[match]_定义相关的函数或性质，例如：*)

Definition option_plus1 (o: option Z): option Z :=
  match o with
  | Some x => Some (x + 1)
  | None => None
  end.

(** 例如上面这一定义说的是：如果_[o]_的值是_[None]_那么就返回_[None]_，如果_[o]_
    的值是某个整数（_[Some]_的情况），那就将它加一返回。*)

(** 利用类似_[option]_类型可以改写表达式的语义定义。*)

Module Lang3.

Import Lang1 Lang2.

Fixpoint eeval (e : expr) (st : prog_state) : option int64 :=
  match e with
  | ENum n =>
      if (n <=? Int64.max_signed) && (n >=? Int64.min_signed)
      then Some (Int64.repr n)
      else None
  | EVar X => Some (st X)
  | EPlus a1 a2 =>
      match eeval a1 st, eeval a2 st with
      | Some i1, Some i2 =>
          if (Int64.signed i1 + Int64.signed i2 <=? Int64.max_signed) &&
             (Int64.signed i1 + Int64.signed i2 >=? Int64.min_signed)
          then Some (Int64.add i1 i2)
          else None
      | _, _ => None
      end
  | EMinus a1 a2  =>
      match eeval a1 st, eeval a2 st with
      | Some i1, Some i2 =>
          if (Int64.signed i1 - Int64.signed i2 <=? Int64.max_signed) &&
             (Int64.signed i1 - Int64.signed i2 >=? Int64.min_signed)
          then Some (Int64.sub i1 i2)
          else None
      | _, _ => None
      end
  | EMult a1 a2 =>
      match eeval a1 st, eeval a2 st with
      | Some i1, Some i2 =>
          if (Int64.signed i1 * Int64.signed i2 <=? Int64.max_signed) &&
             (Int64.signed i1 * Int64.signed i2 >=? Int64.min_signed)
          then Some (Int64.mul i1 i2)
          else None
      | _, _ => None
      end
  end.

(** 上述定义中除了用到Coq的_[option]_类型，还用到了Coq的_[bool]_类型。*)

Print bool.

(** 根据定义_[bool]_类型只有两种可能的取值：_[true]_与_[false]_。请注意，Coq中的
    _[bool]_类型与命题（_[Prop]_类型）并不相同，前者专门用于关于真与假的真值运
    算，而后者则可以描述关于任意、存在等真假难以判定、无法计算真值的命题。上面的
    _[eeval]_定义要用于计算出_[option int64]_类型的结果，因此就只能使用_[bool]_
    类型的Coq函数来做判定了，他们分别是_[<=?]_, _[>=?]_与_[&&]_。*)

Check 1 <=? 2.
Check 1 <= 2.

(** 可以看到，_[1 <=? 2]_是用_[bool]_类型表达的判断两数大小的结果，这一符号对应
    的定义是：_[Z.leb 1 2]_。而_[1 <= 2]_则是关于两数大小关系的命题，这一符号对
    应的定义是：_[Z.le 1 2]_。Coq标准库中也证明了两者的联系。*)

Check Z.leb_le.

(** 这个定理说的是：_[forall n m : Z, (n <=? m) = true <-> n <= m]_。当然，Coq标
    准库中还有很多类似的有用的性质，这里就不再一一罗列了，相关信息也可以通过
    _[Search Z.leb]_或_[Search Z.le]_等方法查找。*)

(** 最后，在Coq中，可以用_[&&]_表示布尔值的合取（Coq定义是_[andb]_）并且使用
    _[if]_，_[then]_，_[else]_针对布尔表达式求值为真以及为假的情况分别采取不同的
    求值方法。将这些定义组合在一起，就得到了上面的_[eeval]_定义。*)

(** 我们可以在Coq中证明一些关于表达式指称语义的基本性质。*)

Example eeval_fact0: forall st,
  st "x" = Int64.repr 0 ->
  eeval [["x" + 1]] st = Some (Int64.repr 1).
Proof.
  intros.
  simpl.
  rewrite H.
  rewrite ! Int64.signed_repr by int64_lia.
  assert (0 + 1 <= Int64.max_signed).
  {
    int64_lia.
  }
  assert (Int64.min_signed <= 0 + 1) by int64_lia.
  apply Z.leb_le in H0.
  apply Z.geb_le in H1.
  rewrite H0, H1.
  simpl.
  rewrite Int64.add_signed.
  reflexivity.
Qed.

End Lang3.

(** 上面定义中有三个分支的定义是相似，我们也可以统一定义。*)

Module Lang3H1.

Import Lang1 Lang2.

(** 这里，_[Zfun: Z -> Z -> Z]_可以看做对整数加法（_[Z.add]_)、整数减法
    （_[Z.sub]_）与整数乘法（_[Z.mul]_）的抽象。而
     _[i64fun: int64 -> int64 -> int64]_可以看做对64位整数二元运算的抽象。*)


Definition arith_denote
             (Zfun: Z -> Z -> Z)
             (int64fun: int64 -> int64 -> int64)
             (o1 o2: option int64): option int64 :=
  match o1, o2 with
  | Some i1, Some i2 =>
      if (Zfun (Int64.signed i1) (Int64.signed i2)
                               <=? Int64.max_signed) &&
         (Zfun (Int64.signed i1) (Int64.signed i2)
                               >=? Int64.min_signed)
      then Some (int64fun i1 i2)
      else None
  | _, _ => None
  end.

(** 例如，下面将_[Zfun]_取_[Z.add]_、_[int64fun]_取_[Int64.add]_代入：*)

Example arith_denote_add_fact: forall o1 o2,
  arith_denote Z.add Int64.add o1 o2 =
  match o1, o2 with
  | Some i1, Some i2 =>
      if (Int64.signed i1 + Int64.signed i2
                               <=? Int64.max_signed) &&
         (Int64.signed i1 + Int64.signed i2
                               >=? Int64.min_signed)
      then Some (Int64.add i1 i2)
      else None
  | _, _ => None
  end.
Proof. intros. reflexivity. Qed.

(** 这样，_[eeval]_的定义就可以简化为：*)

Fixpoint eeval (e : expr) (st : prog_state) : option int64 :=
  match e with
  | ENum n =>
      if (n <=? Int64.max_signed) && (n >=? Int64.min_signed)
      then Some (Int64.repr n)
      else None
  | EVar X =>
      Some (st X)
  | EPlus a1 a2 =>
      arith_denote
        Z.add Int64.add (eeval a1 st) (eeval a2 st)
  | EMinus a1 a2 =>
      arith_denote
        Z.sub Int64.sub (eeval a1 st) (eeval a2 st)
  | EMult a1 a2 =>
      arith_denote
        Z.mul Int64.mul (eeval a1 st) (eeval a2 st)
  end.

End Lang3H1.

(** 当然，我们也可以像定义正则表达式语义时直接定义集合运算那样，直接定义函数之间
    的运算，并基于此定义表达式的语义。*)

Module Lang3H2.

Import Lang1 Lang2.

(** 首先定义常量与变量的情况：*)

Definition const_denote
           (n: Z)
           (s: prog_state): option int64 :=
  if (n <=? Int64.max_signed) && (n >=? Int64.min_signed)
  then Some (Int64.repr n)
  else None.

Definition var_denote
           (X: var_name)
           (s: prog_state): option int64 :=
  Some (s X).

(** 再次提醒大家注意，这里_[const_denote]_既可以被看做一个由整数_[n]_和程序状态
    _[s]_计算64位整数（或运算错误）的二元函数，也可以看错从整数_[n]_到表达式语义
    的一元函数。类似的，_[var_denote]_也可以看做程序变量名到表达式语义的一元函
    数。*)

(** 下面定义则规定：_[arith_denote Zfun int64fun]_是一个从表达式语义到表达式语义
    的二元函数。*)

Definition arith_denote
             (Zfun: Z -> Z -> Z)
             (int64fun: int64 -> int64 -> int64)
             (D1 D2: prog_state -> option int64)
             (s: prog_state): option int64 :=
  match D1 s, D2 s with
  | Some i1, Some i2 =>
      if (Zfun (Int64.signed i1) (Int64.signed i2)
                               <=? Int64.max_signed) &&
         (Zfun (Int64.signed i1) (Int64.signed i2)
                               >=? Int64.min_signed)
      then Some (int64fun i1 i2)
      else None
  | _, _ => None
  end.

(** 基于上述定义，_[eeval]_可重新如下定义：*)

Fixpoint eeval (e : expr) : prog_state -> option int64 :=
  match e with
  | ENum n =>
      const_denote n
  | EVar X =>
      var_denote X
  | EPlus a1 a2 =>
      arith_denote Z.add Int64.add (eeval a1) (eeval a2)
  | EMinus a1 a2 =>
      arith_denote Z.sub Int64.sub (eeval a1) (eeval a2)
  | EMult a1 a2 =>
      arith_denote Z.mul Int64.mul (eeval a1) (eeval a2)
  end.

End Lang3H2.

(** ** Coq高阶函数（更多例子） *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

(** 这里，_[f]_这个参数本身也是一个函数（从_[X]_到_[X]_的函数）而_[doit3times]_
    则把_[f]_在_[n]_上作用了3次。*)

Definition minustwo (x: Z): Z := x - 2.

Example fact_doit3times_1:
  doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.
Example fact_doit3times_2:
  doit3times minustwo (doit3times minustwo 9) = -3.
Proof. reflexivity. Qed.
Example fact_doit3times_3:
  doit3times (doit3times minustwo) 9 = -9.
Proof. reflexivity. Qed.
Example fact_doit3times_4:
  doit3times doit3times minustwo 9 = -45.
Proof. reflexivity. Qed.

(** Coq中允许用户使用_[fun]_关键字表示匿名函数，例如：*)

Example fact_doit3times_anon1:
  doit3times (fun x => x - 2) 9 = 3.
Proof. reflexivity. Qed.

Example fact_doit3times_anon2:
  doit3times (fun x => x * x) 2 = 256.
Proof. reflexivity. Qed.

(** 这里_[fun x => x - 2]_与之前定义的_[minustwo]_是相同的，而_[fun x => x * x]_
    则表示了平方这样一个函数。*)

Example fact_doit3times_anon3:
  doit3times (fun x => - x) 5 = -5.
Proof. reflexivity. Qed.
Example fact_doit3times_anon4:
  doit3times (fun f x y => f y x) (fun x y => x - y) 1 2 = 1.
Proof. reflexivity. Qed.
Definition Func_add {A: Type}: (A -> Z) -> (A -> Z) -> (A -> Z) :=
  fun f g x => f x + g x.

Example fact_doit3times_anon5: forall x,
  doit3times (Func_add minustwo) (fun x => x * x) x = x * x + x * 3 - 6.
Proof. intros. unfold doit3times, Func_add, minustwo. lia. Qed.
Example fact_doit3times_anon6:
  doit3times ((fun x y => y * y - x * y + x * x) 1) 1 = 1.
Proof. reflexivity. Qed.






























(** ** 方案四 *)

(** 上面我们讨论了将表达式语义定义为程序状态到_[option int64]_的函数这一方案。下
    面我们探讨另一种描述程序运行出错或未定义行为的方案，即将表达式的语义定义为程
    序状态与_[int64]_之间的二元关系。*)


Module Lang4.

Import Lang1 Lang2.

(** 在Coq中，程序状态与64位整数之间的二元关系可以用下面类型描述：
    _[prog_state -> int64 -> Prop]_。*)

(** 首先定义常量与变量的情况：*)

Definition const_denote
           (z: Z)
           (s: prog_state)
           (n: int64): Prop :=
  n = Int64.repr z /\
  z <= Int64.max_signed /\
  z >= Int64.min_signed.

Definition var_denote
           (X: var_name)
           (s: prog_state)
           (n: int64) :=
  n = s X.

(** 下面定义规定：_[arith_denote Zfun int64fun]_是一个从表达式语义到表达式语义的
    二元函数。*)

Definition arith_denote
             (Zfun: Z -> Z -> Z)
             (int64fun: int64 -> int64 -> int64)
             (D1 D2: prog_state -> int64 -> Prop)
             (s: prog_state)
             (n: int64): Prop :=
  exists n1 n2,
    D1 s n1 /\ D2 s n2 /\
    n = int64fun n1 n2 /\
    Zfun (Int64.signed n1) (Int64.signed n2)
      <= Int64.max_signed /\
    Zfun (Int64.signed n1) (Int64.signed n2)
      >= Int64.min_signed.

(** 据此，_[eeval]_可重新如下定义：*)

Fixpoint eeval (e : expr) : prog_state -> int64 -> Prop :=
  match e with
  | ENum n =>
      const_denote n
  | EVar X =>
      var_denote X
  | EPlus a1 a2 =>
      arith_denote Z.add Int64.add (eeval a1) (eeval a2)
  | EMinus a1 a2 =>
      arith_denote Z.sub Int64.sub (eeval a1) (eeval a2)
  | EMult a1 a2 =>
      arith_denote Z.mul Int64.mul (eeval a1) (eeval a2)
  end.





End Lang4.



(** ** 方案五 *)

(** 到目前为止，我们考虑了极简的只包含加减乘算术运算的表达式的指称语义。其实，基
    于上面的方案，我们很容易就可以定义大小比较、布尔运算以及地址取值的语义。*)



Module WhileD_Expr.

Definition var_name: Type := string.

(** 再定义二元运算符和一元运算符。*)

Inductive binop : Type :=
  | OOr | OAnd
  | OLt | OLe | OGt | OGe | OEq | ONe
  | OPlus | OMinus | OMul | ODiv | OMod.

Inductive unop : Type :=
  | ONot | ONeg.

(** 下面是表达式的抽象语法树。*)

Inductive expr : Type :=
  | ENum (n: Z): expr
  | EVar (x: var_name): expr
  | EBinop (op: binop) (e1 e2: expr): expr
  | EUnop (op: unop) (e: expr): expr
  | EDeref (e: expr): expr.

(** 下面定义程序状态。在C程序中，每个变量也有其地址，程序中可以用取地址操作获取
    变量的地址。然而，在While+DB语言中，没有取地址操作，我们不妨将程序状态定义为
    这样的二元组：变量的值与地址上的值。这在Coq中可以用_[Record]_来定义。*)

Record prog_state: Type := {
  vars: var_name -> int64;
  mem: int64 -> option int64;
}.

(** 值得一提的是，几乎在一切程序语言中，都不能保证任选一个地址进行读写的安全性。
    因此，我们也在程序状态中规定，一些地址有读写权限（对应_[Some]_），一些地址没
    有读写权限（对应_[None]_）。

    Coq中_[Record]_定义的类型可以这样使用：*)

Example record_ex: forall V M st,
  st = {| vars := V; mem := M; |} ->
  st.(vars) = V /\ st.(mem) = M.
Proof.
  intros.
  rewrite H.
  simpl.
  split; reflexivity.
Qed.

(** 我们可以看到，要用_[Record]_的各个域合并得到整体，可以用带竖线的大括号。要从
    _[Record]_的整体得到它的一个域，应当在点号后写圆括号与域名。*)

(** 下面定义指称语义。常量的语义定义与原先相同。*)

Definition const_denote
           (z: Z)
           (s: prog_state)
           (n: int64): Prop :=
  n = Int64.repr z /\
  z <= Int64.max_signed /\
  z >= Int64.min_signed.

(** 变量的语义定义应当用程序状态中变量的部分定义。*)

Definition var_denote
           (X: var_name)
           (s: prog_state)
           (n: int64) :=
  n = s.(vars) X.

(** 加减乘的语义定义与原先定义相同。*)

Definition arith_denote1
             (Zfun: Z -> Z -> Z)
             (int64fun: int64 -> int64 -> int64)
             (D1 D2: prog_state -> int64 -> Prop)
             (s: prog_state)
             (n: int64): Prop :=
  exists n1 n2,
    D1 s n1 /\ D2 s n2 /\
    n = int64fun n1 n2 /\
    Zfun (Int64.signed n1) (Int64.signed n2)
      <= Int64.max_signed /\
    Zfun (Int64.signed n1) (Int64.signed n2)
      >= Int64.min_signed.

(** 下面是除法和取余的定义。根据C标准（C11标准6.5.5章节第6段落），只有除法运算结
    果不越界的情况下，才能安全计算余数。*)

Definition arith_denote2
             (int64fun: int64 -> int64 -> int64)
             (D1 D2: prog_state -> int64 -> Prop)
             (s: prog_state)
             (n: int64): Prop :=
  exists n1 n2,
    D1 s n1 /\ D2 s n2 /\
    n = int64fun n1 n2 /\
    Int64.signed n2 <> 0 /\
    (Int64.signed n1 <> Int64.min_signed \/
     Int64.signed n2 <> - 1).

(** 下面是整数大小比较的定义，其中将直接使用CompCert中现有的定义。这里，
    _[comparison]_是CompCert中定义六种大小比较运算，_[Int64.cmp]_则定义了大小的
    结果（结果类型为_[bool]_）。*)

Print comparison.

Check Int64.cmp.

Definition cmp_denote
             (c: comparison)
             (D1 D2: prog_state -> int64 -> Prop)
             (s: prog_state)
             (n: int64): Prop :=
  exists n1 n2,
    D1 s n1 /\ D2 s n2 /\
    n = if Int64.cmp c n1 n2 then Int64.repr 1 else Int64.repr 0.

(** 下面是二元布尔运算的语义，请特别注意表述其中的短路求值行为。*)

Definition and_denote
             (D1 D2: prog_state -> int64 -> Prop)
             (s: prog_state)
             (n: int64): Prop :=
  (D1 s (Int64.repr 0) /\ n = Int64.repr 0) \/
  (exists n1,
     D1 s n1 /\
     D2 s (Int64.repr 0) /\
     Int64.signed n1 <> 0 /\
     n = Int64.repr 0) \/
  (exists n1 n2,
     D1 s n1 /\ D2 s n2 /\
     Int64.signed n1 <> 0 /\
     Int64.signed n2 <> 0 /\
     n = Int64.repr 1).

Definition or_denote
             (D1 D2: prog_state -> int64 -> Prop)
             (s: prog_state)
             (n: int64): Prop :=
  (exists n1,
     D1 s n1 /\
     Int64.signed n1 <> 0 /\
     n = Int64.repr 1) \/
  (exists n2,
     D1 s (Int64.repr 0) /\
     D2 s n2 /\
     Int64.signed n2 <> 0 /\
     n = Int64.repr 1) \/
  (D1 s (Int64.repr 0) /\
   D2 s (Int64.repr 0) /\
   n = Int64.repr 0).

(** 最终我们可以将所有二元运算的语义汇总起来：*)

Definition binop_denote
             (op: binop)
             (D1 D2: prog_state -> int64 -> Prop):
  prog_state -> int64 -> Prop :=
  match op with
  | OOr => or_denote D1 D2
  | OAnd => and_denote D1 D2
  | OLt => cmp_denote Clt D1 D2
  | OLe => cmp_denote Cle D1 D2
  | OGt => cmp_denote Cgt D1 D2
  | OGe => cmp_denote Cge D1 D2
  | OEq => cmp_denote Ceq D1 D2
  | ONe => cmp_denote Cne D1 D2
  | OPlus => arith_denote1 Z.add Int64.add D1 D2
  | OMinus => arith_denote1 Z.sub Int64.sub D1 D2
  | OMul => arith_denote1 Z.mul Int64.mul D1 D2
  | ODiv => arith_denote2 Int64.divs D1 D2
  | OMod => arith_denote2 Int64.mods D1 D2
  end.

(** 下面定义一元运算的语义。*)

Definition neg_denote
             (D: prog_state -> int64 -> Prop)
             (s: prog_state)
             (n: int64): Prop :=
  exists n0,
    D s n0 /\
    n = Int64.neg n0 /\
    Int64.signed n0 <> Int64.min_signed.

Definition not_denote
             (D: prog_state -> int64 -> Prop)
             (s: prog_state)
             (n: int64): Prop :=
  (exists n0,
     D s n0 /\
     Int64.signed n0 <> 0 /\
     n = Int64.repr 0) \/
  (D s (Int64.repr 0) /\ n = Int64.repr 1).

Definition unop_denote
             (op: unop)
             (D: prog_state -> int64 -> Prop):
  prog_state -> int64 -> Prop :=
  match op with
  | ONeg => neg_denote D
  | ONot => not_denote D
  end.

(** 最后定义地址取值的语义：*)

Definition deref_denote
             (D: prog_state -> int64 -> Prop)
             (s: prog_state)
             (n: int64): Prop :=
  exists p, D s p /\ s.(mem) p = Some n.

(** 最终，我们可以定义所有表达式的指称语义：*)

Fixpoint eeval (e : expr): prog_state -> int64 -> Prop :=
  match e with
  | ENum n => const_denote n
  | EVar X => var_denote X
  | EBinop op e1 e2 => binop_denote op (eeval e1) (eeval e2)
  | EUnop op e0 => unop_denote op (eeval e0)
  | EDeref e0 => deref_denote (eeval e0)
  end.

End WhileD_Expr.


(** * 程序语句的指称语义 *)



Module Lang5.

Import WhileD_Expr.

(** 下面程序语句语法树的定义只考虑了赋值语句、顺序执行与条件分支语句。*)

Inductive com : Type :=
  | CAss (e1 e2: expr): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com.

(** 先定义对变量进行赋值的程序语义。*)

Definition asgn_var_denote
             (X: var_name)
             (D: prog_state -> int64 -> Prop)
             (st1 st2: prog_state): Prop :=
  exists n,
    D st1 n /\
    st2.(vars) X = n /\
    (forall Y, X <> Y -> st1.(vars) Y = st2.(vars) Y) /\
    (forall p, st1.(mem) p = st2.(mem) p).

(** 再定义对地址上存储的值进行赋值的程序语义。*)

Definition asgn_deref_denote
             (D1 D2: prog_state -> int64 -> Prop)
             (st1 st2: prog_state): Prop :=
  exists p n,
    D1 st1 p /\
    D2 st1 n /\
    st1.(mem) p <> None /\
    st2.(mem) p = Some n /\
    (forall X, st1.(vars) X = st2.(vars) X) /\
    (forall q, p <> q -> st1.(mem) q = st2.(mem) q).

(** 上述两条定义在程序语句语义的整体定义中是这样使用的（此处先不填入顺序执行语句
    与条件分支语句的语义，相应位置用_[TO_BE_FILLED_LATER]_表示）。*)

Definition TO_BE_FILLED_LATER: prog_state -> prog_state -> Prop :=
  fun _ _ => False.

Definition ceval_demo (c: com): prog_state -> prog_state -> Prop :=
  match c with
  | CAss e1 e2 =>
    match e1 with
    | EVar X => asgn_var_denote X (eeval e2)
    | EDeref e0 => asgn_deref_denote (eeval e0) (eeval e2)
    | _ => fun _ _ => False
    end
  | _ => TO_BE_FILLED_LATER
  end.

End Lang5.

(** ** 二元关系的运算 *)

(** 再要进一步定义程序语句的指称语义，就要定义复合语句的指称语义。即，要用子程序
    与子语句的语义定义整体程序与整体语句的语义。为此，我们先回顾一下关于二元关系
    的重要概念。*)

Module BinRel.

(** 相等关系（identity relation）： *)

Definition id {A: Type}: A -> A -> Prop := fun a b => a = b.

(** 二元关系的连接： *)

Definition concat
             {A B C: Type}
             (r1: A -> B -> Prop)
             (r2: B -> C -> Prop): A -> C -> Prop :=
  fun a c => exists b, r1 a b /\ r2 b c.

(** 二元关系与一元关系的连接： *)

Definition dia {A B: Type} (X: A -> B -> Prop) (Y: B -> Prop): A -> Prop :=
  fun a => exists b, X a b /\ Y b.

End BinRel.

Notation "X ∘ Y" := (BinRel.concat X Y)
  (right associativity, at level 60): sets_scope.
Local Open Scope sets_scope.

(** 下面，我们可以证明他们的一些基本性质。引理_[BinRel_concat_assoc]_是二元关系
    连接运算的结合律。 *)

Lemma BinRel_concat_assoc:
  forall
    {A B C D}
    (R1: A -> B -> Prop)
    (R2: B -> C -> Prop)
    (R3: C -> D -> Prop),
  R1 ∘ (R2 ∘ R3) == (R1 ∘ R2) ∘ R3.
Proof.
(* WORK IN CLASS *)
  intros.
  unfold BinRel.concat.
  sets_unfold.
  intros a d.
  split; intros.
  + destruct H as [b [? [c [? ?] ] ] ].
    exists c.
    split.
    - exists b.
      tauto.
    - tauto.
  + destruct H as [c [ [b [? ?] ] ] ?].
    exists b.
    split.
    - tauto.
    - exists c.
      tauto.
Qed.

(** 下面两条性质证明了_[BinRel.id]_是二元关系连接运算的单位元。*)

Lemma BinRel_concat_id_l:
  forall {A B} (R: A -> B -> Prop),
    BinRel.id ∘ R == R.
Proof.
Admitted. (* 留作习题 *)

Lemma BinRel_concat_id_r:
  forall {A B} (R: A -> B -> Prop),
    R ∘ BinRel.id == R.
Proof.
Admitted. (* 留作习题 *)

(** 下面两条性质证明了空集是二元关系连接运算的零元。请注意：在数学中，只要一个集
    合中不包含任何元素，那么这个集合就是空集。然而，在Coq中，任何一个数学对象都
    应当有类型。因此，下面定理中，我们用_[∅: A -> B -> Prop]_以及
    _[∅: B -> C -> Prop]_表示在考虑_[A]_到_[B]_的二元关系时以及在考虑_[B]_到
    _[C]_的二元关系时的空集。*)

Lemma BinRel_concat_empty_l:
  forall {A B C} (R: B -> C -> Prop),
    (∅: A -> B -> Prop) ∘ R == ∅.
Proof.
Admitted. (* 留作习题 *)

Lemma BinRel_concat_empty_r:
  forall {A B C} (R: A -> B -> Prop),
    R ∘ (∅: B -> C -> Prop) == ∅.
Proof.
Admitted. (* 留作习题 *)

(** 下面四条性质是二元关系连接运算对并集运算的分配律。*)

Lemma BinRel_concat_union_distr_r:
  forall
    {A B C}
    (R1 R2: A -> B -> Prop)
    (R3: B -> C -> Prop),
  (R1 ∪ R2) ∘ R3 == (R1 ∘ R3) ∪ (R2 ∘ R3).
Proof.
Admitted. (* 留作习题 *)

Lemma BinRel_concat_union_distr_l:
  forall
    {A B C}
    (R1: A -> B -> Prop)
    (R2 R3: B -> C -> Prop),
  R1 ∘ (R2 ∪ R3) == (R1 ∘ R2) ∪ (R1 ∘ R3).
Proof.
Admitted. (* 留作习题 *)

Lemma BinRel_concat_omega_union_distr_r:
  forall
    {A B C}
    (R1: nat -> A -> B -> Prop)
    (R2: B -> C -> Prop),
  (⋃ R1) ∘ R2 == ⋃ (fun n => R1 n ∘ R2).
Proof.
Admitted. (* 留作习题 *)

Lemma BinRel_concat_omega_union_distr_l:
  forall
    {A B C}
    (R1: A -> B -> Prop)
    (R2: nat -> B -> C -> Prop),
  R1 ∘ (⋃ R2) == ⋃ (fun n => R1 ∘ R2 n).
Proof.
Admitted. (* 留作习题 *)



(** 下面依托上述二元关系间的运算，在Coq中定义顺序执行语句与条件分支语句的行为。*)

Module Lang6.

Import WhileD_Expr Lang5.

Definition seq_denote
             (D1 D2: prog_state -> prog_state -> Prop):
  prog_state -> prog_state -> Prop :=
  D1 ∘ D2.

Definition test0
             (D: prog_state -> int64 -> Prop)
             (st1 st2: prog_state): Prop :=
  st1 = st2 /\ D st1 (Int64.repr 0).

Definition test1
             (D: prog_state -> int64 -> Prop)
             (st1 st2: prog_state): Prop :=
  exists n, st1 = st2 /\ D st1 n /\ Int64.unsigned n <> 0.

Definition if_denote
             (D0: prog_state -> int64 -> Prop)
             (D1 D2: prog_state -> prog_state -> Prop):
  prog_state -> prog_state -> Prop :=
  (test1(D0) ∘ D1) ∪ (test0(D0) ∘ D2).

(** 这样，我们就可以定义只包含赋值语句、顺序执行语句与条件分支语句程序语言的指称
    语义。*)

Fixpoint ceval (c: com): prog_state -> prog_state -> Prop :=
  match c with
  | CAss e1 e2 =>
    match e1 with
    | EVar X => asgn_var_denote X (eeval e2)
    | EDeref e0 => asgn_deref_denote (eeval e0) (eeval e2)
    | _ => fun _ _ => False
    end
  | CSeq c1 c2 => seq_denote (ceval c1) (ceval c2)
  | CIf e c1 c2 => if_denote (eeval e) (ceval c1) (ceval c2)
  end.


(** ** 语义等价 *)



Definition cequiv (c1 c2: com): Prop :=
  ceval c1 == ceval c2.

Declare Scope com_scope.
Delimit Scope com_scope with com.
Notation "c1 == c2" := (cequiv c1 c2)
  (at level 70, no associativity): com_scope.

(** 下面我们可以证明一些简单的语义等价的例子。*)


Theorem CSeq_assoc: forall c1 c2 c3,
  (CSeq c1 (CSeq c2 c3) == CSeq (CSeq c1 c2) c3)%com.
Proof.
  intros.
  unfold cequiv; simpl; unfold seq_denote.
  apply BinRel_concat_assoc.
Qed.


Theorem CIf_CSeq: forall e c1 c2 c3,
  (CSeq (CIf e c1 c2) c3 == CIf e (CSeq c1 c3) (CSeq c2 c3))%com.
Proof.
  intros.
  unfold cequiv; simpl; unfold if_denote, seq_denote.
  rewrite !BinRel_concat_assoc.
  apply BinRel_concat_union_distr_r.
Qed.

End Lang6.




















(** ** Coq中证明并应用Bourbaki-Witt不动点定理 *)

(** 下面我们将在Coq中证明Bourbaki-Witt不动点定理。在Bourbaki-Witt不动点定理中，
    我们需要证明满足某些特定条件（例如偏序、完备偏序等）的二元关系的一些性质。在
    Coq中，我们当然可以通过_[R: A -> A -> Prop]_来探讨二元关系_[R]_的性质。然而
    Coq中并不能给这样的变量设定Notation符号，例如，我们希望用_[a <= b]_来表示
    _[R a b]_，因此我们选择使用Coq的_[Class]_来帮助我们完成定义。*)

(** 下面这一定义说的是：_[Order]_是一类数学对象，任给一个类型_[A]_，_[Order A]_
    也是一个类型，这个类型的每个元素都有一个域，这个域的名称是_[order_rel]_，它
    的类型是_[A -> A -> Prop]_，即_[A]_上的二元关系。*)

Class Order (A: Type): Type :=
  order_rel: A -> A -> Prop.

(** Coq中_[Class]_与_[Record]_有些像，但是有两点区别。第一：_[Class]_如果只有一
    个域，它的中可以不使用大括号将这个域的定义围起来；第二：在定义或证明中，Coq
    系统会试图自动搜索并填充类型为_[Class]_的参数，搜索范围为之前注册过可以使用
    的_[Instance]_以及当前环境中的参数。例如，我们先前在证明等价关系、congruence
    性质时就使用过_[Instance]_。例如，下面例子中，不需要指明_[order_rel]_是哪个
    _[Order A]_的_[order_rel]_域，Coq会自动默认这是指_[RA]_的_[order_rel]_域。*)

Check forall {A: Type} {RA: Order A} (x: A),
        exists (y: A), order_rel x y.

(** 这样，我们就可以为_[order_rel]_定义Notation符号。*)

Declare Scope order_scope.
Notation "a <= b" := (order_rel a b): order_scope.
Local Open Scope order_scope.

Check forall {A: Type} {RA: Order A} (x y: A),
        x <= y \/ y <= x.

(** 基于序关系，我们就可以定义上界与下界的概念。由于Bourbaki-Witt不动点定理中主
    要需要探讨无穷长元素序列的上界与上确界，下面既定义了元素集合的上下界也定义了
    元素序列的上下界。*)


Definition is_lb
             {A: Type} {RA: Order A}
             (X: A -> Prop) (a: A): Prop :=
  forall a', X a' -> a <= a'.

Definition is_ub
             {A: Type} {RA: Order A}
             (X: A -> Prop) (a: A): Prop :=
  forall a', X a' -> a' <= a.

Definition is_omega_lb
             {A: Type} {RA: Order A}
             (l: nat -> A) (a: A): Prop :=
  forall n, a <= l n.

Definition is_omega_ub
             {A: Type} {RA: Order A}
             (l: nat -> A) (a: A): Prop :=
  forall n, l n <= a.

(** 下面定义序列的上确界，所谓上确界就是上界中最小的一个，因此它的定义包含两个子
    句。而在后续证明中，使用上确界性质的时候，有时需要用其第一条性质，有时需要用
    其第二条性质。为了后续证明的方便，这里在定义之外提供了使用这两条性质的方法：
    _[is_omega_lub_sound]_与_[is_omega_lub_tight]_。比起在证明中使用_[destruct]_
    指令拆解上确界的定义，使用这两条引理，可以使得Coq证明更自然地表达我们的证明
    思路。之后我们将在证明偏序集上上确界唯一性的时候会看到相关的用法。*)


Definition is_omega_lub
             {A: Type} {RA: Order A}
             (l: nat -> A) (a: A): Prop :=
  is_omega_ub l a /\ is_lb (is_omega_ub l) a.

Lemma is_omega_lub_sound:
  forall {A: Type} {RA: Order A} {l: nat -> A} {a: A},
    is_omega_lub l a -> is_omega_ub l a.
Proof. unfold is_omega_lub; intros; tauto. Qed.

Lemma is_omega_lub_tight:
  forall {A: Type} {RA: Order A} {l: nat -> A} {a: A},
    is_omega_lub l a -> is_lb (is_omega_ub l) a.
Proof. unfold is_omega_lub; intros; tauto. Qed.

(** 在编写Coq定义时，另有一个问题需要专门考虑，有些数学上的相等关系在Coq中只是一
    种等价关系。例如，我们之前在Coq中用过集合相等的定义。因此，我们描述
    Bourbaki-Witt不动点定理的前提条件时，也需要假设有一个与序关系相关的等价关
    系，我们用_[Equiv]_表示，并用_[==]_这个符号描述这个等价关系。*)


Class Equiv (A: Type): Type :=
  equiv: A -> A -> Prop.

Notation "a == b" := (equiv a b): order_scope.

(** 基于此，我们可以定义基于等价关系的自反性与反对称性。注意，传递性的定义与这个
    等价关系无关。这里我们也用_[Class]_定义，这与Coq标准库中的自反、对称、传递的
    定义是类似的，但是也有不同：(1) 我们的定义需要探讨一个二元关系与一个等价关系
    之间的联系，而Coq标准库中只考虑了这个等价关系是普通等号的情况；(2) Coq标准库
    中直接使用二元关系_[R: A -> A -> Prop]_作为参数，而我们的参数使用了_[Order]_
    与_[Equiv]_这两个_[Class]_。 *)

(** 自反性： *)
Class Reflexive_Setoid
        (A: Type) {RA: Order A} {EA: Equiv A}: Prop :=
  reflexivity_setoid:
    forall a b, a == b -> a <= b.

(** 反对称性： *)
Class AntiSymmetric_Setoid
        (A: Type) {RA: Order A} {EA: Equiv A}: Prop :=
  antisymmetricity_setoid:
    forall a b, a <= b -> b <= a -> a == b.

(** 现在，我们就可以如下定义偏序关系。*)


Class PartialOrder_Setoid
        (A: Type) {RA: Order A} {EA: Equiv A}: Prop :=
{
  PO_Reflexive_Setoid:> Reflexive_Setoid A;
  PO_Transitive:> Transitive order_rel;
  PO_AntiSymmetric_Setoid:> AntiSymmetric_Setoid A
}.

(** 下面证明两条偏序集的基本性质。在Coq中，我们使用前引号_[`]_让Coq自动填充
    _[Class]_类型元素的参数。例如，_[`{POA: PartialOrder_Setoid A}]_会指引Coq
    额外填上_[RA: Order A]_和_[EA: Equiv A]_。*)


(** 序关系两侧做等价变换不改变序关系：*)

#[export] Instance PartialOrder_Setoid_Proper
           {A: Type} `{POA: PartialOrder_Setoid A} {EquivA: Equivalence equiv}:
  Proper (equiv ==> equiv ==> iff) order_rel.
Proof.
  unfold Proper, respectful.
  intros.
  split; intros.
  + transitivity x0; [| apply reflexivity_setoid; tauto].
    transitivity x; [apply reflexivity_setoid; symmetry; tauto |].
    tauto.
  + transitivity y0; [| apply reflexivity_setoid; symmetry; tauto].
    transitivity y; [apply reflexivity_setoid; tauto |].
    tauto.
Qed.

(** 如果两个序列的所有上界都相同，那么他们的上确界也相同（如果有的话）：*)

Lemma same_omega_ub_same_omega_lub:
  forall
    {A: Type}
    `{POA: PartialOrder_Setoid A}
    (l1 l2: nat -> A)
    (a1 a2: A),
  (is_omega_ub l1 == is_omega_ub l2)%sets ->
  is_omega_lub l1 a1 ->
  is_omega_lub l2 a2 ->
  a1 == a2.
Proof.
  intros A ? ? POA.
  sets_unfold.
  intros.
  apply antisymmetricity_setoid.
  + apply (is_omega_lub_tight H0).
    apply H.
    apply (is_omega_lub_sound H1).
  + apply (is_omega_lub_tight H1).
    apply H.
    apply (is_omega_lub_sound H0).
Qed.

(** 证明Bourbaki-Witt不动点定理时还需要定义完备偏序集，由于在其证明中实际只用到
    了完备偏序集有最小元和任意单调不减的元素序列有上确界，我们在Coq定义时也只考
    虑符合这两个条件的偏序集，我们称为OmegaCPO，Omega表示可数无穷多项的意思。另
    外，尽管数学上仅仅要求完备偏序集上的所有链有上确界，但是为了Coq证明的方便，
    我们将_[omega_lub]_定义为所有元素序列的上确界计算函数，只不过我们仅仅要求该
    函数在其参数为单调不减序列时能确实计算出上确界，见_[oCPO_completeness]_。*)


Class OmegaLub (A: Type): Type :=
  omega_lub: (nat -> A) -> A.

Class Bot (A: Type): Type :=
  bot: A.


Definition increasing
             {A: Type} {RA: Order A} (l: nat -> A): Prop :=
  forall n, l n <= l (S n).

Definition is_least {A: Type} {RA: Order A} (a: A): Prop :=
  forall a', a <= a'.

Class OmegaCompletePartialOrder_Setoid
        (A: Type)
        {RA: Order A} {EA: Equiv A}
        {oLubA: OmegaLub A} {BotA: Bot A}: Prop :=
{
  oCPO_PartialOrder:> PartialOrder_Setoid A;
  oCPO_completeness: forall T,
    increasing T -> is_omega_lub T (omega_lub T);
  bot_is_least: is_least bot
}.

(** 利用这里定义中的_[omega_lub]_函数，可以重述先前证明过的性质：两个单调不减序
    列如果拥有完全相同的上界，那么他们也有同样的上确界。*)

Lemma same_omega_ub_same_omega_lub':
  forall
    {A: Type}
    `{oCPOA: OmegaCompletePartialOrder_Setoid A}
    (l1 l2: nat -> A),
  (is_omega_ub l1 == is_omega_ub l2)%sets ->
  increasing l1 ->
  increasing l2 ->
  omega_lub l1 == omega_lub l2.
Proof.
  intros.
  apply (same_omega_ub_same_omega_lub _ _ _ _ H).
  + apply oCPO_completeness.
    apply H0.
  + apply oCPO_completeness.
    apply H1.
Qed.

(** 下面定义单调连续函数。*)


Definition mono
             {A B: Type}
             `{POA: PartialOrder_Setoid A}
             `{POB: PartialOrder_Setoid B}
             (f: A -> B): Prop :=
  forall a1 a2, a1 <= a2 -> f a1 <= f a2.


Definition continuous
             {A B: Type}
             `{oCPOA: OmegaCompletePartialOrder_Setoid A}
             `{oCPOB: OmegaCompletePartialOrder_Setoid B}
             (f: A -> B): Prop :=
  forall l: nat -> A,
    increasing l ->
    f (omega_lub l) == omega_lub (fun n => f (l n)).

(** 下面我们可以证明：自反函数是单调连续的、复合函数能保持单调连续性。*)

(** 自反函数的单调性：*)
Lemma id_mono:
  forall {A: Type}
         `{POA: PartialOrder_Setoid A},
  mono (fun x => x).
Proof.
Admitted. (* 留作习题 *)

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
Admitted. (* 留作习题 *)

(** 自反函数的连续性：*)
Lemma id_continuous:
  forall {A: Type}
         `{oCPOA: OmegaCompletePartialOrder_Setoid A}
         {EquivA: Equivalence equiv},
  continuous (fun x => x).
Proof.
Admitted. (* 留作习题 *)

(** 这里，要证明单调连续函数的复合结果也是连续的要复杂一些。显然，这其中需要证明
    一个单调函数作用在一个单调不减序列的每一项后还会得到一个单调不减序列。下面的
    引理_[increasing_mono_increasing]_描述了这一性质。*)
Lemma increasing_mono_increasing:
  forall {A B: Type}
         `{POA: PartialOrder_Setoid A}
         `{POB: PartialOrder_Setoid B}
         (f: A -> B)
         (l: nat -> A),
  increasing l -> mono f -> increasing (fun n => f (l n)).
Proof.
Admitted. (* 留作习题 *)

(** 除此之外，我们还需要证明单调函数能保持相等关系，即，如果_[f]_是一个单调函
    数，那么_[x == y]_能推出_[f x == f y]_。当然，如果这里的等价关系就是等号描述
    的相等关系，那么这个性质是显然的。但是，对于一般的等价关系，这就并不显然了。
    这一引理的正确性依赖于偏序关系中的自反性和反对称性。*)
Lemma mono_equiv_congr:
  forall {A B: Type}
         `{POA: PartialOrder_Setoid A}
         `{POB: PartialOrder_Setoid B}
          {EquivA: Equivalence (equiv: A -> A -> Prop)}
         (f: A -> B),
  mono f -> Proper (equiv ==> equiv) f.
Proof.
Admitted. (* 留作习题 *)

(** 现在，可以利用上面两条引理证明复合函数的连续性了。*)
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
Admitted. (* 留作习题 *)

(** 到目前为止，我们已经定义了Omega完备偏序集与单调连续函数。在证明Bourbaki-Witt
    不动点定理之前还需要最后一项准备工作：定理描述本身的合法性。即，我们需要证明
    _[bot]_, _[f bot]_, _[f (f bot)]_...这个序列的单调性。我们利用Coq标准库中的
    _[Nat.iter]_来定义这个序列，_[Nat.iter n f bot]_表示将_[f]_连续_[n]_次作用在
    _[bot]_上。*)

Lemma iter_bot_increasing:
  forall
    {A: Type}
    `{oCPOA: OmegaCompletePartialOrder_Setoid A}
    (f: A -> A),
    mono f ->
    increasing (fun n => Nat.iter n f bot).
Proof.
  unfold increasing.
  intros.
  induction n; simpl.
  + apply bot_is_least.
  + apply H.
    apply IHn.
Qed.

(** 当然，_[f bot]_, _[f (f bot)]_, _[f (f (f bot))]_...这个序列也是单调不减的。*)
Lemma iter_S_bot_increasing:
  forall
    {A: Type}
    `{oCPOA: OmegaCompletePartialOrder_Setoid A}
    (f: A -> A),
    mono f ->
    increasing (fun n => f (Nat.iter n f bot)).
Proof.
  unfold increasing.
  intros.
  apply H.
  apply iter_bot_increasing.
  apply H.
Qed.

(** _[BW_LFix]_定义了Bourbaki-Witt最小不动点。*)
Definition BW_LFix
             {A: Type}
             `{CPOA: OmegaCompletePartialOrder_Setoid A}
             (f: A -> A): A :=
  omega_lub (fun n => Nat.iter n f bot).

(** 先证明，_[BW_LFix]_的计算结果确实是一个不动点。*)
Lemma BW_LFix_is_fix:
  forall
    {A: Type}
    `{CPOA: OmegaCompletePartialOrder_Setoid A}
    {EquivA: Equivalence equiv}
    (f: A -> A),
    mono f ->
    continuous f ->
    f (BW_LFix f) == BW_LFix f.
Proof.
  unfold BW_LFix; intros.
  rewrite H0 by (apply iter_bot_increasing; tauto).
  apply same_omega_ub_same_omega_lub'.
  + intros; unfold is_omega_ub.
    split; intros.
    - destruct n.
      * apply bot_is_least.
      * apply H1.
    - specialize (H1 (S n)).
      apply H1.
  + apply iter_S_bot_increasing.
    apply H.
  + apply iter_bot_increasing.
    apply H.
Qed.

(** 再证明，_[BW_LFix]_的计算结果是最小不动点。*)
Lemma BW_LFix_is_least_fix:
  forall
    {A: Type}
    `{CPOA: OmegaCompletePartialOrder_Setoid A}
    {EquivA: Equivalence equiv}
    (f: A -> A)
    (a: A),
    mono f ->
    continuous f ->
    f a == a ->
    BW_LFix f <= a.
Proof.
  unfold BW_LFix; intros.
  pose proof iter_bot_increasing f H.
  pose proof oCPO_completeness (fun n => Nat.iter n f bot) H2.
  apply (is_omega_lub_tight H3).
  unfold is_omega_ub.
  induction n; simpl.
  + apply bot_is_least.
  + rewrite <- H1.
    apply H.
    apply IHn.
Qed.

Local Close Scope order_scope.

(** 接下去我们将利用Bourbaki-Witt最小不动点定义While语句的程序语义中运行终止的情
    况。*)

(** 首先需要定义我们所需的OmegaCPO。在定义_[Class]_类型的值时，可以使用
    _[Intance]_关键字。如果_[Class]_中只有一个域并且_[Class]_的定义没有使用大括
    号包围所有域，那么这个域的定义就是整个_[Class]_类型的值的定义；否则_[Class]_
    类型的值应当像_[Record]_类型的值一样定义。*)
#[export] Instance R_while_fin {A B: Type}: Order (A -> B -> Prop) :=
  Sets.included.

#[export] Instance Equiv_while_fin {A B: Type}: Equiv (A -> B -> Prop) :=
  Sets.equiv.

(** 下面证明这是一个偏序关系。证明的时候需要展开上面两个二元关系（一个表示序关系
    另一个表示等价关系）。以序关系为例，此时需要将_[R_while_fin]_与_[order_rel]_
    全部展开，前者表示将上面的定义展开，后者表示将从_[Class Order]_取出
    _[order_rel]_域这一操作展开。其余的证明则只需用_[sets_unfold]_证明集合相关的
    性质。*)
#[export] Instance PO_while_fin {A B: Type}: PartialOrder_Setoid (A -> B -> Prop).
Proof.
  split.
  + unfold Reflexive_Setoid.
    unfold equiv, order_rel, R_while_fin, Equiv_while_fin; simpl.
    sets_unfold; intros a b H x y.
    specialize (H x y).
    tauto.
  + unfold Transitive.
    unfold equiv, order_rel, R_while_fin, Equiv_while_fin; simpl.
    sets_unfold; intros a b c H H0 x y.
    specialize (H x y).
    specialize (H0 x y).
    tauto.
  + unfold AntiSymmetric_Setoid.
    unfold equiv, order_rel, R_while_fin, Equiv_while_fin; simpl.
    sets_unfold; intros a b H H0 x y.
    specialize (H x y).
    specialize (H0 x y).
    tauto.
Qed.

(** 下面再定义上确界计算函数与完备偏序集中的最小值。*)
#[export] Instance oLub_while_fin {A B: Type}: OmegaLub (A -> B -> Prop) :=
  Sets.omega_union.

#[export] Instance Bot_while_fin {A B: Type}: Bot (A -> B -> Prop) :=
  ∅: A -> B -> Prop.

(** 下面证明这构成一个Omega完备偏序集。*)
#[export] Instance oCPO_while_fin {A B: Type}:
  OmegaCompletePartialOrder_Setoid (A -> B -> Prop).
Proof.
  split.
  + apply PO_while_fin.
  + unfold increasing, is_omega_lub, is_omega_ub, is_lb.
    unfold omega_lub, order_rel, R_while_fin, oLub_while_fin; simpl.
    sets_unfold; intros T H.
    split.
    - intros n x y; intros.
      exists n.
      tauto.
    - intros a H0 x y H1.
      destruct H1 as [n ?].
      specialize (H0 n x y).
      tauto.
  + unfold is_least.
    unfold bot, order_rel, R_while_fin, Bot_while_fin; simpl.
    sets_unfold; intros a.
    tauto.
Qed.

(** 额外需要补充一点：_[Equiv_while_fin]_确实是一个等价关系。先前Bourbaki-Witt不
    动点定理的证明中用到了这一前提。*)
#[export] Instance Equiv_equiv_while_fin {A B: Type}:
  Equivalence (@equiv (A -> B -> Prop) _).
Proof.
  apply Sets_equiv_equiv.
Qed.

(** 下面开始证明_[F(X) = (test1(D0) ∘ D ∘ while_denote D0 D) ∪ test0(D0)]_这个函
    数的单调性与连续性。整体证明思路是：(1) _[F(X) = X]_是单调连续的；(2) 如果
    _[F]_是单调连续的，那么_[G(X) = Y ∘ F(X)]_也是单调连续的；(3) 如果_[F]_是单
    调连续的，那么_[G(X) = F(X) ∪ Y]_也是单调连续的；其中_[Y]_是给定的二元关系。*)

(** 首先证明二元关系的连接能保持集合之间的包含关系。*)
#[export] Instance BinRel_concat_included_congr:
  forall A B C: Type,
    Proper
      (Sets.included ==> Sets.included ==> Sets.included)
      (@BinRel.concat A B C).
Proof.
Admitted. (* 留作习题 *)

(** 基于此也容易证明，二元关系的连接能保持集合之间的相等关系。*)
#[export] Instance BinRel_concat_equiv_congr:
  forall A B C: Type,
    Proper
      (Sets.equiv ==> Sets.equiv ==> Sets.equiv)
      (@BinRel.concat A B C).
Proof.
  intros.
  unfold Proper, respectful; intros.
  apply Sets_equiv_Sets_included.
  split; apply BinRel_concat_included_congr.
  + rewrite H; reflexivity.
  + rewrite H0; reflexivity.
  + rewrite H; reflexivity.
  + rewrite H0; reflexivity.
Qed.

(** 下面证明前面提到的步骤(2)：如果_[F]_是单调连续的，那么_[G(X) = Y ∘ F(X)]_也
    是单调连续的。主结论为_[BinRel_concat_left_mono_and_continuous]_，其用到了两
    条下面的辅助引理以及前面证明过的复合函数单调连续性定理。*)

Lemma BinRel_concat_left_mono:
  forall (A B C: Type) (Y: A -> B -> Prop),
    mono (fun X: B -> C -> Prop => Y ∘ X).
Proof.
  intros.
  unfold mono.
  unfold order_rel, R_while_fin.
  intros.
  apply BinRel_concat_included_congr.
  + reflexivity.
  + apply H.
Qed.

Lemma BinRel_concat_left_continuous:
  forall (A B C: Type) (Y: A -> B -> Prop),
    continuous (fun X: B -> C -> Prop => Y ∘ X).
Proof.
  intros.
  unfold continuous.
  unfold increasing, omega_lub, order_rel, equiv,
         oLub_while_fin, R_while_fin, Equiv_while_fin.
  intros.
  apply BinRel_concat_omega_union_distr_l.
Qed.

Lemma BinRel_concat_left_mono_and_continuous:
  forall
    (A B C: Type)
    (Y: A -> B -> Prop)
    (f: (B -> C -> Prop) -> (B -> C -> Prop)),
  mono f /\ continuous f ->
  mono (fun X => Y ∘ f X) /\ continuous (fun X => Y ∘ f X).
Proof.
  intros.
  destruct H.
  pose proof BinRel_concat_left_mono _ _ C Y.
  pose proof BinRel_concat_left_continuous _ _ C Y.
  split.
  + exact (compose_mono f _ H H1).
  + exact (compose_continuous f _ H H1 H0 H2).
Qed.

(** 下面证明前面提到的步骤(3)：如果_[F]_是单调连续的，那么_[G(X) = Y ∘ F(X)]_也
    是单调连续的。主结论为_[union_right2_mono_and_continuous]_，其用到了两条下面
    的辅助引理以及前面证明过的复合函数单调连续性定理。*)

Lemma union_right2_mono:
  forall (A B: Type) (Y: A -> B -> Prop),
    mono (fun X => X ∪ Y).
Proof.
  intros.
  unfold mono.
  unfold order_rel, R_while_fin.
  sets_unfold.
  intros R R' H st1 st2.
  specialize (H st1 st2).
  tauto.
Qed.

Lemma union_right2_continuous:
  forall (A B: Type) (Y: A -> B -> Prop),
    continuous (fun X => X ∪ Y).
Proof.
  intros.
  unfold continuous.
  unfold increasing, omega_lub, order_rel, equiv,
         oLub_while_fin, R_while_fin, Equiv_while_fin.
  sets_unfold.
  intros l H st1 st2.
  split; intros.
  + destruct H0 as [ [ n ? ] | ?].
    - exists n; tauto.
    - exists O; tauto.
  + destruct H0 as [n [? | ? ] ].
    - left.
      exists n; tauto.
    - tauto.
Qed.

Lemma union_right2_mono_and_continuous:
  forall
    (A B: Type)
    (Y: A -> B -> Prop)
    (f: (A -> B -> Prop) -> (A -> B -> Prop)),
  mono f /\ continuous f ->
  mono (fun X => f X ∪ Y) /\ continuous (fun X => f X ∪ Y).
Proof.
  intros.
  destruct H.
  pose proof union_right2_mono _ _ Y.
  pose proof union_right2_continuous _ _ Y.
  split.
  + exact (compose_mono f _ H H1).
  + exact (compose_continuous f _ H H1 H0 H2).
Qed.

(** 最终我们可以用Bourbaki-Witt不动点定义while语句运行终止的情况。*)
Module Lang7.

Import WhileD_Expr Lang5 Lang6.

(** 首先给出语义定义。*)
Definition while_denote
             (D0: prog_state -> int64 -> Prop)
             (D: prog_state -> prog_state -> Prop):
  prog_state -> prog_state -> Prop :=
  BW_LFix (fun X => (test1(D0) ∘ D ∘ X) ∪ test0(D0)).

(** 下面可以直接使用Bourbaki-Witt不动点定理证明上述定义就是我们要的最小不动点。*)
Theorem while_denote_is_least_fix: forall D0 D,
  ((test1(D0) ∘ D ∘ while_denote D0 D) ∪ test0(D0) == while_denote D0 D)%sets /\
  (forall X, (test1(D0) ∘ D ∘ X) ∪ test0(D0) == X -> while_denote D0 D ⊆ X)%sets.
Proof.
  intros.
  assert (mono (fun X => (test1(D0) ∘ D ∘ X) ∪ test0(D0)) /\
          continuous (fun X => (test1(D0) ∘ D ∘ X) ∪ test0(D0))).
  {
    apply union_right2_mono_and_continuous.
    apply BinRel_concat_left_mono_and_continuous.
    apply BinRel_concat_left_mono_and_continuous.
    split.
    + apply id_mono.
    + apply id_continuous.
  }
  destruct H.
  split.
  + apply (BW_LFix_is_fix (fun X => (test1(D0) ∘ D ∘ X) ∪ test0(D0)));
      tauto.
  + intros X.
    apply (BW_LFix_is_least_fix (fun X => (test1(D0) ∘ D ∘ X) ∪ test0(D0)));
      tauto.
Qed.

End Lang7.


(** 下面可以用类似方法定义循环语句出错的情况。*)



(** 首先定义用于定义不动点的OmegaCPO。*)

#[export] Instance R_while_err {A: Type}: Order (A -> Prop) :=
  Sets.included.

#[export] Instance Equiv_while_err {A: Type}: Equiv (A -> Prop) :=
  Sets.equiv.

#[export] Instance PO_while_err {A: Type}: PartialOrder_Setoid (A -> Prop).
Proof.
  split.
  + unfold Reflexive_Setoid.
    unfold equiv, order_rel, R_while_err, Equiv_while_err; simpl.
    sets_unfold; intros a b H x.
    specialize (H x).
    tauto.
  + unfold Transitive.
    unfold equiv, order_rel, R_while_err, Equiv_while_err; simpl.
    sets_unfold; intros a b c H H0 x.
    specialize (H x).
    specialize (H0 x).
    tauto.
  + unfold AntiSymmetric_Setoid.
    unfold equiv, order_rel, R_while_err, Equiv_while_err; simpl.
    sets_unfold; intros a b H H0 x.
    specialize (H x).
    specialize (H0 x).
    tauto.
Qed.

#[export] Instance oLub_while_err {A: Type}: OmegaLub (A -> Prop) :=
  Sets.omega_union.

#[export] Instance Bot_while_err {A: Type}: Bot (A -> Prop) :=
  ∅: A -> Prop.

#[export] Instance oCPO_while_err {A: Type}:
  OmegaCompletePartialOrder_Setoid (A -> Prop).
Proof.
  split.
  + apply PO_while_err.
  + unfold increasing, is_omega_lub, is_omega_ub, is_lb.
    unfold omega_lub, order_rel, R_while_err, oLub_while_err; simpl.
    sets_unfold; intros T H.
    split.
    - intros n x; intros.
      exists n.
      tauto.
    - intros a H0 x H1.
      destruct H1 as [n ?].
      specialize (H0 n x).
      tauto.
  + unfold is_least.
    unfold bot, order_rel, R_while_err, Bot_while_err; simpl.
    sets_unfold; intros a.
    tauto.
Qed.

#[export] Instance Equiv_equiv_while_err {A: Type}:
  Equivalence (@equiv (A -> Prop) _).
Proof.
  apply Sets_equiv_equiv.
Qed.

(** 其次，我们需要证明_[BinRel.dia]_的系列性质。它与二元关系的连接之间有结合律，
    它本身对并集也有分配律。我们在Coq中当然可以像之前一样直接用集合性质进行证明，
    但是也可以利用先前证明过二元关系连接的性质帮助我们证明。*)

Definition ToRel {A: Type} (X: A -> Prop): A -> unit -> Prop :=
  fun a _ => X a.

(** 上面这个函数将一个一元关系_[X]_变换为了_[A]_与单元集_[unit]_之间的二元关系。
    我们可以利用这个函数将一元关系和二元关系联系起来。在Coq中_[unit]_表示单元
    集，这个集合中的唯一元素是_[tt]_。下面是五个转化引理：*)

Lemma ToRel_equiv:
  forall {A: Type} (X Y: A -> Prop),
    X == Y <-> ToRel X == ToRel Y.
Proof.
  intros A.
  sets_unfold; unfold ToRel; intros.
  split; intros.
  + apply H.
  + apply (H a tt).
Qed.

Lemma ToRel_included:
  forall {A: Type} (X Y: A -> Prop),
    X ⊆ Y <-> ToRel X ⊆ ToRel Y.
Proof.
  intros A.
  sets_unfold; unfold ToRel; intros.
  split; intros.
  + apply H; tauto.
  + apply (H a tt); tauto.
Qed.

Lemma ToRel_BinRel_dia:
  forall {A B: Type} (X: A -> B -> Prop) (Y: B -> Prop),
    ToRel (BinRel.dia X Y) == X ∘ ToRel Y.
Proof.
  intros A.
  sets_unfold; unfold ToRel, BinRel.dia, BinRel.concat; intros.
  tauto.
Qed.

Lemma ToRel_union:
  forall {A: Type} (X Y: A -> Prop),
    ToRel (X ∪ Y) == ToRel X ∪ ToRel Y.
Proof.
  intros A.
  sets_unfold; unfold ToRel, Sets.union; intros.
  tauto.
Qed.

Lemma ToRel_omega_union:
  forall {A: Type} (X: nat -> A -> Prop),
    ToRel (⋃ X) == ⋃ (fun n => ToRel (X n)).
Proof.
  intros A.
  sets_unfold; unfold ToRel, Sets.omega_union; intros.
  tauto.
Qed.

(** 接下去借助上面转化引理证明_[BinRel.dia]_的性质。*)

Lemma BinRel_concat_dia:
  forall {A B C}
    (R1: A -> B -> Prop)
    (R2: B -> C -> Prop)
    (X: C -> Prop),
      BinRel.dia R1 (BinRel.dia R2 X) == BinRel.dia (R1 ∘ R2) X.
Proof.
  intros.
  apply ToRel_equiv.
  rewrite !ToRel_BinRel_dia.
  apply BinRel_concat_assoc.
Qed.

Lemma BinRel_dia_union_distr_r:
  forall
    {A B}
    (R1 R2: A -> B -> Prop)
    (R3: B -> Prop),
  BinRel.dia (R1 ∪ R2) R3 ==
  (BinRel.dia R1 R3) ∪ (BinRel.dia R2 R3).
Proof.
  intros.
  apply ToRel_equiv.
  rewrite !ToRel_BinRel_dia, !ToRel_union.
  apply BinRel_concat_union_distr_r.
Qed.

Lemma BinRel_dia_union_distr_l:
  forall
    {A B}
    (R1: A -> B -> Prop)
    (R2 R3: B -> Prop),
  BinRel.dia R1 (R2 ∪ R3) ==
  (BinRel.dia R1 R2) ∪ (BinRel.dia R1 R3).
Proof.
  intros.
  apply ToRel_equiv.
  rewrite !ToRel_BinRel_dia, !ToRel_union.
  apply BinRel_concat_union_distr_l.
Qed.

Lemma BinRel_dia_omega_union_distr_r:
  forall
    {A B}
    (R1: nat -> A -> B -> Prop)
    (R2: B -> Prop),
  BinRel.dia (⋃ R1) R2 == ⋃ (fun n => BinRel.dia (R1 n) R2).
Proof.
  intros.
  apply ToRel_equiv.
  rewrite !ToRel_BinRel_dia, !ToRel_omega_union.
  rewrite BinRel_concat_omega_union_distr_r.
  apply Sets_omega_union_congr.
  intros n.
  rewrite ToRel_BinRel_dia.
  reflexivity.
Qed.

Lemma BinRel_dia_omega_union_distr_l:
  forall
    {A B}
    (R1: A -> B -> Prop)
    (R2: nat -> B -> Prop),
  BinRel.dia R1 (⋃ R2) == ⋃ (fun n => BinRel.dia R1 (R2 n)).
Proof.
  intros.
  apply ToRel_equiv.
  rewrite !ToRel_BinRel_dia, !ToRel_omega_union.
  rewrite BinRel_concat_omega_union_distr_l.
  apply Sets_omega_union_congr.
  intros n.
  rewrite ToRel_BinRel_dia.
  reflexivity.
Qed.

#[export] Instance BinRel_dia_included_congr:
  forall A B: Type,
    Proper
      (Sets.included ==> Sets.included ==> Sets.included)
      (@BinRel.dia A B).
Proof.
  intros; unfold Proper, respectful; intros.
  apply ToRel_included; apply ToRel_included in H0.
  rewrite !ToRel_BinRel_dia.
  apply BinRel_concat_included_congr; tauto.
Qed.

#[export] Instance BinRel_dia_equiv_congr:
  forall A B: Type,
    Proper
      (Sets.equiv ==> Sets.equiv ==> Sets.equiv)
      (@BinRel.dia A B).
Proof.
  intros; unfold Proper, respectful; intros.
  apply ToRel_equiv; apply ToRel_equiv in H0.
  rewrite !ToRel_BinRel_dia.
  apply BinRel_concat_equiv_congr; tauto.
Qed.

(** 接下去是单调连续性相关的证明。*)

Lemma BinRel_dia_left_mono:
  forall (A B: Type) (Y: A -> B -> Prop),
    mono (fun X => BinRel.dia Y X).
Proof.
  intros.
  unfold mono.
  unfold order_rel, R_while_fin.
  intros.
  apply BinRel_dia_included_congr.
  + reflexivity.
  + apply H.
Qed.

Lemma BinRel_dia_left_continuous:
  forall (A B: Type) (Y: A -> B -> Prop),
    continuous (fun X => BinRel.dia Y X).
Proof.
  intros.
  unfold continuous.
  unfold increasing, omega_lub, order_rel, equiv,
         oLub_while_fin, R_while_fin, Equiv_while_fin.
  intros.
  apply BinRel_dia_omega_union_distr_l.
Qed.

Lemma BinRel_dia_left_mono_and_continuous:
  forall
    (A B: Type)
    (Y: A -> B -> Prop)
    (f: (B -> Prop) -> (B -> Prop)),
  mono f /\ continuous f ->
  mono (fun X => BinRel.dia Y (f X)) /\
  continuous (fun X => BinRel.dia Y (f X)).
Proof.
  intros.
  destruct H.
  pose proof BinRel_dia_left_mono _ _ Y.
  pose proof BinRel_dia_left_continuous _ _ Y.
  split.
  + exact (compose_mono f _ H H1).
  + exact (compose_continuous f _ H H1 H0 H2).
Qed.

Lemma union_right1_mono:
  forall (A: Type) (Y: A -> Prop),
    mono (fun X => X ∪ Y).
Proof.
  intros.
  unfold mono.
  unfold order_rel, R_while_err.
  sets_unfold.
  intros R R' H st.
  specialize (H st).
  tauto.
Qed.

Lemma union_right1_continuous:
  forall (A: Type) (Y: A -> Prop),
    continuous (fun X => X ∪ Y).
Proof.
  intros.
  unfold continuous.
  unfold increasing, omega_lub, order_rel, equiv,
         oLub_while_fin, R_while_fin, Equiv_while_fin.
  sets_unfold.
  intros l H st.
  split; intros.
  + destruct H0 as [ [ n ? ] | ?].
    - exists n; tauto.
    - exists O; tauto.
  + destruct H0 as [n [? | ? ] ].
    - left.
      exists n; tauto.
    - tauto.
Qed.

Lemma union_right1_mono_and_continuous:
  forall
    (A: Type)
    (Y: A -> Prop)
    (f: (A -> Prop) -> (A -> Prop)),
  mono f /\ continuous f ->
  mono (fun X => f X ∪ Y) /\ continuous (fun X => f X ∪ Y).
Proof.
  intros.
  destruct H.
  pose proof union_right1_mono _ Y.
  pose proof union_right1_continuous _ Y.
  split.
  + exact (compose_mono f _ H H1).
  + exact (compose_continuous f _ H H1 H0 H2).
Qed.

(** 最后我们定义while循环语句运行出错的情况，并证明其确实是最小不动点。*)

Module Lang8.

Import WhileD_Expr Lang5 Lang6.

Definition test_err
             (D: prog_state -> int64 -> Prop)
             (st: prog_state): Prop :=
  forall n, ~ D st n.

Definition while_denote_err
             (D0: prog_state -> int64 -> Prop)
             (Dfin: prog_state -> prog_state -> Prop)
             (Derr: prog_state -> Prop):
  prog_state -> Prop :=
  BW_LFix (fun X => BinRel.dia (test1(D0) ∘ Dfin) X ∪
                    BinRel.dia (test1(D0)) Derr ∪
                    test_err(D0)).

Theorem while_denote_err_is_least_fix: forall D0 Dfin Derr,
  (BinRel.dia (test1(D0) ∘ Dfin) (while_denote_err D0 Dfin Derr) ∪
   BinRel.dia (test1(D0)) Derr ∪
   test_err(D0) ==
   while_denote_err D0 Dfin Derr)%sets /\
  (forall X,
     BinRel.dia (test1(D0) ∘ Dfin) X ∪
     BinRel.dia (test1(D0)) Derr ∪
     test_err(D0) == X ->
     while_denote_err D0 Dfin Derr ⊆ X)%sets.
Proof.
  intros.
  assert (mono (fun X => BinRel.dia (test1(D0) ∘ Dfin) X ∪
                         BinRel.dia (test1(D0)) Derr ∪
                         test_err(D0)) /\
          continuous (fun X => BinRel.dia (test1(D0) ∘ Dfin) X ∪
                               BinRel.dia (test1(D0)) Derr ∪
                               test_err(D0))).
  {
    apply union_right1_mono_and_continuous.
    apply union_right1_mono_and_continuous.
    apply BinRel_dia_left_mono_and_continuous.
    split.
    + apply id_mono.
    + apply id_continuous.
  }
  destruct H.
  split.
  + apply (BW_LFix_is_fix (fun X => BinRel.dia (test1(D0) ∘ Dfin) X ∪
                                    BinRel.dia (test1(D0)) Derr ∪
                                    test_err(D0)));
      tauto.
  + intros X.
    apply (BW_LFix_is_least_fix (fun X => BinRel.dia (test1(D0) ∘ Dfin) X ∪
                                          BinRel.dia (test1(D0)) Derr ∪
                                          test_err(D0)));
      tauto.
Qed.

End Lang8.

(** ** While循环语句不终止的情况 *)



(** 下面是这一不动点定理的Coq证明。*)

Local Open Scope order_scope.

(** 首先定义完备格。*)
Definition is_lub {A: Type} {RA: Order A} (X: A -> Prop) (a: A): Prop :=
  is_ub X a /\ is_lb (is_ub X) a.

Definition is_glb {A: Type} {RA: Order A} (X: A -> Prop) (a: A): Prop :=
  is_lb X a /\ is_ub (is_lb X) a.

Class Lub (A: Type): Type :=
  lub: (A -> Prop) -> A.

Class Glb (A: Type): Type :=
  glb: (A -> Prop) -> A.

Class LubProperty (A: Type) {RA: Order A} {LubA: Lub A}: Prop :=
  lub_is_lub: forall X: A -> Prop, is_lub X (lub X).

Class GlbProperty (A: Type) {RA: Order A} {GlbA: Glb A}: Prop :=
  glb_is_glb: forall X: A -> Prop, is_glb X (glb X).

Lemma glb_sound: forall {A: Type} `{GlbPA: GlbProperty A},
  forall X: A -> Prop, is_lb X (glb X).
Proof. intros. destruct (glb_is_glb X). tauto. Qed.

Lemma glb_tight: forall {A: Type} `{GlbPA: GlbProperty A},
  forall X: A -> Prop, is_ub (is_lb X) (glb X).
Proof. intros. destruct (glb_is_glb X). tauto. Qed.

Class CompleteLattice_Setoid (A: Type)
        {RA: Order A} {EA: Equiv A} {LubA: Lub A} {glbA: Glb A}: Prop :=
{
  CL_PartialOrder:> PartialOrder_Setoid A;
  CL_LubP:> LubProperty A;
  CL_GlbP:> GlbProperty A
}.

(** 下面基于完备格与单调函数的定义证明Knaster-Tarski不动点定理。*)
Definition KT_LFix
             {A: Type}
             `{CLA: CompleteLattice_Setoid A}
             (f: A -> A): A :=
  glb (fun a => f a <= a).

Lemma KT_LFix_is_pre_fix:
  forall
    {A: Type}
    `{CLA: CompleteLattice_Setoid A}
    {EquivA: Equivalence equiv}
    (f: A -> A),
    mono f ->
    f (KT_LFix f) <= KT_LFix f.
Proof.
  intros.
  unfold KT_LFix.
  apply glb_tight; unfold is_lb; intros.
  rewrite <- H0.
  apply H.
  apply glb_sound.
  apply H0.
Qed.

Lemma KT_LFix_is_fix:
  forall
    {A: Type}
    `{CLA: CompleteLattice_Setoid A}
    {EquivA: Equivalence equiv}
    (f: A -> A),
    mono f ->
    f (KT_LFix f) == KT_LFix f.
Proof.
  intros.
  pose proof KT_LFix_is_pre_fix f H.
  apply antisymmetricity_setoid.
  + apply H0.
  + apply glb_sound.
    apply H, H0.
Qed.

Lemma KT_LFix_is_least_fix:
  forall
    {A: Type}
    `{CLA: CompleteLattice_Setoid A}
    {EquivA: Equivalence equiv}
    (f: A -> A)
    (a: A),
    mono f ->
    f a == a ->
    KT_LFix f <= a.
Proof.
  intros.
  apply glb_sound.
  apply reflexivity_setoid.
  apply H0.
Qed.

Local Close Scope order_scope.

(** 下面定义用于定义不动点的完备格。*)

#[export] Instance R_while_inf {A: Type}: Order (A -> Prop) :=
  (Basics.flip Sets.included).

#[export] Instance Equiv_while_inf {A: Type}: Equiv (A -> Prop) :=
  Sets.equiv.

#[export] Instance PO_while_inf {A: Type}: PartialOrder_Setoid (A -> Prop).
Proof.
  split.
  + unfold Reflexive_Setoid.
    unfold Basics.flip, equiv, order_rel, R_while_inf, Equiv_while_inf; simpl.
    sets_unfold; intros a b H x.
    specialize (H x).
    tauto.
  + unfold Transitive.
    unfold Basics.flip, equiv, order_rel, R_while_inf, Equiv_while_inf; simpl.
    sets_unfold; intros a b c H H0 x.
    specialize (H x).
    specialize (H0 x).
    tauto.
  + unfold AntiSymmetric_Setoid.
    unfold Basics.flip, equiv, order_rel, R_while_inf, Equiv_while_inf; simpl.
    sets_unfold; intros a b H H0 x.
    specialize (H x).
    specialize (H0 x).
    tauto.
Qed.

#[export] Instance Lub_while_inf {A: Type}: Lub (A -> Prop) :=
  Sets.general_intersect.

#[export] Instance Glb_while_inf {A: Type}: Glb (A -> Prop) :=
  Sets.general_union.

#[export] Instance LubP_while_inf {A: Type}: LubProperty (A -> Prop).
Proof.
  unfold LubProperty.
  unfold is_lub, is_lb, is_ub.
  unfold R_while_inf, order_rel, Lub_while_inf, lub, Basics.flip.
  sets_unfold.
  simpl.
  split; intros.
  + apply H0, H.
  + specialize (H _ H1 _ H0).
    apply H.
Qed.

#[export] Instance GlbP_while_inf {A: Type}: GlbProperty (A -> Prop).
Proof.
  unfold GlbProperty.
  unfold is_glb, is_lb, is_ub.
  unfold R_while_inf, order_rel, Glb_while_inf, glb, Basics.flip.
  sets_unfold.
  split; intros.
  + exists a'.
    tauto.
  + destruct H0 as [? [? ?] ].
    specialize (H _ H0 _ H1).
    apply H.
Qed.

#[export] Instance CL_while_inf {A: Type}:
  CompleteLattice_Setoid (A -> Prop).
Proof.
  split.
  + apply PO_while_inf.
  + apply LubP_while_inf.
  + apply GlbP_while_inf.
Qed.

Lemma BinRel_dia_left__mono:
  forall (A B: Type) (Y: A -> B -> Prop),
    mono (fun X: B -> Prop => BinRel.dia Y X).
Proof.
  intros.
  unfold mono.
  unfold order_rel, R_while_inf.
  intros.
  apply BinRel_dia_included_congr.
  + reflexivity.
  + apply H.
Qed.

Lemma BinRel_dia_left_compose_mono:
  forall
    (A B: Type)
    (Y: A -> B -> Prop)
    (f: (B -> Prop) -> (B -> Prop)),
  mono f ->
  mono (fun X => BinRel.dia Y (f X)).
Proof.
  intros.
  pose proof BinRel_dia_left__mono _ _ Y.
  exact (compose_mono f _ H H0).
Qed.

Lemma union_right1__mono:
  forall (A: Type) (Y: A -> Prop),
    mono (fun X => X ∪ Y).
Proof.
  intros.
  unfold mono.
  unfold order_rel, R_while_inf, Basics.flip.
  sets_unfold.
  intros R R' H st.
  specialize (H st).
  tauto.
Qed.

Lemma union_right1_compose_mono:
  forall
    (A: Type)
    (Y: A -> Prop)
    (f: (A -> Prop) -> (A -> Prop)),
  mono f ->
  mono (fun X => f X ∪ Y).
Proof.
  intros.
  pose proof union_right1__mono _ Y.
  exact (compose_mono f _ H H0).
Qed.

Module Lang9.

Import WhileD_Expr Lang5 Lang6 Lang7 Lang8.

Definition while_denote_inf
             (D0: prog_state -> int64 -> Prop)
             (Dfin: prog_state -> prog_state -> Prop)
             (Dinf: prog_state -> Prop):
  prog_state -> Prop :=
  KT_LFix (fun X => BinRel.dia (test1(D0) ∘ Dfin) X ∪
                    BinRel.dia (test1(D0)) Dinf).

Theorem while_denote_inf_is_greatest_fix: forall D0 Dfin Dinf,
  (BinRel.dia (test1(D0) ∘ Dfin) (while_denote_inf D0 Dfin Dinf) ∪
   BinRel.dia (test1(D0)) Dinf ==
   while_denote_inf D0 Dfin Dinf)%sets /\
  (forall X,
     BinRel.dia (test1(D0) ∘ Dfin) X ∪
     BinRel.dia (test1(D0)) Dinf == X ->
     X ⊆ while_denote_inf D0 Dfin Dinf)%sets.
Proof.
  intros.
  assert (mono (fun X => BinRel.dia (test1(D0) ∘ Dfin) X ∪
                         BinRel.dia (test1(D0)) Dinf)).
  {
    apply union_right1_compose_mono.
    apply BinRel_dia_left_compose_mono.
    apply id_mono.
  }
  split.
  + apply (KT_LFix_is_fix (fun X => BinRel.dia (test1(D0) ∘ Dfin) X ∪
                                    BinRel.dia (test1(D0)) Dinf));
      tauto.
  + intros X.
    unfold while_denote_inf.
    exact (KT_LFix_is_least_fix
             (fun X => BinRel.dia (test1(D0) ∘ Dfin) X ∪
                       BinRel.dia (test1(D0)) Dinf)
             X
             H).
Qed.

End Lang9.









(** ** 小结 *)

(** 所有的程序语句的语义整理如下：*)

Module WhileD_Cmd.

Import WhileD_Expr.

Inductive com : Type :=
  | CAss (e1 e2: expr): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com.

Definition test0
             (D: prog_state -> int64 -> Prop)
             (st1 st2: prog_state): Prop :=
  st1 = st2 /\ D st1 (Int64.repr 0).

Definition test1
             (D: prog_state -> int64 -> Prop)
             (st1 st2: prog_state): Prop :=
  exists n, st1 = st2 /\ D st1 n /\ Int64.unsigned n <> 0.

Definition test_err
             (D: prog_state -> int64 -> Prop)
             (st: prog_state): Prop :=
  forall n, ~ D st n.

Record cmd_denote: Type := {
  fin: prog_state -> prog_state -> Prop;
  err: prog_state -> Prop;
  inf: prog_state -> Prop
}.

Definition asgn_var_denote
             (X: var_name)
             (D: prog_state -> int64 -> Prop): cmd_denote :=
  {|
    fin := fun st1 st2 =>
      exists n,
        D st1 n /\
        st2.(vars) X = n /\
        (forall Y, X <> Y -> st1.(vars) Y = st2.(vars) Y) /\
        (forall p, st1.(mem) p = st2.(mem) p);
    err := fun st =>
      forall n, ~ D st n;
    inf := fun st =>
      False
  |}.

Definition asgn_deref_denote
             (D1 D2: prog_state -> int64 -> Prop): cmd_denote :=
  {|
    fin := fun st1 st2 =>
      exists p n,
        D1 st1 p /\
        D2 st1 n /\
        st1.(mem) p <> None /\
        st2.(mem) p = Some n /\
        (forall X, st1.(vars) X = st2.(vars) X) /\
        (forall q, p <> q -> st1.(mem) q = st2.(mem) q);
    err := fun st =>
      (forall n, ~ D1 st n) \/
      (forall n, ~ D2 st n) \/
      (exists p, D1 st p /\ st.(mem) p = None);
    inf := fun st =>
      False
  |}.

Definition seq_denote (D1 D2: cmd_denote): cmd_denote :=
  {|
    fin := D1.(fin) ∘ D2.(fin);
    err := D1.(err) ∪ (BinRel.dia D1.(fin) D2.(err));
    inf := D1.(inf) ∪ (BinRel.dia D1.(fin) D2.(inf))
  |}.

Definition if_denote
             (D0: prog_state -> int64 -> Prop)
             (D1 D2: cmd_denote): cmd_denote :=
  {|
    fin := (test1(D0) ∘ D1.(fin)) ∪ (test0(D0) ∘ D2.(fin));
    err := test_err D0 ∪
           (BinRel.dia (test1 D0) D1.(err)) ∪
           (BinRel.dia (test0 D0) D2.(err));
    inf := (BinRel.dia (test1 D0) D1.(inf)) ∪
           (BinRel.dia (test0 D0) D2.(inf))
  |}.

Definition while_denote
             (D0: prog_state -> int64 -> Prop)
             (D: cmd_denote): cmd_denote :=
  {|
    fin := BW_LFix (fun X => (test1 D0 ∘ D.(fin) ∘ X) ∪ test0 D0);
    err := BW_LFix (fun X => BinRel.dia (test1 D0 ∘ D.(fin)) X ∪
                             BinRel.dia (test1 D0) D.(err) ∪
                             test_err(D0));
    inf := KT_LFix (fun X => BinRel.dia (test1 D0 ∘ D.(fin)) X ∪
                             BinRel.dia (test1 D0) D.(inf))
  |}.

Fixpoint ceval (c: com): cmd_denote :=
  match c with
  | CAss e1 e2 =>
    match e1 with
    | EVar X => asgn_var_denote X (eeval e2)
    | EDeref e0 => asgn_deref_denote (eeval e0) (eeval e2)
    | _ => {| fin := ∅; err := ∅; inf := ∅ |}
    end
  | CSeq c1 c2 => seq_denote (ceval c1) (ceval c2)
  | CIf e c1 c2 => if_denote (eeval e) (ceval c1) (ceval c2)
  | CWhile e c0 => while_denote (eeval e) (ceval c0)
  end.

End WhileD_Cmd.

