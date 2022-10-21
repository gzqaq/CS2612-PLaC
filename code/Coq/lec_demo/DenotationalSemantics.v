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
  unfold eequiv.
  intros.
  simpl.
  lia.
Qed.


Lemma EPlus_0_r: forall e,
  [[e + 0]] == [[e]].
Proof.
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
  unfold Reflexive, eequiv.
  intros.
  reflexivity.
Qed.

#[export] Instance eequiv_sym: Symmetric eequiv.
Proof.
  unfold Symmetric, eequiv.
  intros.
  rewrite H. reflexivity.
Qed.

#[export] Instance eequiv_trans: Transitive eequiv.
Proof.
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
  intros.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.


(** 减号与乘号保持语义等价关系的证明是类似的。*)

#[export] Instance EMinus_eequiv_congr:
  Proper (eequiv ==> eequiv ==> eequiv) EMinus.
Proof.
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
  (*  + destruct (CF e1), (CF e2).
        2: {
          rewrite <- IHe1, <- IHe2.
          reflexivity.
        }
        the remaining subgoals can also be proved like this, so we use semicolon.
        _[try]_ means "try to apply the proof if possible".
  *)
  + destruct (CF e1), (CF e2); rewrite <- IHe1, <- IHe2; try reflexivity.
    (* Then we prove the first subgoal. *)
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


(** 在Coq中，用户可以用_[Search]_指令搜索已经证明过的结果。例如，下面指令可以搜
    索所有关于_[Int64.add]_的性质。*)

Search Int64.add.

(** 除此之外，_[Search]_指令允许在搜索中对包含命题的形式做更细化的描述。例如：*)

Search (Int64.add _ _ = Int64.add _ _).



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
    的规定。特别的，有符号64位整数的运算越界应当被视为程序错误。然而，这一点并未
    在上面定义中得到体现。*)

(** 为了解决这一问题，我们需要能够在定义中表达『程序表达式求值出错』这一概念。这
    在数学上有两种常见方案。其一是将_[eeval]_的求值结果由64位整数集合改为64位整
    数或求值失败。*)



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
  | ENum n => Some (Int64.repr n)
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

Check Zle_imp_le_bool.

(** 这个定理说的是：_[forall n m : Z, n <= m -> (n <=? m) = true]_。当然，Coq标
    准库中还有很多类似的有用的性质，这里就不再一一罗列了，相关信息也可以通过
    _[Search Z.leb]_或_[Search Z.le]_等方法查找。*)

(** 最后，在Coq中，可以用_[&&]_表示布尔值的合取（Coq定义是_[andb]_）并且使用
    _[if]_，_[then]_，_[else]_针对布尔表达式求值为真以及为假的情况分别采取不同的
    求值方法。将这些定义组合在一起，就得到了上面的_[eeval]_定义。*)

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
      Some (Int64.repr n)
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
  Some (Int64.repr n).

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


(** Coq中允许用户使用_[fun]_关键字表示匿名函数，例如：*)

Example fact_doit3times_anon1:
  doit3times (fun x => x - 2) 9 = 3.
Proof. reflexivity. Qed.

Example fact_doit3times_anon2:
  doit3times (fun x => x * x) 2 = 256.
Proof. reflexivity. Qed.

(** 这里_[fun x => x - 2]_与之前定义的_[minustwo]_是相同的，而_[fun x => x * x]_
    则表示了平方这样一个函数。*)

















(** ** 方案四 *)

(** 上面我们讨论了将表达式语义定义为程序状态到$\mathbb{Z}_{2^64} \cup \{ \epsilon \}$
    的函数这一方案。下面我们探讨另一种描述程序运行出错或未定义行为的方案，即将表
    达式的语义定义为程序状态与64位整数之间的二元关系。*)



Module Lang4.

Import Lang1 Lang2.

(** 在Coq中，程序状态与64位整数之间的二元关系可以用下面类型描述：
    _[prog_state -> int64 -> Prop]_。*)

(** 首先定义常量与变量的情况：*)

Definition const_denote
           (z: Z)
           (s: prog_state)
           (n: int64): Prop :=
  n = Int64.repr z.

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


