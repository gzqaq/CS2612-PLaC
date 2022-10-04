Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import PL.CoqInductiveType.
Require Import PL.SetsDomain.
Local Open Scope string.

(** 我们已经知道，在Coq中可以利用Coq归纳类型定义正则表达式的语法树。*)

Inductive reg_exp: Type :=
  | Char (c: ascii): reg_exp
  | EmptyStr: reg_exp
  | App (r1 r2: reg_exp): reg_exp
  | Union (r1 r2: reg_exp): reg_exp
  | Star (r: reg_exp): reg_exp.

(** 另一方面，我们也知道正则表达式的语法定义不同于其表示的字符串集合。在程序语言
    理论、逻辑学等研究领域中，一般将一套形式语言所表达的含义称为语义。例如，描述
    正则表达式如何描述字符串集合的理论就是正则表达式的语义理论。Coq中除了可以严
    格定义正则表达式的语法，也能定义正则表达式的语义。下面先介绍Coq中定义集合以
    及描述集合运算的方式。*)

(** * Coq中的集合与命题 *)

(** Coq中所有命题的类型都是_[Prop]_，例如下列_[Check]_指令的反馈告诉我们，以下这
    些都是Coq的命题。再次提醒各位：一个命题可以为真也可以为假，_[Check]_指令只负
    责检验一个Coq表达式是否在语法上是合法的。下面这五个命题中第三个命题就是假命
    题。*)

Check 1 = 1.
Check forall n: nat, n < n + 1.
Check forall n: nat, n = n + 1.
Check True.
Check False.

(** Coq中并没有与子集这一概念直接对应的类型。我们需要借助命题来表示子集。例如，
    标准库中提供了_[String.length]_来计算字符串的长度，下面我们可以先借助该函数
    定义一个关于字符串的命题。 *)

Module StringSetDemo.

Definition is_length_1 (s: string): Prop :=
  String.length s = 1.

(** 对于任意一个字符串_[s]_，_[is_length_1 s]_这个命题说的是：_[s]_的长度为1。我
    们可以在Coq中使用_[Check]_指令来检查这一点。*)

Check is_length_1 "".
Check is_length_1 "a".
Check is_length_1 "ab".
Check is_length_1 "xyz".

(** 我们可以在Coq中证明它们成立或者不成立。注：Coq中_[~]_这个符号表示否定。*)

Example EmptyString_is_not_length_1: ~ is_length_1 "".
Proof.
  unfold is_length_1.
  (** 由于_[is_length_1]_本身不是一个递归定义，因此不能利用_[simpl]_对它进行化
      简。Coq中可以用_[unfold]_指令展开一项定义。*)
  simpl.
  (** _[String.length]_本身是一个递归定义，可以用_[simpl]_化简。 *)
  congruence.
Qed.

(** 下面是一个正面的证明。*)

Example a_is_length_1: is_length_1 "a".
Proof.
  unfold is_length_1.
  simpl.
  reflexivity.
Qed.

(** 那么_[is_length_1]_本身的类型是什么呢？*)

Check is_length_1.

(** 它的类型是从字符串集合_[string]_到命题的函数。我们也可以把它看做字符串集合的
    子集，这个集合中包含所有长度为1的字符串。

    本课程提供的SetsDomain.v中提供了有关集合的一系列定义。例如：

    - 空集：用 _[∅]_ 或者一堆方括号表示，定义为_[Sets.empty]_；

    - 单元集：用一对方括号表示，定义为_[Sets.singleton]_；

    - 并集：用_[∪]_表示，定义为_[Sets.union]_；

    - 交集：用_[∩]_表示，定义为_[Sets.intersect]_；

    - 一列集合的并：用_[⋃]_表示，定义为_[Sets.omega_union]_；

    - 一列集合的交：用_[⋂]_表示，定义为_[Sets.omega_intersect]_；

    - 集合相等：用_[==]_表示，定义为_[Sets.equiv]_；

    - 元素与集合关系：用_[∈]_表示，定义为_[Sets.In]_；

    - 子集关系：用_[⊆]_表示，定义为_[Sets.included]_。

    在CoqIDE中，你可以利用CoqIDE对于unicode的支持打出特殊字符：

    - 首先，在打出特殊字符的latex表示法；

    - 再按shift+空格键；

    - latex表示法就自动转化为了相应的特殊字符。

    例如，如果你需要打出符号_[∈]_，请先在输入框中输入_[\in]_，当光标紧跟在_[n]_
    这个字符之后的时候，按shift+空格键即可。*)

Local Open Scope sets_scope.

Check is_length_1 ∪ ∅.

Check is_length_1 ∪ [""].

(** 上面两个例子中描述的集合是：长度为1的字符串集合与空集的并集；长度为1的字符串
    集合与空串单元集的并集。

    Coq标准库以及我们提供的SetsDomain.v还提供了一些与集合相关的定理与自动化证明
    指令。这些待我们后面证明中用到时再做介绍。*)

End StringSetDemo.

(** * 正则表达式的语义 *)

(** 正则表达式共有5中不同的表达式。其中单字符_[Char]_与空串_[EmptyStr]_的语义可
    以用单元集定义，并集_[Union]_的语义可以用集合的并集定义。为了定义全部正则表
    达式的语义，下面先定义与_[App]_、_[Star]_相关的集合运算。*)

Local Open Scope sets_scope.

(** 下面首先定义两个字符串集合的连接。*)

Definition string_set_app (X1 X2: string -> Prop) (s: string): Prop :=
  exists s1 s2, s1 ∈ X1 /\ s2 ∈ X2 /\ s = string_app s1 s2.

(** 这个定义中，_[string_set_app]_有三个参数，前两个参数为字符串的集合，第三个参
    数是一个字符串，它类型是_[Prop]_命题类型。因此，这个定义可看做一个三参数的命
    题，这个命题_[string_set_app X1 X2 s]_要表达：把_[X1]_集合与_[X2]_集合中的字
    符串两两连接起来，得到一个新的集合，_[s]_在这个新集合中。

    它是通过下面数学命题来定义的，定义中的_[exists]_念做『存在』；_[/\]_这个符号
    表示逻辑中的合取符号，念做『并且』。因此，该命题的定义是：存在字符串_[s1]_、
    _[s2]_使得前者是_[X1]_中的元素，后者是_[X2]_中的元素，并且_[s]_是这两个字符
    串相连的结果，其中_[string_app]_是我们上次定义的字符串相连函数。

    除了可以将_[string_set_app]_看做有三个参数的命题，我们还可以将其看做字符串集
    合上的二元函数。我们先通过_[Check]_指令查看其类型。*)

Check string_set_app.

(** 它的类型是：_[(string -> Prop) -> (string -> Prop) -> string -> Prop]_。
    因此，我们可以将其看做一个二元函数，两个参数的类型都是_[string -> Prop]_并且
    函数的返回类型也是_[string -> Prop]_。下面我们利用Coq Notation引入一个表示该
    二元函数的简洁记号。*)

Notation "X ∘ Y" := (string_set_app X Y)
                      (right associativity, at level 60).

(** 下面我们可以在Coq中写出几个关于_[string_set_app]_的定义或命题：*)

Check [] ∘ [].
Check ["a"] ∘ ["b"] ∘ ["c"].
Check ["x"] ∘ ["y"] ∘ ["z"] = ["xyz"].
Check forall X Y Z: string -> Prop, X ∘ (Y ∘ Z) == (X ∘ Y) ∘ Z.

(** 下面我们再定义_[Star]_相关的集合运算。*)

Fixpoint repeat_n (X: string -> Prop) (n: nat): string -> Prop :=
  match n with
  | O => [""]
  | S n' => X ∘ repeat_n X n'
  end.

Definition repeat_any (X: string -> Prop): string -> Prop :=
  ⋃ (repeat_n X).

(** 此处，我们先定义了辅助函数_[repeat_n]_。这是一个二元函数，它的第一个参数是一
    个字符串集合，第二个参数是一个自然数_[n]_。这个函数的计算结果_[repeat_n X n]_
    是在_[X]_中选出_[n]_个字符串（可以重复）拼接得到的所有字符串的集合。在这个
    Coq定义中，我们对自然数_[n]_递归定义，并且在定义中使用了我们之前定义的
    _[string_set_app]_。

    在此基础之上，_[repeat_any]_定义为所有_[repeat_n]_的并集。该定义中用到了一列
    集合的无穷并，其在Coq中的定义是_[Sets.omega_union]_，他的符号是_[⋃]_，它的
    Latex表示是_[\bigcup]_。这里，我们又把_[repeat_n]_看做了一个一元函数，它的参
    数是一个字符串集合，它的返回值是一列字符串集合，而_[repeat_any]_的定义则是对
    这一类集合去并集。

    至此为止，我们已经完成了正则表达式语义定义的预备工作。下面我们给出正则表达式
    语义的递归定义：*)

Fixpoint reg_denote (r: reg_exp): string -> Prop :=
  match r with
  | Char c => [String c ""]
  | EmptyStr => [""]
  | Union r1 r2 => reg_denote r1 ∪ reg_denote r2
  | App r1 r2 => reg_denote r1 ∘ reg_denote r2
  | Star r1 => repeat_any (reg_denote r1)
  end.

(** 至此，我们可以描述并试图证明正则表达式的许多等价性性质。例如：*)

Check forall r1 r2: reg_exp,
        reg_denote (Union r1 r2) ==
        reg_denote (Union r2 r1).

Check forall r1 r2 r3: reg_exp,
        reg_denote (App r1 (App r2 r3)) ==
        reg_denote (App (App r1 r2) r3).

Check forall r: reg_exp,
        reg_denote (App r EmptyStr) ==
        reg_denote r.

Check forall r: reg_exp,
        reg_denote (App EmptyStr r) ==
        reg_denote r.

Check forall r: reg_exp,
        reg_denote (Star (Star r)) ==
        reg_denote (Star r).

Check forall r: reg_exp,
        reg_denote (App r (Star r)) ==
        reg_denote (App (Star r) r).


