

(** 以下代码会预先导入关于整数的定义、证明以及自动证明指令。*)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Local Open Scope Z.

(** * 归纳类型的又一个例子：二叉树 *)


Inductive tree: Type :=
| Leaf: tree
| Node (l: tree) (v: Z) (r: tree): tree.

(** 这个定义说的是，一棵二叉树要么是一棵空树_[Leaf]_，要么有一棵左子树、有一棵右
    子树外加有一个根节点整数标号。Coq中，我们往往可以使用递归函数定义归纳类型元
    素的性质。Coq中定义递归函数时使用的关键字是_[Fixpoint]_。下面的两个定义通过
    递归定义了二叉树的高度和节点个数。*)

Fixpoint tree_height (t: tree): Z :=
  match t with
  | Leaf => 0
  | Node l v r => Z.max (tree_height l) (tree_height r) + 1
  end.
Fixpoint tree_size (t: tree): Z :=
  match t with
  | Leaf => 0
  | Node l v r => tree_size l + tree_size r + 1
  end.

(** Coq中也可以定义树到树的函数。下面的_[tree_reverse]_函数把二叉树进行了左右翻转。 *)

Fixpoint tree_reverse (t: tree): tree :=
  match t with
  | Leaf => Leaf
  | Node l v r => Node (tree_reverse r) v (tree_reverse l)
  end.

(** 下面画出的是一个二叉树左右翻转的例子。如果_[t]_是左边的树，那么
    _[tree_reverse t]_的计算结果就是右边的树。*)

(**      5                5
        / \              / \
       3   9            9   3
          / \          / \
         8  100      100  8     *)

(** 这个例子中的树以及左右翻转的计算结果都可以在Coq中表示出来：*)

(** Coq表示 *)
Example tree_reverse_example:
  tree_reverse
    (Node
       (Node Leaf 3 Leaf)
       5
       (Node (Node Leaf 8 Leaf) 9 (Node Leaf 100 Leaf)))
  =
  Node
    (Node (Node Leaf 100 Leaf) 9 (Node Leaf 8 Leaf))
    5
    (Node Leaf 3 Leaf).
Proof. reflexivity. Qed.

(** * 结构归纳法证明 *)

(** 我们接下去将证明一些关于_[tree_height]_，_[tree_size]_与_[tree_reverse]_的基
    本性质。我们在证明中将会使用的主要方法是归纳法。*)

(** 相信大家都很熟悉自然数集上的数学归纳法。数学归纳法说的是：如果我们要证明某性
    质_[P]_对于任意自然数_[n]_都成立，那么我可以将证明分为如下两步：*)

(** 奠基步骤：证明_[P 0]_成立；*)
(** 归纳步骤：证明对于任意自然数_[n]_，如果_[P n]_成立，那么_[P (n + 1)]_也成
    立。*)


(** 对二叉树的归纳证明与上面的数学归纳法稍有不同。具体而言，如果我们要证明某性质
    _[P]_对于一切二叉树_[t]_都成立，那么我们只需要证明以下两个结论：*)


(** 奠基步骤：证明_[P Leaf]_成立；*)
(** 归纳步骤：证明对于任意二叉树_[l]_ _[r]_以及任意整数标签_[n]_，如果_[P l]_与
    _[P r]_都成立，那么_[P (Node l n r)]_也成立。*)

(** 这样的证明方法就成为结构归纳法。在Coq中，_[induction]_指令表示：使用结构归纳
    法。下面是几个证明的例子。*)


(** 第一个例子是证明_[tree_size]_与_[tree_reverse]_之间的关系。*)

Lemma reverse_size: forall t,
  tree_size (tree_reverse t) = tree_size t.
Proof.
  intros.
  induction t.
  (** 上面这个指令说的是：对_[t]_结构归纳。Coq会自动将原命题规约为两个证明目标，
      即奠基步骤和归纳步骤。为了增加Coq证明的可读性，我们推荐大家使用bullet记号
      把各个子证明过程分割开来，就像一个一个抽屉或者一个一个文件夹一样。Coq中可
      以使用的bullet标记有：_[+ - * ++ -- **]_ ...*)
  + simpl.
    (** 第一个分支是奠基步骤。这个_[simpl]_指令表示将结论中用到的递归函数根据定
        义化简。*)
    reflexivity.
  + simpl.
    (** 第二个分支是归纳步骤。我们看到证明目标中有两个前提_[IHt1]_以及_[IHt2]_。
        在英文中_[IH]_表示induction hypothesis的缩写，也就是归纳假设。在这个证明
        中_[IHt1]_与_[IHt2]_分别是左子树_[t1]_与右子树_[t2]_的归纳假设。 *)

    rewrite IHt1.
    rewrite IHt2.
    lia.
    (** 这个_[lia]_指令的全称是linear integer arithmatic，可以用来自动证明关于整
        数的线性不等式。*)
Qed.


(** 第二个例子很类似，是证明_[tree_height]_与_[tree_reverse]_之间的关系。*)

Lemma reverse_height: forall t,
  tree_height (tree_reverse t) = tree_height t.
Proof.
  intros.
  induction t.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHt1.
    rewrite IHt2.
    lia.
    (** 注意：这个_[lia]_指令也是能够处理_[Z.max]_与_[Z.min]_的。*)
Qed.

(** 下面我们将通过重写上面这一段证明，介绍Coq证明语言的一些其他功能。*)

Lemma reverse_height_attempt2: forall t,
  tree_height (tree_reverse t) = tree_height t.
Proof.
  intros.
  induction t; simpl.
  (** 在Coq证明语言中可以用分号将小的证明指令连接起来形成大的证明指令，其中
      _[tac1 ; tac2]_这个证明指令表示先执行指令_[tac1]_，再对于_[tac1]_生成的每
      一个证明目标执行_[tac2]_。分号是右结合的。*)
  + reflexivity.
  + simpl.
    lia.
    (** 此处的_[lia]_指令不仅可以处理结论中的整数线性运算，其自动证明过程中也会
        使用前提中关于整数线性运算的假设。*)
Qed.

(** 请各位同学证明下面结论。*)

Lemma reverse_involutive: forall t,
  tree_reverse (tree_reverse t) = t.
Proof.
Admitted. (** *)


Lemma reverse_inv: forall t1 t2,
  tree_reverse t1 = t2 ->
  t1 = tree_reverse t2.
Proof.
Admitted. (** *)



(** * 字符串 *)

(** 以下代码会预先导入关于ascii码与字符串的定义。*)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Local Open Scope string.

(** 字符串的定义 *)
(** 下面Coq代码可以用于查看_[string]_在Coq中的定义。*)
Print string.
(** 查询结果如下。*)
(**
Inductive string :=
| EmptyString : string
| String : ascii -> string -> string. *)

(** 当然，Coq也提供了专门表达字符串的符号。*)


Check EmptyString.
Check "c".
Check "c"%char.
Check String "a"%char (String "b"%char EmptyString).


(** 查询结果 *)
(**
"": string
"c": string
"c"%char: ascii
"ab": string
*)

(** 所以，字符串这样的链状结构其实是树状结构的一种退化情况，也可以用Coq的归纳类
    型定义。下面我们可以定义字符串的拼接和取反。*)

Fixpoint string_app (s1 s2: string): string :=
  match s1 with
  | EmptyString => s2
  | String c s1' => String c (string_app s1' s2)
  end.

Fixpoint string_rev (s: string): string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => string_app (string_rev s') (String c EmptyString)
  end.

(** 接下来我们就可以证明一些简单的性质。 *)


(** 引理_[string_app_assoc]_ *)
Lemma string_app_assoc: forall s1 s2 s3,
  string_app s1 (string_app s2 s3) =
  string_app (string_app s1 s2) s3.
Proof.
  intros.
  induction s1.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHs1.
    reflexivity.
Qed.

(** 引理_[string_app_empty_r]_ *)
Lemma string_app_empty_r: forall s,
  string_app s "" = s.
Proof.
  intros.
  induction s.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHs.
    reflexivity.
Qed.

(** 下面性质请大家自行证明 *)
Lemma string_rev_app: forall s1 s2,
  string_rev (string_app s1 s2) =
  string_app (string_rev s2) (string_rev s1).
Proof.
Admitted. (** *)


(** * 自然数 *)

(** 将字符串等链状结构进一步退化，就会得到Coq中自然数的定义。*)


(** 下面Coq代码可以用于查看_[nat]_在Coq中的定义。*)
Print nat.
(** 查询结果如下。*)
(**
Inductive nat := O : nat | S: nat -> nat. *)

(** 下面我们在Coq中去定义自然数的加法，并且也试着证明一条基本性质：加法交换律。*)


(** 由于Coq的标准库中已经定义了自然数以及自然数的加法。我们开辟一个_[NatDemo]_来
    开发我们自己的定义与证明。以免与Coq标准库的定义相混淆。*)
Module NatDemo.

(** 先定义自然数_[nat]_。*)

Inductive nat :=
| O : nat
| S (n: nat): nat.

(** 再定义自然数加法。*)

Fixpoint plus (n m: nat): nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

(** 下面证明加法交换律。*)

Theorem plus_comm: forall n m,
  plus n m = plus m n.
Proof.
Admitted. (** *)

End NatDemo.

(** * While + DB语言的语法树 *)



Module WhileDB.

(** 先定义变量名，我们规定不同的变量名就是不同的字符串。*)

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
  | ENum (n : Z)
  | EVar (x : var_name)
  | EBinop (op: binop) (e1 e2 : expr)
  | EUnop (op: unop) (e: expr)
  | EDeref (e: expr)
  | EMalloc (e: expr)
  | EReadInt
  | EReadChar.

(** 下面是程序语句的抽象语法树。*)

Inductive com : Type :=
  | CDecl (x: var_name)
  | CAss (e1 e2: expr)
  | CSeq (c1 c2 : com)
  | CIf (e : expr) (c1 c2 : com)
  | CWhile (e : expr) (c : com).

(** 下面我们定义一项简单的程序变换：右结合变换。例如，将_[(c1;c2);c3]_变换为
    _[c1;(c2;c3)]_。*)

(** 首先，这里定义一个辅助函数，该函数假设_[c]_与_[c0]_已经是右结合的，计算
    _[c; c0]_转换后的结果*)
Fixpoint CSeq_right_assoc (c c0: com): com :=
  match c with
  | CSeq c1 c2 => CSeq c1 (CSeq_right_assoc c2 c0)
  | _ => CSeq c c0
  end.

(** 现在，可以在_[CSeq_right_assoc]_的基础上定义右结合变换_[right_assoc]_。*)
Fixpoint right_assoc (c: com): com :=
  match c with
  | CDecl x => CDecl x
  | CAss e1 e2 => CAss e1 e2
  | CSeq c1 c2 => CSeq_right_assoc (right_assoc c1) (right_assoc c2)
  | CIf e c1 c2 => CIf e (right_assoc c1) (right_assoc c2)
  | CWhile e c1 => CWhile e (right_assoc c1)
  end.


End WhileDB.

