Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Psatz.
Require Import PL.CoqInductiveType.
Require Import PL.SetsDomain.
Require Import PL.SemanticsIntro.
Local Open Scope string.
Local Open Scope sets_scope.

(** 之前我们已经学习了如何在Coq中用集合来定义正则表达式的语义。在这一讲中，我们
    将在Coq中证明集合的相关性质，并进一步证明正则表达式的相关性质。*)

(** * 集合与命题 *)

(** 由于集合以及集合间的运算是基于Coq中的命题进行定义的，集合相关性质的证明也可
    以规约为与命题有关的逻辑证明。例如，我们想要证明，交集运算具有交换律：*)

Lemma Sets_intersect_comm: forall (X Y: string -> Prop),
  X ∩ Y == Y ∩ X.
Proof.
  intros.
  (** 下面一条命令_[sets_unfold]_是SetsDomain库提供的自动证明指令，它可以将有关
      集合的性质转化为有关命题的性质。*)
  sets_unfold.
  (** 原本要证明的关于交集的性质现在就转化为了：
        _[forall a : string, X a /\ Y a <-> Y a /\ X a]_
      其中_[forall]_就是逻辑中『任意』的意思；_[/\]_之前我们已经了解，它表示『并
      且』的意思；_[<->]_表示『当且仅当』的意思；_[X a]_可以念做性质_[X]_对于
      _[a]_成立，也可以理解为_[a]_是集合_[X]_的元素。

      我们稍后再来完成相关性质的证明。在Coq中，要放弃当前的证明，可以用下面的
      _[Abort]_指令。*)
Abort.

(** 下面是一条关于并集运算的性质。*)

Lemma Sets_included_union1: forall (X Y: string -> Prop),
  X ⊆ X ∪ Y.
Proof.
  intros.
  sets_unfold.
  (** 经过转化，要证明的结论是：_[forall a : string, X a -> X a \/ Y a]_。这里，
      _[\/]_表示『或者』；_[->]_表示推出，也可以念做『如果...那么...』。*)
Abort.

(** 下面是一条关于一列集合的并集运算的性质。*)

Lemma Sets_included_omega_union0: forall (X: nat -> string -> Prop),
  X 0 ⊆ ⋃ X.
Proof.
  intros.
  sets_unfold.
  (** 经过转化，要证明的结论是：
         _[forall a : string, X 0 a -> exists n : nat, X n a]_
      它表示：对于任意一个字符串_[a]_，如果他是_[X 0]_的元素，那么就存在一个自然
      数_[n]_使得_[a]_是_[X n]_的元素。*)
Abort.

(** * 逻辑命题的证明 *)

(** ** 逻辑命题『真』的证明 *)

(** 我们不需要任何前提就可以推出_[True]_。在Coq标准库中，_[I]_是_[True]_的一个证
    明，我们可以用_[exact I]_来证明_[True]_。*)

Example proving_True_1: 1 < 2 -> True.
Proof.
  intros.
  exact I.
Qed.

Example proving_True_2: 1 > 2 -> True.
Proof.
  intros.
  exact I.
Qed.

(** ** 关于『并且』的证明 *)

(** 要证明『某命题并且某命题』成立，可以在Coq中使用_[split]_证明指令进行证明。该
    指令会将当前的证明目标拆成两个子目标。*)

Lemma True2: True /\ True.
Proof.
  split.
  + exact I.
  + exact I.
Qed.

(** 下面证明一个关于_[/\]_的一般性结论：*)

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB.
  split.
  (** 下面的_[apply]_指令表示在证明中使用一条前提，或者使用一条已经经过证明的定
      理或引理。*)
  + apply HA.
  + apply HB.
Qed.

Example and_exercise :
  forall n m : nat, n + 2*m = 10 -> 2*n + m = 5 -> n = 0 /\ True.
Proof.
  intros.
  split.
  - lia.
  - exact I.
Qed.

(** 如果当前一条前提假设具有『某命题并且某命题』的形式，我们可以在Coq中使用
    _[destruct]_指令将其拆分成为两个前提。 *)

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros.
  destruct H as [HP HQ].
  apply HP.
Qed.

(** _[destruct]_指令也可以不指名拆分后的前提的名字，Coq会自动命名。*)

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros.
  destruct H. 
  (* 这里只用到第二个分支，因此可以用_[_]_把第一个扔掉： _[destruct H as [_ ?]]_ *)
  (* _[?]_ 表示让Coq来命名 *)
  apply H0.
Qed.

(** 当前提与结论中，都有_[/\]_的时候，我们就既需要使用_[split]_指令，又需要使用
    _[destruct]_指令。*)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros.
  destruct H as [HP HQ].
  split.
  - apply HQ.
  - apply HP.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros.
  destruct H as [HP HQR].
  destruct HQR as [HQ HR].
  split.
  - split.
    apply HP. apply HQ.
  - apply HR.
Qed.

(** ** 关于『或』的证明 *)

(** 『或』是另一个重要的逻辑连接词。如果『或』出现在前提中，我们可以用Coq中的
    _[destruct]_指令进行分类讨论。*)

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros.
  destruct H as [H | H].
  + rewrite H.
    lia.
  + rewrite H.
    lia.
Qed.

(** 在上面的例子中，我们对于形如_[A \/ B]_的前提进行分类讨论。要证明_[A \/ B]_能
    推出原结论，就需要证明_[A]_与_[B]_中的任意一个都可以推出原结论。下面是一个一
    般性的结论. *)

Lemma or_example2 :
  forall P Q R: Prop, (P -> R) -> (Q -> R) -> (P \/ Q -> R).
Proof.
  intros.
  destruct H1 as [HP | HQ].
  + apply H.
    (* 注意，_[apply]_指令不一定要前提与结论完全吻合才能使用。此处，只要_[H]_中
       推导的结果与待证明的结论一致，就可以使用_[apply H]_。*)
    apply HP.
  + apply H0 in HQ.
    (* _[apply]_指令还可以在前提中做推导，不过这时需要使用_[apply ... in]_这一语
       法。*)
    apply HQ.
Qed.

(** 相反的，如果要证明一条形如_[A \/ B]_的结论整理，我们就只需要证明_[A]_与_[B]_
    两者之一成立就可以了。在Coq中的指令是：_[left]_与_[right]_。例如，下面是选择
    左侧命题的例子。*)

Lemma or_introl : forall A B : Prop, A -> A \/ B.
Proof.
  intros.
  left.
  apply H.
Qed.

(** 下面是选择右侧命题的例子。*)

Lemma or_intror : forall A B : Prop, B -> A \/ B.
Proof.
  intros.
  right.
  apply H.
Qed.

(** 下面性质请各位自行证明。*)

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros.
  destruct H as [HP | HQ].
  - right. apply HP.
  - left. apply HQ.
Qed.

(** ** 关于『如果...那么...』的证明 *)

(** 事实上，在之前的例子中，我们已经多次证明有关_[->]_的结论了。下面我们在看几个
    例子，并额外介绍几条Coq证明指令。

    下面的证明中，_[pose proof]_表示推导出一个新的结论，并将其用作之后证明中的前
    提。*)

Theorem modus_ponens: forall P Q: Prop,
  P /\ (P -> Q) -> Q.
Proof.
  intros.
  destruct H.
  (** 将_[H0: P -> Q]_作用在_[H: P]_上，我们就可以得出一个新结论：_[Q]_。*)
  pose proof H0 H.
  apply H1.
Qed.

(** 下面我们换一种方法证明。_[revert]_证明指令可以看做_[intros]_的反操作。 *)

Theorem modus_ponens_alter1: forall P Q: Prop,
  P /\ (P -> Q) -> Q.
Proof.
  intros.
  destruct H.
  (** 下面_[revert]_指令将前提中的_[P]_又放回了『结论中的前提』中去。*)
  revert H.
  apply H0.
Qed.

(** 下面我们再换一种方式证明，_[specialize]_指令与_[apply ... in]_指令的效果稍有
    不同。*)

Theorem modus_ponens_alter2: forall P Q: Prop,
  P /\ (P -> Q) -> Q.
Proof.
  intros.
  destruct H.
  specialize (H0 H).
  apply H0.
Qed.

(** 另外，我们可以直接使用_[exact]_指令，这个指令的效果像是_[pose proof]_或者
    _[specialize]_与_[apply]_的组合。*)

Theorem modus_ponens_alter3: forall P Q: Prop,
  P /\ (P -> Q) -> Q.
Proof.
  intros.
  destruct H.
  exact (H0 H).
Qed.

(** ** 关于『否定』与『假』的证明 *)

(** 在Coq中[~]表示否定，_[False]_表示假。如果前提为假，那么，矛盾推出一切。在Coq
    中，这可以用_[contradiction]_指令或_[destruct]_指令完成证明。*)

Theorem ex_falso_quodlibet : forall (P: Prop),
  False -> P.
Proof.
  intros.
  contradiction.
Qed.

Theorem ex_falso_quodlibet_alter : forall (P: Prop),
  False -> P.
Proof.
  intros.
  destruct H.
Qed.

(** _[contradiction]_也可以用于_[P]_与_[~ P]_同时出现在前提中的情况： *)

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~ P) -> Q.
Proof.
  intros.
  destruct H.
  contradiction.
Qed.

(** 除了_[P]_与_[~ P]_不能同时为真之外，他们也不能同时为假，或者说，他们中至少有
    一个要为真。这是Coq标准库中的_[classic]_。 *)

Check classic.

(** 它说的是：_[forall P : Prop, P \/ ~ P]_。下面我们利用它做一些证明。 *)

Theorem double_neg_elim : forall P : Prop,
  ~ ~ P -> P.
Proof.
  intros.
  pose proof classic P. (* 把P塞给_[classic]_里面的前提_[forall P]_ *)
  destruct H0.
  + apply H0.
  + contradiction.
Qed.

Theorem not_False :
  ~ False.
Proof.
  pose proof classic False.
  destruct H.
  - contradiction.
  - apply H.
Qed.

Theorem double_neg_intro : forall P : Prop,
  P -> ~ ~ P.
Proof.
  intros.
  pose proof classic (~ P).
  destruct H0.
  - contradiction.
  - apply H0.
Qed.

(** ** 关于『当且仅当』的证明 *)

(** 在Coq中，_[<->]_符号对应的定义是_[iff]_，其将_[P <-> Q]_定义为
          _[(P -> Q) /\ (Q -> P)]_
    因此，要证明关于『当且仅当』的性质，首先可以使用其定义进行证明。*)

Theorem iff_refl: forall P: Prop, P <-> P.
Proof.
  intros.
  unfold iff.
  split.
  + intros.
    apply H.
  + intros.
    apply H.
Qed.    

Theorem iff_imply: forall P Q: Prop, (P <-> Q) -> (P -> Q).
Proof.
  intros P Q H.
  unfold iff in H.
  destruct H.
  exact H.
Qed.

(** 当某前提假设具有形式_[P <-> Q]_，那我们也可以使用_[apply]_指令进行证明。*)

Theorem iff_imply_alter: forall P Q: Prop, (P <-> Q) -> (P -> Q).
Proof.
  intros.
  apply H.
  apply H0.
Qed.

(** 另外，_[rewrite]_指令也可以使用形如_[P <-> Q]_的等价性前提。*)

Theorem iff_imply_alter2: forall P Q: Prop, (P <-> Q) -> (P -> Q).
Proof.
  intros.
  rewrite <- H.
  apply H0.
Qed.

Theorem iff_imply_alter3: forall P Q: Prop, (P <-> Q) -> (P -> Q).
Proof.
  intros P Q.
  tauto. (* tautology, 重言式 *)
Qed.

(** ** 关于『存在』的证明 *)

(** 当待证明结论形为：存在一个_[x]_使得...，那么可以用_[exists]_指明究竟哪个
    _[x]_使得该性质成立。*)

Lemma four_is_even : exists n, 4 = n + n.
Proof.
  exists 2.
  lia.
Qed.

Lemma six_is_not_prime: exists n, 2 <= n < 6 /\ exists q, n * q = 6.
Proof.
  exists 2.
  split.
  + lia.
  + exists 3.
    lia.
Qed.

(** 当某前提形为：存在一个_[x]_使得...，那么可以使用Coq中的_[destruct]_指令进行
    证明。这一证明指令相当于数学证明中的：任意给定一个这样的_[x]_。 *)

Theorem exists_example : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros.
  destruct H as [m H].
  exists (2 + m).
  lia.
Qed.

Theorem dist_exists_and : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
Proof.
  intros.
  destruct H as [x [HP HQ]].
  split.
  - exists x.
    apply HP.
  - exists x.
    apply HQ.
Qed.

Theorem exists_exists : forall (X Y:Type) (P : X -> Y -> Prop),
  (exists x y, P x y) <-> (exists y x, P x y).
Proof.
  intros.
  unfold iff.
  split.
  - intros H. destruct H as [x' [y' H']].
    exists y'. exists x'. apply H'.
  - intros H. destruct H as [x' [y' H']].
    exists y'. exists x'. apply H'.
Qed.

(** * 集合性质的证明 *)

Lemma Sets_intersect_comm: forall (X Y: string -> Prop),
  X ∩ Y == Y ∩ X.
Proof.
  intros.
  sets_unfold.
  (* 此处可直接用_[tauto]_ *)
  intros.
  unfold iff.
  split.
  - apply and_commut.
  - apply and_commut.
Qed.

Lemma Sets_included_union1: forall (X Y: string -> Prop),
  X ⊆ X ∪ Y.
Proof.
  intros.
  sets_unfold.
  intros.
  left.
  apply H.
Qed.

Lemma Sets_included_omega_union0: forall (X: nat -> string -> Prop),
  X 0 ⊆ ⋃ X.
Proof.
  intros.
  sets_unfold.
  intros.
  exists 0.
  apply H.
Qed.

(* reg_denote (app r EmptyStr) == reg_denote r *)
Lemma string_set_app_empty_string_r: forall X: string -> Prop,
  X ∘ [""] == X.
Proof.
  intros.
  unfold string_set_app; sets_unfold.
  intros.
  split; intros.
  - destruct H as [s1 [s2 [? [? ?]]]].
    rewrite H1.
    rewrite <- H0.
    rewrite string_app_empty_r.
    exact H.
  - exists a, "".
    split.
    -- apply H.
    -- split.
       --- reflexivity.
       --- rewrite string_app_empty_r.
           reflexivity.
Qed.

Lemma string_set_app_assoc: forall X Y Z: string -> Prop,
  X ∘ (Y ∘ Z) == (X ∘ Y) ∘ Z.
Proof.
  intros.
  unfold string_set_app; sets_unfold.
  intros.
  split.
  - intros H.
    destruct H as [s1 H].
    destruct H as [s2 H].
    destruct H as [H1 H2].
    destruct H2 as [H2 H3].
    destruct H2 as [s3 [s4 H2]].
    destruct H2 as [H21 [H22 H23]].
    exists (string_app s1 s3). exists s4.
    split.
    -- exists s1. exists s3.
       split.
       --- apply H1.
       --- split.
           * apply H21.
           * reflexivity.
    -- split.
       --- apply H22.
       --- rewrite <- string_app_assoc.
           rewrite <- H23.
           rewrite <- H3.
           reflexivity.
  - intros H. 
    destruct H as [s1 [s2 H]].
    destruct H as [H1 H2].
    destruct H2 as [H2 H3].
    destruct H1 as [s3 [s4 H1]].
    destruct H1 as [H11 H12].
    destruct H12 as [H12 H13].
    exists s3. exists (string_app s4 s2).
    split.
    -- apply H11.
    -- split.
       --- exists s4. exists s2.
           split.
           * apply H12.
           * split.
             ** apply H2.
             ** reflexivity.
       --- rewrite string_app_assoc. 
           rewrite <- H13.
           rewrite <- H3.
           reflexivity.
Qed.
