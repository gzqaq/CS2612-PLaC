Require Import Coq.ZArith.ZArith.
Require Import PL.SetsDomain.
Require Import PL.RTClosure.
Require Import PL.DenotationalSemantics.
Require Import compcert.lib.Integers.
Import WhileD_Expr WhileD_Cmd.
Local Open Scope Z.
Local Open Scope sets_scope.


(** * 小步语义的定义 *)













Inductive expr_ectx: Type :=
| KBinopL (op: binop) (e: expr)
| KBinopR (i: int64) (op: binop)
| KUnop (op: unop)
| KDeref.

Inductive expr_loc: Type :=
| EL_Value (i: int64)
| EL_FocusedExpr (e: expr)
| EL_Cont (el: expr_loc) (k: expr_ectx).


Inductive expr_com_ectx: Type :=
| KWhileCond (e: expr) (c: com)
| KIf (c1 c2: com)
| KAsgnVar (x: var_name)
| KAsgnMemL (e: expr)
| KAsgnMemR (i: int64).

Inductive com_ectx: Type :=
| KSeq (c: com)
| KWhileBody (e: expr) (c: com).

Inductive com_loc: Type :=
| CL_Finished
| CL_FocusedCom (c: com)
| CL_ECont (el: expr_loc) (k: expr_com_ectx)
| CL_CCont (cl: com_loc) (k: com_ectx).




(** Coq预备定义 *)

Definition short_circuit (op: binop) (i i': int64): Prop :=
  match op with
  | OAnd => i = Int64.repr 0 /\ i' = Int64.repr 0
  | OOr => Int64.signed i <> 0 /\ i' = Int64.repr 1
  | _ => False
  end.

Definition no_short_circuit (op: binop) (i: int64): Prop :=
  match op with
  | OAnd => Int64.signed i <> 0
  | OOr => i = Int64.repr 0
  | _ => True
  end.

Definition arith_compute1
             (Zfun: Z -> Z -> Z)
             (int64fun: int64 -> int64 -> int64)
             (n1 n2 n: int64): Prop :=
    n = int64fun n1 n2 /\
    Zfun (Int64.signed n1) (Int64.signed n2)
      <= Int64.max_signed /\
    Zfun (Int64.signed n1) (Int64.signed n2)
      >= Int64.min_signed.

Definition arith_compute2
             (int64fun: int64 -> int64 -> int64)
             (n1 n2 n: int64): Prop :=
    n = int64fun n1 n2 /\
    Int64.signed n2 <> 0 /\
    (Int64.signed n1 <> Int64.min_signed \/
     Int64.signed n2 <> - 1).

Definition cmp_compute
             (c: comparison)
             (n1 n2 n: int64): Prop :=
    n = if Int64.cmp c n1 n2 then Int64.repr 1 else Int64.repr 0.

Definition bool_compute (n1 n2 n: int64): Prop :=
  n2 = Int64.repr 0 /\ n = Int64.repr 0 \/
  Int64.signed n2 <> 0 /\ n = Int64.repr 1.

Definition binop_compute (op: binop):
  int64 -> int64 -> int64 -> Prop :=
  match op with
  | OOr => bool_compute
  | OAnd => bool_compute
  | OLt => cmp_compute Clt
  | OLe => cmp_compute Cle
  | OGt => cmp_compute Cgt
  | OGe => cmp_compute Cge
  | OEq => cmp_compute Ceq
  | ONe => cmp_compute Cne
  | OPlus => arith_compute1 Z.add Int64.add
  | OMinus => arith_compute1 Z.sub Int64.sub
  | OMul => arith_compute1 Z.mul Int64.mul
  | ODiv => arith_compute2 Int64.divs
  | OMod => arith_compute2 Int64.mods
  end.

Definition neg_compute (n0 n: int64): Prop :=
  n = Int64.neg n0 /\
  Int64.signed n0 <> Int64.min_signed.

Definition not_compute (n0 n: int64): Prop :=
  Int64.signed n0 <> 0 /\ n = Int64.repr 0 \/
  n0 = Int64.repr 0 /\ n = Int64.repr 1.

Definition unop_compute (op: unop):
  int64 -> int64 -> Prop :=
  match op with
  | ONeg => neg_compute
  | ONot => not_compute
  end.

(** 表达式求值小步语义的Coq定义 *)


Inductive estep (s: prog_state):
  expr_loc -> expr_loc -> Prop :=
| ES_Var: forall (x: var_name),
    estep s
      (EL_FocusedExpr (EVar x))
      (EL_Value (s.(vars) x))
| ES_Const: forall (n: Z),
    n <= Int64.max_signed ->
    n >= Int64.min_signed ->
    estep s
      (EL_FocusedExpr (ENum n))
      (EL_Value (Int64.repr n))

| ES_BinopL: forall op e1 e2,
    estep s
      (EL_FocusedExpr (EBinop op e1 e2))
      (EL_Cont (EL_FocusedExpr e1) (KBinopL op e2))
| ES_BinopR_SC: forall op n1 n1' e2,
    short_circuit op n1 n1' ->
    estep s
      (EL_Cont (EL_Value n1) (KBinopL op e2))
      (EL_Value n1')
| ES_BinopR_NSC: forall op n1 e2,
    no_short_circuit op n1 ->
    estep s
      (EL_Cont (EL_Value n1) (KBinopL op e2))
      (EL_Cont (EL_FocusedExpr e2) (KBinopR n1 op))
| ES_BinopStep: forall op n1 n2 n,
    binop_compute op n1 n2 n ->
    estep s
      (EL_Cont (EL_Value n2) (KBinopR n1 op))
      (EL_Value n)

| ES_Unop: forall op e,
    estep s
      (EL_FocusedExpr (EUnop op e))
      (EL_Cont (EL_FocusedExpr e) (KUnop op))
| ES_UnopStep: forall op n0 n,
    unop_compute op n0 n ->
    estep s
      (EL_Cont (EL_Value n0) (KUnop op))
      (EL_Value n)
| ES_Deref: forall e,
    estep s
      (EL_FocusedExpr (EDeref e))
      (EL_Cont (EL_FocusedExpr e) KDeref)
| ES_DerefStep: forall n0 n,
    s.(mem) n0 = Some n ->
    estep s
      (EL_Cont (EL_Value n0) KDeref)
      (EL_Value n)

| ES_Cont: forall el1 el2 k,
    estep s el1 el2 ->
    estep s (EL_Cont el1 k) (EL_Cont el2 k).




(** 程序运行小步语义的Coq定义 *)


Inductive cstep:
  com_loc * prog_state -> com_loc * prog_state -> Prop :=
| CS_AsgnVar: forall s x e,
    cstep
      (CL_FocusedCom (CAss (EVar x) e), s)
      (CL_ECont (EL_FocusedExpr e) (KAsgnVar x), s)
| CS_AsgnVarStep: forall s1 s2 x n,
    s2.(vars) x = n ->
    (forall y, x <> y -> s1.(vars) y = s2.(vars) y) ->
    (forall p, s1.(mem) p = s2.(mem) p) ->
    cstep
      (CL_ECont (EL_Value n) (KAsgnVar x), s1)
      (CL_Finished, s2)

| CS_AsgnMemL: forall s e1 e2,
    cstep
      (CL_FocusedCom (CAss (EDeref e1) e2), s)
      (CL_ECont (EL_FocusedExpr e1) (KAsgnMemL e2), s)
| CS_AsgnMemR: forall s n1 e2,
    cstep
      (CL_ECont (EL_Value n1) (KAsgnMemL e2), s)
      (CL_ECont (EL_FocusedExpr e2) (KAsgnMemR n1), s)
| CS_AsgnMemStep: forall s1 s2 n1 n2,
    s1.(mem) n1 <> None ->
    s2.(mem) n1 = Some n2 ->
    (forall x, s1.(vars) x = s2.(vars) x) ->
    (forall p, n1 <> p -> s1.(mem) p = s2.(mem) p) ->
    cstep
      (CL_ECont (EL_Value n2) (KAsgnMemR n1), s1)
      (CL_Finished, s2)

| CS_Seq: forall s c1 c2,
    cstep
      (CL_FocusedCom (CSeq c1 c2), s)
      (CL_CCont (CL_FocusedCom c1) (KSeq c2), s)
| CS_SeqStep: forall s c,
    cstep
      (CL_CCont CL_Finished (KSeq c), s)
      (CL_FocusedCom c, s)

| CS_If: forall s e c1 c2,
    cstep
      (CL_FocusedCom (CIf e c1 c2), s)
      (CL_ECont (EL_FocusedExpr e) (KIf c1 c2), s)
| CS_IfStepTrue: forall s n c1 c2,
    Int64.signed n <> 0 ->
    cstep
      (CL_ECont (EL_Value n) (KIf c1 c2), s)
      (CL_FocusedCom c1, s)
| CS_IfStepFalse: forall s n c1 c2,
    n = Int64.repr 0 ->
    cstep
      (CL_ECont (EL_Value n) (KIf c1 c2), s)
      (CL_FocusedCom c2, s)

| CS_WhileBegin: forall s e c,
    cstep
      (CL_FocusedCom (CWhile e c), s)
      (CL_ECont (EL_FocusedExpr e) (KWhileCond e c), s)
| CS_WhileStepTrue: forall s n e c,
    Int64.signed n <> 0 ->
    cstep
      (CL_ECont (EL_Value n) (KWhileCond e c), s)
      (CL_CCont (CL_FocusedCom c) (KWhileBody e c), s)
| CS_WhileStepFalse: forall s n e c,
    n = Int64.repr 0 ->
    cstep
      (CL_ECont (EL_Value n) (KWhileCond e c), s)
      (CL_Finished, s)
| CS_WhileRestart: forall s e c,
    cstep
      (CL_CCont CL_Finished (KWhileBody e c), s)
      (CL_ECont (EL_FocusedExpr e) (KWhileCond e c), s)

| CS_ECont: forall el1 el2 s k,
    estep s el1 el2 ->
    cstep (CL_ECont el1 k, s) (CL_ECont el2 k, s)
| CS_CCont: forall cl1 s1 cl2 s2 k,
    cstep (cl1, s1) (cl2, s2) ->
    cstep (CL_CCont cl1 k, s1) (CL_CCont cl2 k, s2).





(** * 小步语义与指称语义之间的关系 *)






(** Coq中定义多步关系 *)
Definition multi_estep (s: prog_state):
  expr_loc -> expr_loc -> Prop :=
  clos_refl_trans (estep s).
Definition multi_cstep:
  com_loc * prog_state -> com_loc * prog_state -> Prop :=
  clos_refl_trans cstep.


Check clos_refl_trans.
Print clos_refl_trans.







(** 多步关系的基本性质 *)
Lemma MES_Cont: forall s el1 el2 k,
  multi_estep s el1 el2 ->
  multi_estep s (EL_Cont el1 k) (EL_Cont el2 k).
Proof.
  intros.
  induction_1n H.  (* 将n步长的MES拆为1+n步, el0->el1->*el2 *)
  + reflexivity.  (* 自反传递闭包的自反性 *)
  + transitivity_1n (EL_Cont el1 k).
    - apply ES_Cont; tauto.
    - tauto.
Qed.

(* 从MES的右边开始归纳 *)
Lemma MES_Cont': forall s el1 el2 k,
  multi_estep s el1 el2 ->
  multi_estep s (EL_Cont el1 k) (EL_Cont el2 k).
Proof.
  intros.
  induction_n1 H.  (* 将n步长的MES拆为n+1步, el1->*el2->el0 *)
  + reflexivity.  (* 自反传递闭包的自反性 *)
  + transitivity_n1 (EL_Cont el2 k).
    - tauto.
    - apply ES_Cont; tauto.
Qed.


Lemma MCS_ECont: forall s el1 el2 k,
  multi_estep s el1 el2 ->
  multi_cstep (CL_ECont el1 k, s) (CL_ECont el2 k, s).
Proof.
  intros.
  induction_1n H.
  + reflexivity.
  + transitivity_1n (CL_ECont el1 k, s).
    - apply CS_ECont; tauto.
    - tauto.
Qed.

Lemma MCS_CCont: forall cl1 s1 cl2 s2 k,
  multi_cstep (cl1, s1) (cl2, s2) ->
  multi_cstep (CL_CCont cl1 k, s1) (CL_CCont cl2 k, s2).
Proof.
  intros.
  induction_1n H.
  + reflexivity.
  + transitivity_1n (CL_CCont c k, p).
    - apply CS_CCont; tauto.
    - tauto.
Qed.










(** 首先证明表达式的情况，利用结构归纳进行证明。*)

Lemma eeval_multi_estep: forall e s n,
  eeval e s n ->
  multi_estep s (EL_FocusedExpr e) (EL_Value n).
(* 大方向：对表达式e的语法树归纳 *)
Proof.
  intros.
  revert n H; induction e; simpl; intros.
  + unfold const_denote in H.
    etransitivity_1n; [| reflexivity].
    destruct H.
    subst n0.
    constructor; tauto.
  + unfold var_denote in H.
    subst n.
    etransitivity_1n; [| reflexivity].
    constructor.
  + destruct op; simpl in H.
    - etransitivity_1n; [constructor |].
      unfold or_denote in H.
      destruct H as [? | [? | ?] ].
      * destruct H as [n1 [? [? ?] ] ].
        specialize (IHe1 _ H).
        etransitivity; [apply MES_Cont, IHe1 |].
        etransitivity_1n; [| reflexivity].
        apply ES_BinopR_SC.
        simpl.
        tauto.
      * destruct H as [n2 [? [? [? ?] ] ] ].
        specialize (IHe1 _ H).
        specialize (IHe2 _ H0).
        etransitivity; [apply MES_Cont, IHe1 |].
        etransitivity_1n; [apply ES_BinopR_NSC; simpl; tauto |].
        etransitivity; [apply MES_Cont, IHe2 |].
        etransitivity_1n; [| reflexivity].
        constructor.
        simpl.
        unfold bool_compute.
        tauto.
      * destruct H as [? [? ?] ].
        specialize (IHe1 _ H).
        specialize (IHe2 _ H0).
        etransitivity; [apply MES_Cont, IHe1 |].
        etransitivity_1n; [apply ES_BinopR_NSC; simpl; tauto |].
        etransitivity; [apply MES_Cont, IHe2 |].
        etransitivity_1n; [| reflexivity].
        constructor.
        simpl.
        unfold bool_compute.
        tauto.
    - etransitivity_1n; [constructor |].
      unfold or_denote in H.
      destruct H as [? | [? | ?] ].
      * destruct H as [? ?].
        specialize (IHe1 _ H).
        etransitivity; [apply MES_Cont, IHe1 |].
        etransitivity_1n; [| reflexivity].
        apply ES_BinopR_SC.
        simpl.
        tauto.
      * destruct H as [n1 [? [? [? ?] ] ] ].
        specialize (IHe1 _ H).
        specialize (IHe2 _ H0).
        etransitivity; [apply MES_Cont, IHe1 |].
        etransitivity_1n; [apply ES_BinopR_NSC; simpl; tauto |].
        etransitivity; [apply MES_Cont, IHe2 |].
        etransitivity_1n; [| reflexivity].
        constructor.
        simpl.
        unfold bool_compute.
        tauto.
      * destruct H as [n1 [n2 [? [? [? [? ?] ] ] ] ] ].
        specialize (IHe1 _ H).
        specialize (IHe2 _ H0).
        etransitivity; [apply MES_Cont, IHe1 |].
        etransitivity_1n; [apply ES_BinopR_NSC; simpl; tauto |].
        etransitivity; [apply MES_Cont, IHe2 |].
        etransitivity_1n; [| reflexivity].
        constructor.
        simpl.
        unfold bool_compute.
        tauto.
    - unfold cmp_denote in H.
      destruct H as [n1 [n2 [? [? ?] ] ] ].
      specialize (IHe1 _ H).
      specialize (IHe2 _ H0).
      etransitivity_1n; [constructor |].
      etransitivity; [apply MES_Cont, IHe1 |].
      etransitivity_1n; [apply ES_BinopR_NSC; simpl; tauto |].
      etransitivity; [apply MES_Cont, IHe2 |].
      etransitivity_1n; [| reflexivity].
      constructor.
      simpl.
      unfold cmp_compute.
      tauto.
    - unfold cmp_denote in H.
      destruct H as [n1 [n2 [? [? ?] ] ] ].
      specialize (IHe1 _ H).
      specialize (IHe2 _ H0).
      etransitivity_1n; [constructor |].
      etransitivity; [apply MES_Cont, IHe1 |].
      etransitivity_1n; [apply ES_BinopR_NSC; simpl; tauto |].
      etransitivity; [apply MES_Cont, IHe2 |].
      etransitivity_1n; [| reflexivity].
      constructor.
      simpl.
      unfold cmp_compute.
      tauto.
    - unfold cmp_denote in H.
      destruct H as [n1 [n2 [? [? ?] ] ] ].
      specialize (IHe1 _ H).
      specialize (IHe2 _ H0).
      etransitivity_1n; [constructor |].
      etransitivity; [apply MES_Cont, IHe1 |].
      etransitivity_1n; [apply ES_BinopR_NSC; simpl; tauto |].
      etransitivity; [apply MES_Cont, IHe2 |].
      etransitivity_1n; [| reflexivity].
      constructor.
      simpl.
      unfold cmp_compute.
      tauto.
    - unfold cmp_denote in H.
      destruct H as [n1 [n2 [? [? ?] ] ] ].
      specialize (IHe1 _ H).
      specialize (IHe2 _ H0).
      etransitivity_1n; [constructor |].
      etransitivity; [apply MES_Cont, IHe1 |].
      etransitivity_1n; [apply ES_BinopR_NSC; simpl; tauto |].
      etransitivity; [apply MES_Cont, IHe2 |].
      etransitivity_1n; [| reflexivity].
      constructor.
      simpl.
      unfold cmp_compute.
      tauto.
    - unfold cmp_denote in H.
      destruct H as [n1 [n2 [? [? ?] ] ] ].
      specialize (IHe1 _ H).
      specialize (IHe2 _ H0).
      etransitivity_1n; [constructor |].
      etransitivity; [apply MES_Cont, IHe1 |].
      etransitivity_1n; [apply ES_BinopR_NSC; simpl; tauto |].
      etransitivity; [apply MES_Cont, IHe2 |].
      etransitivity_1n; [| reflexivity].
      constructor.
      simpl.
      unfold cmp_compute.
      tauto.
    - unfold cmp_denote in H.
      destruct H as [n1 [n2 [? [? ?] ] ] ].
      specialize (IHe1 _ H).
      specialize (IHe2 _ H0).
      etransitivity_1n; [constructor |].
      etransitivity; [apply MES_Cont, IHe1 |].
      etransitivity_1n; [apply ES_BinopR_NSC; simpl; tauto |].
      etransitivity; [apply MES_Cont, IHe2 |].
      etransitivity_1n; [| reflexivity].
      constructor.
      simpl.
      unfold cmp_compute.
      tauto.
    - unfold arith_denote1 in H.
      destruct H as [n1 [n2 [? [? [? [? ?] ] ] ] ] ].
      specialize (IHe1 _ H).
      specialize (IHe2 _ H0).
      etransitivity_1n; [constructor |].
      etransitivity; [apply MES_Cont, IHe1 |].
      etransitivity_1n; [apply ES_BinopR_NSC; simpl; tauto |].
      etransitivity; [apply MES_Cont, IHe2 |].
      etransitivity_1n; [| reflexivity].
      constructor.
      simpl.
      unfold arith_compute1.
      tauto.
    - unfold arith_denote1 in H.
      destruct H as [n1 [n2 [? [? [? [? ?] ] ] ] ] ].
      specialize (IHe1 _ H).
      specialize (IHe2 _ H0).
      etransitivity_1n; [constructor |].
      etransitivity; [apply MES_Cont, IHe1 |].
      etransitivity_1n; [apply ES_BinopR_NSC; simpl; tauto |].
      etransitivity; [apply MES_Cont, IHe2 |].
      etransitivity_1n; [| reflexivity].
      constructor.
      simpl.
      unfold arith_compute1.
      tauto.
    - unfold arith_denote1 in H.
      destruct H as [n1 [n2 [? [? [? [? ?] ] ] ] ] ].
      specialize (IHe1 _ H).
      specialize (IHe2 _ H0).
      etransitivity_1n; [constructor |].
      etransitivity; [apply MES_Cont, IHe1 |].
      etransitivity_1n; [apply ES_BinopR_NSC; simpl; tauto |].
      etransitivity; [apply MES_Cont, IHe2 |].
      etransitivity_1n; [| reflexivity].
      constructor.
      simpl.
      unfold arith_compute1.
      tauto.
    - unfold arith_denote2 in H.
      destruct H as [n1 [n2 [? [? [? [? ?] ] ] ] ] ].
      specialize (IHe1 _ H).
      specialize (IHe2 _ H0).
      etransitivity_1n; [constructor |].
      etransitivity; [apply MES_Cont, IHe1 |].
      etransitivity_1n; [apply ES_BinopR_NSC; simpl; tauto |].
      etransitivity; [apply MES_Cont, IHe2 |].
      etransitivity_1n; [| reflexivity].
      constructor.
      simpl.
      unfold arith_compute2.
      tauto.
    - unfold arith_denote2 in H.
      destruct H as [n1 [n2 [? [? [? [? ?] ] ] ] ] ].
      specialize (IHe1 _ H).
      specialize (IHe2 _ H0).
      etransitivity_1n; [constructor |].
      etransitivity; [apply MES_Cont, IHe1 |].
      etransitivity_1n; [apply ES_BinopR_NSC; simpl; tauto |].
      etransitivity; [apply MES_Cont, IHe2 |].
      etransitivity_1n; [| reflexivity].
      constructor.
      simpl.
      unfold arith_compute2.
      tauto.
  + destruct op; simpl in H.
    - unfold not_denote in H.
      destruct H as [H | H].
      * destruct H as [n0 [? [? ? ] ] ].
        specialize (IHe _ H).
        etransitivity_1n; [constructor |].
        etransitivity; [apply MES_Cont, IHe |].
        etransitivity_1n; [| reflexivity].
        constructor.
        simpl.
        unfold not_compute.
        tauto.
      * destruct H as [? ?].
        specialize (IHe _ H).
        etransitivity_1n; [constructor |].
        etransitivity; [apply MES_Cont, IHe |].
        etransitivity_1n; [| reflexivity].
        constructor.
        simpl.
        unfold not_compute.
        tauto.
    - unfold neg_denote in H.
      destruct H as [n0 [? [? ? ] ] ].
      specialize (IHe _ H).
      etransitivity_1n; [constructor |].
      etransitivity; [apply MES_Cont, IHe |].
      etransitivity_1n; [| reflexivity].
      constructor.
      simpl.
      unfold neg_compute.
      tauto.
  + unfold deref_denote in H.
    destruct H as [n0 [? ?] ].
    specialize (IHe _ H).
    etransitivity_1n; [constructor |].
    etransitivity; [apply MES_Cont, IHe |].
    etransitivity_1n; [| reflexivity].
    constructor.
    tauto.
Qed.






Lemma ceval_multi_cstep: forall c s1 s2,
  (ceval c).(fin) s1 s2 ->
  multi_cstep (CL_FocusedCom c, s1) (CL_Finished, s2).
Proof.
  intros c.
  induction c; simpl; intros.
  + destruct e1; try tauto.
    - unfold asgn_var_denote in H; simpl in H.
      destruct H as [n [? [? [? ?] ] ] ].
      pose proof eeval_multi_estep _ _ _ H.
      etransitivity_1n; [constructor |].
      etransitivity; [apply MCS_ECont, H3 |].
      etransitivity_1n; [| reflexivity].
      constructor; tauto.
    - unfold asgn_deref_denote in H; simpl in H.
      destruct H as [n1 [n2 [? [? [? [? [? ?] ] ] ] ] ] ].
      pose proof eeval_multi_estep _ _ _ H.
      pose proof eeval_multi_estep _ _ _ H0.
      etransitivity_1n; [constructor |].
      etransitivity; [apply MCS_ECont, H5 |].
      etransitivity_1n; [constructor |].
      etransitivity; [apply MCS_ECont, H6 |].
      etransitivity_1n; [| reflexivity].
      constructor; tauto.
  + unfold BinRel.concat in H.
    destruct H as [s1' [? ?] ].
    specialize (IHc1 _ _ H).
    specialize (IHc2 _ _ H0).
    etransitivity_1n; [constructor |].
    etransitivity; [apply MCS_CCont, IHc1 |].
    etransitivity_1n; [constructor |].
    etransitivity; [apply IHc2 |].
    reflexivity.
  + destruct H as [H | H]; unfold BinRel.concat in H.
    - destruct H as [s1' [? ?] ].
      unfold test1 in H.
      destruct H as [n [? [? ?] ] ]; subst s1'.
      pose proof eeval_multi_estep _ _ _ H1.
      specialize (IHc1 _ _ H0).
      etransitivity_1n; [constructor |].
      etransitivity; [apply MCS_ECont, H |].
      etransitivity_1n; [constructor; tauto |].
      apply IHc1.
    - destruct H as [s1' [? ?] ].
      unfold test0 in H.
      destruct H as [? ?]; subst s1'.
      pose proof eeval_multi_estep _ _ _ H1.
      specialize (IHc2 _ _ H0).
      etransitivity_1n; [constructor |].
      etransitivity; [apply MCS_ECont, H |].
      etransitivity_1n; [constructor; tauto |].
      apply IHc2.
  + etransitivity_1n; [constructor |].
    unfold BW_LFix in H.
    unfold omega_lub, oLub_while_fin in H.
    destruct H as [n ?].
    revert s1 H; induction n; simpl; intros.
    - unfold bot, Bot_while_fin in H.
      contradiction.
    - destruct H.
      * destruct H as [s1' [? ?]].
        destruct H0 as [s1'' [? ?]].
        specialize (IHn _ H1); clear H1.
        unfold test1 in H.
        destruct H as [n0 [? [? ?] ] ]; subst s1'.
        pose proof eeval_multi_estep _ _ _ H1.
        etransitivity; [apply MCS_ECont, H |].
        etransitivity_1n; [constructor; tauto |].
        specialize (IHc _ _ H0).
        etransitivity; [apply MCS_CCont, IHc |].
        etransitivity_1n; [constructor |].
        apply IHn.
      * destruct H as [? ?].
        subst s2.
        pose proof eeval_multi_estep _ _ _ H0.
        etransitivity; [apply MCS_ECont, H |].
        etransitivity_1n; [constructor; tauto |].
        reflexivity.
Qed.





(** 先定义后续表达式求值的指称语义 *)
Definition binop_compute_step1
             (op: binop)
             (n1: int64)
             (D2: int64 -> Prop)
             (n: int64): Prop :=


  match op with
  | OOr => Int64.signed n1 <> 0 /\ n = Int64.repr 1 \/
           (exists n2,
              n1 = Int64.repr 0 /\
              D2 n2 /\
              Int64.signed n2 <> 0 /\
              n = Int64.repr 1) \/
           (n1 = Int64.repr 0 /\
            D2 (Int64.repr 0) /\
            n = Int64.repr 0)


  | OAnd => n1 = Int64.repr 0 /\ n = Int64.repr 0 \/
            (Int64.signed n1 <> 0 /\
             D2 (Int64.repr 0) /\
             n = Int64.repr 0) \/
            (exists n2,
               Int64.signed n1 <> 0 /\
               D2 n2 /\
               Int64.signed n2 <> 0 /\
               n = Int64.repr 1)
  | _ => exists n2, D2 n2 /\ binop_compute op n1 n2 n
  end.


Definition ek_eval (k: expr_ectx):
  prog_state -> int64 -> int64 -> Prop :=
  match k with
  | KBinopL op e2 => fun s n1 n =>
      binop_compute_step1 op n1 (eeval e2 s) n
  | KBinopR n1 op => fun s n2 n =>
      binop_compute op n1 n2 n
  | KUnop op => fun s n0 n =>
      unop_compute op n0 n
  | KDeref => fun s n0 n =>
      s.(mem) n0 = Some n
  end.


Fixpoint el_eval (el: expr_loc):
  prog_state -> int64 -> Prop :=
  match el with
  | EL_Value n0 => fun s n =>
      n = n0
  | EL_FocusedExpr e =>
      eeval e
  | EL_Cont el k => fun s n =>
      exists n0, el_eval el s n0 /\ ek_eval k s n0 n
  end.







(** 再证明一条辅助性质 *)
Lemma binop_compute_step1_binop_denote:
  forall s op (D1 D2: prog_state -> int64 -> Prop) n1 n,
    D1 s n1 ->
    binop_compute_step1 op n1 (D2 s) n ->
    binop_denote op D1 D2 s n.
Proof.
  intros.
  destruct op; simpl in *.
  + unfold or_denote.
    destruct H0 as [? | [? | ?]]; [left | right; left | right; right].
    - exists n1.
      tauto.
    - destruct H0 as [n2 [? ?]]; exists n2.
      subst; tauto.
    - destruct H0 as [? ?].
      subst; tauto.
  + unfold and_denote.
    destruct H0 as [? | [? | ?]]; [left | right; left | right; right].
    - destruct H0 as [? ?].
      subst; tauto.
    - exists n1.
      tauto.
    - destruct H0 as [n2 [? ?]]; exists n1, n2.
      subst; tauto.
  + unfold cmp_denote; unfold cmp_compute in H0.
    destruct H0 as [n2 ?]; exists n1, n2; tauto.
  + unfold cmp_denote; unfold cmp_compute in H0.
    destruct H0 as [n2 ?]; exists n1, n2; tauto.
  + unfold cmp_denote; unfold cmp_compute in H0.
    destruct H0 as [n2 ?]; exists n1, n2; tauto.
  + unfold cmp_denote; unfold cmp_compute in H0.
    destruct H0 as [n2 ?]; exists n1, n2; tauto.
  + unfold cmp_denote; unfold cmp_compute in H0.
    destruct H0 as [n2 ?]; exists n1, n2; tauto.
  + unfold cmp_denote; unfold cmp_compute in H0.
    destruct H0 as [n2 ?]; exists n1, n2; tauto.
  + unfold arith_denote1; unfold arith_compute1 in H0.
    destruct H0 as [n2 ?]; exists n1, n2; tauto.
  + unfold arith_denote1; unfold arith_compute1 in H0.
    destruct H0 as [n2 ?]; exists n1, n2; tauto.
  + unfold arith_denote1; unfold arith_compute1 in H0.
    destruct H0 as [n2 ?]; exists n1, n2; tauto.
  + unfold arith_denote2; unfold arith_compute2 in H0.
    destruct H0 as [n2 ?]; exists n1, n2; tauto.
  + unfold arith_denote2; unfold arith_compute2 in H0.
    destruct H0 as [n2 ?]; exists n1, n2; tauto.
Qed.


(** 最后对小步语义的定义做归纳证明 *)
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
Admitted. (* 留作习题 *)










Fixpoint ck_eval (k: com_ectx): prog_state -> prog_state -> Prop :=
  match k with
  | KSeq c => (ceval c).(fin)
  | KWhileBody e c => (ceval (CWhile e c)).(fin)
  end.

Fixpoint eck_eval (k: expr_com_ectx):
  int64 -> prog_state -> prog_state -> Prop :=
  match k with
  | KWhileCond e c =>
      fun n s1 s2 =>
        Int64.signed n <> 0 /\
          ((ceval c).(fin) ∘ (ceval (CWhile e c)).(fin)) s1 s2 \/
        n = Int64.repr 0 /\ BinRel.id s1 s2
  | KIf c1 c2 =>
      fun n s1 s2 =>
        Int64.signed n <> 0 /\ ((ceval c1).(fin) s1 s2) \/
        n = Int64.repr 0 /\ ((ceval c2).(fin) s1 s2)
  | KAsgnVar X =>
      fun n s1 s2 =>
        s2.(vars) X = n /\
        (forall Y, X <> Y -> s1.(vars) Y = s2.(vars) Y) /\
        (forall p, s1.(mem) p = s2.(mem) p)
  | KAsgnMemL e2 =>
      fun n1 s1 s2 =>
        exists n2,
          eeval e2 s1 n2 /\
          s1.(mem) n1 <> None /\
          s2.(mem) n1 = Some n2 /\
          (forall X, s1.(vars) X = s2.(vars) X) /\
          (forall q, n1 <> q -> s1.(mem) q = s2.(mem) q)
  | KAsgnMemR n1 =>
      fun n2 s1 s2 =>
        s1.(mem) n1 <> None /\
        s2.(mem) n1 = Some n2 /\
        (forall X, s1.(vars) X = s2.(vars) X) /\
        (forall q, n1 <> q -> s1.(mem) q = s2.(mem) q)
  end.

Fixpoint cl_eval (cl: com_loc): prog_state -> prog_state -> Prop :=
  match cl with
  | CL_Finished => BinRel.id
  | CL_FocusedCom c => (ceval c).(fin)
  | CL_ECont el k => fun s1 s2 => exists n, el_eval el s1 n /\ eck_eval k n s1 s2
  | CL_CCont cl0 k => (cl_eval cl0) ∘ (ck_eval k)
  end.

Lemma cstep_sound: forall cl1 s1 cl2 s2 s,
  cstep (cl1, s1) (cl2, s2) ->
  cl_eval cl2 s2 s ->
  cl_eval cl1 s1 s.
Proof.
  intros.
  revert s H0; induction_step H; intros.
  + simpl in *.
    apply H0.
  + simpl in *.
    exists n.
    unfold BinRel.id in H2; subst s; tauto.
  + simpl in *.
    destruct H0 as [n1 [? [n2 ?] ] ].
    exists n1, n2; tauto.
  + simpl in *.
    destruct H0 as [n2 [n ?] ].
    exists n1; split; [| exists n2]; tauto.
  + simpl in *.
    exists n2.
    unfold BinRel.id in H3; subst s; tauto.
  + simpl in *.
    apply H0.
  + simpl in *.
    apply BinRel_concat_id_l.
    tauto.
  + simpl in *.
    destruct H0 as [n [? [? | ?] ] ].
    - left.
      exists s; simpl; unfold test1.
      split; [exists n |]; tauto.
    - right.
      exists s; simpl; unfold test0.
      destruct H0; subst n; tauto.
  + simpl in *.
    exists n.
    tauto.
  + simpl in *.
    exists n.
    tauto.
  + simpl in *.
    destruct H0 as [n ?].
    apply (while_denote_is_fix e c).
    destruct H as [? [? | ?] ].
    - left.
      unfold test1; exists s.
      split; [exists n; tauto | simpl; tauto].
    - right.
      unfold BinRel.id in H0.
      unfold test0.
      destruct H0; subst n; tauto.
  + simpl in *.
    exists n.
    tauto.
  + simpl in *.
    exists n; subst n.
    tauto.
  + simpl in *.
    destruct H0 as [n [? ?] ].
    apply BinRel_concat_id_l.
    apply (while_denote_is_fix e c).
    destruct H0 as [? | ?].
    - left.
      unfold test1; exists s.
      split; [exists n; tauto | simpl; tauto].
    - right.
      unfold BinRel.id in H0.
      unfold test0.
      destruct H0; subst n; tauto.
  + simpl in *.
    destruct H0 as [n [? ?]].
    eapply estep_sound in H0; eauto.
  + simpl in *.
    destruct H0 as [s' [? ?]].
    exists s'.
    specialize (IHcstep s').
    tauto.
Qed.








