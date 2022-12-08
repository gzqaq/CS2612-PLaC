Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
Require Import PL.RTClosure.
Require Import PL.DenotationalSemantics.
Require Import PL.SmallStepSemantics.
Require Import compcert.lib.Integers.
Import WhileD_Expr WhileD_Cmd.
Local Open Scope Z.
Local Open Scope sets_scope.

(** 请完成下面证明 *)
Lemma multi_cstep_ceval: forall c s1 s2,
  multi_cstep (CL_FocusedCom c, s1) (CL_Finished, s2) ->
  (ceval c).(fin) s1 s2.
Proof.
  intros.
  assert (cl_eval CL_Finished s2 s2). { simpl. reflexivity. }
  assert (cl_eval (CL_FocusedCom c) s1 s2 -> (ceval c).(fin) s1 s2). { simpl. tauto. }
  apply H1; clear H1.
  set (cl1 := CL_FocusedCom c) in *; clearbody cl1.
  set (cl2 := CL_Finished) in *; clearbody cl2.
  induction_1n H.
  + apply H0.
  + eapply cstep_sound; eauto.
Qed.
