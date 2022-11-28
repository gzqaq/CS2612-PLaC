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

(** 请证明下述关于符号执行的结论。*)

Lemma replace_aprop_sep_legal:
  forall Ps m J res1 res2 res n1,
    replace_aprop_sep
      Ps
      res1.(value_of_result)
      res2.(value_of_result) = Some res ->
    Forall (aprop_pure_sat J) res1.(safe_cond) ->
    sep_conj_sat m J Ps ->
    aexpr_denote J (value_of_result res1) = Some n1 ->
    n1 <= Int64.max_signed ->
    n1 >= Int64.min_signed ->
    exists n2,  m (Int64.repr n1) = Some n2.
Proof.
  intros.
  set (val1 := value_of_result res1) in *; clearbody val1.
  set (val2 := value_of_result res2) in *; clearbody val2; clear res2.
  assert (exists m1 m2, mem_join m1 m2 m /\ sep_conj_sat m2 J Ps).
  {
    exists (fun _ => None), m.
    split; [apply mem_join_unit | apply H1].
  }
  clear H1; destruct H5 as [m1 [m2 [JOIN_m SAT]]].
  revert H. revert res.
  revert m1 m2 SAT JOIN_m; induction Ps as [| P Ps0 ?]; intros.
  - simpl in H. discriminate H.
  - simpl in SAT.
    destruct SAT as [m2a [m2b [JOIN_m2 [SAT_P SAT]]]].
    pose proof mem_join_assoc _ _ _ _ _ JOIN_m2 JOIN_m.
    destruct H1 as [m12a [JOIN_m12a JOIN_m']].
    simpl in H.
    destruct P eqn:HP; [destruct (aexpr_eqb val1 e1) eqn:?H | |].
    + apply aexpr_eqb_eq in H1.
      injection H as ?.
      subst e1 res.
      simpl in SAT_P.
      rewrite H2 in SAT_P.
      destruct (aexpr_denote J e2) as [n2 |] eqn:?H; [| contradiction].
      exists (Int64.repr n2).
      unfold store_sat in SAT_P.
      destruct SAT_P as [? [? [? [? ?]]]].
      pose proof mem_join_Some_left _ _ _ _ _ JOIN_m2 H8.
      pose proof mem_join_Some_right _ _ _ _ _ JOIN_m H9.
      tauto.
    + destruct (replace_aprop_sep Ps0 val1 val2) as [res' |]; [| simpl in H; discriminate H].
      assert (Some res' = Some res'). { reflexivity. }
      specialize (IHPs m12a m2b SAT JOIN_m' res' H5).
      tauto.
    + destruct (replace_aprop_sep Ps0 val1 val2) as [res' |]; [| simpl in H; discriminate H].
      assert (Some res' = Some res'). { reflexivity. }
      specialize (IHPs m12a m2b SAT JOIN_m' res' H1).
      tauto.
    + destruct (replace_aprop_sep Ps0 val1 val2) as [res' |]; [| simpl in H; discriminate H].
      assert (Some res' = Some res'). { reflexivity. }
      specialize (IHPs m12a m2b SAT JOIN_m' res' H1).
      tauto.
Qed.

(** 下面的证明中需要构造内存的拆分方案。在此过程中你可能要用到下面两个定义或者它
    们之一。*)

Definition mem_filter_in (mf m: int64 -> option int64):
  int64 -> option int64 :=
  fun i => match mf i with Some _ => m i | _ => None end.

Definition mem_filter_out (mf m: int64 -> option int64):
  int64 -> option int64 :=
  fun i => match mf i with None => m i | _ => None end.

Lemma replace_aprop_sep_replace_now: forall J m1 m2 n1 n2 e1 e2 e2' Ps,
  aexpr_denote J e1 = Some n1 ->
  aexpr_denote J e2 = Some n2 ->
  n2 <= Int64.max_signed ->
  n2 >= Int64.min_signed ->
  sep_conj_sat m1 J (AStore e1 e2' :: Ps) ->
  (forall q : int64, Int64.repr n1 <> q -> m1 q = m2 q) ->
  m2 (Int64.repr n1) = Some (Int64.repr n2) ->
  sep_conj_sat m2 J (AStore e1 e2 :: Ps).
Proof.
  intros J m1 m2 n1 n2 e1 e2 e2' Ps He1 He2 Hn2max Hn2min Hm1s Hass Hm2.
  simpl in Hm1s |- *.
  rewrite He1 in Hm1s |- *; rewrite He2.
  destruct Hm1s as [m1a [m1b [JOIN_m1 [? ?]]]].
  destruct (aexpr_denote J e2') as [n2' |]; [| contradiction].
  set (m2a := mem_filter_out m1b m2).
  exists m2a, m1b.
  unfold store_sat in H |- *.
  destruct H as [Hn1max [Hn1min [Hn2'max [Hn2'min Hm1a]]]].
  split.
  - unfold m2a; unfold mem_filter_out.
    unfold mem_join in JOIN_m1 |- *.
    intros.
    specialize (JOIN_m1 i).
    destruct JOIN_m1 as [[? [? ?] ] | [ [i' [? [? ?] ] ] | [i' [? [? ?] ] ] ] ];
      [left | right; left | right; right]; rewrite H1.
    + rewrite Hass in H2 by congruence.
      tauto.
    + rewrite Hass in H2 by congruence.
      exists i'. tauto.
    + destruct (Int64.eq_dec (Int64.repr n1) i) as [Heq | Hneq].
       * rewrite Heq in Hm1a , Hm2.
         exists (Int64.repr n2). tauto.
       * rewrite Hass in H2 by congruence.
         exists i'. tauto.
  - split; try tauto; split; try tauto; split; try tauto; split; try tauto; split; try tauto.
    + unfold m2a; unfold mem_filter_out.
      assert (m1b (Int64.repr n1) = None).
      {
        unfold mem_join in JOIN_m1.
        specialize (JOIN_m1 (Int64.repr n1)).
        destruct JOIN_m1 as [[? [? ?] ] | [ [i' [? [? ?] ] ] | [i' [? [? ?] ] ] ] ];
          congruence.
      }
      rewrite H.
      congruence.
Qed.
