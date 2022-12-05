Ltac revert_dependent_except x H :=
  repeat
    match goal with
    | H0: context [x] |- _ => revert H0; assert_succeeds (revert H)
    end.

Ltac revert_dependent_component x H :=
  first
  [
    is_var x;
    revert_dependent_except x H
  |
    match x with
    | ?y ?z => match type of y with
               | _ -> _ => revert_dependent_component y H;
                           revert_dependent_component z H
               | _ => idtac
               end
    | _ => idtac
    end
  ].

Ltac revert_component x :=
  first
  [
    is_var x;
    revert x
  |
    match x with
    | ?y ?z => match type of y with
               | _ -> _ => revert_component y; revert_component z
               | _ => idtac
               end
    | _ => idtac
    end
  ].

Ltac intros_until_EQ EQ :=
  match goal with
  | |- ?P -> ?Q => intros EQ
  | _ => intro; intros_until_EQ EQ
  end.

Ltac destruct_to_form a b :=
  first [ is_var b
        | is_var a; destruct a
        | match a with
          | ?a1 ?a2 =>
            match type of a1 with
            | ?P -> ?Q =>
              match b with
              | ?b1 ?b2 => destruct_to_form a1 b1; destruct_to_form a2 b2
              end
            | _ => idtac
            end
          | _ => idtac
          end
        ].

Ltac specialize_until_EQ H :=
  match type of H with
  | ?P -> ?Q => specialize (H eq_refl)
  | forall _:?A, _ => let a := fresh "a" in
                      evar (a: A);
                      specialize (H a);
                      subst a;
                      specialize_until_EQ H
  end.

Ltac intros_and_subst P :=
  match goal with
  | |- ?Q => unify P Q
  | |- _ = ?x -> _ => is_var x;
                      let H := fresh "H" in
                      intros H;
                      rewrite <- H in *;
                      clear x H;
                      intros_and_subst P
  end.           

(*******************************)

Inductive clos_refl_trans {A: Type} (R: A -> A -> Prop) : A -> A -> Prop :=
    | rt_step : forall x y, R x y -> clos_refl_trans R x y
    | rt_refl : forall x, clos_refl_trans R x x
    | rt_trans : forall x y z,
          clos_refl_trans R x y ->
          clos_refl_trans R y z ->
          clos_refl_trans R x z.

Inductive clos_refl_trans_1n {A : Type} (R: A -> A -> Prop) : A -> A -> Prop :=
    | rt1n_refl : forall x, clos_refl_trans_1n R x x
    | rt1n_trans_1n : forall x y z,
          R x y ->
          clos_refl_trans_1n R y z ->
          clos_refl_trans_1n R x z.

Inductive clos_refl_trans_n1 {A : Type} (R: A -> A -> Prop) : A -> A -> Prop :=
    | rtn1_refl : forall x, clos_refl_trans_n1 R x x
    | rtn1_trans_n1 : forall x y z : A,
          R y z ->
          clos_refl_trans_n1 R x y ->
          clos_refl_trans_n1 R x z.

Lemma rt_trans_1n: forall A (R: A -> A -> Prop) x y z,
  R x y ->
  clos_refl_trans R y z ->
  clos_refl_trans R x z.
Proof.
  intros.
  eapply rt_trans with y; [| exact H0].
  apply rt_step.
  exact H.
Qed.

Lemma rt_trans_n1: forall A (R: A -> A -> Prop) x y z,
  R y z ->
  clos_refl_trans R x y ->
  clos_refl_trans R x z.
Proof.
  intros.
  eapply rt_trans with y; [exact H0 |].
  apply rt_step.
  exact H.
Qed.

Lemma rt1n_step: forall A (R: A -> A -> Prop) x y,
  R x y ->
  clos_refl_trans_1n R x y.
Proof.
  intros.
  apply rt1n_trans_1n with y.
  + exact H.
  + apply rt1n_refl.
Qed.

Lemma rtn1_step: forall A (R: A -> A -> Prop) x y,
  R x y ->
  clos_refl_trans_n1 R x y.
Proof.
  intros.
  apply rtn1_trans_n1 with x.
  + exact H.
  + apply rtn1_refl.
Qed.

Lemma rt1n_trans: forall A (R: A -> A -> Prop) a b c,
  clos_refl_trans_1n R a b ->
  clos_refl_trans_1n R b c ->
  clos_refl_trans_1n R a c.
Proof.
  intros.
  revert H0.
  induction H.
  + tauto.
  + intros.
    apply rt1n_trans_1n with y.
    - exact H.
    - apply IHclos_refl_trans_1n, H1.
Qed.

Lemma rt1n_trans_again: forall A (R: A -> A -> Prop) a b c,
  clos_refl_trans_1n R a b ->
  clos_refl_trans_1n R b c ->
  clos_refl_trans_1n R a c.
Proof.
  intros.
  induction H.
  + exact H0.
  + apply IHclos_refl_trans_1n in H0.
    apply rt1n_trans_1n with y.
    - exact H.
    - exact H0.
Qed.

Lemma rtn1_trans: forall A (R: A -> A -> Prop) a b c,
  clos_refl_trans_n1 R a b ->
  clos_refl_trans_n1 R b c ->
  clos_refl_trans_n1 R a c.
Proof.
  intros.
  induction H0.
  + exact H.
  + apply rtn1_trans_n1 with y; tauto.
Qed.

Lemma rt1n_rt: forall A (R: A -> A -> Prop) a b,
  clos_refl_trans_1n R a b -> clos_refl_trans R a b.
Proof.
  intros.
  induction H.
  + apply rt_refl.
  + apply rt_trans_1n with y; tauto.
Qed.

Lemma rt_rt1n: forall A (R: A -> A -> Prop) a b,
  clos_refl_trans R a b -> clos_refl_trans_1n R a b.
Proof.
  intros.
  induction H.
  + apply rt1n_step, H.
  + apply rt1n_refl.
  + apply rt1n_trans with y; tauto.
Qed.

Lemma rtn1_rt: forall A (R: A -> A -> Prop) a b,
  clos_refl_trans_n1 R a b -> clos_refl_trans R a b.
Proof.
  intros.
  induction H.
  + apply rt_refl.
  + apply rt_trans_n1 with y; tauto.
Qed.

Lemma rt_rtn1: forall A (R: A -> A -> Prop) a b,
  clos_refl_trans R a b -> clos_refl_trans_n1 R a b.
Proof.
  intros.
  induction H.
  + apply rtn1_step, H.
  + apply rtn1_refl.
  + apply rtn1_trans with y; tauto.
Qed.

Lemma rt_rt1n_iff: forall A (R: A -> A -> Prop) a b,
  clos_refl_trans R a b <-> clos_refl_trans_1n R a b.
Proof.
  split; intros.
  + apply rt_rt1n; auto.
  + apply rt1n_rt; auto.
Qed.

Lemma rt_rtn1_iff: forall A (R: A -> A -> Prop) a b,
  clos_refl_trans R a b <-> clos_refl_trans_n1 R a b.
Proof.
  split; intros.
  + apply rt_rtn1; auto.
  + apply rtn1_rt; auto.
Qed.

Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.
Require Import Coq.Setoids.Setoid.

Instance rt_refl_ins A R: Reflexive (@clos_refl_trans A R).
Proof.
  hnf; intros.
  apply rt_refl.
Qed.

Instance rt_trans_ins A R: Transitive (@clos_refl_trans A R).
Proof.
  hnf; intros.
  eapply rt_trans; eauto.
Qed.

Section PropReplace.

Variable R: Prop -> Prop -> Prop.

Inductive PropReplace: Prop -> Prop -> Prop :=
| PR_init (P Q: Prop):
    R P Q ->
    PropReplace P Q
| PR_refl (P: Prop):
    PropReplace P P
| PR_and (P1 P2 Q1 Q2: Prop):
    PropReplace P1 Q1 ->
    PropReplace P2 Q2 ->
    PropReplace (P1 /\ P2) (Q1 /\ Q2)
| PR_or (P1 P2 Q1 Q2: Prop):
    PropReplace P1 Q1 ->
    PropReplace P2 Q2 ->
    PropReplace (P1 \/ P2) (Q1 \/ Q2)
| PR_impl (P1 P2 Q1 Q2: Prop):
    PropReplace P1 Q1 ->
    PropReplace P2 Q2 ->
    PropReplace (P1 -> P2) (Q1 -> Q2)
| PR_iff (P1 P2 Q1 Q2: Prop):
    PropReplace P1 Q1 ->
    PropReplace P2 Q2 ->
    PropReplace (P1 <-> P2) (Q1 <-> Q2)
| PR_not (P Q: Prop):
    PropReplace P Q ->
    PropReplace (~ P) (~ Q)
| PR_all' A (P Q: A -> Prop):
    (forall a, PropReplace (P a) (Q a)) ->
    PropReplace (forall a, P a) (forall a, Q a)
| PR_ex' A (P Q: A -> Prop):
    (forall a, PropReplace (P a) (Q a)) ->
    PropReplace (exists a, P a) (exists a, Q a)
.

Lemma PR_all A (P Q: A -> Prop) Q':
  (forall a, exists Qa, PropReplace (P a) Qa /\ Qa = Q a) ->
  (Q' = forall a, Q a) ->
  PropReplace (forall a, P a) Q'.
Proof.
  intros.
  subst.
  apply PR_all'.
  intros; specialize (H a).
  destruct H as [? [? ?]]; subst; auto.
Qed.

Lemma PR_ex A (P Q: A -> Prop) Q':
  (forall a, exists Qa, PropReplace (P a) Qa /\ Qa = Q a) ->
  (Q' = exists a, Q a) ->
  PropReplace (exists a, P a) Q'.
Proof.
  intros.
  subst.
  apply PR_ex'.
  intros; specialize (H a).
  destruct H as [? [? ?]]; subst; auto.
Qed.

Lemma PR_sound: (forall P Q, R P Q -> (P <-> Q)) ->
                (forall P Q, PropReplace P Q -> (P <-> Q)).
Proof.
  intros.
  induction H0; try tauto; try firstorder.
Qed.

End PropReplace.

Ltac ProvePR tac :=
  tac;
  match goal with
  | |- PropReplace _ (_ /\ _) _         => apply PR_and; ProvePR tac
  | |- PropReplace _ (_ \/ _) _         => apply PR_or; ProvePR tac
  | |- PropReplace _ (_ -> _) _         => apply PR_impl; ProvePR tac
  | |- PropReplace _ (_ <-> _) _        => apply PR_iff; ProvePR tac
  | |- PropReplace _ (~ _) _            => apply PR_not; ProvePR tac
  | |- PropReplace _ (forall b:?B, _) _ => eapply PR_all;
                                           [
                                             intro; eexists;
                                             split; [ProvePR tac |];
                                             match goal with
                                             | |- ?Qa = ?Q ?a =>
                                               let Q' := eval pattern a in Qa in
                                               unify Q' (Q a);
                                               reflexivity
                                             end
                                           |
                                             match goal with
                                             | |- ?Q' = forall a, ?Q a =>
                                               unify Q' (forall b: B, Q b);
                                               reflexivity
                                             end
                                           ]
  | |- PropReplace _ (exists b:?B, _) _ => eapply PR_ex;
                                           [
                                             intro; eexists;
                                             split; [ProvePR tac |];
                                             match goal with
                                             | |- ?Qa = ?Q ?a =>
                                               let Q' := eval pattern a in Qa in
                                               unify Q' (Q a);
                                               reflexivity
                                             end
                                           |
                                             match goal with
                                             | |- ?Q' = forall a, ?Q a =>
                                               unify Q' (forall b: B, Q b);
                                               reflexivity
                                             end
                                           ]
  | _                                => apply PR_refl
  end.

Inductive To1N: Prop -> Prop -> Prop :=
| To1N_intro A R x y: To1N (@clos_refl_trans A R x y) (@clos_refl_trans_1n A R x y).

Inductive ToN1: Prop -> Prop -> Prop :=
| ToN1_intro A R x y: ToN1 (@clos_refl_trans A R x y) (@clos_refl_trans_n1 A R x y).

Ltac ProvePR_To1N :=
  try solve [simple apply PR_init; simple apply To1N_intro].

Ltac ProvePR_ToN1 :=
  try solve [simple apply PR_init; simple apply ToN1_intro].

Lemma PR_To1N_sound: forall P Q, PropReplace To1N P Q -> (P <-> Q).
Proof.
  intros.
  eapply PR_sound; [| apply H].
  clear.
  intros.
  inversion H.
  apply rt_rt1n_iff.  
Qed.

Lemma PR_ToN1_sound: forall P Q, PropReplace ToN1 P Q -> (P <-> Q).
Proof.
  intros.
  eapply PR_sound; [| apply H].
  clear.
  intros.
  inversion H.
  apply rt_rtn1_iff.  
Qed.

Tactic Notation "replace_with_1n" :=
  idtac;
  match goal with
  | |- ?P => let Q := fresh "Q" in
             evar (Q: Prop);
             let H := fresh in
             assert (PropReplace To1N P Q) as H; subst Q;
             [ProvePR ProvePR_To1N | rewrite (PR_To1N_sound _ _ H); clear H]
  end.

Tactic Notation "replace_with_1n" "in" constr(H0) :=
  idtac;
  match type of H0 with
  | ?P    => let Q := fresh "Q" in
             evar (Q: Prop);
             let H := fresh in
             assert (PropReplace To1N P Q) as H; subst Q;
             [ProvePR ProvePR_To1N | rewrite (PR_To1N_sound _ _ H) in H0; clear H]
  end.

Tactic Notation "replace_with_1n" "in" constr(H1) "," constr(H2) :=
  replace_with_1n in H1;
  replace_with_1n in H2.

Tactic Notation "replace_with_1n" "in" constr(H1) "," constr(H2) "," constr(H3) :=
  replace_with_1n in H1;
  replace_with_1n in H2;
  replace_with_1n in H3.

Tactic Notation "replace_with_n1" :=
  idtac;
  match goal with
  | |- ?P => let Q := fresh "Q" in
             evar (Q: Prop);
             let H := fresh in
             assert (PropReplace ToN1 P Q) as H; subst Q;
             [ProvePR ProvePR_ToN1 | rewrite (PR_ToN1_sound _ _ H); clear H]
  end.

Tactic Notation "replace_with_n1" "in" constr(H0) :=
  idtac;
  match type of H0 with
  | ?P    => let Q := fresh "Q" in
             evar (Q: Prop);
             let H := fresh in
             assert (PropReplace ToN1 P Q) as H; subst Q;
             [ProvePR ProvePR_ToN1 | rewrite (PR_ToN1_sound _ _ H) in H0; clear H]
  end.

Tactic Notation "replace_with_n1" "in" constr(H1) "," constr(H2) :=
  replace_with_n1 in H1;
  replace_with_n1 in H2.

Tactic Notation "replace_with_n1" "in" constr(H1) "," constr(H2) "," constr(H3) :=
  replace_with_n1 in H1;
  replace_with_n1 in H2;
  replace_with_n1 in H3.

Tactic Notation "unfold_with_1n" constr(X) :=
  unfold X; replace_with_1n.

Tactic Notation "unfold_with_1n" constr(X) "in" constr(H1) :=
  unfold X in H1; replace_with_1n in H1.

Tactic Notation "unfold_with_1n" constr(X) "in" constr(H1) "," constr(H2) :=
  unfold X in H1, H2; replace_with_1n in H1, H2.

Tactic Notation "unfold_with_1n" constr(X) "in" constr(H1) "," constr(H2) "," constr(H3) :=
  unfold X in H1, H2, H3; replace_with_1n in H1, H2, H3.

Tactic Notation "unfold_with_n1" constr(X) :=
  unfold X; replace_with_n1.

Tactic Notation "unfold_with_n1" constr(X) "in" constr(H1) :=
  unfold X in H1; replace_with_n1 in H1.

Tactic Notation "unfold_with_n1" constr(X) "in" constr(H1) "," constr(H2) :=
  unfold X in H1, H2; replace_with_n1 in H1, H2.

Tactic Notation "unfold_with_n1" constr(X) "in" constr(H1) "," constr(H2) "," constr(H3) :=
  unfold X in H1, H2, H3; replace_with_n1 in H1, H2, H3.

Lemma ind_1N: forall A (R RT_R: A -> A -> Prop),
  (RT_R = clos_refl_trans R) ->
  forall x (P: A -> Prop),
  P x ->
  (forall y z (IH: P y), R z y -> RT_R y x -> P z) ->
  (forall y, RT_R y x -> P y).
Proof.
  intros.
  subst RT_R.
  apply rt_rt1n in H2.
  induction H2; auto.
  apply H1 with y; auto.
  apply rt1n_rt; auto.
Qed.

Lemma ind_N1: forall A (R RT_R: A -> A -> Prop),
  (RT_R = clos_refl_trans R) ->
  forall x (P: A -> Prop),  
  P x ->
  (forall y z (IH: P y), R y z -> RT_R x y -> P z) ->
  (forall y, RT_R x y -> P y).
Proof.
  intros.
  subst RT_R.
  apply rt_rtn1 in H2.
  induction H2; auto.
  apply H1 with y; auto.
  apply rtn1_rt; auto.
Qed.

Lemma trans_1N: forall A (R RT_R: A -> A -> Prop),
  (RT_R = clos_refl_trans R) ->
  forall x y z, R x y -> RT_R y z -> RT_R x z.
Proof.
  intros.
  subst.
  apply rt_trans_1n with y; auto.
Qed.

Lemma trans_N1: forall A (R RT_R: A -> A -> Prop),
  (RT_R = clos_refl_trans R) ->
  forall x y z, RT_R x y -> R y z -> RT_R x z.
Proof.
  intros.
  subst.
  apply rt_trans_n1 with y; auto.
Qed.

Ltac induction_1n H :=
  match type of H with
  | ?RT_R ?b ?a =>
    revert_dependent_component b H;
    let b0 := fresh "x" in
    let EQ := fresh "EQ" in
    remember b as b0 eqn:EQ in H;
    revert EQ;
    revert_component b;
    match goal with
    | |- ?Q =>
      let Pb := eval pattern b0 in Q in
      match Pb with
      | ?P b0 =>
        revert b0 H;
        refine (ind_1N _ _ RT_R eq_refl a P _ _);
        [ intros_until_EQ EQ;
          match goal with
          | |- ?Base =>
            let Base0 := fresh in
            remember Base as Base0 in |- *;
            first [ injection EQ; clear EQ; intros_and_subst Base0
                  | revert EQ; intros_and_subst Base0
                  | idtac ];
            subst Base0
          end
        | let b0 := fresh "x" in
          let H0 := fresh "H" in
          let IH := fresh "IHrt" in
          first [intros ?b b0 IH H0 ? | intros ? b0 IH H0 ?]; intros_until_EQ EQ; subst b0;
          repeat progress
          match type of H0 with
          | _ ?y ?x => destruct_to_form x y
          end;
          specialize_until_EQ IH
        ]
      end
    end
  end.

Ltac induction_n1 H :=
  match type of H with
  | ?RT_R ?a ?b =>
    revert_dependent_component b H;
    let b0 := fresh "x" in
    let EQ := fresh "EQ" in
    remember b as b0 eqn:EQ in H;
    revert EQ;
    revert_component b;
    match goal with
    | |- ?Q =>
      let Pb := eval pattern b0 in Q in
      match Pb with
      | ?P b0 =>
        revert b0 H;
        refine (ind_N1 _ _ RT_R eq_refl a P _ _);
        [ intros_until_EQ EQ;
          match goal with
          | |- ?Base =>
            let Base0 := fresh in
            remember Base as Base0 in |- *;
            first [ injection EQ; clear EQ; intros_and_subst Base0
                  | revert EQ; intros_and_subst Base0
                  | idtac ];
            subst Base0
          end
        | let b0 := fresh "x" in
          let H0 := fresh "H" in
          let IH := fresh "IHrt" in
          first [intros ?b b0 IH H0 ? | intros ? b0 IH H0 ?]; intros_until_EQ EQ; subst b0;
          repeat progress
          match type of H0 with
          | _ ?x ?y => destruct_to_form x y
          end;
          specialize_until_EQ IH
        ]
      end
    end
  end.

Ltac transitivity_1n y :=
  match goal with
  | |- ?RT_R ?x ?z =>
    refine (trans_1N _ _ RT_R eq_refl x y z _ _)
  end.

Ltac etransitivity_1n :=
  match goal with
  | |- ?RT_R ?x ?z =>
    match type of x with
    | ?A => let y := fresh "y" in
            evar (y: A);
            transitivity_1n y;
            subst y
    end
  end.

Ltac transitivity_n1 y :=
  match goal with
  | |- ?RT_R ?x ?z =>
    refine (trans_N1 _ _ RT_R eq_refl x y z _ _)
  end.

Ltac etransitivity_n1 :=
  match goal with
  | |- ?RT_R ?x ?z =>
    match type of x with
    | ?A => let y := fresh "y" in
            evar (y: A);
            transitivity_n1 y;
            subst y
    end
  end.

Ltac new_intros_and_subst Base0 :=
  match goal with
  | |- Base0 => idtac
  | |- _ = ?x -> _ => is_var x;
                      let H := fresh "H" in
                      intros H;
                      revert Base0;
                      rewrite <- H in *;
                      clear x H;
                      intros Base0;
                      new_intros_and_subst Base0
  end.

Ltac induction_step H :=
  match type of H with
  | ?cstep ?a ?b =>
    revert_dependent_component a H;
    revert_dependent_component b H;
    let a0 := fresh "cst" in
    let b0 := fresh "cst" in
    let EQa := fresh "EQ" in
    let EQb := fresh "EQ" in
    remember a as a0 eqn:EQa in H;
    remember b as b0 eqn:EQb in H;
    revert EQa EQb;
    revert_component a;
    revert_component b;
    match goal with
    | |- ?Q =>
      let Pab := eval pattern a0, b0 in Q in
      match Pab with
      | ?P0 a0 b0 =>
        let P := fresh "P" in
        set (P := P0); change (P a0 b0);
        induction H; intros_until_EQ EQa; intros EQb;
        repeat
          match goal with
          | IH: context [P] |- _ =>
            unfold P in IH;
            specialize_until_EQ IH;
            specialize (IH eq_refl)
          end;
        unfold P; clear P;
        match goal with
          | |- ?Base =>
            let Base0 := fresh in
            set (Base0 := Base);
            first [ injection EQa; injection EQb; clear EQa; clear EQb;
                    new_intros_and_subst Base0
                  | revert EQa EQb; new_intros_and_subst Base0
                  | idtac ];
            unfold Base0; clear Base0
        end
      end
    end
  end.
