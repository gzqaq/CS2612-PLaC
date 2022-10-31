Require Import Equivalence.
Require Import Morphisms.
Require Import Morphisms_Prop.
Require Import Classical.
Require Import Psatz.
Require Import Basics.

Module Sets.

Class SETS (T: Type): Type :=
{
  full: T;
  empty: T;
  prop_inj: Prop -> T;
  intersect: T -> T -> T;
  union: T -> T -> T;
  omega_intersect: (nat -> T) -> T;
  omega_union: (nat -> T) -> T;
  general_intersect: (T -> Prop) -> T;
  general_union: (T -> Prop) -> T;
  equiv: T -> T -> Prop;
  included: T -> T -> Prop;
}.

Definition complement {A: Type} (X: A -> Prop) := fun a => ~ X a.

Definition lift_full {A B} {_SETS: SETS B}: A -> B := fun _ => full.

Definition lift_empty {A B} {_SETS: SETS B}: A -> B := fun _ => empty.

Definition lift_prop_inj {A B} {_SETS: SETS B}: Prop -> A -> B :=
  fun P _ => prop_inj P.

Definition lift_intersect {A B} {_SETS: SETS B}: (A -> B) -> (A -> B) -> (A -> B) :=
  fun x y a => intersect (x a) (y a).

Definition lift_union {A B} {_SETS: SETS B}: (A -> B) -> (A -> B) -> (A -> B) :=
  fun x y a => union (x a) (y a).

Definition lift_omega_intersect {A B} {_SETS: SETS B}: (nat -> A -> B) -> (A -> B) :=
  fun x a => omega_intersect (fun n => x n a).

Definition lift_omega_union {A B} {_SETS: SETS B}: (nat -> A -> B) -> (A -> B) :=
  fun x a => omega_union (fun n => x n a).

Definition lift_general_intersect {A B} {_SETS: SETS B}: ((A -> B) -> Prop) -> (A -> B) :=
  fun x a => general_intersect (fun b => exists f, x f /\ f a = b).

Definition lift_general_union {A B} {_SETS: SETS B}: ((A -> B) -> Prop) -> (A -> B) :=
  fun x a => general_union (fun b => exists f, x f /\ f a = b).

Definition lift_equiv {A B} {_SETS: SETS B}: (A -> B) -> (A -> B) -> Prop :=
  fun x y => forall a, equiv (x a) (y a).

Definition lift_included {A B} {_SETS: SETS B}: (A -> B) -> (A -> B) -> Prop :=
  fun x y => forall a, included (x a) (y a).

Definition test1 {A B} {_SETS: SETS B}: (A -> Prop) -> (A -> B) :=
  fun P a => prop_inj (P a).

Definition lift1 {A B} {_SETS: SETS B}: B -> (A -> B) :=
  fun x _ => x.

Definition filter1 {A B} {_SETS: SETS B}: (A -> Prop) -> (A -> B) -> (A -> B) :=
  fun P x => lift_intersect (test1 P) x.

Definition projB {A B} (s: (A * B) -> Prop): B -> Prop:= 
  fun b => exists a, s (a,b).

Definition singleton {A: Type} (a: A): A -> Prop := eq a.

Definition In {A: Type} (a: A) (X: A -> Prop): Prop := X a.

End Sets.

Arguments Sets.full: simpl never.
Arguments Sets.empty: simpl never.
Arguments Sets.prop_inj: simpl never.
Arguments Sets.intersect: simpl never.
Arguments Sets.union: simpl never.
Arguments Sets.omega_intersect: simpl never.
Arguments Sets.omega_union: simpl never.
Arguments Sets.general_intersect: simpl never.
Arguments Sets.general_union: simpl never.
Arguments Sets.equiv: simpl never.
Arguments Sets.included: simpl never.
Arguments Sets.singleton: simpl never.
Arguments Sets.In: simpl never.

#[export] Instance Prop_SETS: Sets.SETS Prop :=
  {|
    Sets.full := True;
    Sets.empty := False;
    Sets.prop_inj := fun P => P;
    Sets.intersect := and;
    Sets.union := or;
    Sets.omega_intersect := fun P => forall n, P n;
    Sets.omega_union := (@ex _);
    Sets.general_intersect := fun S => forall P, S P -> P;
    Sets.general_union := fun S => exists P, S P /\ P;
    Sets.equiv := iff;
    Sets.included := fun P Q => P -> Q
  |}.

#[export] Instance lift_SETS (A B: Type) (_SETS: Sets.SETS B): Sets.SETS (A -> B) :=
  {|
    Sets.full := Sets.lift_full;
    Sets.empty := Sets.lift_empty;
    Sets.prop_inj := Sets.lift_prop_inj;
    Sets.intersect := Sets.lift_intersect;
    Sets.union := Sets.lift_union;
    Sets.omega_intersect := Sets.lift_omega_intersect;
    Sets.omega_union := Sets.lift_omega_union;
    Sets.general_intersect := Sets.lift_general_intersect;
    Sets.general_union := Sets.lift_general_union;
    Sets.equiv := Sets.lift_equiv;
    Sets.included := Sets.lift_included
  |}.

Ltac SETS_unfold1 SETS :=
  match SETS with
  | lift_SETS _ _ _ =>
      let p := eval unfold lift_SETS at 1 in SETS in
      constr:(p)
  | Prop_SETS =>
      let p := eval unfold Prop_SETS in SETS in
      constr:(p)
  end.

Ltac SETS_simplify T :=
  first
    [ match T with
      | ?op ?A ?SETS =>
        match SETS with
        | lift_SETS _ _ _ => idtac
        | Prop_SETS => idtac
        end;
        let op1 := eval cbv delta
              [Sets.full
               Sets.empty
               Sets.prop_inj
               Sets.intersect
               Sets.union
               Sets.omega_intersect
               Sets.omega_union
               Sets.general_intersect
               Sets.general_union
               Sets.equiv
               Sets.included] in op in
        let SETS1 := SETS_unfold1 SETS in
        let T1 := eval cbv beta zeta iota in
              (op1 A SETS1) in
        let T2 := eval cbv delta
              [Sets.lift_full
               Sets.lift_empty
               Sets.lift_prop_inj
               Sets.lift_intersect
               Sets.lift_union
               Sets.lift_omega_intersect
               Sets.lift_omega_union
               Sets.lift_general_intersect
               Sets.lift_general_union
               Sets.lift_equiv
               Sets.lift_included] in T1 in
        change T with T2;
        try SETS_simplify T2
      end
    | match T with
      | ?op ?A ?B ?SETS =>
        let op1 := eval cbv delta [Sets.filter1 Sets.test1] in op in
        let T1 := eval cbv beta zeta iota in
              (op1 A B SETS) in
        let T2 := eval cbv delta
              [Sets.lift_prop_inj
               Sets.lift_intersect] in T1 in
        change T with T2;
        try SETS_simplify T2
      end
    ].

Ltac unfold_SETS_tac :=
  repeat
  match goal with
  | |- context [@Sets.full ?T ?_SETS] =>
         SETS_simplify (@Sets.full T _SETS)
  | |- context [@Sets.empty ?T ?_SETS] =>
         SETS_simplify (@Sets.empty T _SETS)
  | |- context [@Sets.prop_inj ?T ?_SETS] =>
         SETS_simplify (@Sets.prop_inj T _SETS)
  | |- context [@Sets.equiv ?T ?_SETS] =>
         SETS_simplify (@Sets.equiv T _SETS)
  | |- context [@Sets.intersect ?T ?_SETS] =>
         SETS_simplify (@Sets.intersect T _SETS)
  | |- context [@Sets.union ?T ?_SETS] =>
         SETS_simplify (@Sets.union T _SETS)
  | |- context [@Sets.omega_intersect ?T ?_SETS] =>
         SETS_simplify (@Sets.omega_intersect T _SETS)
  | |- context [@Sets.omega_union ?T ?_SETS] =>
         SETS_simplify (@Sets.omega_union T _SETS)
  | |- context [@Sets.general_intersect ?T ?_SETS] =>
         SETS_simplify (@Sets.general_intersect T _SETS)
  | |- context [@Sets.general_union ?T ?_SETS] =>
         SETS_simplify (@Sets.general_union T _SETS)
  | |- context [@Sets.included ?T ?_SETS] =>
         SETS_simplify (@Sets.included T _SETS)
  | |- context [@Sets.filter1 ?A ?T ?_SETS] =>
         SETS_simplify (@Sets.filter1 A T _SETS)
  | |- context [@Sets.test1 ?A ?T ?_SETS] =>
         SETS_simplify (@Sets.test1 A T _SETS)
  | |- _ => progress cbv beta
  end.

Class SETS_Properties (T: Type) {_SETS: Sets.SETS T}: Prop :=
{
  Sets_included_refl: Reflexive Sets.included;
  Sets_included_trans: Transitive Sets.included;
  Sets_equiv_Sets_included: forall x y, Sets.equiv x y <-> (Sets.included x y /\ Sets.included y x);
  Sets_empty_included: forall x, Sets.included Sets.empty x;
  Sets_included_full: forall x, Sets.included x Sets.full;
  Sets_prop_inj_included: forall (P: Prop) x y, (P -> Sets.included x y) -> Sets.included (Sets.intersect (Sets.prop_inj P) x) y;
  Sets_included_prop_inj: forall (P: Prop) x, P -> Sets.included x (Sets.prop_inj P);
  Sets_intersect_included1: forall x y, Sets.included (Sets.intersect x y) x;
  Sets_intersect_included2: forall x y, Sets.included (Sets.intersect x y) y;
  Sets_included_intersect: forall x y z, Sets.included x y -> Sets.included x z -> Sets.included x (Sets.intersect y z);
  Sets_included_union1: forall x y, Sets.included x (Sets.union x y);
  Sets_included_union2: forall x y, Sets.included y (Sets.union x y);
  Sets_union_included_strong2: forall x y z u, Sets.included (Sets.intersect x u) z -> Sets.included (Sets.intersect y u) z -> Sets.included (Sets.intersect (Sets.union x y) u) z;
  Sets_included_omega_union: forall xs n, Sets.included (xs n) (Sets.omega_union xs);
  Sets_omega_union_included: forall xs y, (forall n, Sets.included (xs n) y) -> Sets.included (Sets.omega_union xs) y;
  Sets_omega_intersect_included: forall xs n, Sets.included (Sets.omega_intersect xs) (xs n);
  Sets_included_omega_intersect: forall xs y, (forall n, Sets.included y (xs n)) -> Sets.included y (Sets.omega_intersect xs);
  Sets_included_general_union: forall (xs: _ -> Prop) x, xs x -> Sets.included x (Sets.general_union xs);
  Sets_general_union_included: forall (xs: _ -> Prop) y, (forall x, xs x -> Sets.included x y) -> Sets.included (Sets.general_union xs) y;
  Sets_general_intersect_included: forall (xs: _ -> Prop) x, xs x -> Sets.included (Sets.general_intersect xs) x;
  Sets_included_general_intersect: forall (xs: _ -> Prop) y, (forall x, xs x -> Sets.included y x) -> Sets.included y (Sets.general_intersect xs);
}.

#[export] Existing Instances Sets_included_refl Sets_included_trans.

Lemma Sets_filter1_defn: forall {S T} {_SETS: Sets.SETS T} (P: S -> Prop) (Q: S -> T),
  Sets.filter1 P Q = Sets.intersect (Sets.test1 P) Q.
Proof.
  intros.
  reflexivity.
Qed.

#[export] Instance Sets_equiv_refl {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Reflexive Sets.equiv.
Proof.
  hnf; intros.
  apply Sets_equiv_Sets_included.
  split; apply Sets_included_refl.
Qed.

#[export] Instance Sets_equiv_sym {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Symmetric Sets.equiv.
Proof.
  hnf; intros.
  rewrite Sets_equiv_Sets_included in H |- *.
  tauto.
Qed.

#[export] Instance Sets_equiv_trans {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Transitive Sets.equiv.
Proof.
  hnf; intros.
  rewrite Sets_equiv_Sets_included in H, H0 |- *.
  destruct H, H0.
  split; eapply Sets_included_trans; eauto.
Qed.

#[export] Instance Sets_equiv_equiv {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Equivalence Sets.equiv.
Proof.
  constructor; auto.
  + apply Sets_equiv_refl; auto.
  + apply Sets_equiv_sym; auto.
  + apply Sets_equiv_trans; auto.
Qed.

#[export] Instance Sets_included_congr {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv ==> iff) Sets.included.
Proof.
  unfold Proper, respectful.
  intros.
  rewrite Sets_equiv_Sets_included in H, H0.
  destruct H, H0.
  split; intros;
  repeat (eapply Sets_included_trans; eauto).
Qed.

Lemma Sets_intersect_full {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x, Sets.equiv (Sets.intersect x Sets.full) x.
Proof.
  intros.
  apply Sets_equiv_Sets_included.
  split.
  + apply Sets_intersect_included1.
  + apply Sets_included_intersect.
    - reflexivity.
    - apply Sets_included_full.
Qed.

Lemma Sets_union_included {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y z, Sets.included x z -> Sets.included y z -> Sets.included (Sets.union x y) z.
Proof.
  intros.
  pose proof Sets_union_included_strong2 x y z Sets.full.
  rewrite !Sets_intersect_full in H1.
  auto.
Qed.

#[export] Instance Sets_union_mono {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.included ==> Sets.included ==> Sets.included) Sets.union.
Proof.
  unfold Proper, respectful.
  intros.
  apply Sets_union_included.
  + apply Sets_included_trans with y; auto.
    apply Sets_included_union1.
  + apply Sets_included_trans with y0; auto.
    apply Sets_included_union2.
Qed.

#[export] Instance Sets_union_congr {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) Sets.union.
Proof.
  hnf; intros; hnf; intros.
  apply Sets_equiv_Sets_included in H.
  apply Sets_equiv_Sets_included in H0.
  apply Sets_equiv_Sets_included; split;
  apply Sets_union_mono; tauto.
Qed.

#[export] Instance Sets_intersect_mono {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.included ==> Sets.included ==> Sets.included) Sets.intersect.
Proof.
  unfold Proper, respectful.
  intros.
  apply Sets_included_intersect.
  + rewrite <- H.
    apply Sets_intersect_included1.
  + rewrite <- H0.
    apply Sets_intersect_included2.
Qed.

#[export] Instance Sets_intersect_congr {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) Sets.intersect.
Proof.
  hnf; intros; hnf; intros.
  apply Sets_equiv_Sets_included in H.
  apply Sets_equiv_Sets_included in H0.
  apply Sets_equiv_Sets_included; split;
  apply Sets_intersect_mono; tauto.
Qed.

#[export] Instance Sets_omega_union_mono {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.included ==> Sets.included) Sets.omega_union.
Proof.
  unfold Proper, respectful.
  intros.
  apply Sets_omega_union_included.
  intros.
  apply Sets_included_trans with (y n); auto.
  apply Sets_included_omega_union.
Qed.

#[export] Instance Sets_omega_union_congr {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv) Sets.omega_union.
Proof.
  hnf; intros.
  apply Sets_equiv_Sets_included; split;
  apply Sets_omega_union_mono;
  intros n; specialize (H n);
  apply Sets_equiv_Sets_included in H; tauto.
Qed.

#[export] Instance Sets_omega_intersect_mono {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.included ==> Sets.included) Sets.omega_intersect.
Proof.
  unfold Proper, respectful.
  intros.
  apply Sets_included_omega_intersect.
  intros.
  apply Sets_included_trans with (x n); auto.
  apply Sets_omega_intersect_included.
Qed.

#[export] Instance Sets_omega_intersect_congr {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv) Sets.omega_intersect.
Proof.
  hnf; intros.
  apply Sets_equiv_Sets_included; split;
  apply Sets_omega_intersect_mono;
  intros n; specialize (H n);
  apply Sets_equiv_Sets_included in H; tauto.
Qed.

Lemma Sets_intersect_absorb1 {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y,
    Sets.included x y ->
    Sets.equiv (Sets.intersect x y) x.
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + apply Sets_intersect_included1.
  + apply Sets_included_intersect.
    - reflexivity.
    - auto.
Qed.

Lemma Sets_intersect_absorb2 {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y,
    Sets.included x y ->
    Sets.equiv (Sets.intersect y x) x.
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + apply Sets_intersect_included2.
  + apply Sets_included_intersect.
    - auto.
    - reflexivity.
Qed.

Lemma Sets_union_absorb1 {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y,
    Sets.included y x ->
    Sets.equiv (Sets.union x y) x.
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + apply Sets_union_included.
    - reflexivity.
    - auto.
  + apply Sets_included_union1.
Qed.

Lemma Sets_union_absorb2 {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y,
    Sets.included x y ->
    Sets.equiv (Sets.union x y) y.
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + apply Sets_union_included.
    - auto.
    - reflexivity.
  + apply Sets_included_union2.
Qed.

Lemma Sets_union_comm {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall x y,
  Sets.equiv (Sets.union x y) (Sets.union y x).
Proof.
  intros.
  rewrite Sets_equiv_Sets_included; split; apply Sets_union_included;
  first [ apply Sets_included_union1 | apply Sets_included_union2 ].
Qed.

Lemma Sets_union_assoc {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y z,
    Sets.equiv
      (Sets.union (Sets.union x y) z)
      (Sets.union x (Sets.union y z)).
Proof.
  intros.
  apply Sets_equiv_Sets_included; split;
    repeat apply Sets_union_included.
  + apply Sets_included_union1.
  + rewrite <- Sets_included_union2.
    apply Sets_included_union1.
  + rewrite <- Sets_included_union2.
    apply Sets_included_union2.
  + rewrite <- Sets_included_union1.
    apply Sets_included_union1.
  + rewrite <- Sets_included_union1.
    apply Sets_included_union2.
  + apply Sets_included_union2.
Qed.

Lemma Sets_intersect_comm {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall x y,
  Sets.equiv (Sets.intersect x y) (Sets.intersect y x).
Proof.
  intros.
  rewrite Sets_equiv_Sets_included; split; apply Sets_included_intersect;
  first [ apply Sets_intersect_included1 | apply Sets_intersect_included2 ].
Qed.

Lemma Sets_intersect_assoc {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y z,
    Sets.equiv
      (Sets.intersect (Sets.intersect x y) z)
      (Sets.intersect x (Sets.intersect y z)).
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + repeat apply Sets_included_intersect.
    - rewrite Sets_intersect_included1.
      apply Sets_intersect_included1.
    - rewrite Sets_intersect_included1.
      apply Sets_intersect_included2.
    - apply Sets_intersect_included2.
  + repeat apply Sets_included_intersect.
    - apply Sets_intersect_included1.
    - rewrite Sets_intersect_included2.
      apply Sets_intersect_included1.
    - rewrite Sets_intersect_included2.
      apply Sets_intersect_included2.
Qed.

Lemma Sets_union_included_strong1 {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}:
  forall x y z u, Sets.included (Sets.intersect u x) z -> Sets.included (Sets.intersect u y) z -> Sets.included (Sets.intersect u (Sets.union x y)) z.
Proof.
  intros.
  rewrite Sets_intersect_comm in H, H0 |- *.
  apply Sets_union_included_strong2; auto.
Qed.

Lemma Sets_union_empty {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall x,
  Sets.equiv (Sets.union x Sets.empty) x.
Proof.
  intros.
  rewrite Sets_equiv_Sets_included; split.
  + apply Sets_union_included.
    - reflexivity.
    - apply Sets_empty_included.
  + apply Sets_included_union1.
Qed.

Lemma Sets_empty_union {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall x,
  Sets.equiv (Sets.union Sets.empty x) x.
Proof.
  intros.
  rewrite Sets_equiv_Sets_included; split.
  + apply Sets_union_included.
    - apply Sets_empty_included.
    - reflexivity.
  + apply Sets_included_union2.
Qed.

Lemma Sets_prop_inj_included_prop_inj {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall (P Q: Prop),
  (P -> Q) ->
  Sets.included
    (Sets.prop_inj P)
    (Sets.prop_inj Q).
Proof.
  intros.
  rewrite <- Sets_intersect_full.
  apply Sets_prop_inj_included.
  intros.
  apply Sets_included_prop_inj.
  tauto.
Qed.

Lemma Sets_prop_inj_and {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall P Q,
  Sets.equiv
    (Sets.prop_inj (P /\ Q))
    (Sets.intersect (Sets.prop_inj P) (Sets.prop_inj Q)).
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + apply Sets_included_intersect.
    - apply Sets_prop_inj_included_prop_inj; tauto.
    - apply Sets_prop_inj_included_prop_inj; tauto.
  + apply Sets_prop_inj_included.
    intros.
    apply Sets_prop_inj_included_prop_inj; tauto.
Qed.

Lemma Sets_prop_inj_or {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall P Q,
  Sets.equiv
    (Sets.prop_inj (P \/ Q))
    (Sets.union (Sets.prop_inj P) (Sets.prop_inj Q)).
Proof.
  intros.
  apply Sets_equiv_Sets_included; split.
  + rewrite <- Sets_intersect_full.
    apply Sets_prop_inj_included.
    intros [? | ?].
    - rewrite <- Sets_included_union1.
      apply Sets_included_prop_inj, H.
    - rewrite <- Sets_included_union2.
      apply Sets_included_prop_inj, H.
  + apply Sets_union_included.
    - apply Sets_prop_inj_included_prop_inj; tauto.
    - apply Sets_prop_inj_included_prop_inj; tauto.
Qed.

Lemma Sets_test1_imply {S T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall (P Q: S -> Prop),
  (forall a, P a -> Q a) ->
  Sets.included (Sets.test1 P) (Sets.test1 Q).
Proof.
  intros.
  unfold_SETS_tac;intros.
  apply Sets_prop_inj_included_prop_inj.
  auto.
Qed.

Lemma Sets_test1_and {S T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall (P Q: S -> Prop),
  Sets.equiv
    (Sets.test1 (fun a => P a /\ Q a))
    (Sets.intersect (Sets.test1 P) (Sets.test1 Q)).
Proof.
  intros.
  unfold_SETS_tac; intros.
  apply Sets_prop_inj_and.
Qed.

Lemma Sets_test1_or {S T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall (P Q: S -> Prop),
  Sets.equiv
    (Sets.test1 (fun a => P a \/ Q a))
    (Sets.union (Sets.test1 P) (Sets.test1 Q)).
Proof.
  intros.
  unfold_SETS_tac; intros.
  apply Sets_prop_inj_or.
Qed.

Lemma omega_union_union {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall x y xs ys zs,
  (forall n, zs n = Sets.union (xs n) (ys n)) ->
  Sets.equiv x (Sets.omega_union xs) /\ (forall n, Sets.included (xs n) (xs (S n))) ->
  Sets.equiv y (Sets.omega_union ys) /\ (forall n, Sets.included (ys n) (ys (S n))) ->
  Sets.equiv (Sets.union x y) (Sets.omega_union zs) /\ (forall n, Sets.included (zs n) (zs (S n))).
Proof.
  intros ? ? ? ? ? Hzs [Hx Hxs] [Hy Hys].
  rewrite Hx, Hy; clear x y Hx Hy.
  split; [apply Sets_equiv_Sets_included; split |].
  + apply Sets_union_included; apply Sets_omega_union_included; intros n.
    - rewrite (Sets_included_union1 _ (ys n)), <- Hzs.
      apply Sets_included_omega_union.
    - rewrite (Sets_included_union2 (xs n)), <- Hzs.
      apply Sets_included_omega_union.
  + apply Sets_omega_union_included; intros n.
    rewrite Hzs.
    apply Sets_union_included.
    - rewrite <- Sets_included_union1.
      apply Sets_included_omega_union.
    - rewrite <- Sets_included_union2.
      apply Sets_included_omega_union.
  + intros; rewrite !Hzs.
    apply Sets_union_mono; auto.
Qed.

Lemma omega_union_const {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: forall x,
  Sets.equiv x (Sets.omega_union (fun _ => x)) /\ (forall n: nat, Sets.included x x).
Proof.
  intros.
  split; [apply Sets_equiv_Sets_included; split |].
  + change x with ((fun _ => x) O) at 1.
    apply Sets_included_omega_union.
  + apply Sets_omega_union_included; intros n.
    reflexivity.
  + intros.
    reflexivity.
Qed.

#[export] Instance Prop_SETS_Properties: SETS_Properties Prop.
Proof.
  constructor; unfold Proper, respectful; unfold_SETS_tac; simpl;
  hnf; intros; try tauto.
  + firstorder.
  + firstorder.
  + firstorder.
  + firstorder.
  + firstorder.
  + firstorder.
  + firstorder.
  + firstorder.
Qed.

#[export] Instance lift_SETS_Properties (A B: Type) (_SETS: Sets.SETS B) (_SETS_Properties: SETS_Properties B): SETS_Properties (A -> B).
Proof.
  constructor; unfold Proper, respectful; unfold_SETS_tac; hnf; intros.
  + apply Sets_included_refl.
  + eapply Sets_included_trans; eauto.
  + split; intros.
    - split; intros; specialize (H a);
      rewrite Sets_equiv_Sets_included in H;
      tauto.
    - destruct H.
      intros.
      rewrite Sets_equiv_Sets_included; auto.
  + apply Sets_empty_included.
  + apply Sets_included_full.
  + apply Sets_prop_inj_included; auto.
  + apply Sets_included_prop_inj; auto.
  + apply Sets_intersect_included1.
  + apply Sets_intersect_included2.
  + apply Sets_included_intersect; auto.
  + apply Sets_included_union1.
  + apply Sets_included_union2.
  + apply Sets_union_included_strong2; auto.
  + apply (Sets_included_omega_union (fun n => xs n a)).
  + apply (Sets_omega_union_included (fun n => xs n a)).
    auto.
  + apply (Sets_omega_intersect_included (fun n => xs n a)).
  + apply (Sets_included_omega_intersect (fun n => xs n a)).
    auto.
  + apply Sets_included_general_union.
    exists x; auto.
  + apply Sets_general_union_included.
    intros ? [? [? ?]].
    subst.
    auto.
  + apply Sets_general_intersect_included.
    exists x; auto.
  + apply Sets_included_general_intersect.
    intros ? [? [? ?]].
    subst.
    auto.
Qed.

#[export] Instance Sets_prop_inj_mono {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.included ==> Sets.included) (@Sets.prop_inj T _).
Proof.
  unfold Proper, respectful, Sets.test1.
  unfold_SETS_tac.
  intros.
  apply Sets_prop_inj_included_prop_inj.
  auto.
Qed.

#[export] Instance Sets_prop_inj_congr {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv) (@Sets.prop_inj T _).
Proof.
  unfold Proper, respectful.
  intros.
  apply Sets_equiv_Sets_included.
  rewrite Sets_equiv_Sets_included in H.
  split; apply Sets_prop_inj_mono; tauto.
Qed.

#[export] Instance Sets_test1_mono {S T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.included ==> Sets.included) (@Sets.test1 S T _).
Proof.
  unfold Proper, respectful, Sets.test1.
  intros; intros ?.
  rewrite (H a).
  reflexivity.
Qed.

#[export] Instance Sets_test1_congr {S T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv) (@Sets.test1 S T _).
Proof.
  unfold Proper, respectful, Sets.test1.
  intros; intros ?.
  rewrite (H a).
  reflexivity.
Qed.

#[export] Instance Sets_filter1_mono {S T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.included ==> Sets.included ==> Sets.included) (@Sets.filter1 S T _).
Proof.
  unfold Proper, respectful.
  intros.
  rewrite !Sets_filter1_defn.
  rewrite H, H0.
  reflexivity.
Qed.

#[export] Instance Sets_filter1_congr {S T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) (@Sets.filter1 S T _).
Proof.
  unfold Proper, respectful.
  intros.
  rewrite !Sets_filter1_defn.
  rewrite H, H0.
  reflexivity.
Qed.

#[export] Instance Sets_lift1_mono {S T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.included ==> Sets.included) (@Sets.lift1 S T _).
Proof.
  unfold Proper, respectful.
  intros.
  unfold Sets.lift1; intros ?.
  auto.
Qed.

#[export] Instance Sets_lift1_congr {S T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv) (@Sets.lift1 S T _).
Proof.
  unfold Proper, respectful.
  intros.
  unfold Sets.lift1; intros ?.
  auto.
Qed.

#[export] Instance Sets_general_union_congr {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv) Sets.general_union.
Proof.
  intros.
  hnf; intros.
  rewrite Sets_equiv_Sets_included.
  split.
  + apply Sets_general_union_included; intros.
    apply Sets_included_general_union.
    rewrite (H _) in H0.
    tauto.
  + apply Sets_general_union_included; intros.
    apply Sets_included_general_union.
    rewrite (H _).
    tauto.
Qed.

#[export] Instance Sets_general_intersect_congr {T} {_SETS: Sets.SETS T} {_SETS_Properties: SETS_Properties T}: Proper (Sets.equiv ==> Sets.equiv) Sets.general_intersect.
Proof.
  intros.
  hnf; intros.
  rewrite Sets_equiv_Sets_included.
  split.
  + apply Sets_included_general_intersect; intros.
    apply Sets_general_intersect_included.
    rewrite (H _).
    tauto.
  + apply Sets_included_general_intersect; intros.
    apply Sets_general_intersect_included.
    rewrite (H _) in H0.
    tauto.
Qed.

#[export] Instance Sets_complement_equiv A:
  Proper (Sets.equiv ==> Sets.equiv) (@Sets.complement A).
Proof.
  unfold_SETS_tac.
  unfold Sets.complement.
  intros S1 S2 ?.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma Sets_complement_complement: forall A (S: A -> Prop),
  Sets.equiv (Sets.complement (Sets.complement S)) S.
Proof.
  intros.
  unfold Sets.complement; unfold_SETS_tac.
  intros.
  tauto.
Qed.

Ltac solve_mono tac :=
  match goal with
  | |- Proper _ _ =>
         cbv beta delta [Proper respectful flip]; intros; solve_mono tac
  | |- Sets.included ?A ?A =>
         reflexivity
  | |- Sets.included (Sets.union _ _) (Sets.union _ _) =>
         refine (Sets_union_mono _ _ _ _ _ _); solve_mono tac
  | |- Sets.included (Sets.intersect _ _) (Sets.intersect _ _) =>
         refine (Sets_intersect_mono _ _ _ _ _ _); solve_mono tac
  | |- Sets.included (Sets.prop_inj _) (Sets.prop_inj _) =>
         refine (Sets_prop_inj_mono _ _ _); solve_mono tac
  | |- Sets.included (Sets.test1 _) (Sets.test1 _) =>
         refine (Sets_test1_mono _ _ _); solve_mono tac
  | |- Sets.included (Sets.lift1 _) (Sets.lift1 _) =>
         refine (Sets_lift1_mono _ _ _); solve_mono tac
  | |- Sets.included (Sets.filter1 _ _) (Sets.filter1 _ _) =>
         refine (Sets_filter1_mono _ _ _ _ _ _); solve_mono tac
  | |- _ => first [assumption | tac]
  end.

Declare Scope sets_scope.
Delimit Scope sets_scope with sets.
Local Open Scope sets_scope.

Notation "[ ]":= Sets.empty (format "[ ]"): sets_scope.
Notation "∅":= Sets.empty (at level 5, no associativity): sets_scope.
Notation "[ x ]":= (Sets.singleton x) : sets_scope.
Notation "x ∩ y" := (Sets.intersect x y)(at level 11, left associativity): sets_scope.
Notation "x ∪ y" := (Sets.union x y)(at level 12, left associativity): sets_scope.
Notation "⋃ x" := (Sets.omega_union x)(at level 10, no associativity): sets_scope.
Notation "⋂ x" := (Sets.omega_intersect x)(at level 10, no associativity): sets_scope.
Notation "x == y" := (Sets.equiv x y) (at level 70, no associativity): sets_scope.
Notation "x ∈ y" := (Sets.In x y) (at level 70, no associativity): sets_scope.
Notation "x ⊆ y" := (Sets.included x y) (at level 70, no associativity): sets_scope.

Ltac sets_unfold := unfold Sets.In, Sets.singleton; unfold_SETS_tac.

