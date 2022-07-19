Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.
From PromisingLib Require Import Event.

Set Implicit Arguments.


Module BoolMap.
  Definition t :=  Loc.t -> bool.

  Definition bot: t := fun _ => false.
  Definition top: t := fun _ => true.

  Definition le (lhs rhs: t): Prop :=
    forall loc (LHS: lhs loc = true), rhs loc = true.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. auto.
  Qed.
  Next Obligation.
    ii. auto.
  Qed.

  Lemma antisym l r
        (LR: le l r)
        (RL: le r l):
    l = r.
  Proof.
    extensionality loc.
    specialize (LR loc). specialize (RL loc).
    destruct (l loc) eqn:L, (r loc) eqn:R; eauto.
    exploit LR; eauto.
  Qed.

  Lemma bot_spec bm: le bot bm.
  Proof.
    ii. ss.
  Qed.

  Lemma top_spec bm: le bm top.
  Proof.
    ii. ss.
  Qed.

  Definition disjoint (x y: t): Prop :=
    forall loc (GET1: x loc = true) (GET2: y loc = true), False.

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    ii. eauto.
  Qed.

  Lemma bot_disjoint bm: disjoint bot bm.
  Proof.
    ii. ss.
  Qed.

  Definition finite (bm: t): Prop :=
    exists dom,
    forall loc (GET: bm loc = true),
      List.In loc dom.

  Lemma bot_finite: finite bot.
  Proof.
    exists []. ss.
  Qed.


  Variant add (bm1: t) (loc: Loc.t) (bm2: t): Prop :=
  | add_intro
      (GET: bm1 loc = false)
      (BM2: bm2 = LocFun.add loc true bm1)
  .
  #[global] Hint Constructors add: core.

  Variant remove (bm1: t) (loc: Loc.t) (bm2: t): Prop :=
  | remove_intro
      (GET: bm1 loc = true)
      (BM2: bm2 = LocFun.add loc false bm1)
  .
  #[global] Hint Constructors remove: core.


  Lemma add_o
        bm2 bm1 loc l
        (ADD: add bm1 loc bm2):
    bm2 l = if Loc.eq_dec l loc then true else bm1 l.
  Proof.
    inv ADD. unfold LocFun.add. ss.
  Qed.

  Lemma add_get0
        bm1 loc bm2
        (ADD: add bm1 loc bm2):
    (<<GET1: bm1 loc = false>>) /\
    (<<GET2: bm2 loc = true>>).
  Proof.
    inv ADD. split; ss.
    unfold LocFun.add. condtac; ss.
  Qed.

  Lemma add_get1
        bm1 loc bm2 l
        (ADD: add bm1 loc bm2)
        (GET: bm1 l = true):
    bm2 l = true.
  Proof.
    inv ADD. unfold LocFun.add. condtac; ss.
  Qed.

  Lemma add_le
        bm1 loc bm2
        (ADD: add bm1 loc bm2):
    le bm1 bm2.
  Proof.
    ii. erewrite add_o; eauto. condtac; ss.
  Qed.

  Lemma add_finite
        bm1 loc bm2
        (ADD: add bm1 loc bm2)
        (FINITE: finite bm1):
    finite bm2.
  Proof.
    inv ADD. inv FINITE.
    exists (loc :: x). unfold LocFun.add. intro.
    condtac; ss; eauto.
  Qed.

  Lemma remove_o
        bm2 bm1 loc l
        (REMOVE: remove bm1 loc bm2):
    bm2 l = if Loc.eq_dec l loc then false else bm1 l.
  Proof.
    inv REMOVE. unfold LocFun.add. ss.
  Qed.

  Lemma remove_get0
        bm1 loc bm2
        (REMOVE: remove bm1 loc bm2):
    (<<GET1: bm1 loc = true>>) /\
    (<<GET2: bm2 loc = false>>).
  Proof.
    inv REMOVE. split; ss.
    unfold LocFun.add. condtac; ss.
  Qed.

  Lemma remove_get1
        bm1 loc bm2 l
        (REMOVE: remove bm1 loc bm2)
        (GET: bm1 l = true):
    (<<LOC: l = loc>>) \/
    (<<GET2: bm2 l = true>>).
  Proof.
    inv REMOVE. unfold LocFun.add. condtac; auto.
  Qed.

  Lemma remove_le
        bm1 loc bm2
        (REMOVE: remove bm1 loc bm2):
    le bm2 bm1.
  Proof.
    ii. revert LHS.
    erewrite remove_o; eauto. condtac; ss.
  Qed.

  Lemma remove_finite
        bm1 loc bm2
        (REMOVE: remove bm1 loc bm2)
        (FINITE: finite bm1):
    finite bm2.
  Proof.
    inv REMOVE. inv FINITE.
    exists x. unfold LocFun.add. intro.
    condtac; ss; eauto.
  Qed.


  Definition minus (gbm bm: t): t :=
    fun loc => andb (gbm loc) (negb (bm loc)).

  Lemma minus_true_spec gbm bm loc:
    minus gbm bm loc = true <->
    gbm loc = true /\ bm loc = false.
  Proof.
    unfold minus. split; i.
    - rewrite Bool.andb_true_iff in *. des. split; ss.
      destruct (bm loc); ss.
    - des. rewrite H, H0. ss.
  Qed.

  Lemma add_minus
        gbm1 gbm2
        bm1 bm2
        loc
        (GADD: add gbm1 loc gbm2)
        (ADD: add bm1 loc bm2):
    minus gbm1 bm1 = minus gbm2 bm2.
  Proof.
    extensionality l. unfold minus.
    inv GADD. inv ADD.
    unfold LocFun.add. condtac; ss. subst.
    rewrite GET, GET0. ss.
  Qed.

  Lemma remove_minus
        gbm1 gbm2
        bm1 bm2
        loc
        (GREMOVE: remove gbm1 loc gbm2)
        (REMOVE: remove bm1 loc bm2):
    minus gbm1 bm1 = minus gbm2 bm2.
  Proof.
    extensionality l. unfold minus.
    inv GREMOVE. inv REMOVE.
    unfold LocFun.add. condtac; ss. subst.
    rewrite GET, GET0. ss.
  Qed.
End BoolMap.
