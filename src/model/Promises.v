Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.
From PromisingLib Require Import Event.

Require Import Time.

Set Implicit Arguments.


Module Promises.
  Definition t :=  Loc.t -> bool.

  Definition bot: t := fun _ => false.

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

  Lemma bot_spec prm: le bot prm.
  Proof.
    ii. ss.
  Qed.

  Definition disjoint (x y: t): Prop :=
    forall loc (GET1: x loc = true) (GET2: y loc = true), False.

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    ii. eauto.
  Qed.

  Lemma bot_disjoint prm: disjoint bot prm.
  Proof.
    ii. ss.
  Qed.

  Definition finite (prm: t): Prop :=
    exists dom,
    forall loc (GET: prm loc = true),
      List.In loc dom.

  Lemma bot_finite: finite bot.
  Proof.
    exists []. ss.
  Qed.

  
  Variant add (prm1: t) (loc: Loc.t) (prm2: t): Prop :=
  | add_intro
      (GET: prm1 loc = false)
      (PRM2: prm2 = LocFun.add loc true prm1)
  .

  Variant remove (prm1: t) (loc: Loc.t) (prm2: t): Prop :=
  | remove_intro
      (GET: prm1 loc = true)
      (PRM2: prm2 = LocFun.add loc false prm1)
  .

  Variant promise (prm1 gprm1: t) (loc: Loc.t) (prm2 gprm2: t): Prop :=
  | promise_intro
      (ADD: add prm1 loc prm2)
      (GADD: add gprm1 loc gprm2)
  .

  Variant fulfill (prm1 gprm1: t) (loc: Loc.t) (ord: Ordering.t) (prm2 gprm2: t): Prop :=
  | fulfill_refl
      (PROMISES: prm2 = prm1)
      (GPROMISES: gprm2 = gprm1)
  | fulfill_remove
      (ORD: Ordering.le ord Ordering.na)
      (REMOVE: remove prm1 loc prm2)
      (GREMOVE: remove gprm1 loc gprm2)
  .


  Lemma add_o
        prm2 prm1 loc l
        (ADD: add prm1 loc prm2):
    prm2 l = if Loc.eq_dec l loc then true else prm1 l.
  Proof.
    inv ADD. unfold LocFun.add. ss.
  Qed.

  Lemma add_get0
        prm1 loc prm2
        (ADD: add prm1 loc prm2):
    (<<GET1: prm1 loc = false>>) /\
    (<<GET2: prm2 loc = true>>).
  Proof.
    inv ADD. split; ss.
    unfold LocFun.add. condtac; ss.
  Qed.

  Lemma add_get1
        prm1 loc prm2 l
        (ADD: add prm1 loc prm2)
        (GET: prm1 l = true):
    prm2 l = true.
  Proof.
    inv ADD. unfold LocFun.add. condtac; ss.
  Qed.

  Lemma add_finite
        prm1 loc prm2
        (ADD: add prm1 loc prm2)
        (FINITE: finite prm1):
    finite prm2.
  Proof.
    inv ADD. inv FINITE.
    exists (loc :: x). unfold LocFun.add. intro.
    condtac; ss; eauto.
  Qed.

  Lemma remove_o
        prm2 prm1 loc l
        (REMOVE: remove prm1 loc prm2):
    prm2 l = if Loc.eq_dec l loc then false else prm1 l.
  Proof.
    inv REMOVE. unfold LocFun.add. ss.
  Qed.

  Lemma remove_get0
        prm1 loc prm2
        (REMOVE: remove prm1 loc prm2):
    (<<GET1: prm1 loc = true>>) /\
    (<<GET2: prm2 loc = false>>).
  Proof.
    inv REMOVE. split; ss.
    unfold LocFun.add. condtac; ss.
  Qed.

  Lemma remove_get1
        prm1 loc prm2 l
        (REMOVE: remove prm1 loc prm2)
        (GET: prm1 l = true):
    (<<LOC: l = loc>>) \/
    (<<GET2: prm2 l = true>>).
  Proof.
    inv REMOVE. unfold LocFun.add. condtac; auto.
  Qed.

  Lemma remove_finite
        prm1 loc prm2
        (REMOVE: remove prm1 loc prm2)
        (FINITE: finite prm1):
    finite prm2.
  Proof.
    inv REMOVE. inv FINITE.
    exists x. unfold LocFun.add. intro.
    condtac; ss; eauto.
  Qed.

  Lemma promise_le
        prm1 gprm1 loc prm2 gprm2
        (PROMISE: promise prm1 gprm1 loc prm2 gprm2)
        (LE1: le prm1 gprm1):
    le prm2 gprm2.
  Proof.
    ii. revert LHS.
    inv PROMISE. inv ADD. inv GADD.
    unfold LocFun.add. condtac; ss. eauto.
  Qed.

  Lemma fulfill_le
        prm1 gprm1 loc ord prm2 gprm2
        (FULFILL: fulfill prm1 gprm1 loc ord prm2 gprm2)
        (LE1: le prm1 gprm1):
    le prm2 gprm2.
  Proof.
    ii. revert LHS.
    inv FULFILL; auto. inv REMOVE. inv GREMOVE.
    unfold LocFun.add. condtac; ss. eauto.
  Qed.

  Lemma promise_disjoint
        prm1 gprm1 loc prm2 gprm2
        ctx
        (PROMISE: promise prm1 gprm1 loc prm2 gprm2)
        (LE_CTX: le ctx gprm1)
        (DISJOINT: disjoint prm1 ctx):
    (<<DISJOINT: disjoint prm2 ctx>>) /\
    (<<LE_CTX: le ctx gprm2>>).
  Proof.
    inv PROMISE. inv ADD. inv GADD. splits; ii.
    - revert GET1. unfold LocFun.add.
      condtac; ss; subst; eauto.
    - unfold LocFun.add. condtac; ss; eauto.
  Qed.

  Lemma fulfill_disjoint
        prm1 gprm1 loc ord prm2 gprm2
        ctx
        (FULFILL: fulfill prm1 gprm1 loc ord prm2 gprm2)
        (LE_CTX: le ctx gprm1)
        (DISJOINT: disjoint prm1 ctx):
    (<<DISJOINT: disjoint prm2 ctx>>) /\
    (<<LE_CTX: le ctx gprm2>>).
  Proof.
    inv FULFILL; auto. inv REMOVE. inv GREMOVE. splits; ii.
    - revert GET1. unfold LocFun.add.
      condtac; ss; subst; eauto.
    - unfold LocFun.add. condtac; ss; subst; eauto.
  Qed.

  Lemma promise_finite
        prm1 gprm1 loc prm2 gprm2
        (PROMISE: promise prm1 gprm1 loc prm2 gprm2)
        (FINITE1: finite prm1):
    finite prm2.
  Proof.
    inv PROMISE. eauto using add_finite.
  Qed.

  Lemma fulfill_finite
        prm1 gprm1 loc ord prm2 gprm2
        (FULFILL: fulfill prm1 gprm1 loc ord prm2 gprm2)
        (FINITE1: finite prm1):
    finite prm2.
  Proof.
    inv FULFILL; auto. eauto using remove_finite.
  Qed.
End Promises.
