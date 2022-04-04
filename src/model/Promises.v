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

  Lemma bot_spec prom: le bot prom.
  Proof.
    ii. ss.
  Qed.

  Definition disjoint (x y: t): Prop :=
    forall loc (GET1: x loc = true) (GET2: y loc = true), False.

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    ii. eauto.
  Qed.

  Lemma bot_disjoint prom: disjoint bot prom.
  Proof.
    ii. ss.
  Qed.

  Definition finite (prom: t): Prop :=
    exists dom,
    forall loc (GET: prom loc = true),
      List.In loc dom.

  Lemma bot_finite: finite bot.
  Proof.
    exists []. ss.
  Qed.

  
  Variant add (prom1: t) (loc: Loc.t) (prom2: t): Prop :=
  | add_intro
      (GET: prom1 loc = false)
      (PROM2: prom2 = LocFun.add loc true prom1)
  .

  Variant remove (prom1: t) (loc: Loc.t) (prom2: t): Prop :=
  | remove_intro
      (GET: prom1 loc = true)
      (PROM2: prom2 = LocFun.add loc false prom1)
  .

  Variant promise (prom1 gprom1: t) (loc: Loc.t) (prom2 gprom2: t): Prop :=
  | promise_intro
      (PROM: add prom1 loc prom2)
      (GPROM: add gprom1 loc gprom2)
  .

  Variant fulfill (prom1 gprom1: t) (loc: Loc.t) (prom2 gprom2: t): Prop :=
  | fulfill_intro
      (PROM: remove prom1 loc prom2)
      (GPROM: remove gprom1 loc gprom2)
  .


  Lemma add_o
        prom2 prom1 loc l
        (ADD: add prom1 loc prom2):
    prom2 l = if Loc.eq_dec l loc then true else prom1 l.
  Proof.
    inv ADD. unfold LocFun.add. ss.
  Qed.

  Lemma add_get0
        prom1 loc prom2
        (ADD: add prom1 loc prom2):
    (<<GET1: prom1 loc = false>>) /\
    (<<GET2: prom2 loc = true>>).
  Proof.
    inv ADD. split; ss.
    unfold LocFun.add. condtac; ss.
  Qed.

  Lemma add_get1
        prom1 loc prom2 l
        (ADD: add prom1 loc prom2)
        (GET: prom1 l = true):
    prom2 l = true.
  Proof.
    inv ADD. unfold LocFun.add. condtac; ss.
  Qed.

  Lemma add_finite
        prom1 loc prom2
        (ADD: add prom1 loc prom2)
        (FINITE: finite prom1):
    finite prom2.
  Proof.
    inv ADD. inv FINITE.
    exists (loc :: x). unfold LocFun.add. intro.
    condtac; ss; eauto.
  Qed.

  Lemma remove_o
        prom2 prom1 loc l
        (REMOVE: remove prom1 loc prom2):
    prom2 l = if Loc.eq_dec l loc then false else prom1 l.
  Proof.
    inv REMOVE. unfold LocFun.add. ss.
  Qed.

  Lemma remove_get0
        prom1 loc prom2
        (REMOVE: remove prom1 loc prom2):
    (<<GET1: prom1 loc = true>>) /\
    (<<GET2: prom2 loc = false>>).
  Proof.
    inv REMOVE. split; ss.
    unfold LocFun.add. condtac; ss.
  Qed.

  Lemma remove_get1
        prom1 loc prom2 l
        (REMOVE: remove prom1 loc prom2)
        (GET: prom1 l = true):
    (<<LOC: l = loc>>) \/
    (<<GET2: prom2 l = true>>).
  Proof.
    inv REMOVE. unfold LocFun.add. condtac; auto.
  Qed.

  Lemma remove_finite
        prom1 loc prom2
        (REMOVE: remove prom1 loc prom2)
        (FINITE: finite prom1):
    finite prom2.
  Proof.
    inv REMOVE. inv FINITE.
    exists x. unfold LocFun.add. intro.
    condtac; ss; eauto.
  Qed.

  Lemma promise_le
        prom1 gprom1 loc prom2 gprom2
        (PROMISE: promise prom1 gprom1 loc prom2 gprom2)
        (LE1: le prom1 gprom1):
    le prom2 gprom2.
  Proof.
    ii. revert LHS.
    inv PROMISE. inv PROM. inv GPROM.
    unfold LocFun.add. condtac; ss. eauto.
  Qed.

  Lemma fulfill_le
        prom1 gprom1 loc prom2 gprom2
        (FULFILL: fulfill prom1 gprom1 loc prom2 gprom2)
        (LE1: le prom1 gprom1):
    le prom2 gprom2.
  Proof.
    ii. revert LHS.
    inv FULFILL. inv PROM. inv GPROM.
    unfold LocFun.add. condtac; ss. eauto.
  Qed.

  Lemma promise_disjoint
        prom1 gprom1 loc prom2 gprom2
        ctx
        (PROMISE: promise prom1 gprom1 loc prom2 gprom2)
        (LE_CTX: le ctx gprom1)
        (DISJOINT: disjoint prom1 ctx):
    (<<DISJOINT: disjoint prom2 ctx>>) /\
    (<<LE_CTX: le ctx gprom2>>).
  Proof.
    inv PROMISE. inv PROM. inv GPROM. splits; ii.
    - revert GET1. unfold LocFun.add.
      condtac; ss; subst; eauto.
    - unfold LocFun.add. condtac; ss; eauto.
  Qed.

  Lemma fulfill_disjoint
        prom1 gprom1 loc prom2 gprom2
        ctx
        (FULFILL: fulfill prom1 gprom1 loc prom2 gprom2)
        (LE_CTX: le ctx gprom1)
        (DISJOINT: disjoint prom1 ctx):
    (<<DISJOINT: disjoint prom2 ctx>>) /\
    (<<LE_CTX: le ctx gprom2>>).
  Proof.
    inv FULFILL. inv PROM. inv GPROM. splits; ii.
    - revert GET1. unfold LocFun.add.
      condtac; ss; subst; eauto.
    - unfold LocFun.add. condtac; ss; subst; eauto.
  Qed.
End Promises.
