Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.
From PromisingLib Require Import Event.

Require Import BoolMap.

Set Implicit Arguments.


Module Promises.
  Import BoolMap.

  Variant promise (prm1 gprm1: t) (loc: Loc.t) (prm2 gprm2: t): Prop :=
  | promise_intro
      (ADD: add prm1 loc prm2)
      (GADD: add gprm1 loc gprm2)
  .
  #[global] Hint Constructors promise: core.

  Variant fulfill (prm1 gprm1: t) (loc: Loc.t) (ord: Ordering.t) (prm2 gprm2: t): Prop :=
  | fulfill_refl
      (PROMISES: prm2 = prm1)
      (GPROMISES: gprm2 = gprm1)
  | fulfill_remove
      (ORD: Ordering.le ord Ordering.na)
      (REMOVE: remove prm1 loc prm2)
      (GREMOVE: remove gprm1 loc gprm2)
  .
  #[global] Hint Constructors fulfill: core.


  Lemma promise_le
        prm1 gprm1 loc prm2 gprm2
        (PROMISE: promise prm1 gprm1 loc prm2 gprm2)
        (LE1: le prm1 gprm1):
    le prm2 gprm2.
  Proof.
    inv PROMISE. eauto using BoolMap.le_add.
  Qed.

  Lemma fulfill_le
        prm1 gprm1 loc ord prm2 gprm2
        (FULFILL: fulfill prm1 gprm1 loc ord prm2 gprm2)
        (LE1: le prm1 gprm1):
    le prm2 gprm2.
  Proof.
    inv FULFILL; eauto using BoolMap.le_remove.
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

  Lemma promise_minus
        prm1 gprm1 loc prm2 gprm2
        (PROMISE: promise prm1 gprm1 loc prm2 gprm2):
    minus gprm1 prm1 = minus gprm2 prm2.
  Proof.
    inv PROMISE. eauto using add_minus.
  Qed.

  Lemma fulfill_minus
        prm1 gprm1 loc ord prm2 gprm2
        (FULFILL: fulfill prm1 gprm1 loc ord prm2 gprm2):
    minus gprm1 prm1 = minus gprm2 prm2.
  Proof.
    inv FULFILL; ss. eauto using remove_minus.
  Qed.

  Lemma promise_minus_inv
        prm1 gprm1 loc prm2 gprm2
        (PROMISE: promise prm1 gprm1 loc prm2 gprm2):
    minus prm1 gprm1 = minus prm2 gprm2.
  Proof.
    inv PROMISE. eauto using add_minus.
  Qed.

  Lemma fulfill_minus_inv
        prm1 gprm1 loc ord prm2 gprm2
        (FULFILL: fulfill prm1 gprm1 loc ord prm2 gprm2):
    minus prm1 gprm1 = minus prm2 gprm2.
  Proof.
    inv FULFILL; ss. eauto using remove_minus.
  Qed.


  (* reorder *)

  Lemma reorder_promise_promise
        prm0 gprm0
        loc1 prm1 gprm1
        loc2 prm2 gprm2
        (PROMISE1: promise prm0 gprm0 loc1 prm1 gprm1)
        (PROMISE2: promise prm1 gprm1 loc2 prm2 gprm2):
    exists prm1' gprm1',
      (<<PROMISE1: promise prm0 gprm0 loc2 prm1' gprm1'>>) /\
      (<<PROMISE2: promise prm1' gprm1' loc1 prm2 gprm2>>).
  Proof.
    inv PROMISE1. inv PROMISE2.
    exploit BoolMap.reorder_add_add; try exact ADD; eauto. i. des.
    exploit BoolMap.reorder_add_add; try exact GADD; eauto. i. des.
    esplits; eauto.
  Qed.

  Lemma reorder_fulfill_promise
        prm0 gprm0
        loc1 ord1 prm1 gprm1
        loc2 prm2 gprm2
        (FULFILL1: fulfill prm0 gprm0 loc1 ord1 prm1 gprm1)
        (PROMISE2: promise prm1 gprm1 loc2 prm2 gprm2)
        (LOC: loc1 <> loc2):
    exists prm1' gprm1',
      (<<PROMISE1: promise prm0 gprm0 loc2 prm1' gprm1'>>) /\
      (<<FULFILL2: fulfill prm1' gprm1' loc1 ord1 prm2 gprm2>>).
  Proof.
    inv FULFILL1; [esplits; eauto|]. inv PROMISE2.
    exploit BoolMap.reorder_remove_add; try exact REMOVE; eauto. i. des; try congr.
    exploit BoolMap.reorder_remove_add; try exact GREMOVE; eauto. i. des; try congr.
    esplits; eauto.
  Qed.

  Lemma reorder_fulfill_promise_same
        prm0 gprm0
        loc ord1 prm1 gprm1
        prm2 gprm2
        (FULFILL1: fulfill prm0 gprm0 loc ord1 prm1 gprm1)
        (PROMISE2: promise prm1 gprm1 loc prm2 gprm2):
    exists prm1' gprm1',
      (<<PROMISE1: __guard__ (prm1' = prm0 /\ gprm1' = gprm0 \/
                              promise prm0 gprm0 loc prm1' gprm1')>>) /\
      (<<FULFILL2: fulfill prm1' gprm1' loc ord1 prm2 gprm2>>).
  Proof.
    inv FULFILL1.
    { esplits; eauto. right. ss. }
    inv PROMISE2. esplits; [left; eauto|]. econs.
    - extensionality l.
      erewrite (@BoolMap.add_o prm2); eauto.
      erewrite (@BoolMap.remove_o prm1); eauto.
      condtac; ss. subst. inv REMOVE. ss.
    - extensionality l.
      erewrite (@BoolMap.add_o gprm2); eauto.
      erewrite (@BoolMap.remove_o gprm1); eauto.
      condtac; ss. subst. inv GREMOVE. ss.
  Qed.

  Lemma reorder_promise_fulfill
        prm0 gprm0
        loc1 prm1 gprm1
        loc2 ord2 prm2 gprm2
        (PROMISE1: promise prm0 gprm0 loc1 prm1 gprm1)
        (FULFILL2: fulfill prm1 gprm1 loc2 ord2 prm2 gprm2)
        (LOC: loc1 <> loc2):
    exists prm1' gprm1',
      (<<FULFILL1: fulfill prm0 gprm0 loc2 ord2 prm1' gprm1'>>) /\
      (<<PROMISE2: promise prm1' gprm1' loc1 prm2 gprm2>>).
  Proof.
    inv FULFILL2; [esplits; eauto|]. inv PROMISE1.
    exploit BoolMap.reorder_add_remove; try exact ADD; eauto. i. des; try congr.
    exploit BoolMap.reorder_add_remove; try exact GADD; eauto. i. des; try congr.
    esplits; [econs 2|]; eauto.
  Qed.

  Lemma reorder_fulfill_fulfill
        prm0 gprm0
        loc1 ord1 prm1 gprm1
        loc2 ord2 prm2 gprm2
        (FULFILL1: fulfill prm0 gprm0 loc1 ord1 prm1 gprm1)
        (FULFILL2: fulfill prm1 gprm1 loc2 ord2 prm2 gprm2)
        (LOC: loc1 <> loc2):
    exists prm1' gprm1',
      (<<FULFILL1: fulfill prm0 gprm0 loc2 ord2 prm1' gprm1'>>) /\
      (<<FULFILL2: fulfill prm1' gprm1' loc1 ord1 prm2 gprm2>>).
  Proof.
    inv FULFILL1; [esplits; eauto|].
    inv FULFILL2; [esplits; eauto|].
    exploit BoolMap.reorder_remove_remove; try exact REMOVE; eauto. i. des; try congr.
    exploit BoolMap.reorder_remove_remove; try exact GREMOVE; eauto. i. des; try congr.
    esplits; [econs 2|]; eauto.
  Qed.
End Promises.
