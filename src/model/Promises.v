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
End Promises.
