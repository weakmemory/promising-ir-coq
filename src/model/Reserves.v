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


Module Reserves.
  Import BoolMap.

  Variant reserve (rsv1 grsv1: t) (loc: Loc.t) (rsv2 grsv2: t): Prop :=
  | reserve_intro
      (ADD: add rsv1 loc rsv2)
      (GADD: add grsv1 loc grsv2)
  .
  #[global] Hint Constructors reserve: core.

  Variant cancel (rsv1 grsv1: t) (loc: Loc.t) (rsv2 grsv2: t): Prop :=
  | cancel_intro
      (REMOVE: remove rsv1 loc rsv2)
      (GREMOVE: remove grsv1 loc grsv2)
  .
  #[global] Hint Constructors cancel: core.


  Lemma reserve_le
        rsv1 grsv1 loc rsv2 grsv2
        (RESERVE: reserve rsv1 grsv1 loc rsv2 grsv2)
        (LE1: le rsv1 grsv1):
    le rsv2 grsv2.
  Proof.
    ii. revert LHS.
    inv RESERVE. inv ADD. inv GADD.
    unfold LocFun.add. condtac; ss. eauto.
  Qed.

  Lemma cancel_le
        rsv1 grsv1 loc rsv2 grsv2
        (CANCEL: cancel rsv1 grsv1 loc rsv2 grsv2)
        (LE1: le rsv1 grsv1):
    le rsv2 grsv2.
  Proof.
    ii. revert LHS.
    inv CANCEL. inv REMOVE. inv GREMOVE.
    unfold LocFun.add. condtac; ss. eauto.
  Qed.

  Lemma reserve_disjoint
        rsv1 grsv1 loc rsv2 grsv2
        ctx
        (RESERVE: reserve rsv1 grsv1 loc rsv2 grsv2)
        (LE_CTX: le ctx grsv1)
        (DISJOINT: disjoint rsv1 ctx):
    (<<DISJOINT: disjoint rsv2 ctx>>) /\
    (<<LE_CTX: le ctx grsv2>>).
  Proof.
    inv RESERVE. inv ADD. inv GADD. splits; ii.
    - revert GET1. unfold LocFun.add.
      condtac; ss; subst; eauto.
    - unfold LocFun.add. condtac; ss; eauto.
  Qed.

  Lemma cancel_disjoint
        rsv1 grsv1 loc rsv2 grsv2
        ctx
        (CANCEL: cancel rsv1 grsv1 loc rsv2 grsv2)
        (LE_CTX: le ctx grsv1)
        (DISJOINT: disjoint rsv1 ctx):
    (<<DISJOINT: disjoint rsv2 ctx>>) /\
    (<<LE_CTX: le ctx grsv2>>).
  Proof.
    inv CANCEL. inv REMOVE. inv GREMOVE. splits; ii.
    - revert GET1. unfold LocFun.add.
      condtac; ss; subst; eauto.
    - unfold LocFun.add. condtac; ss; subst; eauto.
  Qed.

  Lemma reserve_finite
        rsv1 grsv1 loc rsv2 grsv2
        (RESERVE: reserve rsv1 grsv1 loc rsv2 grsv2)
        (FINITE: finite rsv1):
    finite rsv2.
  Proof.
    inv RESERVE. eauto using add_finite.
  Qed.

  Lemma cancel_finite
        rsv1 grsv1 loc rsv2 grsv2
        (CANCEL: cancel rsv1 grsv1 loc rsv2 grsv2)
        (FINITE: finite rsv1):
    finite rsv2.
  Proof.
    inv CANCEL. eauto using remove_finite.
  Qed.
End Reserves.
