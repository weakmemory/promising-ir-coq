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


Module Reserves.
  Definition t := Loc.t -> option Time.t.

  Definition eq := @eq t.

  Definition le (lhs rhs: t): Prop :=
    forall loc ts (LHS: lhs loc = Some ts),
      rhs loc = Some ts.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. eauto. Qed.
  #[global] Hint Resolve le_PreOrder_obligation_2: core.

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

  Definition bot: t := fun _ => None.

  Lemma bot_spec (tm:t): le bot tm.
  Proof.
    ii. ss.
  Qed.

  Definition disjoint (x y: t): Prop :=
    forall loc ts1 ts2
      (GET1: x loc = Some ts1)
      (GET2: y loc = Some ts2),
      False.

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    ii. eauto.
  Qed.

  Lemma bot_disjoint prom: disjoint bot prom.
  Proof.
    ii. ss.
  Qed.

  Definition finite (rsv: t): Prop :=
    exists dom,
    forall loc ts (GET: rsv loc = Some ts),
      List.In loc dom.

  Lemma bot_finite: finite bot.
  Proof.
    exists []. ss.
  Qed.

  
  Variant add (rsv1: t) (loc: Loc.t) (ts: Time.t) (rsv2: t): Prop :=
  | add_intro
      (GET: rsv1 loc = None)
      (RSV2: rsv2 = LocFun.add loc (Some ts) rsv1)
  .

  Variant remove (rsv1: t) (loc: Loc.t) (ts: Time.t) (rsv2: t): Prop :=
  | remove_intro
      (GET: rsv1 loc = Some ts)
      (RSV2: rsv2 = LocFun.add loc None rsv1)
  .

  Variant reserve (rsv1 grsv1: t) (loc: Loc.t) (ts: Time.t) (rsv2 grsv2: t): Prop :=
  | reserve_intro
      (RSV: add rsv1 loc ts rsv2)
      (GRSV: add grsv1 loc ts grsv2)
  .

  Variant cancel (rsv1 grsv1: t) (loc: Loc.t) (ts: Time.t) (rsv2 grsv2: t): Prop :=
  | cancel_intro
      (RSV: remove rsv1 loc ts rsv2)
      (GRSV: remove grsv1 loc ts grsv2)
  .


  Lemma add_o
        rsv2 rsv1 loc ts l
        (ADD: add rsv1 loc ts rsv2):
    rsv2 l = if Loc.eq_dec l loc then Some ts else rsv1 l.
  Proof.
    inv ADD. unfold LocFun.add. ss.
  Qed.

  Lemma add_get0
        rsv1 loc ts rsv2
        (ADD: add rsv1 loc ts rsv2):
    (<<GET1: rsv1 loc = None>>) /\
    (<<GET2: rsv2 loc = Some ts>>).
  Proof.
    inv ADD. split; ss.
    unfold LocFun.add. condtac; ss.
  Qed.

  Lemma add_get1
        rsv1 loc ts rsv2 l ts'
        (ADD: add rsv1 loc ts rsv2)
        (GET: rsv1 l = Some ts'):
    rsv2 l = Some ts'.
  Proof.
    inv ADD. unfold LocFun.add. condtac; ss. subst. congr.
  Qed.

  Lemma add_finite
        rsv1 loc ts rsv2
        (ADD: add rsv1 loc ts rsv2)
        (FINITE: finite rsv1):
    finite rsv2.
  Proof.
    inv ADD. inv FINITE.
    exists (loc :: x). unfold LocFun.add. intro.
    condtac; ss; eauto.
  Qed.

  Lemma remove_o
        rsv2 rsv1 loc ts l
        (REMOVE: remove rsv1 loc ts rsv2):
    rsv2 l = if Loc.eq_dec l loc then None else rsv1 l.
  Proof.
    inv REMOVE. unfold LocFun.add. ss.
  Qed.

  Lemma remove_get0
        rsv1 loc ts rsv2
        (REMOVE: remove rsv1 loc ts rsv2):
    (<<GET1: rsv1 loc = Some ts>>) /\
    (<<GET2: rsv2 loc = None>>).
  Proof.
    inv REMOVE. split; ss.
    unfold LocFun.add. condtac; ss.
  Qed.

  Lemma remove_get1
        rsv1 loc ts rsv2 l ts'
        (REMOVE: remove rsv1 loc ts rsv2)
        (GET: rsv1 l = Some ts'):
    (<<LOC: l = loc>>) \/
    (<<GET2: rsv2 l = Some ts'>>).
  Proof.
    inv REMOVE. unfold LocFun.add. condtac; auto.
  Qed.

  Lemma remove_finite
        rsv1 loc ts rsv2
        (REMOVE: remove rsv1 loc ts rsv2)
        (FINITE: finite rsv1):
    finite rsv2.
  Proof.
    inv REMOVE. inv FINITE.
    exists x. unfold LocFun.add. intro.
    condtac; ss; eauto.
  Qed.

  Lemma reserve_le
        rsv1 grsv1 loc ts rsv2 grsv2
        (RESERVE: reserve rsv1 grsv1 loc ts rsv2 grsv2)
        (LE1: le rsv1 grsv1):
    le rsv2 grsv2.
  Proof.
    ii. revert LHS.
    inv RESERVE. inv RSV. inv GRSV.
    unfold LocFun.add. condtac; ss. eauto.
  Qed.

  Lemma cancel_le
        rsv1 grsv1 loc ts rsv2 grsv2
        (CANCEL: cancel rsv1 grsv1 loc ts rsv2 grsv2)
        (LE1: le rsv1 grsv1):
    le rsv2 grsv2.
  Proof.
    ii. revert LHS.
    inv CANCEL. inv RSV. inv GRSV.
    unfold LocFun.add. condtac; ss. eauto.
  Qed.

  Lemma reserve_disjoint
        rsv1 grsv1 loc ts rsv2 grsv2
        ctx
        (RESERVE: reserve rsv1 grsv1 loc ts rsv2 grsv2)
        (LE_CTX: le ctx grsv1)
        (DISJOINT: disjoint rsv1 ctx):
    (<<DISJOINT: disjoint rsv2 ctx>>) /\
    (<<LE_CTX: le ctx grsv2>>).
  Proof.
    inv RESERVE. inv RSV. inv GRSV. splits; ii.
    - revert GET1. unfold LocFun.add.
      condtac; ss; subst; eauto. i. clarify.
      exploit LE_CTX; eauto. i. congr.
    - unfold LocFun.add. condtac; ss; eauto. clarify.
      exploit LE_CTX; eauto. i. congr.
  Qed.

  Lemma cancel_disjoint
        rsv1 grsv1 loc ts rsv2 grsv2
        ctx
        (CANCEL: cancel rsv1 grsv1 loc ts rsv2 grsv2)
        (LE_CTX: le ctx grsv1)
        (DISJOINT: disjoint rsv1 ctx):
    (<<DISJOINT: disjoint rsv2 ctx>>) /\
    (<<LE_CTX: le ctx grsv2>>).
  Proof.
    inv CANCEL. inv RSV. inv GRSV. splits; ii.
    - revert GET1. unfold LocFun.add.
      condtac; ss; subst; eauto.
    - unfold LocFun.add. condtac; ss; subst; eauto.
      exploit DISJOINT; eauto. ss.
  Qed.
End Reserves.
