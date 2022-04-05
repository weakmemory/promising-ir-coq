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


(* TODO: move to promising-lib *)

Variant option_le (A: Type) (le: A -> A -> Prop): forall (lhs rhs: option A), Prop :=
| option_le_None
    rhs:
  option_le le None rhs
| option_le_Some
    lhs rhs
    (LE: le lhs rhs):
  option_le le (Some lhs) (Some rhs)
.
#[export] Hint Constructors option_le: core.

#[export] Program Instance option_le_PreOrder A (le: A -> A -> Prop) `{PreOrder A le}:
  PreOrder (option_le le).
Next Obligation.
  ii. destruct x; eauto. econs. refl.
Qed.
Next Obligation.
  ii. inv H0; inv H1; eauto. econs. etrans; eauto.
Qed.

Definition option_join (A: Type) (join: A -> A -> A) (lhs rhs: option A): option A :=
  match lhs, rhs with
  | None, _ => rhs
  | _, None => lhs
  | Some l, Some r => Some (join l r)
  end.

Lemma option_join_comm
      A (join: A -> A -> A)
      (COMM: forall x y, join x y = join y x):
  forall x y, option_join join x y = option_join join y x.
Proof.
  i. destruct x, y; ss. f_equal. auto.
Qed.

Lemma option_join_assoc
      A (join: A -> A -> A)
      (ASSOC: forall x y z, join (join x y) z = join x (join y z)):
  forall x y z,
    option_join join (option_join join x y) z =
    option_join join x (option_join join y z).
Proof.
  i. destruct x, y, z; ss. f_equal. auto.
Qed.

Lemma option_join_spec
      A (le: A -> A -> Prop) (join: A -> A -> A)
      (SPEC: forall x y o, le x o -> le y o -> le (join x y) o):
  forall x y o,
    option_le le x o -> option_le le y o ->
    option_le le (option_join join x y) o.
Proof.
  i. inv H; inv H0; econs; eauto.
Qed.


Module Reserves.
  Definition t := Loc.t -> option Time.t.

  Definition eq := @eq t.

  Definition incl (lhs rhs: t): Prop :=
    forall loc ts (LHS: lhs loc = Some ts),
      rhs loc = Some ts.

  Lemma incl_antisym l r
        (LR: incl l r)
        (RL: incl r l):
    l = r.
  Proof.
    extensionality loc.
    specialize (LR loc). specialize (RL loc).
    destruct (l loc) eqn:L, (r loc) eqn:R; eauto.
    exploit LR; eauto.
  Qed.

  Global Program Instance incl_PreOrder: PreOrder incl.
  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. eauto. Qed.
  #[global] Hint Resolve incl_PreOrder_obligation_2: core.

  Definition le (lhs rhs: t): Prop :=
    forall loc, option_le Time.le (lhs loc) (rhs loc).

  Lemma le_antisym l r
        (LR: le l r)
        (RL: le r l):
    l = r.
  Proof.
    extensionality loc.
    specialize (LR loc). specialize (RL loc).
    inv LR; inv RL; try congr.
    rewrite <- H0, <- H in *. clarify.
    f_equal. apply TimeFacts.antisym; ss.
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

  Definition finite (rsv: t): Prop :=
    exists dom,
    forall loc ts (GET: rsv loc = Some ts),
      List.In loc dom.

  Definition bot: t := fun _ => None.

  Lemma bot_incl (rsv: t): incl bot rsv.
  Proof.
    ii. ss.
  Qed.

  Lemma bot_le (rsv: t): le bot rsv.
  Proof.
    ii. econs.
  Qed.

  Lemma bot_disjoint prom: disjoint bot prom.
  Proof.
    ii. ss.
  Qed.

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
      (ADD: add rsv1 loc ts rsv2)
      (GADD: add grsv1 loc ts grsv2)
  .

  Variant cancel (rsv1 grsv1: t) (loc: Loc.t) (ts: Time.t) (rsv2 grsv2: t): Prop :=
  | cancel_intro
      (REMOVE: remove rsv1 loc ts rsv2)
      (GREMOVE: remove grsv1 loc ts grsv2)
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

  Lemma reserve_incl
        rsv1 grsv1 loc ts rsv2 grsv2
        (RESERVE: reserve rsv1 grsv1 loc ts rsv2 grsv2)
        (LE1: incl rsv1 grsv1):
    incl rsv2 grsv2.
  Proof.
    ii. revert LHS.
    inv RESERVE. inv ADD. inv GADD.
    unfold LocFun.add. condtac; ss. eauto.
  Qed.

  Lemma cancel_incl
        rsv1 grsv1 loc ts rsv2 grsv2
        (CANCEL: cancel rsv1 grsv1 loc ts rsv2 grsv2)
        (LE1: incl rsv1 grsv1):
    incl rsv2 grsv2.
  Proof.
    ii. revert LHS.
    inv CANCEL. inv REMOVE. inv GREMOVE.
    unfold LocFun.add. condtac; ss. eauto.
  Qed.

  Lemma reserve_disjoint
        rsv1 grsv1 loc ts rsv2 grsv2
        ctx
        (RESERVE: reserve rsv1 grsv1 loc ts rsv2 grsv2)
        (LE_CTX: incl ctx grsv1)
        (DISJOINT: disjoint rsv1 ctx):
    (<<DISJOINT: disjoint rsv2 ctx>>) /\
    (<<LE_CTX: incl ctx grsv2>>).
  Proof.
    inv RESERVE. inv ADD. inv GADD. splits; ii.
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
        (LE_CTX: incl ctx grsv1)
        (DISJOINT: disjoint rsv1 ctx):
    (<<DISJOINT: disjoint rsv2 ctx>>) /\
    (<<LE_CTX: incl ctx grsv2>>).
  Proof.
    inv CANCEL. inv REMOVE. inv GREMOVE. splits; ii.
    - revert GET1. unfold LocFun.add.
      condtac; ss; subst; eauto.
    - unfold LocFun.add. condtac; ss; subst; eauto.
      exploit DISJOINT; eauto. ss.
  Qed.
End Reserves.
