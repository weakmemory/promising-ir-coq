Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Event.

Require Import Time.
Require Import View.
Require Import BoolMap.
Require Import Promises.
Require Import Reserves.
Require Import Cell.
Require Import Memory.

Set Implicit Arguments.


Module Global.
  Structure t := mk {
    sc: TimeMap.t;
    promises: BoolMap.t;
    reserves: BoolMap.t;
    memory: Memory.t;
  }.

  Definition init := mk TimeMap.bot BoolMap.bot BoolMap.bot Memory.init.

  Definition fully_reserved (gl: t): t :=
    mk (sc gl) (promises gl) BoolMap.top (memory gl).
  #[export] Hint Unfold fully_reserved: core.

  Variant wf (gl: t): Prop :=
  | wf_intro
      (SC_CLOSED: Memory.closed_timemap (sc gl) (memory gl))
      (MEM_CLOSED: Memory.closed (memory gl))
  .
  #[export] Hint Constructors wf: core.

  Lemma init_wf: wf init.
  Proof.
    econs; ss.
    - apply Memory.closed_timemap_bot.
      apply Memory.init_closed.
    - apply Memory.init_closed.
  Qed.

  Lemma fully_reserved_wf
        gl
        (WF: wf gl):
    wf (fully_reserved gl).
  Proof.
    inv WF. econs; ss.
  Qed.

  Variant future (gl1 gl2: t): Prop :=
  | future_intro
      (SC: TimeMap.le (sc gl1) (sc gl2))
      (MEMORY: Memory.future (memory gl1) (memory gl2))
  .
  #[export] Hint Constructors future: core.

  Global Program Instance future_PreOrder: PreOrder future.
  Next Obligation.
    ii. destruct x. econs; refl.
  Qed.
  Next Obligation.
    ii. destruct x, y, z. inv H. inv H0. ss.
    econs; etrans; eauto.
  Qed.
End Global.
