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
Require Import Promises.
Require Import Reserves.
Require Import Cell.
Require Import Memory.

Set Implicit Arguments.


Module Global.
  Structure t := mk {
    sc: TimeMap.t;
    promises: Promises.t;
    reserves: Reserves.t;
    memory: Memory.t;
  }.

  Definition init := mk TimeMap.bot Promises.bot Reserves.bot Memory.init.

  Variant wf (gl: t): Prop :=
  | wf_intro
      (SC_CLOSED: Memory.closed_timemap (sc gl) (memory gl))
      (RSV_CLOSED: Memory.closed_reserves (reserves gl) (memory gl))
      (MEM_CLOSED: Memory.closed (memory gl))
  .

  Lemma init_wf: wf init.
  Proof.
    econs; ss.
    - apply Memory.closed_timemap_bot.
      apply Memory.init_closed.
    - apply Memory.init_closed.
  Qed.

  Lemma max_reserves_wf
        gl
        (WF: wf gl):
    wf (mk (sc gl) (promises gl) (Memory.max_reserves (memory gl)) (memory gl)).
  Proof.
    destruct gl as [sc prm rsv mem]. inv WF. ss.
    econs; eauto; ss.
    eapply Memory.max_reserves_closed.
    apply MEM_CLOSED.
  Qed.
End Global.
