From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.
From PromisingLib Require Import Event.

Require Import Time.
Require Import View.
Require Import BoolMap.
Require Import Promises.
Require Import Reserves.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Global.
Require Import Local.
Require Import Thread.


Section PFCertify.
  Variable lang: language.

  Variant pf_certify (loc: Loc.t) (th: Thread.t lang): Prop :=
    | pf_certify_failure
        pf e th1 th2
        (STEPS: rtc (Thread.pf_tau_step (Global.max_reserved (Thread.global th))) th th1)
        (STEP_FAILURE: Thread.step (Global.max_reserved (Thread.global th)) pf e th1 th2)
        (EVENT_FAILURE: ThreadEvent.get_machine_event e = MachineEvent.failure)
    | pf_certify_fulfill
        pf e th1 th2
        from to val released ord
        (STEPS: rtc (Thread.pf_tau_step (Global.max_reserved (Thread.global th))) th th1)
        (STEP_FULFILL: Thread.step (Global.max_reserved (Thread.global th)) pf e th1 th2)
        (EVENT_FULFILL: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord))
        (TO: Time.lt (Memory.max_ts loc (Global.memory (Thread.global th1))) to)
        (ORD: Ordering.le ord Ordering.na)
  .

  Lemma consistent_pf_certify
        th loc
        (CONS: Thread.consistent th)
        (PROMISED: th.(Thread.local).(Local.promises) loc = true):
    pf_certify loc th.
  Proof.
  Admitted.
End PFCertify.
