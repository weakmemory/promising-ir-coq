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
Require Import Cell.
Require Import Memory.
Require Import Global.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import MemoryReorder.

Set Implicit Arguments.


(* reorder step-promise *)

Lemma reorder_read_promise
      lc0 gl0
      loc1 ts1 val1 released1 ord1 lc1
      loc2 lc2 gl2
      (STEP1: Local.read_step lc0 gl0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.promise_step lc1 gl0 loc2 lc2 gl2):
  exists lc1',
    <<STEP1: Local.promise_step lc0 gl0 loc2 lc1' gl2>> /\
    <<STEP2: Local.read_step lc1' gl2 loc1 ts1 val1 released1 ord1 lc2>>.
Proof.
  inv STEP1. inv STEP2. ss. esplits; eauto.
Qed.

Lemma reorder_fulfill_promise
      prm0 gprm0
      loc1 ord1 prm1 gprm1
      loc2 prm2 gprm2
      (FULFILL: Promises.fulfill prm0 gprm0 loc1 ord1 prm1 gprm1)
      (PROMISE: Promises.promise prm1 gprm1 loc2 prm2 gprm2)
      (LOC: loc1 <> loc2):
  exists prm1' gprm1',
    (<<PROMISE: Promises.promise prm0 gprm0 loc2 prm1' gprm1'>>) /\
    (<<FULFILL: Promises.fulfill prm1' gprm1' loc1 ord1 prm2 gprm2>>).
Proof.
  inv FULFILL; [esplits; eauto|].
  inv PROMISE.
  exploit BoolMap.remove_add; try exact REMOVE; eauto. i. des; try congr.
  exploit BoolMap.remove_add; try exact GREMOVE; eauto. i. des; try congr.
  esplits; eauto.
Qed.

Lemma reorder_write_promise
      lc0 gl0
      loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1
      loc2 lc2 gl2
      (STEP1: Local.write_step lc0 gl0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1)
      (STEP2: Local.promise_step lc1 gl1 loc2 lc2 gl2)
      (LOC: loc1 <> loc2):
  exists lc1' gl1',
    <<STEP1: Local.promise_step lc0 gl0 loc2 lc1' gl1'>> /\
    <<STEP2: Local.write_step lc1' gl1' loc1 from1 to1 val1 releasedm1 released1 ord1 lc2 gl2>>.
Proof.
  destruct lc0, lc1, lc2, gl0, gl1, gl2.
  inv STEP1. inv STEP2. ss. clarify.
  exploit reorder_fulfill_promise; eauto. i. des.
  esplits; eauto.
Qed.

Lemma reorder_fence_promise
      lc0 gl0
      ordr1 ordw1
      lc1 gl1
      loc2 lc2 gl2
      (ORDW1: Ordering.le ordw1 Ordering.acqrel)
      (STEP1: Local.fence_step lc0 gl0 ordr1 ordw1 lc1 gl1)
      (STEP2: Local.promise_step lc1 gl1 loc2 lc2 gl2):
  exists lc1' gl1',
    <<STEP1: Local.promise_step lc0 gl0 loc2 lc1' gl1'>> /\
    <<STEP2: Local.fence_step lc1' gl1' ordr1 ordw1 lc2 gl2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits; eauto.
  econs; eauto. s. i.
  destruct ordw1; ss.
Qed.

Lemma reorder_is_racy_promise
      lc0 gl0
      loc1 to1 ord1
      loc2 lc2 gl2
      (STEP1: Local.is_racy lc0 gl0 loc1 to1 ord1)
      (STEP2: Local.promise_step lc0 gl0 loc2 lc2 gl2):
  <<STEP: Local.is_racy lc2 gl2 loc1 to1 ord1>>.
Proof.
  inv STEP2. inv PROMISE. inv ADD. inv GADD.
  inv STEP1; eauto.
  econs; ss; unfold LocFun.add; condtac; ss; try congr.
Qed.

Lemma reorder_racy_read_promise
      lc0 gl0
      loc1 to1 val1 ord1
      loc2 lc2 gl2
      (STEP1: Local.racy_read_step lc0 gl0 loc1 to1 val1 ord1)
      (STEP2: Local.promise_step lc0 gl0 loc2 lc2 gl2):
  <<STEP: Local.racy_read_step lc2 gl2 loc1 to1 val1 ord1>>.
Proof.
  inv STEP1.
  exploit reorder_is_racy_promise; eauto.
Qed.

Lemma reorder_racy_write_promise
      lc0 gl0
      loc1 to1 ord1
      loc2 lc2 gl2
      (STEP1: Local.racy_write_step lc0 gl0 loc1 to1 ord1)
      (STEP2: Local.promise_step lc0 gl0 loc2 lc2 gl2):
  <<STEP: Local.racy_write_step lc2 gl2 loc1 to1 ord1>>.
Proof.
  inv STEP1.
  exploit reorder_is_racy_promise; eauto.
Qed.

Lemma reorder_racy_update_promise
      lc0 gl0
      loc1 to1 ordr1 ordw1
      loc2 lc2 gl2
      (STEP1: Local.racy_update_step lc0 gl0 loc1 to1 ordr1 ordw1)
      (STEP2: Local.promise_step lc0 gl0 loc2 lc2 gl2):
  <<STEP: Local.racy_update_step lc2 gl2 loc1 to1 ordr1 ordw1>>.
Proof.
  inv STEP1; eauto.
  exploit reorder_is_racy_promise; eauto.
Qed.


(* reorder step-reserve *)

Lemma reorder_read_reserve
      lc0 gl0
      loc1 ts1 val1 released1 ord1 lc1
      loc2 from2 to2 lc2 gl2
      (STEP1: Local.read_step lc0 gl0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.reserve_step lc1 gl0 loc2 from2 to2 lc2 gl2):
  exists lc1',
    <<STEP1: Local.reserve_step lc0 gl0 loc2 from2 to2 lc1' gl2>> /\
    <<STEP2: Local.read_step lc1' gl2 loc1 ts1 val1 released1 ord1 lc2>>.
Proof.
  inv STEP1. inv STEP2. inv RESERVE. ss.
  exploit Memory.add_get1; try exact MEM; eauto. i.
  esplits; eauto.
Qed.

Lemma reorder_write_reserve
      lc0 gl0
      loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1
      loc2 from2 to2 lc2 gl2
      (STEP1: Local.write_step lc0 gl0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1)
      (STEP2: Local.reserve_step lc1 gl1 loc2 from2 to2 lc2 gl2):
  exists lc1' gl1',
    <<STEP1: Local.reserve_step lc0 gl0 loc2 from2 to2 lc1' gl1'>> /\
    <<STEP2: Local.write_step lc1' gl1' loc1 from1 to1 val1 releasedm1 released1 ord1 lc2 gl2>>.
Proof.
  destruct lc0, lc1, lc2, gl0, gl1, gl2.
  inv STEP1. inv STEP2. inv RESERVE. ss. clarify.
  exploit MemoryReorder.add_add; try exact WRITE; eauto. i. des.
  esplits; eauto.
Qed.

Lemma reorder_fence_reserve
      lc0 gl0
      ordr1 ordw1
      lc1 gl1
      loc2 from2 to2 lc2 gl2
      (ORDW1: Ordering.le ordw1 Ordering.acqrel)
      (STEP1: Local.fence_step lc0 gl0 ordr1 ordw1 lc1 gl1)
      (STEP2: Local.reserve_step lc1 gl1 loc2 from2 to2 lc2 gl2):
  exists lc1' gl1',
    <<STEP1: Local.reserve_step lc0 gl0 loc2 from2 to2 lc1' gl1'>> /\
    <<STEP2: Local.fence_step lc1' gl1' ordr1 ordw1 lc2 gl2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits; eauto.
Qed.

Lemma reorder_is_racy_reserve
      lc0 gl0
      loc1 to1 ord1
      loc2 from2 to2 lc2 gl2
      (STEP1: Local.is_racy lc0 gl0 loc1 to1 ord1)
      (STEP2: Local.reserve_step lc0 gl0 loc2 from2 to2 lc2 gl2):
  <<STEP: Local.is_racy lc2 gl2 loc1 to1 ord1>>.
Proof.
  inv STEP2. inv RESERVE.
  inv STEP1; eauto.
  exploit Memory.add_get1; try exact MEM; eauto.
Qed.

Lemma reorder_racy_read_reserve
      lc0 gl0
      loc1 to1 val1 ord1
      loc2 from2 to2 lc2 gl2
      (STEP1: Local.racy_read_step lc0 gl0 loc1 to1 val1 ord1)
      (STEP2: Local.reserve_step lc0 gl0 loc2 from2 to2 lc2 gl2):
  <<STEP: Local.racy_read_step lc2 gl2 loc1 to1 val1 ord1>>.
Proof.
  inv STEP1.
  exploit reorder_is_racy_reserve; eauto.
Qed.

Lemma reorder_racy_write_reserve
      lc0 gl0
      loc1 to1 ord1
      loc2 from2 to2 lc2 gl2
      (STEP1: Local.racy_write_step lc0 gl0 loc1 to1 ord1)
      (STEP2: Local.reserve_step lc0 gl0 loc2 from2 to2 lc2 gl2):
  <<STEP: Local.racy_write_step lc2 gl2 loc1 to1 ord1>>.
Proof.
  inv STEP1.
  exploit reorder_is_racy_reserve; eauto.
Qed.

Lemma reorder_racy_update_reserve
      lc0 gl0
      loc1 to1 ordr1 ordw1
      loc2 from2 to2 lc2 gl2
      (STEP1: Local.racy_update_step lc0 gl0 loc1 to1 ordr1 ordw1)
      (STEP2: Local.reserve_step lc0 gl0 loc2 from2 to2 lc2 gl2):
  <<STEP: Local.racy_update_step lc2 gl2 loc1 to1 ordr1 ordw1>>.
Proof.
  inv STEP1; eauto.
  exploit reorder_is_racy_reserve; eauto.
Qed.


(* reorder step-cancel *)

Lemma reorder_read_cancel
      lc0 gl0
      loc1 ts1 val1 released1 ord1 lc1
      loc2 from2 to2 lc2 gl2
      (STEP1: Local.read_step lc0 gl0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.cancel_step lc1 gl0 loc2 from2 to2 lc2 gl2):
  exists lc1',
    <<STEP1: Local.cancel_step lc0 gl0 loc2 from2 to2 lc1' gl2>> /\
    <<STEP2: Local.read_step lc1' gl2 loc1 ts1 val1 released1 ord1 lc2>>.
Proof.
  inv STEP1. inv STEP2. inv CANCEL. ss.
  exploit Memory.remove_get1; try exact MEM; eauto. i. des; ss.
  esplits; eauto.
Qed.

Lemma reorder_write_cancel
      lc0 gl0
      loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1
      loc2 from2 to2 lc2 gl2
      (STEP1: Local.write_step lc0 gl0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1)
      (STEP2: Local.cancel_step lc1 gl1 loc2 from2 to2 lc2 gl2):
  exists lc1' gl1',
    <<STEP1: Local.cancel_step lc0 gl0 loc2 from2 to2 lc1' gl1'>> /\
    <<STEP2: Local.write_step lc1' gl1' loc1 from1 to1 val1 releasedm1 released1 ord1 lc2 gl2>>.
Proof.
  destruct lc0, lc1, lc2, gl0, gl1, gl2.
  inv STEP1. inv STEP2. inv CANCEL. ss. clarify.
  exploit MemoryReorder.add_remove; try exact WRITE; eauto.
  { ii. clarify.
    exploit Memory.add_get0; try exact WRITE. i. des.
    exploit Memory.remove_get0; try exact MEM. i. des.
    congr.
  }
  i. des.
  esplits; eauto.
Qed.

Lemma reorder_fence_cancel
      lc0 gl0
      ordr1 ordw1
      lc1 gl1
      loc2 from2 to2 lc2 gl2
      (ORDW1: Ordering.le ordw1 Ordering.acqrel)
      (STEP1: Local.fence_step lc0 gl0 ordr1 ordw1 lc1 gl1)
      (STEP2: Local.cancel_step lc1 gl1 loc2 from2 to2 lc2 gl2):
  exists lc1' gl1',
    <<STEP1: Local.cancel_step lc0 gl0 loc2 from2 to2 lc1' gl1'>> /\
    <<STEP2: Local.fence_step lc1' gl1' ordr1 ordw1 lc2 gl2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits; eauto.
Qed.

Lemma reorder_is_racy_cancel
      lc0 gl0
      loc1 to1 ord1
      loc2 from2 to2 lc2 gl2
      (STEP1: Local.is_racy lc0 gl0 loc1 to1 ord1)
      (STEP2: Local.cancel_step lc0 gl0 loc2 from2 to2 lc2 gl2):
  <<STEP: Local.is_racy lc2 gl2 loc1 to1 ord1>>.
Proof.
  inv STEP2. inv CANCEL.
  inv STEP1; eauto.
  exploit Memory.remove_get1; try exact MEM; eauto. i. des; ss.
  eauto.
Qed.

Lemma reorder_racy_read_cancel
      lc0 gl0
      loc1 to1 val1 ord1
      loc2 from2 to2 lc2 gl2
      (STEP1: Local.racy_read_step lc0 gl0 loc1 to1 val1 ord1)
      (STEP2: Local.cancel_step lc0 gl0 loc2 from2 to2 lc2 gl2):
  <<STEP: Local.racy_read_step lc2 gl2 loc1 to1 val1 ord1>>.
Proof.
  inv STEP1.
  exploit reorder_is_racy_cancel; eauto.
Qed.

Lemma reorder_racy_write_cancel
      lc0 gl0
      loc1 to1 ord1
      loc2 from2 to2 lc2 gl2
      (STEP1: Local.racy_write_step lc0 gl0 loc1 to1 ord1)
      (STEP2: Local.cancel_step lc0 gl0 loc2 from2 to2 lc2 gl2):
  <<STEP: Local.racy_write_step lc2 gl2 loc1 to1 ord1>>.
Proof.
  inv STEP1.
  exploit reorder_is_racy_cancel; eauto.
Qed.

Lemma reorder_racy_update_cancel
      lc0 gl0
      loc1 to1 ordr1 ordw1
      loc2 from2 to2 lc2 gl2
      (STEP1: Local.racy_update_step lc0 gl0 loc1 to1 ordr1 ordw1)
      (STEP2: Local.cancel_step lc0 gl0 loc2 from2 to2 lc2 gl2):
  <<STEP: Local.racy_update_step lc2 gl2 loc1 to1 ordr1 ordw1>>.
Proof.
  inv STEP1; eauto.
  exploit reorder_is_racy_cancel; eauto.
Qed.


(* reorder step-internal *)

Lemma reorder_read_internal
      lc0 gl0
      loc1 ts1 val1 released1 ord1 lc1
      e lc2 gl2
      (STEP1: Local.read_step lc0 gl0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.internal_step e lc1 gl0 lc2 gl2):
  exists lc1',
    <<STEP1: Local.internal_step e lc0 gl0 lc1' gl2>> /\
    <<STEP2: Local.read_step lc1' gl2 loc1 ts1 val1 released1 ord1 lc2>>.
Proof.
  inv STEP2.
  - exploit reorder_read_promise; eauto. i. des. eauto.
  - exploit reorder_read_reserve; eauto. i. des. eauto.
  - exploit reorder_read_cancel; eauto. i. des. eauto.
Qed.

Lemma reorder_write_internal
      lc0 gl0
      loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1
      e lc2 gl2
      (STEP1: Local.write_step lc0 gl0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1)
      (STEP2: Local.internal_step e lc1 gl1 lc2 gl2)
      (LOC: forall loc (EVENT: e = ThreadEvent.promise loc), loc1 <> loc):
  exists lc1' gl1',
    <<STEP1: Local.internal_step e lc0 gl0 lc1' gl1'>> /\
    <<STEP2: Local.write_step lc1' gl1' loc1 from1 to1 val1 releasedm1 released1 ord1 lc2 gl2>>.
Proof.
  inv STEP2.
  - exploit reorder_write_promise; eauto. i. des. esplits; eauto.
  - exploit reorder_write_reserve; eauto. i. des. esplits; eauto.
  - exploit reorder_write_cancel; eauto. i. des. esplits; eauto.
Qed.

Lemma reorder_fence_internal
      lc0 gl0
      ordr1 ordw1
      lc1 gl1
      e lc2 gl2
      (ORDW1: Ordering.le ordw1 Ordering.acqrel)
      (STEP1: Local.fence_step lc0 gl0 ordr1 ordw1 lc1 gl1)
      (STEP2: Local.internal_step e lc1 gl1 lc2 gl2):
  exists lc1' gl1',
    <<STEP1: Local.internal_step e lc0 gl0 lc1' gl1'>> /\
    <<STEP2: Local.fence_step lc1' gl1' ordr1 ordw1 lc2 gl2>>.
Proof.
  inv STEP2.
  - exploit reorder_fence_promise; eauto. i. des. esplits; eauto.
  - exploit reorder_fence_reserve; eauto. i. des. esplits; eauto.
  - exploit reorder_fence_cancel; eauto. i. des. esplits; eauto.
Qed.

Lemma reorder_is_racy_internal
      lc0 gl0
      loc1 to1 ord1
      e lc2 gl2
      (STEP1: Local.is_racy lc0 gl0 loc1 to1 ord1)
      (STEP2: Local.internal_step e lc0 gl0 lc2 gl2):
  <<STEP: Local.is_racy lc2 gl2 loc1 to1 ord1>>.
Proof.
  inv STEP2.
  - exploit reorder_is_racy_promise; eauto.
  - exploit reorder_is_racy_reserve; eauto.
  - exploit reorder_is_racy_cancel; eauto.
Qed.

Lemma reorder_racy_read_internal
      lc0 gl0
      loc1 to1 val1 ord1
      e lc2 gl2
      (STEP1: Local.racy_read_step lc0 gl0 loc1 to1 val1 ord1)
      (STEP2: Local.internal_step e lc0 gl0 lc2 gl2):
  <<STEP: Local.racy_read_step lc2 gl2 loc1 to1 val1 ord1>>.
Proof.
  inv STEP1.
  exploit reorder_is_racy_internal; eauto.
Qed.

Lemma reorder_racy_write_internal
      lc0 gl0
      loc1 to1 ord1
      e lc2 gl2
      (STEP1: Local.racy_write_step lc0 gl0 loc1 to1 ord1)
      (STEP2: Local.internal_step e lc0 gl0 lc2 gl2):
  <<STEP: Local.racy_write_step lc2 gl2 loc1 to1 ord1>>.
Proof.
  inv STEP1.
  exploit reorder_is_racy_internal; eauto.
Qed.

Lemma reorder_racy_update_internal
      lc0 gl0
      loc1 to1 ordr1 ordw1
      e lc2 gl2
      (STEP1: Local.racy_update_step lc0 gl0 loc1 to1 ordr1 ordw1)
      (STEP2: Local.internal_step e lc0 gl0 lc2 gl2):
  <<STEP: Local.racy_update_step lc2 gl2 loc1 to1 ordr1 ordw1>>.
Proof.
  inv STEP1; eauto.
  exploit reorder_is_racy_internal; eauto.
Qed.
