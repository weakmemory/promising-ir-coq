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


(* reorder step; promise *)

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
  exploit Promises.reorder_fulfill_promise; eauto. i. des.
  esplits; eauto.
Qed.

Lemma reorder_write_promise_same
      lc0 gl0
      loc from1 to1 val1 releasedm1 released1 ord1 lc1 gl1
      lc2 gl2
      (STEP1: Local.write_step lc0 gl0 loc from1 to1 val1 releasedm1 released1 ord1 lc1 gl1)
      (STEP2: Local.promise_step lc1 gl1 loc lc2 gl2):
  exists lc1' gl1',
    <<STEP1: __guard__ (lc1' = lc0 /\ gl1' = gl0 \/
                        Local.promise_step lc0 gl0 loc lc1' gl1')>> /\
    <<STEP2: Local.write_step lc1' gl1' loc from1 to1 val1 releasedm1 released1 ord1 lc2 gl2>>.
Proof.
  destruct lc0, lc1, lc2, gl0, gl1, gl2.
  inv STEP1. inv STEP2. ss. clarify.
  exploit Promises.reorder_fulfill_promise_same; eauto. i.
  unguard. des; subst; esplits; eauto.
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


(* reorder step; reserve *)

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


(* reorder step; cancel *)

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


(* reorder step; internal *)

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

Lemma reorder_write_internal_same
      lc0 gl0
      loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1
      e lc2 gl2
      (STEP1: Local.write_step lc0 gl0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1)
      (STEP2: Local.internal_step e lc1 gl1 lc2 gl2)
      (LOC: e = ThreadEvent.promise loc1):
  exists lc1' gl1',
    <<STEP1: __guard__ (lc1' = lc0 /\ gl1' = gl0 \/
                        Local.internal_step e lc0 gl0 lc1' gl1')>> /\
    <<STEP2: Local.write_step lc1' gl1' loc1 from1 to1 val1 releasedm1 released1 ord1 lc2 gl2>>.
Proof.
  subst. inv STEP2.
  exploit reorder_write_promise_same; eauto. i. des. esplits; eauto.
  unguard. des; eauto.
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


(* reorder program; internal *)

Lemma reorder_program_internal
      lc0 gl0
      e1 lc1 gl1
      e2 lc2 gl2
      (STEP1: Local.program_step e1 lc0 gl0 lc1 gl1)
      (STEP2: Local.internal_step e2 lc1 gl1 lc2 gl2)
      (SC: ~ ThreadEvent.is_sc e1):
  exists lc1' gl1',
    (<<STEP1: __guard__ (lc1' = lc0 /\ gl1' = gl0 \/
                         Local.internal_step e2 lc0 gl0 lc1' gl1')>>) /\
    (<<STEP2: Local.program_step e1 lc1' gl1' lc2 gl2>>).
Proof.
  unguard. inv STEP1.
  { esplits; eauto. }
  { exploit reorder_read_internal; eauto. i. des. esplits; eauto. }
  { destruct (classic (e2 = ThreadEvent.promise loc)).
    { subst. exploit reorder_write_internal_same; eauto. i. des.
      esplits; eauto.
    }
    { exploit reorder_write_internal; eauto; try congr. i. des.
      esplits; eauto.
    }
  }
  { destruct (classic (e2 = ThreadEvent.promise loc)).
    { subst. exploit reorder_write_internal_same; eauto. i. des.
      unguard. des; subst; [esplits; eauto|].
      exploit reorder_read_internal; eauto. i. des.
      esplits; eauto.
    }
    { exploit reorder_write_internal; eauto; try congr. i. des.
      exploit reorder_read_internal; eauto. i. des.
      esplits; eauto.
    }
  }
  { exploit reorder_fence_internal; eauto;
      try by (destruct ordw; ss). i. des. esplits; eauto.
  }
  { ss. }
  { esplits; eauto. }
  { exploit reorder_racy_read_internal; eauto. i. des. esplits; eauto. }
  { exploit reorder_racy_write_internal; eauto. i. des. esplits; eauto. }
  { exploit reorder_racy_update_internal; eauto. i. des. esplits; eauto. }
Qed.


(* reorder promise; step *)

Lemma reorder_promise_promise
      lc0 gl0
      loc1 lc1 gl1
      loc2 lc2 gl2
      (STEP1: Local.promise_step lc0 gl0 loc1 lc1 gl1)
      (STEP2: Local.promise_step lc1 gl1 loc2 lc2 gl2):
  exists lc1' gl1',
    <<STEP1: Local.promise_step lc0 gl0 loc2 lc1' gl1'>> /\
    <<STEP1: Local.promise_step lc1' gl1' loc1 lc2 gl2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit Promises.reorder_promise_promise; [exact PROMISE|..]; eauto. i. des.
  esplits; eauto.
Qed.

Lemma reorder_promise_reserve
      lc0 gl0
      loc1 lc1 gl1
      loc2 from2 to2 lc2 gl2
      (STEP1: Local.promise_step lc0 gl0 loc1 lc1 gl1)
      (STEP2: Local.reserve_step lc1 gl1 loc2 from2 to2 lc2 gl2):
  exists lc1' gl1',
    <<STEP1: Local.reserve_step lc0 gl0 loc2 from2 to2 lc1' gl1'>> /\
    <<STEP1: Local.promise_step lc1' gl1' loc1 lc2 gl2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits; eauto.
Qed.

Lemma reorder_promise_cancel
      lc0 gl0
      loc1 lc1 gl1
      loc2 from2 to2 lc2 gl2
      (STEP1: Local.promise_step lc0 gl0 loc1 lc1 gl1)
      (STEP2: Local.cancel_step lc1 gl1 loc2 from2 to2 lc2 gl2):
  exists lc1' gl1',
    <<STEP1: Local.cancel_step lc0 gl0 loc2 from2 to2 lc1' gl1'>> /\
    <<STEP1: Local.promise_step lc1' gl1' loc1 lc2 gl2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits; eauto.
Qed.

Lemma reorder_promise_read
      lc0 gl0
      loc1 lc1 gl1
      loc2 ts2 val2 released2 ord2 lc2
      (STEP1: Local.promise_step lc0 gl0 loc1 lc1 gl1)
      (STEP2: Local.read_step lc1 gl1 loc2 ts2 val2 released2 ord2 lc2):
  exists lc1' gl1,
    <<STEP1: Local.read_step lc0 gl0 loc2 ts2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.promise_step lc1' gl0 loc1 lc2 gl1>>.
Proof.
  inv STEP1. inv STEP2. ss. esplits; eauto.
Qed.

Lemma reorder_promise_write
      lc0 gl0
      loc1 lc1 gl1
      loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 gl2
      (STEP1: Local.promise_step lc0 gl0 loc1 lc1 gl1)
      (STEP2: Local.write_step lc1 gl1 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 gl2):
  exists lc1' gl1',
    <<STEP1: Local.write_step lc0 gl0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' gl1'>> /\
    (<<LOC: loc1 = loc2>> /\ <<LC: lc1' = lc2>> /\ <<GL: gl1' = gl2>> \/
     <<STEP2: Local.promise_step lc1' gl1' loc1 lc2 gl2>>).
Proof.
  destruct lc0, lc1, lc2, gl0, gl1, gl2.
  inv STEP1. inv STEP2. ss. clarify.
  destruct (Loc.eq_dec loc1 loc2).
  - subst. inv FULFILL; [esplits; eauto|].
    inv PROMISE.
    exploit BoolMap.reorder_add_remove; try exact ADD; eauto. i. des; ss.
    exploit BoolMap.reorder_add_remove; try exact GADD; eauto. i. des; ss.
    subst. esplits; eauto.
  - exploit Promises.reorder_promise_fulfill; eauto. i. des.
    esplits; eauto.
Qed.

Lemma reorder_promise_fence
      lc0 gl0
      loc1 lc1 gl1
      ordr2 ordw2 lc2 gl2
      (STEP1: Local.promise_step lc0 gl0 loc1 lc1 gl1)
      (STEP2: Local.fence_step lc1 gl1 ordr2 ordw2 lc2 gl2):
  exists lc1' gl1',
    <<STEP1: Local.fence_step lc0 gl0 ordr2 ordw2 lc1' gl1'>> /\
    <<STEP2: Local.promise_step lc1' gl1' loc1 lc2 gl2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits.
  - econs; eauto. i.
    exploit PROMISES; ss. i. subst.
    inv PROMISE.
    hexploit BoolMap.add_le; try exact ADD. i.
    apply BoolMap.antisym; ss.
  - eauto.
Qed.

Lemma reorder_promise_is_racy
      lc0 gl0
      loc1 lc1 gl1
      loc2 to2 ord2
      (STEP1: Local.promise_step lc0 gl0 loc1 lc1 gl1)
      (STEP2: Local.is_racy lc1 gl1 loc2 to2 ord2):
  <<STEP: Local.is_racy lc0 gl0 loc2 to2 ord2>>.
Proof.
  inv STEP1. inv PROMISE.
  inv STEP2; eauto. ss.
  revert GET. erewrite BoolMap.add_o; eauto.
  revert GETP. erewrite BoolMap.add_o; eauto.
  condtac; ss. eauto.
Qed.

Lemma reorder_promise_racy_read
      lc0 gl0
      loc1 lc1 gl1
      loc2 to2 val2 ord2
      (STEP1: Local.promise_step lc0 gl0 loc1 lc1 gl1)
      (STEP2: Local.racy_read_step lc1 gl1 loc2 to2 val2 ord2):
  <<STEP: Local.racy_read_step lc0 gl0 loc2 to2 val2 ord2>>.
Proof.
  inv STEP2.
  exploit reorder_promise_is_racy; eauto.
Qed.

Lemma reorder_promise_racy_write
      lc0 gl0
      loc1 lc1 gl1
      loc2 to2 ord2
      (STEP1: Local.promise_step lc0 gl0 loc1 lc1 gl1)
      (STEP2: Local.racy_write_step lc1 gl1 loc2 to2 ord2):
  <<STEP: Local.racy_write_step lc0 gl0 loc2 to2 ord2>>.
Proof.
  inv STEP2.
  exploit reorder_promise_is_racy; eauto.
Qed.

Lemma reorder_promise_racy_update
      lc0 gl0
      loc1 lc1 gl1
      loc2 to2 ordr2 ordw2
      (STEP1: Local.promise_step lc0 gl0 loc1 lc1 gl1)
      (STEP2: Local.racy_update_step lc1 gl1 loc2 to2 ordr2 ordw2):
  <<STEP: Local.racy_update_step lc0 gl0 loc2 to2 ordr2 ordw2>>.
Proof.
  inv STEP2; eauto.
  exploit reorder_promise_is_racy; eauto.
Qed.


(* reorder reserve; step *)

Lemma reorder_reserve_promise
      lc0 gl0
      loc1 from1 to1 lc1 gl1
      loc2 lc2 gl2
      (STEP1: Local.reserve_step lc0 gl0 loc1 from1 to1 lc1 gl1)
      (STEP2: Local.promise_step lc1 gl1 loc2 lc2 gl2):
  exists lc1' gl1',
    <<STEP1: Local.promise_step lc0 gl0 loc2 lc1' gl1'>> /\
    <<STEP1: Local.reserve_step lc1' gl1' loc1 from1 to1 lc2 gl2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits; eauto.
Qed.

Lemma reorder_reserve_reserve
      lc0 gl0
      loc1 from1 to1 lc1 gl1
      loc2 from2 to2 lc2 gl2
      (STEP1: Local.reserve_step lc0 gl0 loc1 from1 to1 lc1 gl1)
      (STEP2: Local.reserve_step lc1 gl1 loc2 from2 to2 lc2 gl2):
  exists lc1' gl1',
    <<STEP1: Local.reserve_step lc0 gl0 loc2 from2 to2 lc1' gl1'>> /\
    <<STEP1: Local.reserve_step lc1' gl1' loc1 from1 to1 lc2 gl2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  inv RESERVE. inv RESERVE0.
  exploit MemoryReorder.add_add; try exact RSV; eauto. i. des.
  exploit MemoryReorder.add_add; try exact MEM; eauto. i. des.
  esplits; eauto.
Qed.

Lemma reorder_reserve_cancel
      lc0 gl0
      loc1 from1 to1 lc1 gl1
      loc2 from2 to2 lc2 gl2
      (STEP1: Local.reserve_step lc0 gl0 loc1 from1 to1 lc1 gl1)
      (STEP2: Local.cancel_step lc1 gl1 loc2 from2 to2 lc2 gl2):
  <<LOC: loc1 = loc2>> /\ <<FROM: from1 = from2>> /\ <<TO: to1 = to2>> \/
  <<LOCTS: (loc1, to1) <> (loc2, to2)>> /\
  exists lc1' gl1',
     <<STEP1: Local.cancel_step lc0 gl0 loc2 from2 to2 lc1' gl1'>> /\
     <<STEP1: Local.reserve_step lc1' gl1' loc1 from1 to1 lc2 gl2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  inv RESERVE. inv CANCEL.
  destruct (classic ((loc1, to1) = (loc2, to2))).
  - inv H.
    exploit MemoryReorder.add_remove_same; try exact RSV; eauto. i. des.
    exploit MemoryReorder.add_remove_same; try exact MEM; eauto. i. des.
    subst. auto.
  - exploit MemoryReorder.add_remove; try exact RSV; eauto. i. des.
    exploit MemoryReorder.add_remove; try exact MEM; eauto. i. des.
    right. esplits; eauto.
Qed.

Lemma reorder_reserve_read
      lc0 gl0
      loc1 from1 to1 lc1 gl1
      loc2 ts2 val2 released2 ord2 lc2
      (STEP1: Local.reserve_step lc0 gl0 loc1 from1 to1 lc1 gl1)
      (STEP2: Local.read_step lc1 gl1 loc2 ts2 val2 released2 ord2 lc2):
  exists lc1' gl1,
    <<STEP1: Local.read_step lc0 gl0 loc2 ts2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.reserve_step lc1' gl0 loc1 from1 to1 lc2 gl1>>.
Proof.
  inv STEP1. inv STEP2. ss.
  inv RESERVE. revert GET.
  erewrite Memory.add_o; eauto. condtac; ss. i.
  esplits; eauto.
Qed.

Lemma reorder_reserve_write
      lc0 gl0
      loc1 from1 to1 lc1 gl1
      loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 gl2
      (STEP1: Local.reserve_step lc0 gl0 loc1 from1 to1 lc1 gl1)
      (STEP2: Local.write_step lc1 gl1 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 gl2):
  exists lc1' gl1',
    <<STEP1: Local.write_step lc0 gl0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' gl1'>> /\
    <<STEP2: Local.reserve_step lc1' gl1' loc1 from1 to1 lc2 gl2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  inv RESERVE.
  exploit MemoryReorder.add_add; try exact MEM; eauto. i. des.
  esplits; eauto.
Qed.

Lemma reorder_reserve_fence
      lc0 gl0
      loc1 from1 to1 lc1 gl1
      ordr2 ordw2 lc2 gl2
      (STEP1: Local.reserve_step lc0 gl0 loc1 from1 to1 lc1 gl1)
      (STEP2: Local.fence_step lc1 gl1 ordr2 ordw2 lc2 gl2):
  exists lc1' gl1',
    <<STEP1: Local.fence_step lc0 gl0 ordr2 ordw2 lc1' gl1'>> /\
    <<STEP2: Local.reserve_step lc1' gl1' loc1 from1 to1 lc2 gl2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits; eauto.
Qed.

Lemma reorder_reserve_is_racy
      lc0 gl0
      loc1 from1 to1 lc1 gl1
      loc2 to2 ord2
      (STEP1: Local.reserve_step lc0 gl0 loc1 from1 to1 lc1 gl1)
      (STEP2: Local.is_racy lc1 gl1 loc2 to2 ord2):
  <<STEP: Local.is_racy lc0 gl0 loc2 to2 ord2>>.
Proof.
  inv STEP1. inv RESERVE.
  inv STEP2; eauto. ss.
  revert GET. erewrite Memory.add_o; eauto.
  condtac; ss. eauto.
Qed.

Lemma reorder_reserve_racy_read
      lc0 gl0
      loc1 from1 to1 lc1 gl1
      loc2 to2 val2 ord2
      (STEP1: Local.reserve_step lc0 gl0 loc1 from1 to1 lc1 gl1)
      (STEP2: Local.racy_read_step lc1 gl1 loc2 to2 val2 ord2):
  <<STEP: Local.racy_read_step lc0 gl0 loc2 to2 val2 ord2>>.
Proof.
  inv STEP2.
  exploit reorder_reserve_is_racy; eauto.
Qed.

Lemma reorder_reserve_racy_write
      lc0 gl0
      loc1 from1 to1 lc1 gl1
      loc2 to2 ord2
      (STEP1: Local.reserve_step lc0 gl0 loc1 from1 to1 lc1 gl1)
      (STEP2: Local.racy_write_step lc1 gl1 loc2 to2 ord2):
  <<STEP: Local.racy_write_step lc0 gl0 loc2 to2 ord2>>.
Proof.
  inv STEP2.
  exploit reorder_reserve_is_racy; eauto.
Qed.

Lemma reorder_reserve_racy_update
      lc0 gl0
      loc1 from1 to1 lc1 gl1
      loc2 to2 ordr2 ordw2
      (STEP1: Local.reserve_step lc0 gl0 loc1 from1 to1 lc1 gl1)
      (STEP2: Local.racy_update_step lc1 gl1 loc2 to2 ordr2 ordw2):
  <<STEP: Local.racy_update_step lc0 gl0 loc2 to2 ordr2 ordw2>>.
Proof.
  inv STEP2; eauto.
  exploit reorder_reserve_is_racy; eauto.
Qed.


(* reorder cancel; step *)

Lemma reorder_cancel_promise
      lc0 gl0
      loc1 from1 to1 lc1 gl1
      loc2 lc2 gl2
      (STEP1: Local.cancel_step lc0 gl0 loc1 from1 to1 lc1 gl1)
      (STEP2: Local.promise_step lc1 gl1 loc2 lc2 gl2):
  exists lc1' gl1',
    <<STEP1: Local.promise_step lc0 gl0 loc2 lc1' gl1'>> /\
    <<STEP2: Local.cancel_step lc1' gl1' loc1 from1 to1 lc2 gl2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits; eauto.
Qed.

Lemma reorder_cancel_reserve
      lc0 gl0
      loc1 from1 to1 lc1 gl1
      loc2 from2 to2 lc2 gl2
      (STEP1: Local.cancel_step lc0 gl0 loc1 from1 to1 lc1 gl1)
      (STEP2: Local.reserve_step lc1 gl1 loc2 from2 to2 lc2 gl2)
      (TS: Time.lt from1 to1)
      (LOCTS: loc1 <> loc2 \/ Interval.disjoint (from1, to1) (from2, to2)):
  exists lc1' gl1',
    <<STEP1: Local.reserve_step lc0 gl0 loc2 from2 to2 lc1' gl1'>> /\
    <<STEP2: Local.cancel_step lc1' gl1' loc1 from1 to1 lc2 gl2>>.
Proof.
  guardH LOCTS.
  inv STEP1. inv STEP2. ss.
  inv CANCEL. inv RESERVE.
  exploit MemoryReorder.remove_add; try exact RSV; eauto. i. des.
  exploit MemoryReorder.remove_add; try exact MEM; eauto. i. des.
  esplits; eauto.
Qed.

Lemma reorder_cancel_cancel
      lc0 gl0
      loc1 from1 to1 lc1 gl1
      loc2 from2 to2 lc2 gl2
      (STEP1: Local.cancel_step lc0 gl0 loc1 from1 to1 lc1 gl1)
      (STEP2: Local.cancel_step lc1 gl1 loc2 from2 to2 lc2 gl2):
  exists lc1' gl1',
     <<STEP1: Local.cancel_step lc0 gl0 loc2 from2 to2 lc1' gl1'>> /\
     <<STEP2: Local.cancel_step lc1' gl1' loc1 from1 to1 lc2 gl2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  inv CANCEL. inv CANCEL0.
  exploit MemoryReorder.remove_remove; try exact RSV; eauto. i. des.
  exploit MemoryReorder.remove_remove; try exact MEM; eauto. i. des.
  esplits; eauto.
Qed.

Lemma reorder_cancel_read
      lc0 gl0
      loc1 from1 to1 lc1 gl1
      loc2 ts2 val2 released2 ord2 lc2
      (STEP1: Local.cancel_step lc0 gl0 loc1 from1 to1 lc1 gl1)
      (STEP2: Local.read_step lc1 gl1 loc2 ts2 val2 released2 ord2 lc2):
  exists lc1' gl1,
    <<STEP1: Local.read_step lc0 gl0 loc2 ts2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.cancel_step lc1' gl0 loc1 from1 to1 lc2 gl1>>.
Proof.
  inv STEP1. inv STEP2. ss.
  inv CANCEL. revert GET.
  erewrite Memory.remove_o; eauto. condtac; ss. i.
  esplits; eauto.
Qed.

(* Lemma reorder_cancel_write *)
(*       lc0 gl0 *)
(*       loc1 from1 to1 lc1 gl1 *)
(*       loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 gl2 *)
(*       (STEP1: Local.cancel_step lc0 gl0 loc1 from1 to1 lc1 gl1) *)
(*       (STEP2: Local.write_step lc1 gl1 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 gl2): *)
(*   exists lc1' gl1', *)
(*     <<STEP1: Local.write_step lc0 gl0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' gl1'>> /\ *)
(*     <<STEP2: Local.cancel_step lc1' gl1' loc1 from1 to1 lc2 gl2>>. *)
(* Proof. *)
(*   inv STEP1. inv STEP2. ss. *)
(*   inv CANCEL. *)
(*   exploit MemoryReorder.add_add; try exact MEM; eauto. i. des. *)
(*   esplits; eauto. *)
(* Qed. *)

Lemma reorder_cancel_fence
      lc0 gl0
      loc1 from1 to1 lc1 gl1
      ordr2 ordw2 lc2 gl2
      (STEP1: Local.cancel_step lc0 gl0 loc1 from1 to1 lc1 gl1)
      (STEP2: Local.fence_step lc1 gl1 ordr2 ordw2 lc2 gl2):
  exists lc1' gl1',
    <<STEP1: Local.fence_step lc0 gl0 ordr2 ordw2 lc1' gl1'>> /\
    <<STEP2: Local.cancel_step lc1' gl1' loc1 from1 to1 lc2 gl2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits; eauto.
Qed.

Lemma reorder_cancel_is_racy
      lc0 gl0
      loc1 from1 to1 lc1 gl1
      loc2 to2 ord2
      (STEP1: Local.cancel_step lc0 gl0 loc1 from1 to1 lc1 gl1)
      (STEP2: Local.is_racy lc1 gl1 loc2 to2 ord2):
  <<STEP: Local.is_racy lc0 gl0 loc2 to2 ord2>>.
Proof.
  inv STEP1. inv CANCEL.
  inv STEP2; eauto. ss.
  revert GET. erewrite Memory.remove_o; eauto.
  condtac; ss. eauto.
Qed.

Lemma reorder_cancel_racy_read
      lc0 gl0
      loc1 from1 to1 lc1 gl1
      loc2 to2 val2 ord2
      (STEP1: Local.cancel_step lc0 gl0 loc1 from1 to1 lc1 gl1)
      (STEP2: Local.racy_read_step lc1 gl1 loc2 to2 val2 ord2):
  <<STEP: Local.racy_read_step lc0 gl0 loc2 to2 val2 ord2>>.
Proof.
  inv STEP2.
  exploit reorder_cancel_is_racy; eauto.
Qed.

Lemma reorder_cancel_racy_write
      lc0 gl0
      loc1 from1 to1 lc1 gl1
      loc2 to2 ord2
      (STEP1: Local.cancel_step lc0 gl0 loc1 from1 to1 lc1 gl1)
      (STEP2: Local.racy_write_step lc1 gl1 loc2 to2 ord2):
  <<STEP: Local.racy_write_step lc0 gl0 loc2 to2 ord2>>.
Proof.
  inv STEP2.
  exploit reorder_cancel_is_racy; eauto.
Qed.

Lemma reorder_cancel_racy_update
      lc0 gl0
      loc1 from1 to1 lc1 gl1
      loc2 to2 ordr2 ordw2
      (STEP1: Local.cancel_step lc0 gl0 loc1 from1 to1 lc1 gl1)
      (STEP2: Local.racy_update_step lc1 gl1 loc2 to2 ordr2 ordw2):
  <<STEP: Local.racy_update_step lc0 gl0 loc2 to2 ordr2 ordw2>>.
Proof.
  inv STEP2; eauto.
  exploit reorder_cancel_is_racy; eauto.
Qed.
