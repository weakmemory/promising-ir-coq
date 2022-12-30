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

Require Import SimLocal.
Require Import SimMemory.
Require Import SimGlobal.
Require Import SimThread.
Require Import MergeTView.

Set Implicit Arguments.


Lemma merge_read_read
      loc ts val released ord
      lc0 lc2 gl0
      (LC_WF: Local.wf lc0 gl0)
      (GL_WF: Global.wf gl0)
      (STEP1: Local.read_step lc0 gl0 loc ts val released ord lc2):
  Local.read_step lc2 gl0 loc ts val released ord lc2.
Proof.
  inv STEP1. econs; s; eauto.
  - unfold View.singleton_ur_if.
    econs; repeat (try condtac; aggrtac); try apply READABLE; auto.
    + inv GL_WF. inv MEM_CLOSED.
      exploit CLOSED; eauto. i. des. inv MSG_WF. inv MSG_TS.
      etrans; eauto. apply View.unwrap_opt_wf. ss.
    + inv GL_WF. inv MEM_CLOSED.
      exploit CLOSED; eauto. i. des. inv MSG_WF. inv MSG_TS.
      etrans; eauto. apply View.unwrap_opt_wf. ss.
    + inv GL_WF. inv MEM_CLOSED.
      exploit CLOSED; eauto. i. des. inv MSG_WF. inv MSG_TS.
      auto.
  - f_equal. apply TView.antisym.
    + apply TViewFacts.read_tview_incr.
    + apply MergeTView.read_read_tview; try refl; try apply LC_WF.
      inv GL_WF. inv MEM_CLOSED.
      exploit CLOSED; eauto. i. des. inv MSG_WF. inv MSG_TS.
      auto.
Qed.

Lemma merge_write_read
      loc from to val releasedm released ord1 ord2
      lc0 gl0
      lc1 gl1
      (ORD: Ordering.le Ordering.seqcst ord2 -> Ordering.le Ordering.seqcst ord1)
      (LC_WF: Local.wf lc0 gl0)
      (GL_WF: Global.wf gl0)
      (RELEASEDM_WF: View.opt_wf releasedm)
      (RELEASEDM_CLOSED: Memory.closed_opt_view releasedm (Global.memory gl0))
      (RLX: Ordering.le Ordering.relaxed ord2 -> View.le (View.unwrap releasedm) (TView.acq (Local.tview lc0)))
      (ACQ: Ordering.le Ordering.acqrel ord2 -> View.le (View.unwrap releasedm) (TView.cur (Local.tview lc0)))
      (STEP: Local.write_step lc0 gl0 loc from to val releasedm released ord1 lc1 gl1):
  Local.read_step lc1 gl1 loc to val released ord2 lc1.
Proof.
  inv STEP.
  exploit Memory.add_get0; eauto. i. des.
  econs; eauto; s.
  - refl.
  - inv WRITABLE. unfold TView.write_released. s.
    econs; repeat (try condtac; aggrtac); (try by left; eauto).
    + etrans; [|left; eauto]. apply LC_WF.
  - unfold TView.read_tview, TView.write_released, TView.write_tview. s.
    f_equal. apply TView.antisym; econs;
      repeat (try condtac; aggrtac; rewrite <- ? View.join_l; try apply LC_WF; eauto).
    etrans; apply LC_WF.
Qed.

Lemma split_add
      ts2 msg2' msg3'
      mem1 loc ts1 ts3 msg3 mem3
      (ADD: Memory.add mem1 loc ts1 ts3 msg3 mem3)
      (TS12: Time.lt ts1 ts2)
      (TS23: Time.lt ts2 ts3)
      (MSG2'_WF: Message.wf msg2')
      (MSG3'_WF: Message.wf msg3')
      (MSG3_LE: Message.le msg3' msg3)
      (MSG2': msg2' <> Message.reserve)
      (MSG3: msg3 <> Message.reserve)
      (MSG3': msg3' <> Message.reserve):
  exists mem2' mem3',
    (<<ADD1: Memory.add mem1 loc ts1 ts2 msg2' mem2'>>) /\
    (<<ADD2: Memory.add mem2' loc ts2 ts3 msg3' mem3'>>) /\
    (<<MEM: sim_memory mem3' mem3>>).
Proof.
  exploit Memory.add_ts; eauto. i.
  exploit Memory.add_wf; eauto. i.
  exploit Memory.add_get0; eauto. i. des.
  exploit (@Memory.add_exists mem1 loc); try exact TS12; try exact MSG2'_WF.
  { ii. inv LHS. inv RHS; ss.
    exploit Memory.add_get1; try exact GET2; eauto. i.
    exploit Memory.get_disjoint; [exact GET0|exact x3|]. i. des.
    - subst. congr.
    - apply (x4 x); econs; ss.
      etrans; [exact TO|]. timetac.
  }
  i. des.
  exploit (@Memory.add_exists mem2 loc); try exact TS23; try exact MSG3'_WF.
  { ii. inv LHS. inv RHS. ss.
    revert GET2. erewrite Memory.add_o; eauto. condtac; ss.
    - i. des. inv GET2. timetac.
    - guardH o. i.
      exploit Memory.add_get1; try exact GET2; try exact ADD. i.
      exploit Memory.get_disjoint; [exact GET0|exact x4|]. i. des.
      + subst. congr.
      + apply (x5 x); econs; ss.
        etrans; [exact TS12|]. assumption.
  }
  i. des.
  esplits; eauto.
  econs; i; try split; i.
  - inv H. inv ITV. ss.
    revert GET1. erewrite Memory.add_o; eauto. condtac; ss.
    { i. des. clarify.
      econs; try exact GET0. econs; ss.
      etrans; [exact TS12|]. assumption.
    }
    guardH o. erewrite Memory.add_o; eauto. condtac; ss.
    { i. des. clarify.
      econs; try exact GET0. econs; ss. econs. timetac.
    }
    guardH o0. i.
    exploit Memory.add_get1; try exact GET1; try exact ADD. i.
    econs; eauto. econs; ss.
  - inv H. inv ITV. ss.
    revert GET1. erewrite Memory.add_o; eauto. condtac; ss; cycle 1.
    { guardH o. i.
      exploit Memory.add_get1; try exact GET1; try exact x2. i.
      exploit Memory.add_get1; try exact x4; try exact x3. i.
      econs; eauto. econs; ss.
    }
    i. des. clarify.
    destruct (TimeFacts.le_lt_dec ts ts2).
    + exploit Memory.add_get0; try exact x2. i. des.
      exploit Memory.add_get1; try exact GET2; eauto. i.
      econs; try exact x4. econs; ss.
    + exploit Memory.add_get0; try exact x3. i. des.
      econs; try exact GET2. econs; ss.
  - revert GET1. erewrite Memory.add_o; eauto. condtac; ss.
    + i. des. clarify.
      exploit Memory.add_get0; try exact x3. i. des.
      esplits; eauto.
    + guardH o. i.
      exploit Memory.add_get1; try exact GET1; try exact x2. i.
      exploit Memory.add_get1; try exact x4; try exact x3. i.
      esplits; eauto. refl.
  - revert H. erewrite Memory.add_o; eauto. condtac; ss.
    { i. des. clarify. }
    guardH o. erewrite Memory.add_o; eauto. condtac; ss.
    { i. des. clarify. }
    i. erewrite Memory.add_o; eauto. condtac; ss.
  - revert H. erewrite Memory.add_o; eauto. condtac; ss.
    { i. des. clarify. }
    guardH o. i. erewrite Memory.add_o; eauto. condtac; ss.
    guardH o0. erewrite Memory.add_o; eauto. condtac; ss.
    i. des. clarify.
    exploit Memory.add_get1; try exact H; try exact ADD. i.
    exploit Memory.get_disjoint; [exact GET0|exact x4|]. i. des.
    + subst. ss.
    + exfalso. apply (x5 ts2); econs; ss.
      * timetac.
      * exploit Memory.get_ts; try exact H. i. des; ss.
        rewrite x7 in *. timetac.
      * refl.
Qed.

Lemma merge_write_write
      loc ts1 ts3 val1 val2 released0 released2 ord
      lc0 gl0
      lc2 gl2
      (LC_WF: Local.wf lc0 gl0)
      (GL_WF: Global.wf gl0)
      (REL0_WF: View.opt_wf released0)
      (REL0_TS: Time.le ((View.rlx (View.unwrap released0)) loc) ts1)
      (REL0_CLOSED: Memory.closed_opt_view released0 (Global.memory gl0))
      (STEP: Local.write_step lc0 gl0 loc ts1 ts3 val2 released0 released2 ord lc2 gl2):
  exists ts2 lc1' gl1' lc2' gl2' released1',
    (<<STEP1: Local.write_step lc0 gl0 loc ts1 ts2 val1 released0 released1' ord lc1' gl1'>>) /\
    (<<STEP2: Local.write_step lc1' gl1' loc ts2 ts3 val2 released1' released2 ord lc2' gl2'>>) /\
    (<<LOCAL2: sim_local lc2' lc2>>) /\
    (<<GL2: sim_global gl2' gl2>>).
Proof.
  inv STEP.
  exploit Memory.add_ts; try exact WRITE. i.
  exploit Time.middle_spec; try exact x0. i. des.
  set (released1' := TView.write_released (Local.tview lc0) loc (Time.middle ts1 ts3) released0 ord).
  assert (REL1'_WF: View.opt_wf released1').
  { unfold released1', TView.write_released. condtac; econs.
    repeat (try condtac; aggrtac; try by apply LC_WF).
  }
  exploit (@split_add
             (Time.middle ts1 ts3)
             (Message.message val1 released1' (Ordering.le ord Ordering.na)));
    try exact WRITE; ss; try refl; eauto; ss.
  { exploit Memory.add_wf; eauto. }
  i. des.
  esplits.
  - econs; try exact ADD1; eauto.
    inv WRITABLE. econs.
    inv LC_WF. inv TVIEW_CLOSED. inv CUR.
    specialize (RLX loc). des.
    exploit Memory.add_get0; try exact WRITE. i. des.
    exploit Memory.add_get1; try exact RLX; try exact WRITE. i.
    exploit Memory.lt_get; try exact TS; eauto. i.
    timetac.
  - econs; s; eauto.
    + unfold released1', TView.write_released.
      condtac; ss. f_equal. aggrtac.
      condtac; ss; apply View.antisym; aggrtac; try apply LC_WF.
    + inv WRITABLE. econs.
      apply TimeFacts.join_spec_lt; ss.
      unfold TimeMap.singleton, LocFun.add. condtac; ss.
  - econs; ss. eapply write_write_tview; ss. apply LC_WF.
  - econs; ss. refl.
Qed.

Lemma merge_write_write_None
      loc ts1 ts3 val1 val2 released0 released2 ord
      lc0 gl0
      lc2 gl2
      (LC_WF: Local.wf lc0 gl0)
      (GL_WF: Global.wf gl0)
      (REL0_WF: View.opt_wf released0)
      (REL0_TS: Time.le ((View.rlx (View.unwrap released0)) loc) ts1)
      (REL0_CLOSED: Memory.closed_opt_view released0 (Global.memory gl0))
      (STEP: Local.write_step lc0 gl0 loc ts1 ts3 val2 released0 released2 ord lc2 gl2):
  exists ts2 lc1' gl1' lc2' gl2' released1' released2',
    (<<STEP1: Local.write_step lc0 gl0 loc ts1 ts2 val1 released0 released1' ord lc1' gl1'>>) /\
    (<<STEP2: Local.write_step lc1' gl1' loc ts2 ts3 val2 None released2' ord lc2' gl2'>>) /\
    (<<RELEASED: View.opt_le released2' released2>>) /\
    (<<LOCAL2: sim_local lc2' lc2>>) /\
    (<<GL2: sim_global gl2' gl2>>).
Proof.
  inv STEP.
  exploit Memory.add_ts; try exact WRITE. i.
  exploit Time.middle_spec; try exact x0. i. des.
  set (released1' := TView.write_released (Local.tview lc0) loc (Time.middle ts1 ts3) released0 ord).
  assert (REL1'_WF: View.opt_wf released1').
  { unfold released1', TView.write_released. condtac; econs.
    repeat (try condtac; aggrtac; try by apply LC_WF).
  }
  set (released2' := TView.write_released
                       (TView.write_tview (Local.tview lc0) loc (Time.middle ts1 ts3) ord)
                       loc ts3 None ord).
  assert (REL2'_WF: View.opt_wf released2').
  { eapply TViewFacts.write_future0; ss.
    eapply TViewFacts.write_future0; try by econs.
    apply LC_WF.
  }
  assert(REL2_LE: View.opt_le
                    released2'
                    (TView.write_released (Local.tview lc0) loc ts3 released0 ord)).
  { unfold released2', TView.write_released.
    condtac; ss. econs. aggrtac.
    condtac; ss; aggrtac; apply LC_WF.
  }
  exploit (@split_add
             (Time.middle ts1 ts3)
             (Message.message val1 released1' (Ordering.le ord Ordering.na))
             (Message.message val2 released2' (Ordering.le ord Ordering.na)));
    eauto; ss.
  { econs; try refl; try by (destruct ord; ss). }
  i. des.
  esplits.
  - econs; try exact ADD1; eauto.
    inv WRITABLE. econs.
    inv LC_WF. inv TVIEW_CLOSED. inv CUR.
    specialize (RLX loc). des.
    exploit Memory.add_get0; try exact WRITE. i. des.
    exploit Memory.add_get1; try exact RLX; try exact WRITE. i.
    exploit Memory.lt_get; try exact TS; eauto. i.
    timetac.
  - econs; s; eauto.
    inv WRITABLE. econs.
    apply TimeFacts.join_spec_lt; ss.
    unfold TimeMap.singleton, LocFun.add. condtac; ss.
  - ss.
  - econs; ss. eapply write_write_tview; ss. apply LC_WF.
  - econs; ss. refl.
Qed.

Lemma merge_fence_fence
      ordr ordw
      lc0 gl0
      lc2 gl2
      (LC_WF: Local.wf lc0 gl0)
      (STEP: Local.fence_step lc0 gl0 ordr ordw lc2 gl2):
  exists lc1 lc2' gl1' gl2',
    (<<STEP1: Local.fence_step lc0 gl0 ordr ordw lc1 gl1'>>) /\
    (<<STEP2: Local.fence_step lc1 gl1' ordr ordw lc2' gl2'>>) /\
    (<<LOCAL2: sim_local lc2' lc2>>) /\
    (<<GL2: sim_global gl2' gl2>>).
Proof.
  inv STEP. esplits.
  - econs; eauto.
  - econs; eauto.
  - s. econs; ss.
    unfold TView.read_fence_tview, TView.write_fence_tview, TView.write_fence_sc.
    econs; repeat (try condtac; aggrtac; try apply LC_WF).
  - econs; try refl. s.
    unfold TView.read_fence_tview, TView.write_fence_tview, TView.write_fence_sc.
    repeat (try condtac; aggrtac; try apply LC_WF).
Qed.
