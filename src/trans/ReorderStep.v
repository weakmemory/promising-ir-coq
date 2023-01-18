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
Require Import ReorderTView.

Require Import SimLocal.
Require Import SimMemory.
Require Import SimGlobal.

Set Implicit Arguments.


Lemma future_read_step
      lc1 gl1 gl1' loc ts val released ord lc2
      (FUTURE: Global.le gl1 gl1')
      (STEP: Local.read_step lc1 gl1 loc ts val released ord lc2):
  exists released' lc2',
    <<STEP: Local.read_step lc1 gl1' loc ts val released' ord lc2'>> /\
    <<REL: View.opt_le released' released>> /\
    <<LOCAL: sim_local lc2' lc2>>.
Proof.
  inv FUTURE. inv STEP.
  exploit MEMORY; eauto. i.
  esplits.
  - econs; eauto; try by etrans; eauto.
  - refl.
  - econs; s; refl.
Qed.

Lemma future_write_step
      lc1 gl1 loc from to val releasedm released ord lc2 gl2
      releasedm' gl1'
      (FUTURE: Global.strong_le gl1 gl1')
      (REL_LE: View.opt_le releasedm' releasedm)
      (STEP: Local.write_step lc1 gl1 loc from to val releasedm released ord lc2 gl2):
  (exists to',
      <<STEP: Local.racy_write_step lc1 gl1' loc to' ord>>) \/
  (exists released' lc2' gl2',
      (<<STEP: Local.write_step lc1 gl1' loc from to val releasedm' released' ord lc2' gl2'>>) /\
      (<<REL: View.opt_le released' released>>) /\
      (<<LOCAL: sim_local lc2' lc2>>)).
Proof.
Admitted.

(* Lemma future_fulfill_step *)
(*       lc1 sc1 sc1' loc from to val releasedm releasedm' released ord lc2 sc2 *)
(*       (REL_LE: View.opt_le releasedm' releasedm) *)
(*       (STEP: fulfill_step lc1 sc1 loc from to val releasedm released ord lc2 sc2): *)
(*   fulfill_step lc1 sc1' loc from to val releasedm' released ord lc2 sc1'. *)
(* Proof. *)
(*   assert (TVIEW: TView.write_tview (Local.tview lc1) sc1 loc to ord = TView.write_tview (Local.tview lc1) sc1' loc to ord). *)
(*   { unfold TView.write_tview. repeat (condtac; viewtac). } *)
(*   inversion STEP. subst lc2 sc2. *)
(*   rewrite TVIEW. econs; eauto. *)
(*   - etrans; eauto. unfold TView.write_released. condtac; econs. repeat apply View.join_spec. *)
(*     + rewrite <- View.join_l. apply View.unwrap_opt_le. auto. *)
(*     + rewrite <- ? View.join_r. rewrite TVIEW. refl. *)
(*   - econs; try apply WRITABLE. *)
(* Qed. *)

Lemma future_fence_step
      lc1 gl1 gl1' ordr ordw lc2 gl2
      (ORDW: Ordering.le ordw Ordering.acqrel)
      (FUTURE: Global.le gl1 gl1')
      (STEP: Local.fence_step lc1 gl1 ordr ordw lc2 gl2):
  Local.fence_step lc1 gl1' ordr ordw lc2 gl1'.
Proof.
  inv STEP.
  erewrite TViewFacts.write_fence_tview_acqrel; auto.
  econs; ss.
  rewrite TViewFacts.write_fence_sc_acqrel; ss.
  destruct gl1'. ss.
Qed.

Lemma future_is_racy
      lc1 gl1 gl1' loc to ord
      (LC_WF: Local.wf lc1 gl1)
      (FUTURE: Global.strong_le gl1 gl1')
      (STEP: Local.is_racy lc1 gl1 loc to ord):
  exists to',
    <<STEP: Local.is_racy lc1 gl1' loc to' ord>>.
Proof.
  inv FUTURE. inv LE.
  inv STEP; eauto.
  specialize (ADDNA loc). des.
  - esplits; econs 1; eauto.
    rewrite GET in *. ss.
  - r in LATEST. des.
    esplits. econs 2; eauto.
    inv LC_WF. inv TVIEW_CLOSED. inv CUR.
    specialize (PLN loc). des.
    unfold TView.racy_view. eauto.
Qed.

Lemma future_racy_read_step
      lc1 gl1 gl1' loc to val ord
      (LC_WF: Local.wf lc1 gl1)
      (FUTURE: Global.strong_le gl1 gl1')
      (STEP: Local.racy_read_step lc1 gl1 loc to val ord):
  exists to',
    <<STEP: Local.racy_read_step lc1 gl1' loc to' val ord>>.
Proof.
  inv STEP.
  exploit future_is_racy; eauto. i. des.
  esplits. econs. eauto.
Qed.

Lemma future_racy_write_step
      lc1 gl1 gl1' loc to ord
      (LC_WF: Local.wf lc1 gl1)
      (FUTURE: Global.strong_le gl1 gl1')
      (STEP: Local.racy_write_step lc1 gl1 loc to ord):
  exists to',
    <<STEP: Local.racy_write_step lc1 gl1' loc to' ord>>.
Proof.
  inv STEP.
  exploit future_is_racy; eauto. i. des.
  esplits. econs. eauto.
Qed.

Lemma future_racy_update_step
      lc1 gl1 gl1' loc to ordr ordw
      (LC_WF: Local.wf lc1 gl1)
      (FUTURE: Global.strong_le gl1 gl1')
      (STEP: Local.racy_update_step lc1 gl1 loc to ordr ordw):
  exists to',
    <<STEP: Local.racy_update_step lc1 gl1' loc to' ordr ordw>>.
Proof.
  inv STEP; eauto.
  exploit future_is_racy; eauto. i. des.
  esplits. econs 3. eauto.
Qed.


(** reorder read; step *)

Lemma reorder_read_read
      loc1 ts1 val1 released1 ord1
      loc2 ts2 val2 released2 ord2
      lc0 gl0
      lc1
      lc2
      (LOC: loc1 = loc2 -> Ordering.le ord1 Ordering.plain /\ Ordering.le ord2 Ordering.plain)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (LC_WF0: Local.wf lc0 gl0)
      (GL_WF0: Global.wf gl0)
      (STEP1: Local.read_step lc0 gl0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.read_step lc1 gl0 loc2 ts2 val2 released2 ord2 lc2):
  exists lc1',
    <<STEP1: Local.read_step lc0 gl0 loc2 ts2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.read_step lc1' gl0 loc1 ts1 val1 released1 ord1 lc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits.
  - econs; eauto.
    eapply TViewFacts.readable_mon; try apply READABLE0; eauto; try refl.
    apply TViewFacts.read_tview_incr.
  - econs; eauto.
    + s. unfold View.singleton_ur_if.
      econs; repeat (try condtac; try splits; aggrtac; eauto; try apply READABLE;
                     unfold TimeMap.singleton, LocFun.add in *; s).
      * specialize (LOC eq_refl). des. viewtac.
      * specialize (LOC eq_refl). des. viewtac.
      * specialize (LOC eq_refl). des. viewtac.
    + f_equal.
      inv GL_WF0. inv MEM_CLOSED.
      exploit CLOSED; try exact GET. i. des.
      exploit CLOSED; try exact GET0. i. des.
      inv MSG_WF. inv MSG_WF0.
      apply TView.antisym; apply ReorderTView.read_read_tview;
        (try by apply LC_WF0); eauto.
Qed.

Lemma reorder_read_write
      lc0 gl0 
      loc1 ts1 val1 released1 ord1 lc1
      loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 gl2
      (LOC: loc1 <> loc2)
      (ORD: Ordering.le ord1 Ordering.acqrel \/ Ordering.le ord2 Ordering.acqrel)
      (RELM_WF: View.opt_wf releasedm2)
      (LC_WF0: Local.wf lc0 gl0)
      (GL_WF0: Global.wf gl0)
      (STEP1: Local.read_step lc0 gl0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.write_step lc1 gl0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 gl2):
  exists lc1' released2' gl2' lc2',
    <<STEP1: Local.write_step lc0 gl0 loc2 from2 to2 val2 releasedm2 released2' ord2 lc1' gl2'>> /\
    <<STEP2: Local.read_step lc1' gl2' loc1 ts1 val1 released1 ord1 lc2'>> /\
    <<RELEASED: View.opt_le released2' released2>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<GLOBAL: sim_global gl2' gl2>>.
Proof.
  guardH ORD.
  exploit Local.read_step_future; eauto. i. des.
  inv STEP1. inv STEP2. ss.
  exploit TViewFacts.write_future0; try exact RELM_WF; try apply LC_WF0. i. des.
  exploit sim_memory_add_exists; try exact WRITE.
  { econs 1. exact WF_RELEASED. }
  { econs; try refl; try apply Bool.implb_same.
    eapply TViewFacts.write_released_mon;
      try apply TViewFacts.read_tview_incr; try refl; ss.
    apply LC_WF2.
  }
  { refl. }
  i. des. esplits.
  - econs; eauto.
    eapply TViewFacts.writable_mon; eauto; aggrtac. refl.
  - econs; eauto; s.
    + erewrite Memory.add_o; eauto. condtac; ss; eauto. des. congr.
    + inv READABLE.
      econs; repeat (try condtac; aggrtac; eauto; unfold TimeMap.singleton).
  - eapply TViewFacts.write_released_mon; try refl; ss. apply LC_WF2.
  - econs; ss.
    apply ReorderTView.read_write_tview; try apply LC_WF0; auto.
  - econs; ss. refl.
Qed.

Lemma reorder_read_update
      lc0 gl0
      loc1 ts1 val1 released1 ord1 lc1
      loc2 ts2 val2 released2 ord2 lc2
      from3 to3 val3 released3 ord3 lc3 gl3
      (LOC: loc1 <> loc2)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (ORD3: Ordering.le ord1 Ordering.acqrel \/ Ordering.le ord3 Ordering.acqrel)
      (LC_WF0: Local.wf lc0 gl0)
      (GL_WF0: Global.wf gl0)
      (STEP1: Local.read_step lc0 gl0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.read_step lc1 gl0 loc2 ts2 val2 released2 ord2 lc2)
      (STEP3: Local.write_step lc2 gl0 loc2 from3 to3 val3 released2 released3 ord3 lc3 gl3):
  exists released3' lc1' lc2' lc3' gl3',
    <<STEP1: Local.read_step lc0 gl0 loc2 ts2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.write_step lc1' gl0 loc2 from3 to3 val3 released2 released3' ord3 lc2' gl3'>> /\
    <<STEP3: Local.read_step lc2' gl3' loc1 ts1 val1 released1 ord1 lc3'>> /\
    <<RELEASED: View.opt_le released3' released3>> /\
    <<LOCAL: sim_local lc3' lc3>> /\
    <<GLOBAL: sim_global gl3' gl3>>.
Proof.
  guardH ORD3.
  exploit Local.read_step_future; try exact STEP1; eauto. i. des.
  exploit Local.read_step_future; try exact STEP2; eauto. i. des.
  exploit reorder_read_read; try exact STEP1; try exact STEP2; eauto; try congr. i. des.
  exploit Local.read_step_future; try exact STEP0; eauto. i. des.
  hexploit reorder_read_write; try exact STEP4; try exact STEP_SRC; eauto. i. des.
  esplits; eauto.
Qed.

Lemma reorder_read_fence
      loc1 ts1 val1 released1 ord1
      ordr2 ordw2
      lc0 gl0
      lc1
      lc2 gl2
      (ORDR2: Ordering.le ordr2 Ordering.relaxed)
      (ORDW2: Ordering.le ordw2 Ordering.acqrel)
      (LC_WF0: Local.wf lc0 gl0)
      (GL_WF0: Global.wf gl0)
      (STEP1: Local.read_step lc0 gl0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.fence_step lc1 gl0 ordr2 ordw2 lc2 gl2):
  exists lc1' lc2' gl2',
    <<STEP1: Local.fence_step lc0 gl0 ordr2 ordw2 lc1' gl2'>> /\
    <<STEP2: Local.read_step lc1' gl0 loc1 ts1 val1 released1 ord1 lc2'>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<GLOBAL: sim_global gl2' gl2>>.
Proof.
  exploit Local.read_step_future; eauto. i. des.
  inv STEP1. inv STEP2. ss.
  esplits.
  - econs; eauto.
  - econs; eauto. s.
    unfold TView.write_fence_tview, TView.read_fence_tview, TView.write_fence_sc.
    econs; repeat (try condtac; try splits; aggrtac; try apply READABLE).
  - econs; eauto. s.
    etrans.
    + apply ReorderTView.read_write_fence_tview; auto.
      eapply TViewFacts.read_fence_future; apply LC_WF0.
    + apply TViewFacts.write_fence_tview_mon; try refl.
      apply ReorderTView.read_read_fence_tview; try apply LC_WF0; auto.
      exploit TViewFacts.read_fence_future; try apply LC_WF0; eauto. i. des.
      eapply TViewFacts.read_future; eauto. apply GL_WF0.
  - econs; ss; try refl.
    unfold TView.write_fence_sc, TView.read_fence_tview.
    repeat condtac; aggrtac.
Qed.

Lemma reorder_read_is_racy
      loc1 ts1 val1 released1 ord1
      loc2 to2 ord2
      lc0 gl0
      lc1
      (STEP1: Local.read_step lc0 gl0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.is_racy lc1 gl0 loc2 to2 ord2):
  <<STEP1: Local.is_racy lc0 gl0 loc2 to2 ord2>>.
Proof.
  inv STEP1. inv STEP2; eauto. ss.
  econs; try exact GET0; eauto.
  eapply TViewFacts.racy_view_mon; try apply RACE; eauto.
  apply TViewFacts.read_tview_incr.
Qed.

Lemma reorder_read_racy_read
      loc1 ts1 val1 released1 ord1
      loc2 to2 val2 ord2
      lc0 gl0
      lc1
      (STEP1: Local.read_step lc0 gl0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.racy_read_step lc1 gl0 loc2 to2 val2 ord2):
  <<STEP1: Local.racy_read_step lc0 gl0 loc2 to2 val2 ord2>>.
Proof.
  inv STEP2.
  exploit reorder_read_is_racy; eauto.
Qed.

Lemma reorder_read_racy_write
      loc1 ts1 val1 released1 ord1
      loc2 to2 ord2
      lc0 gl0
      lc1
      (STEP1: Local.read_step lc0 gl0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.racy_write_step lc1 gl0 loc2 to2 ord2):
  <<STEP1: Local.racy_write_step lc0 gl0 loc2 to2 ord2>>.
Proof.
  inv STEP2.
  exploit reorder_read_is_racy; eauto.
Qed.


(** reorder write; step *)

Lemma reorder_write_read
      loc1 from1 to1 val1 releasedm1 released1 ord1
      loc2 ts2 val2 released2 ord2
      lc0 gl0
      lc1 gl1
      lc2
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (LC_WF0: Local.wf lc0 gl0)
      (GL_WF0: Global.wf gl0)
      (STEP1: Local.write_step lc0 gl0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1)
      (STEP2: Local.read_step lc1 gl1 loc2 ts2 val2 released2 ord2 lc2):
  exists lc1',
    <<STEP1: Local.read_step lc0 gl0 loc2 ts2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.write_step lc1' gl0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc2 gl1>>.
Proof.
  inv STEP1. inv STEP2. ss.
  revert GET. erewrite Memory.add_o; eauto.
  condtac; ss; try by (des; subst; congr). clear o COND. i.
  esplits.
  - econs; eauto.
    eapply TViewFacts.readable_mon; try apply READABLE; aggrtac; try refl.
  - rewrite ReorderTView.read_write_tview_eq; eauto; try apply LC_WF0; cycle 1.
    { inv GL_WF0. inv MEM_CLOSED.
      exploit CLOSED; eauto. i. des. inv MSG_WF. ss.
    }
    econs; ss; eauto.
    + unfold TView.write_released. ss.
      repeat (condtac; ss); try by (destruct ord1, ord2; ss).
    + s. unfold View.singleton_ur_if.
      econs; repeat (try condtac; try splits; aggrtac; eauto; try apply WRITABLE;
                     unfold TimeMap.singleton, LocFun.add in *; s);
        (try by inv WRITABLE; eapply TimeFacts.le_lt_lt; eauto; aggrtac).
Qed.

Lemma reorder_write_write
      lc0 gl0
      loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1
      loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 gl2
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (LOC: loc1 <> loc2)
      (LC_WF0: Local.wf lc0 gl0)
      (GL_WF0: Global.wf gl0)
      (REL1_WF: View.opt_wf releasedm1)
      (REL2_WF: View.opt_wf releasedm2)
      (STEP1: Local.write_step lc0 gl0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1)
      (STEP2: Local.write_step lc1 gl1 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 gl2):
  exists released2' lc1' lc2' gl1' gl2',
    <<STEP1: Local.write_step lc0 gl0 loc2 from2 to2 val2 releasedm2 released2' ord2 lc1' gl1'>> /\
    <<STEP2: Local.write_step lc1' gl1' loc1 from1 to1 val1 releasedm1 released1 ord1 lc2' gl2'>> /\
    <<RELEASED: View.opt_le released2' released2>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<GLOBAL: sim_global gl2' gl2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit Promises.reorder_fulfill_fulfill; [exact FULFILL|..]; eauto. i. des.
  exploit MemoryReorder.add_add; [exact WRITE|exact WRITE0|]. i. des.
  exploit TViewFacts.write_future0; try exact REL2_WF; try apply LC_WF0. i. des.
  exploit sim_memory_add_exists; try exact ADD1.
  { econs 1. exact WF_RELEASED. }
  { econs; try refl; try apply Bool.implb_same.
    eapply TViewFacts.write_released_mon;
      try apply TViewFacts.write_tview_incr; try refl; ss; try apply LC_WF0.
    eapply TViewFacts.write_future0; eauto. apply LC_WF0.
  }
  { refl. }
  i. des.
  exploit sim_memory_add_exists; try exact SIM; try exact ADD2; try refl.
  { econs. eapply TViewFacts.write_future0; ss. apply LC_WF0. }
  i. des.
  esplits.
  - econs; try exact FULFILL1; eauto.
    eapply TViewFacts.writable_mon; eauto; try refl. aggrtac.
  - econs; s; try exact FULFILL2; eauto.
    + unfold TView.write_released. ss. repeat (condtac; aggrtac).
    + inv WRITABLE. econs; i.
      * eapply TimeFacts.le_lt_lt; [|apply TS].
        repeat (try condtac; viewtac; unfold TimeMap.singleton in *; s).
  - eapply TViewFacts.write_released_mon; eauto; try refl.
    + eapply TViewFacts.write_tview_incr. apply LC_WF0.
    + eapply TViewFacts.write_future0; eauto. apply LC_WF0.
  - econs; ss.
    apply ReorderTView.write_write_tview; auto. apply LC_WF0.
  - econs; ss. refl.
Qed.

Lemma reorder_write_update
      lc0 gl0
      loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1
      loc2 ts2 val2 released2 ord2 lc2
      from3 to3 val3 released3 ord3 lc3 gl3
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (LC_WF0: Local.wf lc0 gl0)
      (GL_WF0: Global.wf gl0)
      (REL1_WF: View.opt_wf releasedm1)
      (STEP1: Local.write_step lc0 gl0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1)
      (STEP2: Local.read_step lc1 gl1 loc2 ts2 val2 released2 ord2 lc2)
      (STEP3: Local.write_step lc2 gl1 loc2 from3 to3 val3 released2 released3 ord3 lc3 gl3):
  exists released3' lc1' lc2' lc3' gl2' gl3',
    <<STEP1: Local.read_step lc0 gl0 loc2 ts2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.write_step lc1' gl0 loc2 from3 to3 val3 released2 released3' ord3 lc2' gl2'>> /\
    <<STEP3: Local.write_step lc2' gl2' loc1 from1 to1 val1 releasedm1 released1 ord1 lc3' gl3'>> /\
    <<RELEASED: View.opt_le released3' released3>> /\
    <<LOCAL: sim_local lc3' lc3>> /\
    <<GLOBAL: sim_global gl3' gl3>>.
Proof.
  exploit reorder_write_read; try exact STEP1; eauto. i. des.
  exploit Local.read_step_future; try exact STEP0; eauto. i. des.
  exploit reorder_write_write; try exact STEP4; try exact STEP3; eauto. i. des.
  esplits; eauto.
Qed.

Lemma reorder_write_is_racy
      lc0 gl0
      loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1
      loc2 to2 ord2
      (LOC: loc1 <> loc2)
      (STEP1: Local.write_step lc0 gl0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1)
      (STEP2: Local.is_racy lc1 gl1 loc2 to2 ord2):
  <<STEP1: Local.is_racy lc0 gl0 loc2 to2 ord2>>.
Proof.
  inv STEP1. inv STEP2; eauto; ss.
  - inv FULFILL; eauto.
    revert GET. erewrite BoolMap.remove_o; eauto.
    revert GETP. erewrite BoolMap.remove_o; eauto.
    condtac; ss. eauto.
  - revert GET. erewrite Memory.add_o; eauto.
    condtac; ss; try by (des; subst; congr). guardH o. i.
    econs; try exact GET; eauto.
    eapply TViewFacts.racy_view_mon; try apply RACE.
    apply View.join_l.
Qed.

Lemma reorder_write_racy_read
      lc0 gl0
      loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1
      loc2 to2 val2 ord2
      (LOC: loc1 <> loc2)
      (STEP1: Local.write_step lc0 gl0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1)
      (STEP2: Local.racy_read_step lc1 gl1 loc2 to2 val2 ord2):
  <<STEP1: Local.racy_read_step lc0 gl0 loc2 to2 val2 ord2>>.
Proof.
  inv STEP2.
  exploit reorder_write_is_racy; eauto.
Qed.

Lemma reorder_write_racy_write
      lc0 gl0
      loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1
      loc2 to2 ord2
      (LOC: loc1 <> loc2)
      (STEP1: Local.write_step lc0 gl0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1)
      (STEP2: Local.racy_write_step lc1 gl1 loc2 to2 ord2):
  <<STEP1: Local.racy_write_step lc0 gl0 loc2 to2 ord2>>.
Proof.
  inv STEP2.
  exploit reorder_write_is_racy; eauto.
Qed.

Lemma reorder_write_racy_update
      lc0 gl0
      loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1
      loc2 to2 ordr2 ordw2
      (LOC: loc1 <> loc2)
      (STEP1: Local.write_step lc0 gl0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 gl1)
      (STEP2: Local.racy_update_step lc1 gl1 loc2 to2 ordr2 ordw2):
  <<STEP1: Local.racy_update_step lc0 gl0 loc2 to2 ordr2 ordw2>>.
Proof.
  inv STEP2; eauto.
  exploit reorder_write_is_racy; eauto.
Qed.


(* reorder update; step *)

Lemma reorder_update_read
      lc0 gl0
      loc1 ts1 val1 released1 ord1 lc1
      from2 to2 val2 released2 ord2 lc2 gl2
      loc3 ts3 val3 released3 ord3 lc3
      (LOC: loc1 <> loc3)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (ORD3: Ordering.le ord3 Ordering.relaxed)
      (LC_WF0: Local.wf lc0 gl0)
      (GL_WF0: Global.wf gl0)
      (STEP1: Local.read_step lc0 gl0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.write_step lc1 gl0 loc1 from2 to2 val2 released1 released2 ord2 lc2 gl2)
      (STEP3: Local.read_step lc2 gl2 loc3 ts3 val3 released3 ord3 lc3):
  exists lc1' lc2',
    <<STEP1: Local.read_step lc0 gl0 loc3 ts3 val3 released3 ord3 lc1'>> /\
    <<STEP2: Local.read_step lc1' gl0 loc1 ts1 val1 released1 ord1 lc2'>> /\
    <<STEP3: Local.write_step lc2' gl0 loc1 from2 to2 val2 released1 released2 ord2 lc3 gl2>>.
Proof.
  exploit Local.read_step_future; try exact STEP1; eauto. i. des.
  exploit reorder_write_read; try exact STEP2; eauto. i. des.
  exploit reorder_read_read; try exact STEP1; eauto; try congr. i. des.
  esplits; eauto.
Qed.

Lemma reorder_update_write
      lc0 gl0
      loc1 ts1 val1 released1 ord1 lc1
      from2 to2 val2 released2 ord2 lc2 gl2
      loc3 from3 to3 val3 releasedm3 released3 ord3 lc3 gl3
      (LOC: loc1 <> loc3)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (ORD3: Ordering.le ord1 Ordering.acqrel \/ Ordering.le ord3 Ordering.acqrel)
      (LC_WF0: Local.wf lc0 gl0)
      (GL_WF0: Global.wf gl0)
      (REL_WF: View.opt_wf releasedm3)
      (REL_CLOSED: Memory.closed_opt_view releasedm3 (Global.memory gl0))
      (REL_TS: Time.le (View.rlx (View.unwrap releasedm3) loc3) to3)
      (STEP1: Local.read_step lc0 gl0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.write_step lc1 gl0 loc1 from2 to2 val2 released1 released2 ord2 lc2 gl2)
      (STEP3: Local.write_step lc2 gl2 loc3 from3 to3 val3 releasedm3 released3 ord3 lc3 gl3):
  exists released3' released2' lc1' lc2' lc3' gl1' gl3',
    <<STEP1: Local.write_step lc0 gl0 loc3 from3 to3 val3 releasedm3 released3' ord3 lc1' gl1'>> /\
    <<STEP2: Local.read_step lc1' gl1' loc1 ts1 val1 released1 ord1 lc2'>> /\
    <<STEP3: Local.write_step lc2' gl1' loc1 from2 to2 val2 released1 released2' ord2 lc3' gl3'>> /\
    <<RELEASED2: View.opt_le released2' released2>> /\
    <<RELEASED3: View.opt_le released3' released3>> /\
    <<LOCAL: sim_local lc3' lc3>> /\
    <<GLOBAL: sim_global gl3' gl3>>.
Proof.
  guardH ORD3.
  exploit Local.read_step_future; try exact STEP1; eauto. i. des.
  exploit reorder_write_write; try exact STEP2; try exact STEP3; eauto. i. des.
  exploit reorder_read_write; try exact STEP1; try exact STEP0; eauto. i. des.
  exploit Local.write_step_future; try exact STEP0; eauto. i. des.
  exploit Local.write_step_future; try exact STEP5; eauto. i. des.
  exploit Local.read_step_future; try exact STEP6; eauto. i. des.
  exploit sim_local_write; try exact STEP4;
    try exact LOCAL0; try exact GLOBAL0; try refl; eauto. i. des.
  esplits; eauto; etrans; eauto.
Qed.

Lemma update_ts
      lc0 gl0
      loc ts1 val1 released1 ord1 lc1
      from2 to2 val2 releasedm2 released2 ord2 lc2 gl2
      (STEP1: Local.read_step lc0 gl0 loc ts1 val1 released1 ord1 lc1)
      (STEP2: Local.write_step lc1 gl0 loc from2 to2 val2 releasedm2 released2 ord2 lc2 gl2):
  Time.lt ts1 to2.
Proof.
  inv STEP1. inv STEP2. inv WRITABLE. ss.
  eapply TimeFacts.le_lt_lt; eauto.
  etrans; [|apply TimeMap.join_l].
  etrans; [|apply TimeMap.join_r].
  unfold View.singleton_ur_if.
  condtac; ss; aggrtac.
Qed.

Lemma reorder_update_update
      lc0 gl0
      loc1 ts1 val1 released1 ord1 lc1
      from2 to2 val2 released2 ord2 lc2 gl2
      loc3 ts3 val3 released3 ord3 lc3
      from4 to4 val4 released4 ord4 lc4 gl4
      (LOC: loc1 <> loc3)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (ORD3: Ordering.le ord3 Ordering.relaxed)
      (ORD: Ordering.le ord1 Ordering.acqrel \/ Ordering.le ord4 Ordering.acqrel)
      (LC_WF0: Local.wf lc0 gl0)
      (GL_WF0: Global.wf gl0)
      (STEP1: Local.read_step lc0 gl0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.write_step lc1 gl0 loc1 from2 to2 val2 released1 released2 ord2 lc2 gl2)
      (STEP3: Local.read_step lc2 gl2 loc3 ts3 val3 released3 ord3 lc3)
      (STEP4: Local.write_step lc3 gl2 loc3 from4 to4 val4 released3 released4 ord4 lc4 gl4):
  exists released2' released4' lc1' lc2' lc3' lc4' gl2' gl4',
    <<STEP1: Local.read_step lc0 gl0 loc3 ts3 val3 released3 ord3 lc1'>> /\
    <<STEP2: Local.write_step lc1' gl0 loc3 from4 to4 val4 released3 released4' ord4 lc2' gl2'>> /\
    <<STEP3: Local.read_step lc2' gl2' loc1 ts1 val1 released1 ord1 lc3'>> /\
    <<STEP4: Local.write_step lc3' gl2' loc1 from2 to2 val2 released1 released2' ord2 lc4' gl4'>> /\
    <<RELEASED2: View.opt_le released2' released2>> /\
    <<RELEASED4: View.opt_le released4' released4>> /\
    <<LOCAL: sim_local  lc4' lc4>> /\
    <<GLOBAL: sim_global gl4' gl4>>.
Proof.
  guardH ORD.
  exploit reorder_update_read; try exact STEP2; try exact STEP1; try exact STEP3; eauto. i. des.
  exploit Local.read_step_future; try exact STEP0; eauto. i. des.
  hexploit reorder_update_write; try exact STEP5; try exact STEP6; try exact STEP4; eauto.
  { etrans; eauto.
    exploit update_ts; try exact STEP3; eauto. i. econs. ss.
  }
  i. des.
  esplits; eauto.
Qed.


(** reorder fence; step *)

Lemma reorder_fence_read
      lc0 gl0
      ordr1 ordw1 lc1 gl1
      loc2 to2 val2 released2 ord2 lc2
      (ORDR1: Ordering.le ordr1 Ordering.acqrel)
      (ORDW1: Ordering.le ordw1 Ordering.relaxed)
      (ORD2: Ordering.le ord2 Ordering.plain \/ Ordering.le Ordering.acqrel ord2)
      (LC_WF0: Local.wf lc0 gl0)
      (GL_WF0: Global.wf gl0)
      (STEP1: Local.fence_step lc0 gl0 ordr1 ordw1 lc1 gl1)
      (STEP2: Local.read_step lc1 gl0 loc2 to2 val2 released2 ord2 lc2):
  exists lc1' lc2' gl2',
    <<STEP1: Local.read_step lc0 gl0 loc2 to2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.fence_step lc1' gl0 ordr1 ordw1 lc2' gl2'>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<GLOBAL: sim_global gl2' gl1>>.
Proof.
  guardH ORD2. inv STEP1. inv STEP2. ss.
  esplits.
  - econs; eauto.
    eapply TViewFacts.readable_mon; eauto; try refl.
    etrans.
    + apply TViewFacts.write_fence_tview_incr. apply LC_WF0.
    + apply TViewFacts.write_fence_tview_mon; try refl; try apply LC_WF0.
      apply TViewFacts.read_fence_tview_incr. apply LC_WF0.
  - econs; eauto.
  - econs; ss.
    inv GL_WF0. inv MEM_CLOSED. exploit CLOSED; eauto. i. des. inv MSG_WF.
    exploit TViewFacts.read_future; try exact GET; try apply LC_WF0; eauto. i. des.
    exploit TViewFacts.read_fence_future; try apply LC_WF0; eauto. i. des.
    etrans; [|etrans].
    + apply TViewFacts.write_fence_tview_mon; [|refl|refl|].
      * apply ReorderTView.read_fence_read_tview; auto. apply LC_WF0.
      * eapply TViewFacts.read_fence_future; eauto.
    + apply ReorderTView.write_fence_read_tview; eauto.
    + apply TViewFacts.read_tview_mon; auto; try refl.
      eapply TViewFacts.write_fence_future; eauto.
  - econs; try refl. s. etrans.
    + apply TViewFacts.write_fence_sc_mon; [|refl|refl].
      apply ReorderTView.read_fence_read_tview; auto. apply LC_WF0.
    + eapply ReorderTView.write_fence_read_sc; auto.
      eapply TViewFacts.read_fence_future; eauto; apply LC_WF0.
Qed.

Lemma reorder_fence_write
      lc0 gl0
      ordr1 ordw1 lc1 gl1
      loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 gl2
      (ORDR1: Ordering.le ordr1 Ordering.acqrel)
      (ORDW1: Ordering.le ordw1 Ordering.relaxed)
      (LC_WF0: Local.wf lc0 gl0)
      (GL_WF0: Global.wf gl0)
      (REL2_WF: View.opt_wf releasedm2)
      (REL2_CLOSED: Memory.closed_opt_view releasedm2 (Global.memory gl0))
      (STEP1: Local.fence_step lc0 gl0 ordr1 ordw1 lc1 gl1)
      (STEP2: Local.write_step lc1 gl1 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 gl2):
  exists released2' lc1' lc2' gl1' gl2',
    <<STEP1: Local.write_step lc0 gl0 loc2 from2 to2 val2 releasedm2 released2' ord2 lc1' gl1'>> /\
    <<STEP2: Local.fence_step lc1' gl1' ordr1 ordw1 lc2' gl2'>> /\
    <<RELEASED: View.opt_le released2' released2>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<GLOBAL: sim_global gl2' gl2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit TViewFacts.read_fence_future; try apply LC_WF0; eauto. i. des.
  hexploit TViewFacts.write_fence_future; eauto; try apply GL_WF0. s. i. des.
  exploit TViewFacts.write_future0; try exact REL2_WF; try apply LC_WF0. i. des.
  exploit sim_memory_add_exists; try exact WRITE.
  { econs 1. exact WF_RELEASED. }
  { econs; try refl; try apply Bool.implb_same.
    eapply TViewFacts.write_released_mon; try refl; ss; try apply LC_WF0; eauto.
    etrans; [|eapply TViewFacts.write_fence_tview_incr]; eauto.
    apply TViewFacts.read_fence_tview_incr. apply LC_WF0.
  }
  { refl. }
  i. des. esplits.
  - econs; eauto.
    eapply TViewFacts.writable_mon; eauto; try refl.
    etrans.
    + apply TViewFacts.read_fence_tview_incr. apply LC_WF0.
    + apply TViewFacts.write_fence_tview_incr.
      eapply TViewFacts.read_fence_future; apply LC_WF0.
  - econs; eauto. i. destruct ordw1; ss.
  - eapply TViewFacts.write_released_mon; try refl; ss.
    etrans; [|eapply TViewFacts.write_fence_tview_incr]; eauto.
    apply TViewFacts.read_fence_tview_incr. apply LC_WF0.
  - econs; ss.
    etrans; [|etrans].
    + apply TViewFacts.write_fence_tview_mon; [|refl|refl|].
      * apply ReorderTView.read_fence_write_tview; auto. apply LC_WF0.
      * exploit TViewFacts.write_future; try exact ADD;
          try apply LC_WF0; try apply GL_WF0; ss. i. des.
        eapply TViewFacts.read_fence_future; eauto.
    + apply ReorderTView.write_fence_write_tview; auto.
    + apply TViewFacts.write_tview_mon; auto; try refl.
  - econs; ss. etrans.
    + apply TViewFacts.write_fence_sc_mon; [|refl|refl].
      apply ReorderTView.read_fence_write_tview; auto. apply LC_WF0.
    + eapply ReorderTView.write_fence_write_sc; auto.
Qed.

Lemma reorder_fence_fence
      lc0 gl0
      ordr1 ordw1 lc1 gl1
      ordr2 ordw2 lc2 gl2
      (ORDR1: Ordering.le ordr1 Ordering.acqrel)
      (ORDW1: Ordering.le ordw1 Ordering.relaxed)
      (ORDR2: Ordering.le ordr2 Ordering.relaxed)
      (ORDW2: Ordering.le ordw2 Ordering.acqrel)
      (LC_WF0: Local.wf lc0 gl0)
      (GL_WF0: Global.wf gl0)
      (STEP1: Local.fence_step lc0 gl0 ordr1 ordw1 lc1 gl2)
      (STEP2: Local.fence_step lc1 gl1 ordr2 ordw2 lc2 gl2):
  exists lc1' lc2' gl1' gl2',
    <<STEP1: Local.fence_step lc0 gl0 ordr2 ordw2 lc1' gl1'>> /\
    <<STEP2: Local.fence_step lc1' gl1' ordr1 ordw1 lc2' gl2'>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<GLOBAL: sim_global gl2' gl2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits.
  - econs; eauto.
  - econs; eauto.
  - econs; ss.
    unfold TView.write_fence_tview, TView.write_fence_sc.
    econs; repeat (try condtac; aggrtac; try apply LC_WF0).
  - econs; ss; try refl.
    unfold TView.write_fence_sc.
    repeat (try condtac; aggrtac).
Qed.


(* (** reorder racy read *) *)

(* Lemma reorder_is_racy_read *)
(*       loc1 to1 ord1 *)
(*       loc2 ts2 val2 released2 ord2 *)
(*       lc0 mem0 *)
(*       lc2 *)
(*       (LOC: loc1 = loc2 -> Ordering.le ord1 Ordering.plain /\ Ordering.le ord2 Ordering.plain) *)
(*       (ORD2: Ordering.le ord2 Ordering.relaxed) *)
(*       (STEP1: Local.is_racy lc0 mem0 loc1 to1 ord1) *)
(*       (STEP2: Local.read_step lc0 mem0 loc2 ts2 val2 released2 ord2 lc2): *)
(*   <<STEP: Local.is_racy lc2 mem0 loc1 to1 ord1>>. *)
(* Proof. *)
(*   inv STEP1. inv STEP2. ss. *)
(*   econs; eauto; ss. inv READABLE. *)
(*   condtac; try by (destruct ord2; ss). *)
(*   repeat apply TimeFacts.join_spec_lt; ss. *)
(*   - unfold View.singleton_ur_if. condtac; ss. *)
(*     + unfold TimeMap.singleton, LocFun.add, LocFun.find. condtac; ss. *)
(*       * subst. exploit LOC; eauto. i. des. destruct ord2; ss. *)
(*       * eapply TimeFacts.le_lt_lt; eauto. apply Time.bot_spec. *)
(*     + eapply TimeFacts.le_lt_lt; eauto. apply Time.bot_spec. *)
(*   - eapply TimeFacts.le_lt_lt; eauto. apply Time.bot_spec. *)
(* Qed. *)

(* Lemma reorder_is_racy_fulfill *)
(*       loc1 to1 ord1 *)
(*       loc2 from2 to2 val2 releasedm2 released2 ord2 *)
(*       lc0 sc0 mem0 *)
(*       lc2 sc2 *)
(*       (LOC: loc1 <> loc2) *)
(*       (STEP1: Local.is_racy lc0 mem0 loc1 to1 ord1) *)
(*       (STEP2: fulfill_step lc0 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2): *)
(*   <<STEP: Local.is_racy lc2 mem0 loc1 to1 ord1>>. *)
(* Proof. *)
(*   inv STEP1. inv STEP2. *)
(*   econs; eauto; ss. *)
(*   - erewrite Memory.remove_o; eauto. condtac; ss. *)
(*   - apply TimeFacts.join_spec_lt; ss. *)
(*     unfold TimeMap.singleton, LocFun.add. condtac; ss. *)
(*     eapply TimeFacts.le_lt_lt; eauto. apply Time.bot_spec. *)
(* Qed. *)

(* Lemma reorder_is_racy_write *)
(*       loc1 to1 ord1 *)
(*       loc2 from2 to2 val2 releasedm2 released2 ord2 *)
(*       lc0 sc0 mem0 *)
(*       lc2 sc2 mem2 *)
(*       kind *)
(*       (LOC: loc1 <> loc2) *)
(*       (RELM_WF: View.opt_wf releasedm2) *)
(*       (RELM_CLOSED: Memory.closed_opt_view releasedm2 mem0) *)
(*       (WF0: Local.wf lc0 mem0) *)
(*       (SC0: Memory.closed_timemap sc0 mem0) *)
(*       (MEM0: Memory.closed mem0) *)
(*       (STEP1: Local.is_racy lc0 mem0 loc1 to1 ord1) *)
(*       (STEP2: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind): *)
(*   <<STEP: Local.is_racy lc2 mem2 loc1 to1 ord1>>. *)
(* Proof. *)
(*   exploit write_promise_fulfill; try exact STEP2; eauto. i. des. *)
(*   exploit reorder_is_racy_promise; eauto. i. des. *)
(*   exploit reorder_is_racy_fulfill; eauto. *)
(* Qed. *)

(* Lemma reorder_is_racy_update *)
(*       loc1 to1 ord1 *)
(*       loc2 ts2 val2 released2 ord2 *)
(*       from3 to3 val3 released3 ord3 *)
(*       lc0 sc0 mem0 *)
(*       lc2 *)
(*       lc3 sc3 mem3 *)
(*       kind *)
(*       (LOC: loc1 <> loc2) *)
(*       (ORD2: Ordering.le ord2 Ordering.relaxed) *)
(*       (WF0: Local.wf lc0 mem0) *)
(*       (SC0: Memory.closed_timemap sc0 mem0) *)
(*       (MEM0: Memory.closed mem0) *)
(*       (STEP1: Local.is_racy lc0 mem0 loc1 to1 ord1) *)
(*       (STEP2: Local.read_step lc0 mem0 loc2 ts2 val2 released2 ord2 lc2) *)
(*       (STEP3: Local.write_step lc2 sc0 mem0 loc2 from3 to3 val3 released2 released3 ord3 lc3 sc3 mem3 kind): *)
(*   <<STEP: Local.is_racy lc3 mem3 loc1 to1 ord1>>. *)
(* Proof. *)
(*   exploit Local.read_step_future; try exact STEP2; eauto. i. des. *)
(*   exploit reorder_is_racy_read; eauto; ss. i. des. *)
(*   exploit reorder_is_racy_write; try exact STEP3; eauto. *)
(* Qed. *)

(* Lemma reorder_is_racy_fence *)
(*       loc1 to1 ord1 *)
(*       ordr2 ordw2 *)
(*       lc0 sc0 mem0 *)
(*       lc2 sc2 *)
(*       (ORDR2: Ordering.le ordr2 Ordering.relaxed) *)
(*       (ORDW2: Ordering.le ordw2 Ordering.acqrel) *)
(*       (WF0: Local.wf lc0 mem0) *)
(*       (MEM0: Memory.closed mem0) *)
(*       (STEP1: Local.is_racy lc0 mem0 loc1 to1 ord1) *)
(*       (STEP2: Local.fence_step lc0 sc0 ordr2 ordw2 lc2 sc2): *)
(*   <<STEP: Local.is_racy lc2 mem0 loc1 to1 ord1>>. *)
(* Proof. *)
(*   inv STEP1. inv STEP2. ss. *)
(*   econs; eauto; ss. *)
(*   condtac; try by (destruct ordw2; ss). *)
(*   condtac; try by (destruct ordr2; ss). *)
(* Qed. *)

(* Lemma reorder_racy_read_read *)
(*       loc1 to1 val1 ord1 *)
(*       loc2 ts2 val2 released2 ord2 *)
(*       lc0 mem0 *)
(*       lc2 *)
(*       (LOC: loc1 = loc2 -> Ordering.le ord1 Ordering.plain /\ Ordering.le ord2 Ordering.plain) *)
(*       (ORD2: Ordering.le ord2 Ordering.relaxed) *)
(*       (STEP1: Local.racy_read_step lc0 mem0 loc1 to1 val1 ord1) *)
(*       (STEP2: Local.read_step lc0 mem0 loc2 ts2 val2 released2 ord2 lc2): *)
(*   <<STEP: Local.racy_read_step lc2 mem0 loc1 to1 val1 ord1>>. *)
(* Proof. *)
(*   inv STEP1. *)
(*   exploit reorder_is_racy_read; eauto. *)
(* Qed. *)

(* Lemma reorder_racy_read_fulfill *)
(*       loc1 to1 val1 ord1 *)
(*       loc2 from2 to2 val2 releasedm2 released2 ord2 *)
(*       lc0 sc0 mem0 *)
(*       lc2 sc2 *)
(*       (LOC: loc1 <> loc2) *)
(*       (STEP1: Local.racy_read_step lc0 mem0 loc1 to1 val1 ord1) *)
(*       (STEP2: fulfill_step lc0 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2): *)
(*   <<STEP: Local.racy_read_step lc2 mem0 loc1 to1 val1 ord1>>. *)
(* Proof. *)
(*   inv STEP1. *)
(*   exploit reorder_is_racy_fulfill; eauto. *)
(* Qed. *)

(* Lemma reorder_racy_read_write *)
(*       loc1 to1 val1 ord1 *)
(*       loc2 from2 to2 val2 releasedm2 released2 ord2 *)
(*       lc0 sc0 mem0 *)
(*       lc2 sc2 mem2 *)
(*       kind *)
(*       (LOC: loc1 <> loc2) *)
(*       (RELM_WF: View.opt_wf releasedm2) *)
(*       (RELM_CLOSED: Memory.closed_opt_view releasedm2 mem0) *)
(*       (WF0: Local.wf lc0 mem0) *)
(*       (SC0: Memory.closed_timemap sc0 mem0) *)
(*       (MEM0: Memory.closed mem0) *)
(*       (STEP1: Local.racy_read_step lc0 mem0 loc1 to1 val1 ord1) *)
(*       (STEP2: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind): *)
(*   <<STEP: Local.racy_read_step lc2 mem2 loc1 to1 val1 ord1>>. *)
(* Proof. *)
(*   exploit write_promise_fulfill; try exact STEP2; eauto. i. des. *)
(*   exploit reorder_racy_read_promise; eauto. i. des. *)
(*   exploit reorder_racy_read_fulfill; eauto. *)
(* Qed. *)

(* Lemma reorder_racy_read_update *)
(*       loc1 to1 val1 ord1 *)
(*       loc2 ts2 val2 released2 ord2 *)
(*       from3 to3 val3 released3 ord3 *)
(*       lc0 sc0 mem0 *)
(*       lc2 *)
(*       lc3 sc3 mem3 *)
(*       kind *)
(*       (LOC: loc1 <> loc2) *)
(*       (ORD2: Ordering.le ord2 Ordering.relaxed) *)
(*       (WF0: Local.wf lc0 mem0) *)
(*       (SC0: Memory.closed_timemap sc0 mem0) *)
(*       (MEM0: Memory.closed mem0) *)
(*       (STEP1: Local.racy_read_step lc0 mem0 loc1 to1 val1 ord1) *)
(*       (STEP2: Local.read_step lc0 mem0 loc2 ts2 val2 released2 ord2 lc2) *)
(*       (STEP3: Local.write_step lc2 sc0 mem0 loc2 from3 to3 val3 released2 released3 ord3 lc3 sc3 mem3 kind): *)
(*   <<STEP: Local.racy_read_step lc3 mem3 loc1 to1 val1 ord1>>. *)
(* Proof. *)
(*   exploit Local.read_step_future; try exact STEP2; eauto. i. des. *)
(*   exploit reorder_racy_read_read; eauto; ss. i. des. *)
(*   exploit reorder_racy_read_write; try exact STEP3; eauto. *)
(* Qed. *)

(* Lemma reorder_racy_read_fence *)
(*       loc1 to1 val1 ord1 *)
(*       ordr2 ordw2 *)
(*       lc0 sc0 mem0 *)
(*       lc2 sc2 *)
(*       (ORDR2: Ordering.le ordr2 Ordering.relaxed) *)
(*       (ORDW2: Ordering.le ordw2 Ordering.acqrel) *)
(*       (WF0: Local.wf lc0 mem0) *)
(*       (MEM0: Memory.closed mem0) *)
(*       (STEP1: Local.racy_read_step lc0 mem0 loc1 to1 val1 ord1) *)
(*       (STEP2: Local.fence_step lc0 sc0 ordr2 ordw2 lc2 sc2): *)
(*   <<STEP: Local.racy_read_step lc2 mem0 loc1 to1 val1 ord1>>. *)
(* Proof. *)
(*   inv STEP1. *)
(*   exploit reorder_is_racy_fence; eauto. *)
(* Qed. *)
