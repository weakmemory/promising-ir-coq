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

Require Import SimLocal.
Require Import SimMemory.
Require Import SimGlobal.

Set Implicit Arguments.


(** rel-fenced *)

Definition local_relfenced (lc:Local.t) :=
  (Local.mk (TView.mk
               (fun _ => (TView.cur (Local.tview lc)))
               (TView.cur (Local.tview lc))
               (TView.acq (Local.tview lc)))
            (Local.promises lc)
            (Local.reserves lc)).

Lemma local_relfenced_wf
      lc gl
      (WF: Local.wf lc gl):
  Local.wf (local_relfenced lc) gl.
Proof.
  inv WF. econs; ss; eauto.
  - inv TVIEW_WF. econs; ss. refl.
  - inv TVIEW_CLOSED. econs; ss.
Qed.

Lemma local_relfenced_sim_local
      lc gl
      (WF: Local.wf lc gl):
  sim_local lc (local_relfenced lc).
Proof.
  econs; ss. econs; try refl; apply WF.
Qed.

Lemma sim_local_relfenced
      lc_src
      lc_tgt gl_tgt
      (LOCAL: sim_local lc_src lc_tgt)
      (LC_WF_TGT: Local.wf lc_tgt gl_tgt):
  sim_local lc_src (local_relfenced lc_tgt).
Proof.
  etrans; eauto using local_relfenced_sim_local.
Qed.

Lemma sim_local_internal_relfenced
      e
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      lc2_tgt gl2_tgt
      (STEP_TGT: Local.internal_step e lc1_tgt gl1_tgt lc2_tgt gl2_tgt)
      (LOCAL1: sim_local lc1_src (local_relfenced lc1_tgt))
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (LC_WF1_SRC: Local.wf lc1_src gl1_src)
      (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF1_SRC: Global.wf gl1_src)
      (GL_WF1_TGT: Global.wf gl1_tgt):
  exists lc2_src gl2_src,
    <<STEP_SRC: Local.internal_step e lc1_src gl1_src lc2_src gl2_src>> /\
    <<LOCAL2: sim_local lc2_src (local_relfenced lc2_tgt)>> /\
    <<GLOBAL2: sim_global gl2_src gl2_tgt>>.
Proof.
  exploit local_relfenced_wf; try exact LC_WF1_TGT. i.
  exploit sim_local_internal; try exact LOCAL1; eauto.
  unfold local_relfenced. destruct lc1_tgt.
  inv STEP_TGT; inv LOCAL; ss; eauto.
Qed.

Lemma sim_local_read_relfenced
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      lc2_tgt
      loc ts val released_tgt ord_src ord_tgt
      (STEP_TGT: Local.read_step lc1_tgt gl1_tgt loc ts val released_tgt ord_tgt lc2_tgt)
      (LOCAL1: sim_local lc1_src (local_relfenced lc1_tgt))
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (LC_WF1_SRC: Local.wf lc1_src gl1_src)
      (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF1_SRC: Global.wf gl1_src)
      (GL_WF1_TGT: Global.wf gl1_tgt)
      (ORD: Ordering.le ord_src ord_tgt):
  exists released_src lc2_src,
    <<REL: View.opt_le released_src released_tgt>> /\
    <<STEP_SRC: Local.read_step lc1_src gl1_src loc ts val released_src ord_src lc2_src>> /\
    <<LOCAL2: sim_local lc2_src (local_relfenced lc2_tgt)>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit sim_memory_get; try exact GET; try apply GLOBAL1. i. des. inv MSG.
  esplits; eauto.
  - econs; eauto; try by etrans; eauto.
    eapply TViewFacts.readable_mon; eauto. apply TVIEW.
  - econs; eauto. inv TVIEW. ss. econs; s.
    + i. unfold LocFun.find. etrans; [apply LC_WF1_SRC|].
      eauto using View.join_l.
    + repeat apply View.join_le; ss.
      * unfold View.singleton_ur_if. repeat condtac; viewtac.
      * repeat condtac; viewtac.
    + repeat apply View.join_le; ss.
      * unfold View.singleton_ur_if. repeat condtac; viewtac.
      * repeat condtac; viewtac.
Qed.

Lemma sim_local_write_relfenced
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      lc2_tgt gl2_tgt
      loc from to val releasedm_src releasedm_tgt released_tgt ord_src ord_tgt
      (RELM_LE: View.opt_le releasedm_src releasedm_tgt)
      (RELM_WF_SRC: View.opt_wf releasedm_src)
      (RELM_CLOSED_SRC: Memory.closed_opt_view releasedm_src (Global.memory gl1_src))
      (RELM_WF_TGT: View.opt_wf releasedm_tgt)
      (ORD_TGT: Ordering.le ord_tgt Ordering.plain \/ Ordering.le Ordering.acqrel ord_tgt)
      (ORD: Ordering.le ord_src ord_tgt)
      (STEP_TGT: Local.write_step lc1_tgt gl1_tgt loc from to val releasedm_tgt released_tgt ord_tgt lc2_tgt gl2_tgt)
      (LOCAL1: sim_local lc1_src (local_relfenced lc1_tgt))
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (LC_WF1_SRC: Local.wf lc1_src gl1_src)
      (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF1_SRC: Global.wf gl1_src)
      (GL_WF1_TGT: Global.wf gl1_tgt):
  exists released_src lc2_src gl2_src,
    <<STEP_SRC: Local.write_step lc1_src gl1_src loc from to val releasedm_src released_src ord_src lc2_src gl2_src>> /\
    <<RELEASED: View.opt_le released_src released_tgt>> /\
    <<LOCAL2: sim_local lc2_src (local_relfenced lc2_tgt)>> /\
    <<GLOBAL2: sim_global gl2_src gl2_tgt>>.
Proof.
  guardH ORD_TGT. inv STEP_TGT.
  assert (REL:
   View.opt_le
     (TView.write_released (Local.tview lc1_src) loc to releasedm_src ord_src)
     (TView.write_released (Local.tview lc1_tgt) loc to releasedm_tgt ord_tgt)).
  { unfold TView.write_released.
    condtac; [|econs].
    condtac; try by (destruct ord_src, ord_tgt; ss).
    econs. unfold TView.write_tview. s.
    repeat (condtac; aggrtac); try by apply LC_WF1_TGT.
    + rewrite <- View.join_r. rewrite <- ? View.join_l. apply LOCAL1.
    + rewrite <- View.join_r. rewrite <- ? View.join_l.
      etrans; [|apply LOCAL1]. apply LC_WF1_SRC.
    + unguard. des; destruct ord_src, ord_tgt; ss.
  }
  assert (REL_WF:
   View.opt_wf (TView.write_released (Local.tview lc1_src) loc to releasedm_src ord_src)).
  { unfold TView.write_released. condtac; econs.
    repeat (try condtac; viewtac; try apply LC_WF1_SRC).
  }
  exploit sim_memory_add_exists; try exact WRITE; try apply GLOBAL1.
  { econs 1. exact REL_WF. }
  { econs; try exact REL; try refl.
    apply ord_implb. eassumption.
  }
  i. des.
  exploit sim_local_fulfill; try apply LOCAL1; eauto. i.
  esplits.
  - econs; eauto.
    eapply TViewFacts.writable_mon; try exact WRITABLE; eauto. apply LOCAL1.
  - ss.
  - inv LOCAL1. ss. econs; ss. inv TVIEW. econs; ss.
    + i. rewrite LocFun.add_spec. condtac; ss.
      * subst. unfold LocFun.find.
        condtac; apply View.join_le; viewtac.
        etrans; eauto. refl.
      * unfold LocFun.find. etrans; [apply LC_WF1_SRC|].
        eauto using View.join_l.
    + apply View.join_le; viewtac.
    + apply View.join_le; viewtac.
  - econs; ss. apply GLOBAL1.
Qed.

Lemma sim_local_update_relfenced
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      lc2_tgt
      lc3_tgt gl3_tgt
      loc ts1 val1 released1_tgt ord1_src ord1_tgt
      from2 to2 val2 released2_tgt ord2_src ord2_tgt
      (STEP1_TGT: Local.read_step lc1_tgt gl1_tgt loc ts1 val1 released1_tgt ord1_tgt lc2_tgt)
      (STEP2_TGT: Local.write_step lc2_tgt gl1_tgt loc from2 to2 val2 released1_tgt released2_tgt ord2_tgt lc3_tgt gl3_tgt)
      (LOCAL1: sim_local lc1_src (local_relfenced lc1_tgt))
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (LC_WF1_SRC: Local.wf lc1_src gl1_src)
      (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF1_SRC: Global.wf gl1_src)
      (GL_WF1_TGT: Global.wf gl1_tgt)
      (ORD1: Ordering.le ord1_src ord1_tgt)
      (ORD2: Ordering.le ord2_src ord2_tgt)
      (ORD2_TGT: Ordering.le ord2_tgt Ordering.plain \/ Ordering.le Ordering.acqrel ord2_tgt):
  exists released1_src released2_src lc2_src lc3_src gl3_src,
    <<REL1: View.opt_le released1_src released1_tgt>> /\
    <<REL2: View.opt_le released2_src released2_tgt>> /\
    <<STEP1_SRC: Local.read_step lc1_src gl1_src loc ts1 val1 released1_src ord1_src lc2_src>> /\
    <<STEP2_SRC: Local.write_step lc2_src gl1_src loc from2 to2 val2 released1_src released2_src ord2_src lc3_src gl3_src>> /\
    <<LOCAL3: sim_local lc3_src (local_relfenced lc3_tgt)>> /\
    <<GLOBAL3: sim_global gl3_src gl3_tgt>>.
Proof.
  guardH ORD2_TGT.
  exploit Local.read_step_future; eauto. i. des.
  exploit sim_local_read_relfenced; eauto. i. des.
  exploit Local.read_step_future; eauto. i. des.
  hexploit sim_local_write_relfenced; eauto. i. des.
  esplits; eauto.
Qed.

Lemma sim_local_fence_relfenced
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      lc2_tgt gl2_tgt
      ordr_src ordw_src
      ordr_tgt ordw_tgt
      (STEP_TGT: Local.fence_step lc1_tgt gl1_tgt ordr_tgt ordw_tgt lc2_tgt gl2_tgt)
      (LOCAL1: sim_local lc1_src (local_relfenced lc1_tgt))
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (LC_WF1_SRC: Local.wf lc1_src gl1_src)
      (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (ORDR: Ordering.le ordr_src ordr_tgt)
      (ORDW: Ordering.le ordw_src ordw_tgt)
      (ORDR_TGT: Ordering.le ordr_tgt Ordering.acqrel)
      (ORDW_TGT: Ordering.le ordw_tgt Ordering.relaxed):
  exists lc2_src gl2_src,
    <<STEP_SRC: Local.fence_step lc1_src gl1_src ordr_src ordw_src lc2_src gl2_src>> /\
    <<LOCAL2: sim_local lc2_src (local_relfenced lc2_tgt)>> /\
    <<GLOBAL2: sim_global gl2_src gl2_tgt>>.
Proof.
  inv STEP_TGT. esplits.
  - econs; eauto.
    i. inv LOCAL1. ss. rewrite PROMISES0.
    apply PROMISES. destruct ordw_src, ordw_tgt; ss.
  - inv LOCAL1. inv TVIEW. econs; ss.
    econs; s; unfold LocFun.find; repeat condtac; aggrtac.
    + etrans; eauto. apply LC_WF1_TGT.
    + etrans; eauto. apply LC_WF1_TGT.
    + etrans; eauto. apply LC_WF1_TGT.
  - inv GLOBAL1. econs; ss.
    unfold TView.write_fence_sc.
    repeat (condtac; viewtac).
Qed.

Lemma sim_local_is_racy_relfenced
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      loc to ord_src ord_tgt
      (STEP_TGT: Local.is_racy lc1_tgt gl1_tgt loc to ord_tgt)
      (LOCAL1: sim_local lc1_src (local_relfenced lc1_tgt))
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (ORD: Ordering.le ord_src ord_tgt):
  <<STEP_SRC: Local.is_racy lc1_src gl1_src loc to ord_src>>.
Proof.
  inv LOCAL1. inv GLOBAL1. inv STEP_TGT; ss.
  - econs; congr.
  - exploit sim_memory_get; try exact GET; try eassumption. i. des. inv MSG0.
    econs; try exact GET0.
    + eapply TViewFacts.racy_view_mon; eauto. apply TVIEW.
    + i. destruct na, na1; ss.
      exploit MSG; ss. destruct ord_src, ord_tgt; ss.
Qed.

Lemma sim_local_racy_read_relfenced
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      loc to val ord_src ord_tgt
      (STEP_TGT: Local.racy_read_step lc1_tgt gl1_tgt loc to val ord_tgt)
      (LOCAL1: sim_local lc1_src (local_relfenced lc1_tgt))
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (ORD: Ordering.le ord_src ord_tgt):
  <<STEP_SRC: Local.racy_read_step lc1_src gl1_src loc to val ord_src>>.
Proof.
  inv STEP_TGT.
  exploit sim_local_is_racy_relfenced; eauto.
Qed.

Lemma sim_local_racy_write_relfenced
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      loc to ord_src ord_tgt
      (STEP_TGT: Local.racy_write_step lc1_tgt gl1_tgt loc to ord_tgt)
      (LOCAL1: sim_local lc1_src (local_relfenced lc1_tgt))
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (ORD: Ordering.le ord_src ord_tgt):
  <<STEP_SRC: Local.racy_write_step lc1_src gl1_src loc to ord_src>>.
Proof.
  inv STEP_TGT.
  exploit sim_local_is_racy_relfenced; eauto.
Qed.

Lemma sim_local_racy_update_relfenced
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      loc to ordr_src ordw_src ordr_tgt ordw_tgt
      (STEP_TGT: Local.racy_update_step lc1_tgt gl1_tgt loc to ordr_tgt ordw_tgt)
      (LOCAL1: sim_local lc1_src (local_relfenced lc1_tgt))
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (ORDR: Ordering.le ordr_src ordr_tgt)
      (ORDW: Ordering.le ordw_src ordw_tgt):
  <<STEP_SRC: Local.racy_update_step lc1_src gl1_src loc to ordr_src ordw_src>>.
Proof.
  inv STEP_TGT; eauto.
  exploit sim_local_is_racy_relfenced; eauto.
Qed.

Lemma sim_local_fence_src_relfenced
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      (LOCAL1: sim_local lc1_src (local_relfenced lc1_tgt))
      (GLOBAL1: sim_global gl1_src gl1_tgt):
  exists lc2_src gl2_src,
    <<STEP_SRC: Local.fence_step lc1_src gl1_src Ordering.plain Ordering.acqrel lc2_src gl2_src>> /\
    <<LOCAL2: sim_local lc2_src (local_relfenced lc1_tgt)>> /\
    <<GLOBAL2: sim_global gl2_src gl1_tgt>>.
Proof.
  inv LOCAL1. inv TVIEW. ss.
  esplits.
  - econs; eauto. i. ss.
  - econs; eauto. econs; ss; eauto.
    repeat (condtac; aggrtac).
  - inv GLOBAL1. ss.
Qed.

Lemma sim_local_fence_tgt_relfenced
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      lc2_tgt gl2_tgt
      (STEP_TGT: Local.fence_step lc1_tgt gl1_tgt Ordering.plain Ordering.acqrel lc2_tgt gl2_tgt)
      (LOCAL1: sim_local lc1_src (local_relfenced lc1_tgt))
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (LC_WF1_SRC: Local.wf lc1_src gl1_src)
      (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt):
  <<LOCAL2: sim_local lc1_src lc2_tgt>> /\
  <<GLOBAL2: sim_global gl1_src gl2_tgt>>.
Proof.
  inv LOCAL1. inv TVIEW. inv STEP_TGT. splits.
  - econs; ss.
    unfold TView.read_fence_tview. condtac; ss.
    unfold TView.write_fence_tview. econs; repeat (condtac; aggrtac).
  - inv GLOBAL1. ss.
Qed.


(** acquired *)

Definition local_acquired (lc:Local.t) :=
  (Local.mk
     (TView.read_fence_tview (Local.tview lc) Ordering.acqrel)
     (Local.promises lc)
     (Local.reserves lc)).

Lemma local_acquired_wf
      lc gl
      (WF: Local.wf lc gl):
  Local.wf (local_acquired lc) gl.
Proof.
  inv WF. econs; ss.
  - inv TVIEW_WF. econs; ss.
    + condtac; ss. etrans; eauto.
    + condtac; ss. refl.
  - inv TVIEW_CLOSED. econs; ss.
Qed.

Lemma sim_local_internal_acquired
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      e lc2_tgt gl2_tgt
      (STEP_TGT: Local.internal_step e lc1_tgt gl1_tgt lc2_tgt gl2_tgt)
      (LOCAL1: sim_local lc1_src (local_acquired lc1_tgt))
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (LC_WF1_SRC: Local.wf lc1_src gl1_src)
      (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF1_SRC: Global.wf gl1_src)
      (GL_WF1_TGT: Global.wf gl1_tgt):
  exists lc2_src gl2_src,
    <<STEP_SRC: Local.internal_step e lc1_src gl1_src lc2_src gl2_src>> /\
    <<LOCAL2: sim_local lc2_src (local_acquired lc2_tgt)>> /\
    <<GLOBAL2: sim_global gl2_src gl2_tgt>>.
Proof.
  exploit local_acquired_wf; try exact LC_WF1_TGT. i.
  exploit sim_local_internal; try exact LOCAL1; eauto.
  unfold local_acquired. destruct lc1_tgt.
  inv STEP_TGT; inv LOCAL; ss; eauto.
Qed.

Lemma sim_local_read_acquired
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      lc2_tgt
      loc ts val released_tgt
      (STEP_TGT: Local.read_step lc1_tgt gl1_tgt loc ts val released_tgt Ordering.relaxed lc2_tgt)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (LC_WF1_SRC: Local.wf lc1_src gl1_src)
      (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF1_SRC: Global.wf gl1_src)
      (GL_WF1_TGT: Global.wf gl1_tgt):
  exists released_src lc2_src,
    <<REL: View.opt_le released_src released_tgt>> /\
    <<STEP_SRC: Local.read_step lc1_src gl1_src loc ts val released_src Ordering.acqrel lc2_src>> /\
    <<LOCAL2: sim_local lc2_src (local_acquired lc2_tgt)>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit sim_memory_get; try apply GET; try apply GLOBAL1. i. des. inv MSG.
  esplits; eauto.
  - econs; eauto; try by (etrans; eauto). inv READABLE. econs; ss; i.
    + rewrite <- PLN. apply TVIEW.
    + rewrite <- RLX; ss. apply TVIEW.
  - econs; eauto. s.
    unfold TView.read_tview, TView.read_fence_tview. ss.
    econs; repeat (condtac; aggrtac).
    all: try by apply TVIEW.
    all: try by apply LC_WF1_TGT.
    + rewrite <- ? View.join_l. etrans; [apply TVIEW|]. apply LC_WF1_TGT.
    + inv GL_WF1_TGT. inv MEM_CLOSED.
      exploit CLOSED; eauto. i. des.
      apply View.unwrap_opt_wf. inv MSG_WF. ss.
    + rewrite <- ? View.join_l. apply TVIEW.
    + inv GL_WF1_TGT. inv MEM_CLOSED.
      exploit CLOSED; eauto. i. des.
      apply View.unwrap_opt_wf. inv MSG_WF. ss.
Qed.

Lemma sim_local_write_acquired
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      lc2_tgt gl2_tgt
      loc from to val releasedm_src releasedm_tgt released_tgt ord_src ord_tgt
      (RELM_LE: View.opt_le releasedm_src releasedm_tgt)
      (RELM_WF_SRC: View.opt_wf releasedm_src)
      (RELM_CLOSED_SRC: Memory.closed_opt_view releasedm_src (Global.memory gl1_src))
      (RELM_WF_TGT: View.opt_wf releasedm_tgt)
      (RELM_TO_TGT: Time.le (View.rlx (View.unwrap releasedm_tgt) loc) from)
      (ORD: Ordering.le ord_src ord_tgt)
      (ORD_TGT: Ordering.le ord_tgt Ordering.strong_relaxed)
      (STEP_TGT: Local.write_step lc1_tgt gl1_tgt loc from to val releasedm_tgt released_tgt ord_tgt lc2_tgt gl2_tgt)
      (LOCAL1: sim_local lc1_src (local_acquired lc1_tgt))
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (LC_WF1_SRC: Local.wf lc1_src gl1_src)
      (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF1_SRC: Global.wf gl1_src)
      (GL_WF1_TGT: Global.wf gl1_tgt)
      (ACQUIRED1: View.le (TView.cur (Local.tview lc1_src))
                          (View.join (TView.cur (Local.tview lc1_tgt)) (View.unwrap releasedm_tgt))):
  exists released_src lc2_src gl2_src,
    <<STEP_SRC: Local.write_step lc1_src gl1_src loc from to val releasedm_src released_src ord_src lc2_src gl2_src>> /\
    <<REL: View.opt_le released_src released_tgt>> /\
    <<LOCAL2: sim_local lc2_src (local_acquired lc2_tgt)>> /\
    <<GLOBAL2: sim_global gl2_src gl2_tgt>>.
Proof.
  inv STEP_TGT.
  assert (REL:
   View.opt_le
     (TView.write_released (Local.tview lc1_src) loc to releasedm_src ord_src)
     (TView.write_released (Local.tview lc1_tgt) loc to releasedm_tgt ord_tgt)).
  { unfold TView.write_released, TView.write_tview. ss. viewtac.
    repeat (condtac; aggrtac;
            try match goal with
                | [|- View.opt_le _ _] => econs
                end);
      try apply LC_WF1_TGT.
    - etrans; eauto. aggrtac.
    - etrans; [apply LC_WF1_SRC|]. etrans; eauto. aggrtac.
    - etrans; [apply LOCAL1|]. aggrtac.
  }
  assert (REL_WF:
   View.opt_wf (TView.write_released (Local.tview lc1_src) loc to releasedm_src ord_src)).
  { unfold TView.write_released. condtac; econs.
    repeat (try condtac; viewtac; try apply LC_WF1_SRC).
  }
  exploit sim_memory_add_exists; try exact WRITE; try apply GLOBAL1.
  { econs 1. exact REL_WF. }
  { econs; try exact REL; try refl.
    apply ord_implb. eassumption.
  }
  i. des.
  exploit sim_local_fulfill; try apply LOCAL1; try exact ORD; eauto. i.
  esplits.
  - econs; eauto.
    inv WRITABLE. econs.
    eapply TimeFacts.le_lt_lt; [apply ACQUIRED1|]. viewtac.
    eapply TimeFacts.le_lt_lt; eauto.
    exploit Memory.add_ts; eauto.
  - ss.
  - inv LOCAL1. ss. econs; ss.
    unfold TView.write_tview, TView.read_fence_tview. ss.
    econs; ss; repeat (try condtac; aggrtac).
    all: try by destruct ord_src, ord_tgt.
    all: try by apply LC_WF1_TGT.
    + etrans; [apply TVIEW|]. aggrtac.
    + etrans; [apply TVIEW|]. aggrtac.
    + etrans; [apply LC_WF1_SRC|].
      etrans; [apply TVIEW|]. aggrtac.
    + etrans; [apply TVIEW|]. aggrtac.
  - econs; ss. apply GLOBAL1.
Qed.

Lemma sim_local_update_acquired
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      lc2_tgt
      lc3_tgt gl3_tgt
      loc ts1 val1 released1_tgt
      to2 val2 released2_tgt ord2_src ord2_tgt
      (STEP1_TGT: Local.read_step lc1_tgt gl1_tgt loc ts1 val1 released1_tgt Ordering.relaxed lc2_tgt)
      (STEP2_TGT: Local.write_step lc2_tgt gl1_tgt loc ts1 to2 val2 released1_tgt released2_tgt ord2_tgt lc3_tgt gl3_tgt)
      (ORD2: Ordering.le ord2_src ord2_tgt)
      (ORD2_TGT: Ordering.le ord2_tgt Ordering.strong_relaxed)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (LC_WF1_SRC: Local.wf lc1_src gl1_src)
      (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF1_SRC: Global.wf gl1_src)
      (GL_WF1_TGT: Global.wf gl1_tgt):
  exists released1_src released2_src lc2_src lc3_src gl3_src,
    <<REL1: View.opt_le released1_src released1_tgt>> /\
    <<REL2: View.opt_le released2_src released2_tgt>> /\
    <<STEP1_SRC: Local.read_step lc1_src gl1_src loc ts1 val1 released1_src Ordering.acqrel lc2_src>> /\
    <<STEP2_SRC: Local.write_step lc2_src gl1_src loc ts1 to2 val2 released1_src released2_src ord2_src lc3_src gl3_src>> /\
    <<LOCAL3: sim_local lc3_src (local_acquired lc3_tgt)>> /\
    <<GLOBAL3: sim_global gl3_src gl3_tgt>>.
Proof.
  exploit sim_local_read_acquired; eauto. i. des.
  exploit Local.read_step_future; try exact STEP1_TGT; eauto. i. des.
  exploit Local.read_step_future; try exact STEP_SRC; eauto. i. des.
  exploit sim_local_write_acquired; try exact STEP2_TGT; try exact LOCAL2; eauto.
  { inv STEP1_TGT. inv STEP_SRC. ss.
    do 2 (condtac; ss).
    rewrite View.join_bot_r.
    repeat apply View.join_le; try apply LOCAL1; try refl.
    inv REL; ss. apply View.bot_spec.
  }
  i. des.
  esplits; try exact STEP_SRC; try exact STEP_SRC0; eauto.
Qed.

Lemma sim_local_is_racy_acquired
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      loc to
      (STEP_TGT: Local.is_racy lc1_tgt gl1_tgt loc to Ordering.relaxed)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GLOBAL1: sim_global gl1_src gl1_tgt):
  <<STEP_SRC: Local.is_racy lc1_src gl1_src loc to Ordering.acqrel>>.
Proof.
  exploit sim_local_is_racy; try exact STEP_TGT;
    try exact LOCAL1; try exact GLOBAL1; try refl; eauto. i. des.
  inv x0; eauto.
Qed.

Lemma sim_local_racy_read_acquired
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      loc to val
      (STEP_TGT: Local.racy_read_step lc1_tgt gl1_tgt loc to val Ordering.relaxed)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GLOBAL1: sim_global gl1_src gl1_tgt):
  <<STEP_SRC: Local.racy_read_step lc1_src gl1_src loc to val Ordering.acqrel>>.
Proof.
  inv STEP_TGT.
  exploit sim_local_is_racy_acquired; eauto.
Qed.

Lemma sim_local_racy_update_acquired
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      loc to ow
      (STEP_TGT: Local.racy_update_step lc1_tgt gl1_tgt loc to Ordering.relaxed ow)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GLOBAL1: sim_global gl1_src gl1_tgt):
  <<STEP_SRC: Local.racy_update_step lc1_src gl1_src loc to Ordering.acqrel ow>>.
Proof.
  inv STEP_TGT; eauto.
  exploit sim_local_is_racy_acquired; eauto.
Qed.


(* released *)

Lemma sim_local_fulfill_released
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      loc prm2 gprm2
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (FULFILL_TGT: Promises.fulfill lc1_tgt.(Local.promises) gl1_tgt.(Global.promises) loc Ordering.strong_relaxed prm2 gprm2):
  Promises.fulfill lc1_src.(Local.promises) gl1_src.(Global.promises) loc Ordering.acqrel prm2 gprm2.
Proof.
  destruct lc1_src, lc1_tgt, gl1_src, gl1_tgt.
  inv LOCAL1. inv GLOBAL1. ss. subst.
  inv FULFILL_TGT; eauto.
Qed.

Lemma sim_local_write_released
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      lc2_tgt gl2_tgt
      loc from to val releasedm_src releasedm_tgt released_tgt
      (RELM_LE: View.opt_le releasedm_src releasedm_tgt)
      (RELM_WF_SRC: View.opt_wf releasedm_src)
      (RELM_CLOSED_SRC: Memory.closed_opt_view releasedm_src (Global.memory gl1_src))
      (RELM_WF_TGT: View.opt_wf releasedm_tgt)
      (STEP_TGT: Local.write_step lc1_tgt gl1_tgt loc from to val releasedm_tgt released_tgt Ordering.strong_relaxed lc2_tgt gl2_tgt)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (LC_WF1_SRC: Local.wf lc1_src gl1_src)
      (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF1_SRC: Global.wf gl1_src)
      (GL_WF1_TGT: Global.wf gl1_tgt)
      (RELEASED1: View.le (TView.cur (Local.tview lc1_tgt))
                          (View.join ((TView.rel (Local.tview lc1_tgt)) loc) (View.singleton_ur loc to))):
  exists released_src lc2_src gl2_src,
    <<STEP_SRC: Local.write_step lc1_src gl1_src loc from to val releasedm_src released_src Ordering.acqrel lc2_src gl2_src>> /\
    <<REL: View.opt_le released_src released_tgt>> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
    <<GLOBAL2: sim_global gl2_src gl2_tgt>>.
Proof.
  inv STEP_TGT.
  assert (REL:
   View.opt_le
     (TView.write_released (Local.tview lc1_src) loc to releasedm_src Ordering.acqrel)
     (TView.write_released (Local.tview lc1_tgt) loc to releasedm_tgt Ordering.strong_relaxed)).
  { unfold TView.write_released, TView.write_tview. ss. viewtac;
      try econs; repeat (condtac; aggrtac); try apply LC_WF1_TGT.
    rewrite <- View.join_r. etrans; eauto. apply LOCAL1.
  }
  assert (REL_WF:
   View.opt_wf (TView.write_released (Local.tview lc1_src) loc to releasedm_src Ordering.acqrel)).
  { unfold TView.write_released. condtac; econs.
    repeat (try condtac; viewtac; try apply LC_WF1_SRC).
  }
  exploit sim_memory_add_exists; try exact WRITE; try apply GLOBAL1.
  { econs 1. exact REL_WF. }
  { econs; try exact REL; [refl|].
    instantiate (1:=Ordering.le Ordering.acqrel Ordering.na).
    refl.
  }
  i. des.
  exploit sim_local_fulfill_released; try apply LOCAL1; eauto. i.
  esplits.
  - econs; eauto.
    inv WRITABLE. econs; ss. eapply TimeFacts.le_lt_lt; [apply LOCAL1|apply TS].
  - ss.
  - inv LOCAL1. econs; eauto. ss.
    unfold TView.write_tview, View.singleton_ur_if. repeat (condtac; aggrtac).
    econs; repeat (condtac; aggrtac);
      (try by etrans; [apply LOCAL1|aggrtac]);
      (try by rewrite <- ? View.join_r; econs; aggrtac);
      (try apply LC_WF1_TGT).
    + ss. i. unfold LocFun.find. repeat (condtac; aggrtac).
      * etrans; eauto. apply TVIEW.
      * apply TVIEW.
    + ss. aggrtac; try apply LC_WF1_TGT.
      rewrite <- ? View.join_l. apply TVIEW.
    + ss. aggrtac; try apply LC_WF1_TGT.
      rewrite <- ? View.join_l. apply TVIEW.
  - inv GLOBAL1. econs; ss.
Qed.

Lemma sim_local_update_released
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      lc2_tgt
      lc3_tgt gl3_tgt
      loc ts1 val1 released1_tgt ord1_src ord1_tgt
      to2 val2 released2_tgt
      (STEP1_TGT: Local.read_step lc1_tgt gl1_tgt loc ts1 val1 released1_tgt ord1_tgt lc2_tgt)
      (STEP2_TGT: Local.write_step lc2_tgt gl1_tgt loc ts1 to2 val2 released1_tgt released2_tgt Ordering.strong_relaxed lc3_tgt gl3_tgt)
      (ORD1: Ordering.le ord1_src ord1_tgt)
      (ORD1_TGT: Ordering.le ord1_tgt Ordering.strong_relaxed)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (LC_WF1_SRC: Local.wf lc1_src gl1_src)
      (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF1_SRC: Global.wf gl1_src)
      (GL_WF1_TGT: Global.wf gl1_tgt)
      (RELEASED1: View.le (TView.cur (Local.tview lc1_tgt)) ((TView.rel (Local.tview lc1_tgt)) loc)):
  exists released1_src released2_src lc2_src lc3_src gl3_src,
    <<STEP1_SRC: Local.read_step lc1_src gl1_src loc ts1 val1 released1_src ord1_src lc2_src>> /\
    <<STEP2_SRC: Local.write_step lc2_src gl1_src loc ts1 to2 val2 released1_src released2_src Ordering.acqrel lc3_src gl3_src>> /\
    <<REL1: View.opt_le released1_src released1_tgt>> /\
    <<REL2: View.opt_le released2_src released2_tgt>> /\
    <<LOCAL3: sim_local lc3_src lc3_tgt>> /\
    <<GLOBAL3: sim_global gl3_src gl3_tgt>>.
Proof.
  exploit sim_local_read; try exact STEP1_TGT; eauto. i. des.
  exploit Local.read_step_future; try exact STEP1_TGT; eauto. i. des.
  exploit Local.read_step_future; try exact STEP_SRC; eauto. i. des.
  exploit sim_local_write_released; try exact STEP2_TGT; eauto.
  { inv STEP1_TGT. ss.
    condtac; try by (destruct ord1_tgt; ss).
    rewrite View.join_bot_r.
    apply View.join_le; ss.
    inv STEP2_TGT. exploit Memory.add_ts; eauto. i.
    aggrtac. condtac; aggrtac.
  }
  i. des.
  esplits; eauto.
Qed.

Lemma sim_local_is_racy_released
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      loc to
      (STEP_TGT: Local.is_racy lc1_tgt gl1_tgt loc to Ordering.strong_relaxed)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (LC_WF1_SRC: Local.wf lc1_src gl1_src)
      (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF1_SRC: Global.wf gl1_src)
      (GL_WF1_TGT: Global.wf gl1_tgt):
  <<STEP_SRC: Local.is_racy lc1_src gl1_src loc to Ordering.acqrel>>.
Proof.
  exploit sim_local_is_racy;
    try exact LOCAL1; try exact GLOBAL1; try refl; eauto. i. des.
  inv x0; eauto.
Qed.

Lemma sim_local_racy_write_released
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      loc to
      (STEP_TGT: Local.racy_write_step lc1_tgt gl1_tgt loc to Ordering.strong_relaxed)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (LC_WF1_SRC: Local.wf lc1_src gl1_src)
      (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF1_SRC: Global.wf gl1_src)
      (GL_WF1_TGT: Global.wf gl1_tgt):
  <<STEP_SRC: Local.racy_write_step lc1_src gl1_src loc to Ordering.acqrel>>.
Proof.
  inv STEP_TGT.
  exploit sim_local_is_racy_released; eauto.
Qed.

Lemma sim_local_racy_update_released
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      loc to ordr
      (STEP_TGT: Local.racy_update_step lc1_tgt gl1_tgt loc to ordr Ordering.strong_relaxed)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (LC_WF1_SRC: Local.wf lc1_src gl1_src)
      (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF1_SRC: Global.wf gl1_src)
      (GL_WF1_TGT: Global.wf gl1_tgt):
  <<STEP_SRC: Local.racy_update_step lc1_src gl1_src loc to ordr Ordering.acqrel>>.
Proof.
  exploit sim_local_racy_update;
    try exact LOCAL1; try exact GLOBAL1; try refl; eauto. i. des.
  inv x0.
  - econs 1; eauto.
  - econs 2; eauto.
  - econs 3; eauto.
Qed.


(** acqrel *)

Definition local_acqrel (lc:Local.t) :=
  (Local.mk (TView.write_fence_tview
               (TView.read_fence_tview (Local.tview lc) Ordering.acqrel)
               TimeMap.bot
               Ordering.acqrel)
            (Local.promises lc)
            (Local.reserves lc)).

Lemma local_acqrel_wf
      lc gl
      (WF: Local.wf lc gl):
  Local.wf (local_acqrel lc) gl.
Proof.
  inv WF. econs; ss.
  - inv TVIEW_WF. econs; ss; repeat (condtac; ss).
    + rewrite View.join_bot_r. apply ACQ.
    + refl.
    + rewrite View.join_bot_r. refl.
  - inv TVIEW_CLOSED.
    econs; ss. condtac; ss.
    rewrite View.join_bot_r. apply ACQ.
Qed.

Lemma sim_local_internal_acqrel
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      e lc2_tgt gl2_tgt
      (STEP_TGT: Local.internal_step e lc1_tgt gl1_tgt lc2_tgt gl2_tgt)
      (LOCAL1: sim_local lc1_src (local_acqrel lc1_tgt))
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (LC_WF1_SRC: Local.wf lc1_src gl1_src)
      (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF1_SRC: Global.wf gl1_src)
      (GL_WF1_TGT: Global.wf gl1_tgt):
  exists lc2_src gl2_src,
    <<STEP_SRC: Local.internal_step e lc1_src gl1_src lc2_src gl2_src>> /\
    <<LOCAL2: sim_local lc2_src (local_acqrel lc2_tgt)>> /\
    <<GLOBAL2: sim_global gl2_src gl2_tgt>>.
Proof.
  exploit local_acqrel_wf; try exact LC_WF1_TGT. i.
  exploit sim_local_internal; try exact LOCAL1; eauto.
  destruct lc1_tgt.
  inv STEP_TGT; inv LOCAL; ss; eauto.
Qed.

Lemma sim_local_write_acqrel
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      lc2_tgt gl2_tgt
      loc from to val releasedm_src releasedm_tgt released_tgt ord_src ord_tgt
      (RELM_LE: View.opt_le releasedm_src releasedm_tgt)
      (RELM_WF_SRC: View.opt_wf releasedm_src)
      (RELM_CLOSED_SRC: Memory.closed_opt_view releasedm_src (Global.memory gl1_src))
      (RELM_WF_TGT: View.opt_wf releasedm_tgt)
      (RELM_TGT: Time.le (View.rlx (View.unwrap releasedm_tgt) loc) from)
      (ORD: Ordering.le ord_src ord_tgt)
      (ORD_TGT: Ordering.le ord_tgt Ordering.acqrel)
      (STEP_TGT: Local.write_step lc1_tgt gl1_tgt loc from to val releasedm_tgt released_tgt ord_tgt lc2_tgt gl2_tgt)
      (LOCAL1: sim_local lc1_src (local_acquired lc1_tgt))
      (ACQUIRED1: View.le (TView.cur (Local.tview lc1_src))
                          (View.join (TView.cur (Local.tview lc1_tgt)) (View.unwrap releasedm_tgt)))
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (LC_WF1_SRC: Local.wf lc1_src gl1_src)
      (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF1_SRC: Global.wf gl1_src)
      (GL_WF1_TGT: Global.wf gl1_tgt):
  exists released_src lc2_src gl2_src,
    <<STEP_SRC: Local.write_step lc1_src gl1_src loc from to val releasedm_src released_src ord_src lc2_src gl2_src>> /\
    <<REL: View.opt_le released_src released_tgt>> /\
    <<LOCAL2: sim_local lc2_src (local_acqrel lc2_tgt)>> /\
    <<GLOBAL2: sim_global gl2_src gl2_tgt>>.
Proof.
  inv STEP_TGT.
  assert (REL:
   View.opt_le
     (TView.write_released (Local.tview lc1_src) loc to releasedm_src ord_src)
     (TView.write_released (Local.tview lc1_tgt) loc to releasedm_tgt ord_tgt)).
  { unfold TView.write_released, TView.write_tview. ss. viewtac.
    repeat (condtac; aggrtac;
            try match goal with
                | [|- View.opt_le _ _] => econs
                end);
      try apply LC_WF1_TGT.
    - etrans; eauto. aggrtac.
    - etrans; [apply LC_WF1_SRC|]. etrans; eauto. aggrtac.
    - etrans; [apply LOCAL1|]. aggrtac.
  }
  assert (REL_WF:
   View.opt_wf (TView.write_released (Local.tview lc1_src) loc to releasedm_src ord_src)).
  { unfold TView.write_released. condtac; econs.
    repeat (try condtac; viewtac; try apply LC_WF1_SRC).
  }
  exploit sim_memory_add_exists; try exact WRITE; try apply GLOBAL1.
  { econs 1. exact REL_WF. }
  { econs; try exact REL; try refl.
    apply ord_implb. eassumption.
  }
  i. des.
  exploit sim_local_fulfill; try apply LOCAL1; try exact ORD; eauto. i.
  exploit Memory.add_ts; eauto. i.
  esplits.
  - econs; eauto.
    inv WRITABLE. econs.
    eapply TimeFacts.le_lt_lt; [apply ACQUIRED1|]. viewtac.
    eapply TimeFacts.le_lt_lt; eauto.
  - ss.
  - inv LOCAL1. ss. econs; ss.
    unfold TView.write_tview, TView.write_fence_tview, TView.read_fence_tview. ss.
    econs; ss; repeat (condtac; aggrtac).
    all: try by destruct ord_src, ord_tgt.
    all: try by apply LC_WF1_TGT.
    + etrans; [apply TVIEW|]. repeat (try condtac; aggrtac).
    + etrans; [apply TVIEW|]. aggrtac.
      etrans; [apply LC_WF1_TGT|].
      etrans; [apply LC_WF1_TGT|]. aggrtac.
    + etrans; [apply TVIEW|]. aggrtac.
      etrans; [apply LC_WF1_TGT|].
      etrans; [apply LC_WF1_TGT|]. aggrtac.
    + etrans; [apply TVIEW|]. repeat (try condtac; aggrtac).
      etrans; [apply LC_WF1_TGT|].
      etrans; [apply LC_WF1_TGT|]. aggrtac.
    + etrans; [apply TVIEW|]. ss. condtac; aggrtac.
    + etrans; [apply TVIEW|]. aggrtac.
  - inv GLOBAL1. ss.
Qed.

Lemma sim_local_update_acqrel
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      lc2_tgt
      lc3_tgt gl3_tgt
      loc ts1 val1 released1_tgt
      to2 val2 released2_tgt ord2_src ord2_tgt
      (STEP1_TGT: Local.read_step lc1_tgt gl1_tgt loc ts1 val1 released1_tgt Ordering.relaxed lc2_tgt)
      (STEP2_TGT: Local.write_step lc2_tgt gl1_tgt loc ts1 to2 val2 released1_tgt released2_tgt ord2_tgt lc3_tgt gl3_tgt)
      (ORD2: Ordering.le ord2_src ord2_tgt)
      (ORD2_TGT: Ordering.le ord2_tgt Ordering.acqrel)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (LC_WF1_SRC: Local.wf lc1_src gl1_src)
      (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF1_SRC: Global.wf gl1_src)
      (GL_WF1_TGT: Global.wf gl1_tgt):
  exists released1_src released2_src lc2_src lc3_src gl3_src,
    <<REL1: View.opt_le released1_src released1_tgt>> /\
    <<REL2: View.opt_le released2_src released2_tgt>> /\
    <<STEP1_SRC: Local.read_step lc1_src gl1_src loc ts1 val1 released1_src Ordering.acqrel lc2_src>> /\
    <<STEP2_SRC: Local.write_step lc2_src gl1_src loc ts1 to2 val2 released1_src released2_src ord2_src lc3_src gl3_src>> /\
    <<LOCAL3: sim_local lc3_src (local_acqrel lc3_tgt)>> /\
    <<GLOBAL3: sim_global gl3_src gl3_tgt>>.
Proof.
  exploit sim_local_read_acquired; eauto. i. des.
  exploit Local.read_step_future; try exact STEP1_TGT; eauto. i. des.
  exploit Local.read_step_future; try exact STEP_SRC; eauto. i. des.
  exploit sim_local_write_acqrel; try exact STEP2_TGT; try exact LOCAL2; eauto.
  { inv STEP1_TGT. inv STEP_SRC. ss.
    do 2 (condtac; ss).
    rewrite View.join_bot_r.
    repeat apply View.join_le; try apply LOCAL1; try refl.
    inv REL; ss. apply View.bot_spec.
  }
  i. des.
  esplits; try exact STEP_SRC; try exact STEP_SRC0; eauto.
Qed.
