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

Require Import SimLocal.
Require Import SimMemory.
Require Import SimGlobal.

Set Implicit Arguments.


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
