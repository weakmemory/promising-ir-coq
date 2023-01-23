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
