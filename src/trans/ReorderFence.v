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

Require Import Progress.
Require Import ReorderInternal.

Require Import SimLocal.
Require Import SimMemory.
Require Import SimGlobal.
Require Import SimThread.
Require Import Compatibility.

Require Import ReorderStep.

Require Import ITreeLang.
Require Import ITreeLib.

Set Implicit Arguments.


Variant reorder_fence (or1 ow1:Ordering.t): forall R (i2:MemE.t R), Prop :=
| reorder_fence_load
    l2 o2
    (ORDR1: Ordering.le or1 Ordering.acqrel)
    (ORDW1: Ordering.le ow1 Ordering.relaxed)
    (ORD2: Ordering.le o2 Ordering.plain \/ Ordering.le Ordering.acqrel o2):
    reorder_fence or1 ow1 (MemE.read l2 o2)
| reorder_fence_store
    l2 v2 o2
    (ORDR1: Ordering.le or1 Ordering.acqrel)
    (ORDW1: Ordering.le ow1 Ordering.relaxed)
    (ORD2: Ordering.le Ordering.plain o2):
    reorder_fence or1 ow1 (MemE.write l2 v2 o2)
| reorder_fence_update
    l2 rmw2 or2 ow2
    (ORDR1: Ordering.le or1 Ordering.acqrel)
    (ORDW1: Ordering.le ow1 Ordering.relaxed)
    (ORDR2: Ordering.le or2 Ordering.plain \/ Ordering.le Ordering.acqrel or2):
    reorder_fence or1 ow1 (MemE.update l2 rmw2 or2 ow2)
| reorder_fence_choose
    (ORDW1: Ordering.le ow1 Ordering.acqrel):
    reorder_fence or1 ow1 MemE.choose
.

Variant sim_fence: forall R
                            (st_src:itree MemE.t (unit * R)%type) (lc_src:Local.t) (gl1_src:Global.t)
                            (st_tgt:itree MemE.t (unit * R)%type) (lc_tgt:Local.t) (gl1_tgt:Global.t), Prop :=
| sim_fence_intro
    R
    or1 ow1 (i2: MemE.t R)
    lc1_src gl1_src
    lc1_tgt gl1_tgt
    lc2_src gl2_src
    (REORDER: reorder_fence or1 ow1 i2)
    (FENCE: Local.fence_step lc1_src gl1_src or1 ow1 lc2_src gl2_src)
    (LOCAL: sim_local lc2_src lc1_tgt)
    (GLOBAL: sim_global gl1_src gl1_tgt)
    (LC_WF_SRC: Local.wf lc1_src gl1_src)
    (LC_WF_TGT: Local.wf lc1_tgt gl1_tgt)
    (GL_WF_SRC: Global.wf gl1_src)
    (GL_WF_TGT: Global.wf gl1_tgt):
    sim_fence
      (Vis i2 (fun v2 => Vis (MemE.fence or1 ow1) (fun v1 => Ret (v1, v2)))) lc1_src gl1_src
      (Vis i2 (fun r => Ret (tt, r))) lc1_tgt gl1_tgt
.

Lemma read_fence_wf
      tview ord
      (WF: TView.wf tview):
  TView.wf (TView.read_fence_tview tview ord).
Proof.
  inv WF. econs; ss; condtac; eauto. refl.
Qed.

Lemma fence_step_non_sc
      lc1 gl1 or ow lc2 gl2
      (STEP: Local.fence_step lc1 gl1 or ow lc2 gl2)
      (SC: Ordering.le ow Ordering.acqrel):
  gl2 = gl1.
Proof.
  destruct gl1. inv STEP. ss. f_equal.
  apply TViewFacts.write_fence_sc_acqrel. ss.
Qed.

Lemma sim_fence_mon
      R
      st_src lc_src gl1_src
      st_tgt lc_tgt gl1_tgt
      gl2_src
      gl2_tgt
      (SIM1: sim_fence st_src lc_src gl1_src
                       st_tgt lc_tgt gl1_tgt)
      (GL_LE_SRC: Global.le gl1_src gl2_src)
      (GL_LE_TGT: Global.le gl1_tgt gl2_tgt)
      (GLOBAL1: sim_global gl2_src gl2_tgt)
      (LC_WF_SRC: Local.wf lc_src gl2_src)
      (LC_WF_TGT: Local.wf lc_tgt gl2_tgt)
      (GL_WF_SRC: Global.wf gl2_src)
      (GL_WF_TGT: Global.wf gl2_tgt):
  @sim_fence R
             st_src lc_src gl2_src
             st_tgt lc_tgt gl2_tgt.
Proof.
  dependent destruction SIM1.
  exploit future_fence_step; try exact FENCE; try apply GL_LE_SRC; eauto.
  { inv REORDER; destruct ow1; ss. }
  i. econs; eauto.
Qed.

Lemma sim_fence_sim_local
      R
      st_src lc_src gl_src
      st_tgt lc_tgt gl_tgt
      (SIM: @sim_fence R st_src lc_src gl_src st_tgt lc_tgt gl_tgt):
  sim_local lc_src lc_tgt.
Proof.
  inv SIM. inv FENCE. inv LOCAL. ss.
  econs; eauto. etrans; eauto.
  etrans; cycle 1.
  { eapply TViewFacts.write_fence_tview_incr.
    eapply read_fence_wf; eauto. apply LC_WF_SRC.
  }
  eapply TViewFacts.read_fence_tview_incr. apply LC_WF_SRC.
Qed.

Lemma sim_fence_step
      R
      st1_src lc1_src gl1_src
      st1_tgt lc1_tgt gl1_tgt
      (SIM: sim_fence st1_src lc1_src gl1_src
                      st1_tgt lc1_tgt gl1_tgt):
  _sim_thread_step (lang (unit * R)%type) (lang (unit * R)%type)
                   ((@sim_thread (lang (unit * R)%type) (lang (unit * R)%type) (sim_terminal eq)) \6/ @sim_fence R)
                     st1_src lc1_src gl1_src
                     st1_tgt lc1_tgt gl1_tgt.
Proof.
  exploit sim_fence_sim_local; eauto; try apply WF_SRC. intro SIM_LC.
  destruct SIM. ii.
  assert (OW: Ordering.le ow1 Ordering.acqrel)
    by (inv FENCE; inv REORDER; destruct ow1; ss).
  exploit Local.fence_step_future; eauto. i. des.
  exploit fence_step_non_sc; try exact FENCE; ss. i. subst.
  inv STEP_TGT; ss.
  { (* internal *)
    right.
    exploit Local.internal_step_future; eauto. i. des.
    exploit sim_local_internal; try exact LOCAL; eauto. i. des.
    exploit reorder_fence_internal; try exact FENCE; try exact STEP_SRC; eauto. i. des.
    exploit Local.internal_step_future; eauto. i. des.
    exploit fence_step_non_sc; try exact STEP2; eauto. i. subst.
    esplits; try apply GL2; eauto; ss.
    + inv LOCAL0; ss.
    + right. econs; eauto.
  }
  inv LOCAL0; ss; dependent destruction REORDER; dependent destruction STATE.
  - (* choose *)
    right.
    esplits.
    + ss.
    + econs 2; [|econs 1]. econs.
      * econs 2; [|econs 1]. econs. refl.
      * ss.
    + econs 2. econs 2; [|econs 5]; eauto. econs. refl.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
  - (* load *)
    right.
    guardH ORD2.
    exploit sim_local_read; try exact LOCAL1; try exact LOCAL; eauto; try refl. i. des.
    exploit reorder_fence_read; try exact FENCE; try exact STEP_SRC; eauto. i. des.
    esplits.
    + ss.
    + econs 2; [|econs 1]. econs.
      * econs 2; [|econs 2]; eauto. econs. refl.
      * ss.
    + econs 2. econs 2; [|econs 5]; eauto. econs. refl.
    + ss.
    + etrans; eauto.
    + left. eapply paco9_mon; [apply sim_itree_ret|]; ss. etrans; eauto.
  - (* update-load *)
    right.
    guardH ORDR2.
    exploit sim_local_read; try exact LOCAL1; try exact LOCAL; eauto; try refl. i. des.
    exploit reorder_fence_read; try exact FENCE; try exact STEP_SRC; eauto. i. des.
    esplits.
    + ss.
    + econs 2; [|econs 1]. econs.
      * econs 2; [|econs 2]; eauto. econs; eauto.
      * ss.
    + econs 2. econs 2; [|econs 5]; eauto. econs. refl.
    + ss.
    + etrans; eauto.
    + left. eapply paco9_mon; [apply sim_itree_ret|]; ss. etrans; eauto.
  - (* store *)
    right.
    hexploit sim_local_write; try exact LOCAL1; try exact LOCAL;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; eauto; try refl.
    i. des.
    exploit reorder_fence_write; try apply FENCE; try apply STEP_SRC; eauto. i. des.
    esplits.
    + ss.
    + econs 2; [|econs 1]. econs.
      * econs 2; [|econs 3]; eauto. econs. refl.
      * ss.
    + econs 2. econs 2; [|econs 5]; eauto. econs. refl.
    + ss.
    + etrans; eauto.
    + left. eapply paco9_mon; [apply sim_itree_ret|]; ss. etrans; eauto.
  - (* update *)
    right.
    guardH ORDR2.
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_read; try exact LOCAL1; try exact LOCAL; eauto; try refl. i. des.
    exploit reorder_fence_read; try apply FENCE; try apply STEP_SRC; eauto. i. des.
    exploit Local.read_step_future; eauto. i. des.
    exploit Local.fence_step_future; eauto. i. des.
    generalize LOCAL3. i. rewrite LOCAL0 in LOCAL3.
    generalize GLOBAL0. i. rewrite GLOBAL in GLOBAL0.
    hexploit sim_local_write; try exact LOCAL2; try exact GLOBAL1; eauto; try refl. i. des.
    exploit reorder_fence_write; try apply STEP2; try apply STEP_SRC0; eauto. i. des.
    esplits.
    + ss.
    + econs 2; [|econs 1]. econs.
      * econs 2; [|econs 4]; eauto. econs; eauto.
      * ss.
    + econs 2. econs 2; [|econs 5]; eauto. econs. refl.
    + ss.
    + etrans; eauto.
    + left. eapply paco9_mon; [apply sim_itree_ret|]; ss. etrans; eauto.
  - (* racy read *)
    right. guardH ORD2.
    exploit sim_local_racy_read; try exact LOCAL1; eauto; try refl. i. des.
    esplits.
    + ss.
    + econs 2; [|econs 1]. econs.
      * econs 2; [|econs 8]; eauto. econs. refl.
      * ss.
    + econs 2. econs 2; [|econs 5]; eauto. econs. refl.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
  - (* racy read *)
    right. guardH ORDR2.
    exploit sim_local_racy_read; try exact LOCAL1; eauto; try refl. i. des.
    esplits.
    + ss.
    + econs 2; [|econs 1]. econs.
      * econs 2; [|econs 8]; eauto. econs; eauto.
      * ss.
    + econs 2. econs 2; [|econs 5]; eauto. econs. refl.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
  - (* racy write *)
    left.
    exploit sim_local_racy_write; try exact LOCAL1; try exact SIM_LC;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; eauto.
    i. des.
    econs; try refl.
    + econs 2; [|econs 9]; eauto. econs. refl.
    + ss.
  - (* racy update *)
    left. guardH ORDR2.
    exploit sim_local_racy_update; try exact LOCAL1; try exact SIM_LC;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; eauto.
    i. des.
    econs; try refl.
    + econs 2; [|econs 10]; eauto. econs; eauto.
    + ss.
Qed.

Lemma sim_fence_sim_thread R:
  @sim_fence R <6= @sim_thread (lang (unit * R)%type) (lang (unit * R)%type) (sim_terminal eq).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss; ii.
  - right. inv TERMINAL_TGT. inv PR; ss.
  - right. esplits; eauto.
    inv PR. inv FENCE. inv LOCAL. ss. congr.
  - exploit sim_fence_mon; eauto; try apply GL_FUTURE_SRC. i.
    exploit sim_fence_step; try exact x0; eauto. i. des; eauto.
    + right. esplits; eauto.
      left. eapply paco9_mon; eauto. ss.
    + right. esplits; eauto.
Qed.
