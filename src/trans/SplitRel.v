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
Require Import SimThread.
Require Import Compatibility.

Require Import SimLocalAdvance.

Require Import ITreeLang.
Require Import ITreeLib.

Set Implicit Arguments.


Variant split_release: forall R (i1: MemE.t R) (i2: MemE.t R), Prop :=
| split_release_store
    l v:
    split_release (MemE.write l v Ordering.acqrel) (MemE.write l v Ordering.strong_relaxed)
| split_release_update
    l rmw or
    (OR: Ordering.le or Ordering.strong_relaxed):
    split_release (MemE.update l rmw or Ordering.acqrel) (MemE.update l rmw or Ordering.strong_relaxed)
.

Variant sim_released: forall R
                        (st_src:(Language.state (lang R))) (lc_src:Local.t) (gl1_src:Global.t)
                        (st_tgt:(Language.state (lang R))) (lc_tgt:Local.t) (gl1_tgt:Global.t), Prop :=
| sim_released_intro
    R
    (i_src i_tgt: MemE.t R)
    lc1_src gl1_src
    lc1_tgt gl1_tgt
    (SPLIT: split_release i_src i_tgt)
    (LOCAL: sim_local lc1_src lc1_tgt)
    (RELEASED: forall l, View.le (TView.cur (Local.tview lc1_tgt)) ((TView.rel (Local.tview lc1_tgt)) l))
    (GLOBAL: sim_global gl1_src gl1_tgt)
    (LC_WF_SRC: Local.wf lc1_src gl1_src)
    (LC_WF_TGT: Local.wf lc1_tgt gl1_tgt)
    (GL_WF_SRC: Global.wf gl1_src)
    (GL_WF_TGT: Global.wf gl1_tgt):
    sim_released
      (Vis i_src (fun r => Ret r)) lc1_src gl1_src
      (Vis i_tgt (fun r => Ret r)) lc1_tgt gl1_tgt
.

Lemma sim_released_mon
      R
      st_src lc_src gl1_src
      st_tgt lc_tgt gl1_tgt
      gl2_src
      gl2_tgt
      (SIM1: sim_released st_src lc_src gl1_src
                          st_tgt lc_tgt gl1_tgt)
      (GLOBAL: sim_global gl2_src gl2_tgt)
      (LC_WF_SRC: Local.wf lc_src gl2_src)
      (LC_WF_TGT: Local.wf lc_tgt gl2_tgt)
      (GL_WF_SRC: Global.wf gl2_src)
      (GL_WF_TGT: Global.wf gl2_tgt):
  @sim_released R
                st_src lc_src gl2_src
                st_tgt lc_tgt gl2_tgt.
Proof.
  destruct SIM1. econs; eauto.
Qed.

Lemma sim_released_step
      R
      st1_src lc1_src gl1_src
      st1_tgt lc1_tgt gl1_tgt
      (SIM: @sim_released R
                          st1_src lc1_src gl1_src
                          st1_tgt lc1_tgt gl1_tgt):
  _sim_thread_step (lang R) (lang R)
                   ((@sim_thread (lang R) (lang R) (sim_terminal eq)) \6/ @sim_released R)
                   st1_src lc1_src gl1_src
                   st1_tgt lc1_tgt gl1_tgt.
Proof.
  destruct SIM. ii.
  inv STEP_TGT; [|inv LOCAL0; destruct SPLIT; ss; dependent destruction STATE].
  - (* internal *)
    right.
    exploit Local.internal_step_future; eauto. i. des.
    exploit sim_local_internal; try exact LOCAL; eauto. i. des.
    exploit Local.internal_step_future; eauto. i. des.
    esplits; try exact GL2; eauto.
    + inv LOCAL0; ss.
    + right. econs; eauto.
      inv LOCAL0; inv LOCAL1; ss.
  - (* update-load *)
    right.
    exploit sim_local_read; try exact LOCAL1; eauto; try refl. i. des.
    esplits.
    + ss.
    + refl.
    + econs 2. econs 2; [|econs 2]; eauto. econs; eauto.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
  - (* write *)
    right.
    hexploit sim_local_write_released; try exact LOCAL1; eauto; try refl.
    { by rewrite <- View.join_l. }
    i. des.
    esplits.
    + ss.
    + refl.
    + econs 2. econs 2; [|econs 3]; eauto. econs. refl.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
  - (* update *)
    right.
    exploit sim_local_update_released; try exact LOCAL1; try exact LOCAL2; eauto; try refl. i. des.
    esplits.
    + ss.
    + refl.
    + econs 2. econs 2; [|econs 4]; eauto. econs; eauto.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
  - (* racy read *)
    right.
    exploit sim_local_racy_read; try exact LOCAL1; eauto; try refl. i. des.
    esplits.
    + ss.
    + refl.
    + econs 2. econs 2; [|econs 8]; eauto. econs; eauto.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
  - (* racy write *)
    left.
    exploit sim_local_racy_write_released; try exact LOCAL1; eauto. i. des.
    econs; try refl.
    + econs 2; [|econs 9]; eauto. econs; eauto.
    + ss.
  - (* racy update *)
    left.
    exploit sim_local_racy_update_released; try exact LOCAL1; eauto. i. des.
    econs; try refl.
    + econs 2; [|econs 10]; eauto. econs; eauto.
    + ss.
Qed.

Lemma sim_released_sim_thread R:
  @sim_released R <6= @sim_thread (lang R) (lang R) (sim_terminal eq).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss; ii.
  - inv TERMINAL_TGT. inv PR; ss.
  - right. esplits; eauto.
    inv PR. eapply sim_local_promises_bot; eauto.
  - exploit sim_released_mon; eauto. i.
    exploit sim_released_step; eauto. i. des; eauto.
    + right. esplits; eauto.
      left. eapply paco9_mon; eauto. ss.
    + right. esplits; eauto.
Qed.

Lemma split_release_sim_itree R
      (i_src i_tgt: MemE.t R)
      (SPLIT: split_release i_src i_tgt):
  sim_itree eq
            (ITree.trigger i_src)
            (ITree.trigger (MemE.fence Ordering.plain Ordering.acqrel);; ITree.trigger i_tgt).
Proof.
  replace (ITree.trigger i_src) with (Vis i_src (fun r => Ret r)).
  2: { unfold ITree.trigger. grind. }
  replace (ITree.trigger (MemE.fence Ordering.plain Ordering.acqrel);; ITree.trigger i_tgt) with
      (Vis (MemE.fence Ordering.plain Ordering.acqrel) (fun _ => Vis i_tgt (fun r => Ret r))).
  2: { unfold ITree.trigger. grind. repeat f_equal. extensionality u. grind. }
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { inv TERMINAL_TGT. eapply f_equal with (f:=observe) in H; ss. }
  { right. esplits; eauto.
    eapply sim_local_promises_bot; eauto.
  }
  right.
  inv STEP_TGT; ss.
  - (* internal *)
    exploit sim_local_internal; eauto. i. des.
    esplits; try apply GL2; eauto; ss.
    inv LOCAL0; ss.
  - (* fence *)
    inv LOCAL0; dependent destruction STATE.
    exploit Local.fence_step_future; eauto. i. des.
    esplits.
    + ss.
    + refl.
    + econs 1.
    + ss.
    + exploit Local.fence_step_non_sc; eauto. i. subst. ss.
    + left. eapply paco9_mon; [apply sim_released_sim_thread|]; ss.
      inv LOCAL1. econs; eauto.
      * inv LOCAL. econs; ss. etrans; eauto.
      * s. i. repeat condtac; ss. refl.
      * inv GLOBAL. econs; ss.        
Qed.
