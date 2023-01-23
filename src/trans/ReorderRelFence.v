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

Require Import SimLocalAdvance.

Require Import ITreeLang.
Require Import ITreeLib.

Set Implicit Arguments.


Variant reorder_release_fenceF: forall R (i2:MemE.t R), Prop :=
| reorder_release_fenceF_load
    l2 o2:
    reorder_release_fenceF (MemE.read l2 o2)
| reorder_release_fenceF_store
    l2 v2 o2
    (ORD21: Ordering.le o2 Ordering.plain \/ Ordering.le Ordering.acqrel o2)
    (ORD22: Ordering.le Ordering.plain o2):
    reorder_release_fenceF (MemE.write l2 v2 o2)
| reorder_release_fenceF_update
    l2 rmw2 or2 ow2
    (ORDW2: Ordering.le ow2 Ordering.plain \/ Ordering.le Ordering.acqrel ow2):
    reorder_release_fenceF (MemE.update l2 rmw2 or2 ow2)
| reorder_release_fenceF_fence:
    reorder_release_fenceF (MemE.fence Ordering.acqrel Ordering.plain)
.

Variant sim_release_fenceF: forall R
                              (st_src:itree MemE.t (unit * R)%type) (lc_src:Local.t) (gl1_src:Global.t)
                              (st_tgt:itree MemE.t (unit * R)%type) (lc_tgt:Local.t) (gl1_tgt:Global.t), Prop :=
| sim_relese_fenceF_intro
    R (v: R)
    lc1_src gl1_src
    lc1_tgt gl1_tgt
    (LOCALF: sim_local lc1_src (local_relfenced lc1_tgt)):
    sim_release_fenceF
      (Ret (tt, v)) lc1_src gl1_src
      (Vis (MemE.fence Ordering.plain Ordering.acqrel) (fun r => Ret (r, v))) lc1_tgt gl1_tgt
.

Lemma sim_release_fenceF_step
      R
      st1_src lc1_src gl0_src
      st1_tgt lc1_tgt gl0_tgt
      (SIM: sim_release_fenceF st1_src lc1_src gl0_src
                               st1_tgt lc1_tgt gl0_tgt):
  forall gl1_src gl1_tgt
    (GLOBAL: sim_global gl1_src gl1_tgt)
    (LC_WF_SRC: Local.wf lc1_src gl1_src)
    (LC_WF_TGT: Local.wf lc1_tgt gl1_tgt)
    (GL_WF_SRC: Global.wf gl1_src)
    (GL_WF_TGT: Global.wf gl1_tgt),
    _sim_thread_step (lang (unit * R)%type) (lang (unit * R)%type)
                     ((@sim_thread (lang (unit * R)%type) (lang (unit * R)%type) (sim_terminal eq)) \6/ @sim_release_fenceF R)
                     st1_src lc1_src gl1_src
                     st1_tgt lc1_tgt gl1_tgt.
Proof.
  destruct SIM; ii. right.
  inv STEP_TGT; ss.
  { (* internal *)
    exploit sim_local_internal_relfenced; eauto. i. des.
    esplits.
    + inv LOCAL; ss.
    + refl.
    + econs 2. econs 1. eauto.
    + ss.
    + ss.
    + right. econs 1; eauto.
  }
  inv LOCAL; ss; dependent destruction LOCALF; dependent destruction STATE.
  (* fence *)
  exploit sim_local_fence_tgt_relfenced; try exact GLOBAL; eauto. i. des.
  esplits.
  + ss.
  + refl.
  + econs 1.
  + ss.
  + ss.
  + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
Qed.

Lemma sim_release_fenceF_sim_thread R:
  @sim_release_fenceF R <6= (@sim_thread (lang (unit * R)%type) (lang (unit * R)%type) (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss; ii.
  - right. inv TERMINAL_TGT. inv PR; ss.
  - right. inv PR.
    esplits; eauto.
    inv LOCALF. ss. congr.
  - exploit sim_release_fenceF_step; try apply PR; try apply GLOBAL; eauto. i. des; eauto.
    + right. esplits; eauto.
      left. eapply paco9_mon; eauto. ss.
    + right. esplits; eauto.
Qed.

Lemma reorder_release_fenceF_sim_itree R
      (i1: MemE.t R) (REORDER: reorder_release_fenceF i1):
  sim_itree eq
            (Vis (MemE.fence Ordering.plain Ordering.acqrel) (fun r0 => Vis i1 (fun r => Ret (r0, r))))
            (Vis i1 (fun r => Vis (MemE.fence Ordering.plain Ordering.acqrel) (fun r0 => Ret (r0, r)))).
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { inv TERMINAL_TGT. eapply f_equal with (f:=observe) in H; ss. }
  { right. esplits; eauto. inv LOCAL. congr. }
  inv STEP_TGT.
  { (* internal *)
    right.
    exploit sim_local_internal; eauto. i. des.
    esplits; try apply GL2; eauto; ss.
    inv LOCAL0; ss.
  }
  exploit sim_local_relfenced; eauto. i.
  exploit sim_local_fence_src_relfenced; eauto. i. des.
  exploit Local.fence_step_future; eauto. i. des.
  inv LOCAL0; ss; dependent destruction REORDER; dependent destruction STATE.
  - (* load *)
    right.
    exploit sim_local_read_relfenced; eauto; try refl. i. des.
    esplits.
    + ss.
    + econs 2; [|refl]. econs.
      * econs 2; [|econs 5]; eauto. econs. refl.
      * ss.
    + econs 2. econs 2; [|econs 2]; eauto. econs. refl.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_release_fenceF_sim_thread|]; ss.
  - (* update-load *)
    right.
    guardH ORDW2.
    exploit sim_local_read_relfenced; eauto; try refl. i. des.
    esplits.
    + ss.
    + econs 2; [|refl]. econs.
      * econs 2; [|econs 5]; eauto. econs. refl.
      * ss.
    + econs 2. econs 2; [|econs 2]; eauto. econs; eauto.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_release_fenceF_sim_thread|]; ss.
  - (* write *)
    right.
    guardH ORD21.
    hexploit sim_local_write_relfenced; try exact GLOBAL2;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; eauto; (try by econs). i. des.
    esplits.
    + ss.
    + econs 2; [|refl]. econs.
      * econs 2; [|econs 5]; eauto. econs. refl.
      * ss.
    + econs 2. econs 2; [|econs 3]; eauto. econs. refl.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_release_fenceF_sim_thread|]; ss.
  - (* update *)
    right.
    guardH ORDW2.
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_read_relfenced; eauto; try refl. i. des.
    exploit Local.read_step_future; eauto. i. des.
    hexploit sim_local_write_relfenced; try exact GLOBAL2;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; eauto; (try by econs). i. des.
    esplits.
    + ss.
    + econs 2; [|refl]. econs.
      * econs 2; [|econs 5]; eauto. econs. refl.
      * ss.
    + econs 2. econs 2; [|econs 4]; eauto. econs; eauto.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_release_fenceF_sim_thread|]; ss.
  - (* fence *)
    right.
    exploit sim_local_fence_relfenced; try exact GLOBAL2; eauto; try refl. i. des.
    esplits.
    + ss.
    + econs 2; [|refl]. econs.
      * econs 2; [|econs 5]; eauto. econs. refl.
      * ss.
    + econs 2. econs 2; [|econs 5]; eauto. econs. refl.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_release_fenceF_sim_thread|]; ss.
  - (* racy read *)
    right.
    exploit sim_local_racy_read_relfenced; eauto; try refl. i. des.
    esplits.
    + ss.
    + econs 2; [|refl]. econs.
      * econs 2; [|econs 5]; eauto. econs. refl.
      * ss.
    + econs 2. econs 2; [|econs 8]; eauto. econs. refl.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_release_fenceF_sim_thread|]; ss.
  - (* racy update-load *)
    right.
    guardH ORDW2.
    exploit sim_local_racy_read_relfenced; eauto; try refl. i. des.
    esplits.
    + ss.
    + econs 2; [|refl]. econs.
      * econs 2; [|econs 5]; eauto. econs. refl.
      * ss.
    + econs 2. econs 2; [|econs 8]; eauto. econs; eauto.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_release_fenceF_sim_thread|]; ss.
  - (* racy write *)
    left.
    guardH ORD21.
    exploit sim_local_racy_write_relfenced;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; eauto. i. des.
    econs.
    + econs 2; [|refl]. econs.
      * econs 2; [|econs 5]; eauto. econs. refl.
      * ss.
    + econs 2; [|econs 9]; eauto. econs. refl.
    + ss.
  - (* racy update *)
    left.
    guardH ORDW2.
    exploit sim_local_racy_update_relfenced;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; eauto. i. des.
    econs.
    + econs 2; [|refl]. econs.
      * econs 2; [|econs 5]; eauto. econs. refl.
      * ss.
    + econs 2; [|econs 10]; eauto. econs; eauto.
    + ss.
Qed.
