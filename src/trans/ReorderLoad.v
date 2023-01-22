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


Variant reorder_load l1 o1: forall R (i2:MemE.t R), Prop :=
| reorder_load_load
    l2 o2
    (ORD2: Ordering.le o2 Ordering.relaxed)
    (LOC: l1 = l2 -> Ordering.le o1 Ordering.plain /\ Ordering.le o2 Ordering.plain):
    reorder_load l1 o1 (MemE.read l2 o2)
| reorder_load_store
    l2 v2 o2
    (ORD: Ordering.le o1 Ordering.acqrel \/ Ordering.le o2 Ordering.acqrel)
    (ORD2: Ordering.le Ordering.plain o2)
    (LOC: l1 <> l2):
    reorder_load l1 o1 (MemE.write l2 v2 o2)
| reorder_load_update
    l2 rmw2 or2 ow2
    (ORDR2: Ordering.le or2 Ordering.relaxed)
    (ORDW2: Ordering.le o1 Ordering.acqrel \/ Ordering.le ow2 Ordering.acqrel)
    (LOC: l1 <> l2):
    reorder_load l1 o1 (MemE.update l2 rmw2 or2 ow2)
| reorder_load_fence
    or2 ow2
    (ORDR2: Ordering.le or2 Ordering.relaxed)
    (ORDW2: Ordering.le ow2 Ordering.acqrel):
    reorder_load l1 o1 (MemE.fence or2 ow2)
| reorder_load_choose:
    reorder_load l1 o1 MemE.choose
.

Variant sim_load: forall R
                      (st_src:itree MemE.t (Const.t * R)%type) (lc_src:Local.t) (gl1_src:Global.t)
                      (st_tgt:itree MemE.t (Const.t * R)%type) (lc_tgt:Local.t) (gl1_tgt:Global.t), Prop :=
| sim_load_read
    R
    l1 ts1 v1 released1 o1 (i2: MemE.t R)
    lc1_src gl1_src
    lc1_tgt gl1_tgt
    lc2_src
    (REORDER: reorder_load l1 o1 i2)
    (READ: Local.read_step lc1_src gl1_src l1 ts1 v1 released1 o1 lc2_src)
    (LOCAL: sim_local lc2_src lc1_tgt)
    (GLOBAL: sim_global gl1_src gl1_tgt)
    (LC_WF_SRC: Local.wf lc1_src gl1_src)
    (LC_WF_TGT: Local.wf lc1_tgt gl1_tgt)
    (GL_WF_SRC: Global.wf gl1_src)
    (GL_WF_TGT: Global.wf gl1_tgt):
    sim_load
      (Vis i2 (fun v2 => Vis (MemE.read l1 o1) (fun v1 => Ret (v1, v2)))) lc1_src gl1_src
      (Vis i2 (fun v2 => Ret (v1, v2))) lc1_tgt gl1_tgt
| sim_load_racy_read
    R
    l1 t1 v1 o1 (i2: MemE.t R)
    lc1_src gl1_src
    lc1_tgt gl1_tgt
    (REORDER: reorder_load l1 o1 i2)
    (READ: Local.racy_read_step lc1_src gl1_src l1 t1 v1 o1)
    (LOCAL: sim_local lc1_src lc1_tgt)
    (GLOBAL: sim_global gl1_src gl1_tgt)
    (LC_WF_SRC: Local.wf lc1_src gl1_src)
    (LC_WF_TGT: Local.wf lc1_tgt gl1_tgt)
    (GL_WF_SRC: Global.wf gl1_src)
    (GL_WF_TGT: Global.wf gl1_tgt):
    sim_load
      (Vis i2 (fun v2 => Vis (MemE.read l1 o1) (fun v1 => Ret (v1, v2)))) lc1_src gl1_src
      (Vis i2 (fun v2 => Ret (v1, v2))) lc1_tgt gl1_tgt
.

Lemma sim_load_sim_local
      R
      st_src lc_src gl_src
      st_tgt lc_tgt gl_tgt
      (SIM: @sim_load R st_src lc_src gl_src st_tgt lc_tgt gl_tgt):
  sim_local lc_src lc_tgt.
Proof.
  inv SIM; eauto.
  exploit Local.read_step_future; eauto. i. des.
  inv READ. inv LOCAL. ss.
  econs; eauto. etrans; eauto.
Qed.

Lemma sim_load_mon
      R
      st_src lc_src gl1_src
      st_tgt lc_tgt gl1_tgt
      gl2_src
      gl2_tgt
      (SIM1: sim_load st_src lc_src gl1_src
                      st_tgt lc_tgt gl1_tgt)
      (GL_LE_SRC: Global.strong_le gl1_src gl2_src)
      (GL_LE_TGT: Global.le gl1_tgt gl2_tgt)
      (GLOBAL1: sim_global gl2_src gl2_tgt)
      (LC_WF_SRC: Local.wf lc_src gl2_src)
      (LC_WF_TGT: Local.wf lc_tgt gl2_tgt)
      (GL_WF_SRC: Global.wf gl2_src)
      (GL_WF_TGT: Global.wf gl2_tgt):
  @sim_load R
            st_src lc_src gl2_src
            st_tgt lc_tgt gl2_tgt.
Proof.
  dependent destruction SIM1.
  - exploit future_read_step; try exact READ; try apply GL_LE_SRC; eauto. i. des.
    econs; eauto. etrans; eauto.
  - exploit future_racy_read_step; try exact READ; try apply GL_LE_SRC; eauto. i. des.
    econs 2; eauto.
Qed.

Lemma sim_load_step
      R
      st1_src lc1_src gl1_src
      st1_tgt lc1_tgt gl1_tgt
      (SIM: sim_load st1_src lc1_src gl1_src
                     st1_tgt lc1_tgt gl1_tgt):
  _sim_thread_step (lang (Const.t * R)%type) (lang (Const.t * R)%type)
                   ((@sim_thread (lang (Const.t * R)%type) (lang (Const.t * R)%type) (sim_terminal eq)) \6/ @sim_load R)
                   st1_src lc1_src gl1_src
                   st1_tgt lc1_tgt gl1_tgt.
Proof.
  exploit sim_load_sim_local; eauto. intro SIM_LC.
  dependent destruction SIM.
  { (* read *)
    ii.
    exploit Local.read_step_future; eauto. i. des.
    inv STEP_TGT; ss.
    { (* internal *)
      right.
      exploit Local.internal_step_future; eauto. i. des.
      exploit sim_local_internal; try exact LOCAL; eauto. i. des.
      exploit reorder_read_internal; try exact READ; try exact STEP_SRC; eauto. i. des.
      exploit Local.internal_step_future; eauto. i. des.
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
      + econs 2. econs 2; [|econs 2]; eauto. econs. refl.
      + ss.
      + ss.
      + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
    - (* load *)
      right.
      exploit sim_local_read; try exact LOCAL; try exact LOCAL1; eauto; try refl. i. des.
      exploit reorder_read_read; try exact READ; try exact STEP_SRC; eauto. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs 2; [|econs 2]; eauto. econs. refl.
        * ss.
      + econs 2. econs 2; [|econs 2]; eauto. econs. refl.
      + ss.
      + ss.
      + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
    - (* update-load *)
      right.
      guardH ORDW2.
      exploit sim_local_read; try exact LOCAL; try exact LOCAL1; eauto; try refl. i. des.
      exploit reorder_read_read; try exact READ; try exact STEP_SRC; try by eauto. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs 2; [|econs 2]; eauto. econs; eauto.
        * ss.
      + econs 2. econs 2; [|econs 2]; eauto. econs. refl.
      + ss.
      + ss.
      + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
    - (* store *)
      right.
      guardH ORD.
      hexploit sim_local_write; try exact LOCAL; try exact LOCAL1;
        try match goal with
          | [|- is_true (Ordering.le ?a ?b)] => refl
          end ; eauto. i. des.
      exploit reorder_read_write; try exact READ; try exact STEP_SRC; eauto. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs 2; [|econs 3]; eauto. ss. econs; eauto.
        * ss.
      + econs 2. econs 2; [|econs 2]; eauto. econs. refl.
      + ss.
      + etrans; eauto.
      + left. eapply paco9_mon; [apply sim_itree_ret|]; ss. etrans; eauto.
    - (* update *)
      right.
      guardH ORDW2.
      exploit Local.read_step_future; try exact LOCAL1; eauto. i. des.
      exploit sim_local_read; try exact LOCAL1; try exact LOCAL; eauto; try refl. i. des.
      exploit Local.read_step_future; try exact STEP_SRC; eauto. i. des.
      hexploit sim_local_write; try exact LOCAL2; try exact GLOBAL; eauto; try refl. i. des.
      exploit reorder_read_read; try exact READ; try exact STEP_SRC; eauto; try congr. i. des.
      exploit Local.read_step_future; try exact STEP1; eauto. i. des.
      exploit reorder_read_write; try exact STEP2; try exact STEP_SRC0; eauto; try congr. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs 2; [|econs 4]; eauto. econs; eauto.
        * ss.
      + econs 2. econs 2; [|econs 2]; eauto. econs. refl.
      + ss.
      + etrans; eauto.
      + left. eapply paco9_mon; [apply sim_itree_ret|]; ss. etrans; eauto.
    - (* fence *)
      right.
      exploit sim_local_fence; try exact LOCAL1; try exact LOCAL; eauto; try refl. i. des.
      exploit reorder_read_fence; try exact READ; try exact STEP_SRC; eauto. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs 2; [|econs 5]; eauto. econs. refl.
        * ss.
      + econs 2. econs 2; [|econs 2]; eauto. econs. refl.
      + eauto.
      + etrans; eauto.
      + left. eapply paco9_mon; [apply sim_itree_ret|]; ss. etrans; eauto.
    - (* racy read *)
      right.
      exploit sim_local_racy_read; try exact LOCAL; try exact LOCAL1; eauto; try refl. i. des.
      exploit reorder_read_racy_read; try exact READ; try exact x0; eauto. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs 2; [|econs 8]; eauto. econs. refl.
        * ss.
      + econs 2. econs 2; [|econs 2]; eauto. econs. refl.
      + ss.
      + ss.
      + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
    - (* update - racy read *)
      right. guardH ORDW2.
      exploit sim_local_racy_read; try exact LOCAL; try exact LOCAL1; eauto; try refl. i. des.
      exploit reorder_read_racy_read; try exact READ; try exact x0; eauto. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs 2; [|econs 8]; eauto. econs; eauto.
        * ss.
      + econs 2. econs 2; [|econs 2]; eauto. econs. refl.
      + ss.
      + ss.
      + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
    - (* racy write *)
      left. guardH ORD.
      exploit sim_local_racy_write; try exact LOCAL1; try exact SIM_LC;
        try match goal with
            | [|- is_true (Ordering.le _ _)] => refl
            end; eauto.
      i. des.
      econs; try refl.
      + econs 2; [|econs 9]; eauto. econs. refl.
      + ss.
    - (* racy update *)
      left. guardH ORDW2.
      exploit sim_local_racy_update; try exact LOCAL1; try exact SIM_LC;
        try match goal with
            | [|- is_true (Ordering.le _ _)] => refl
            end; eauto.
      i. des.
      econs; try refl.
      + econs 2; [|econs 10]; eauto. econs; eauto.
      + ss.
  }

  { (* racy read *)
    ii.
    inv STEP_TGT; ss.
    { (* internal *)
      right.
      exploit Local.internal_step_future; eauto. i. des.
      exploit sim_local_internal; try exact LOCAL; eauto. i. des.
      exploit reorder_racy_read_internal; try exact READ; try exact STEP_SRC; eauto. i. des.
      exploit Local.internal_step_future; eauto. i. des.
      esplits; try apply GL2; eauto; ss.
      + inv LOCAL0; ss.
      + right. econs 2; eauto.
    }
    inv LOCAL0; ss; dependent destruction REORDER; dependent destruction STATE.
    - (* choose *)
      right.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs 2; [|econs 1]. econs. refl.
        * ss.
      + econs 2. econs 2; [|econs 8]; eauto. econs. refl.
      + ss.
      + ss.
      + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
    - (* load *)
      right.
      exploit sim_local_read; try exact LOCAL; try exact LOCAL1; eauto; try refl. i. des.
      exploit reorder_racy_read_read; try exact READ; try exact STEP_SRC; eauto. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs 2; [|econs 2]; eauto. econs. refl.
        * ss.
      + econs 2. econs 2; [|econs 8]; eauto. econs. refl.
      + ss.
      + ss.
      + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
    - (* update-load *)
      right.
      guardH ORDW2.
      exploit sim_local_read; try exact LOCAL; try exact LOCAL1; eauto; try refl. i. des.
      exploit reorder_racy_read_read; try exact READ; try exact STEP_SRC; try by eauto. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs 2; [|econs 2]; eauto. econs; eauto.
        * ss.
      + econs 2. econs 2; [|econs 8]; eauto. econs. refl.
      + ss.
      + ss.
      + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
    - (* store *)
      right.
      guardH ORD.
      hexploit sim_local_write; try exact LOCAL; try exact LOCAL1;
        try match goal with
            | [|- is_true (Ordering.le ?a ?b)] => refl
            end; eauto.
      i. des.
      exploit reorder_racy_read_write; try exact READ; eauto. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs 2; [|econs 3]; eauto. econs. refl.
        * ss.
      + econs 2. econs 2; [|econs 8]; eauto. econs. refl.
      + ss.
      + ss.
      + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
    - (* update *)
      right.
      guardH ORDW2.
      exploit Local.read_step_future; try exact LOCAL; try exact LOCAL1; eauto. i. des.
      exploit sim_local_read; try exact LOCAL1; eauto; try refl. i. des.
      exploit Local.read_step_future; try exact STEP_SRC; eauto. i. des.
      hexploit sim_local_write; try exact LOCAL2; try exact GLOBAL; eauto; try refl. i. des.
      exploit reorder_racy_read_update; try exact READ; eauto. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs 2; [|econs 4]; eauto. econs; eauto.
        * ss.
      + econs 2. econs 2; [|econs 8]; eauto. econs. refl.
      + ss.
      + ss.
      + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
    - (* fence *)
      right.
      exploit sim_local_fence; try exact LOCAL; try exact LOCAL1; eauto; try refl. i. des.
      exploit reorder_racy_read_fence; try exact READ; try exact STEP_SRC; eauto. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs 2; [|econs 5]; eauto. econs. refl.
        * ss.
      + econs 2. econs 2; [|econs 8]; eauto. econs. refl.
      + ss.
      + ss.
      + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
    - (* racy read *)
      right.
      exploit sim_local_racy_read; try exact LOCAL; try exact LOCAL1; eauto; try refl. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs 2; [|econs 8]; eauto. econs. refl.
        * ss.
      + econs 2. econs 2; [|econs 8]; try exact READ. econs. refl.
      + ss.
      + ss.
      + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
    - (* racy read *)
      right. guardH ORDW2.
      exploit sim_local_racy_read; try exact LOCAL; try exact LOCAL1; eauto; try refl. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs 2; [|econs 8]; eauto. econs; eauto.
        * ss.
      + econs 2. econs 2; [|econs 8]; try exact READ. econs. refl.
      + ss.
      + ss.
      + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
    - (* racy write *)
      left. guardH ORD.
      exploit sim_local_racy_write; try exact LOCAL1; try exact SIM_LC;
        try match goal with
            | [|- is_true (Ordering.le _ _)] => refl
            end; eauto.
      i. des.
      econs; try refl.
      + econs 2; [|econs 9]; eauto. econs. refl.
      + ss.
    - (* racy update *)
      left. guardH ORDW2.
      exploit sim_local_racy_update; try exact LOCAL1; try exact SIM_LC;
        try match goal with
            | [|- is_true (Ordering.le _ _)] => refl
            end; eauto.
      i. des.
      econs; try refl.
      + econs 2; [|econs 10]; eauto. econs; eauto.
      + ss.
  }
Qed.

Lemma sim_load_sim_thread R:
  @sim_load R <6= @sim_thread (lang (Const.t * R)%type) (lang (Const.t * R)%type) (sim_terminal eq).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss; ii.
  - inv TERMINAL_TGT. inv PR; ss.
  - right.
    esplits; eauto.
    inv PR.
    + inv READ. inv LOCAL. ss. congr.
    + inv READ. inv LOCAL. ss. congr.
  - exploit sim_load_mon; eauto. i.
    exploit sim_load_step; eauto. i. des; eauto.
    + right. esplits; eauto.
      left. eapply paco9_mon; eauto. ss.
    + right. esplits; eauto.
Qed.
