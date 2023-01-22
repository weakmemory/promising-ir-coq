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
Require Import ReorderLoad.
Require Import ReorderFence.
Require Import ReorderAbort.

Require Import ITreeLang.
Require Import ITreeLib.

Set Implicit Arguments.


Definition reorder_choose (R:Type) (i2: MemE.t R): Prop :=
  match i2 with
  | MemE.syscall _ => False
  | _ => True
  end.

Variant sim_choose: forall R
                      (st_src:itree MemE.t (Const.t * R)%type) (lc_src:Local.t) (gl1_src:Global.t)
                      (st_tgt:itree MemE.t (Const.t * R)%type) (lc_tgt:Local.t) (gl1_tgt:Global.t), Prop :=
| sim_choose_intro
    R (i2: MemE.t R)
    v1
    lc1_src gl1_src
    lc1_tgt gl1_tgt
    (REORDER: reorder_choose i2)
    (LOCAL: sim_local lc1_src lc1_tgt):
    sim_choose
      (Vis i2 (fun v2 => Vis MemE.choose (fun v1 => Ret (v1, v2)))) lc1_src gl1_src
      (Vis i2 (fun v2 => Ret (v1, v2))) lc1_tgt gl1_tgt
.

Lemma sim_choose_sim_thread R:
  @sim_choose R <6= @sim_thread (lang (Const.t * R)%type) (lang (Const.t * R)%type) (sim_terminal eq).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss; ii.
  { inv TERMINAL_TGT. inv PR; ss. }
  { right. esplits; eauto. inv PR. inv LOCAL. congr. }
  destruct PR.
  inv STEP_TGT; ss.
  { (* internal *)
    right.
    exploit sim_local_internal; eauto. i. des.
    esplits; try exact GL2; eauto.
    + inv LOCAL0; ss.
    + right. apply CIH. ss.
  }
  inv LOCAL0; ss; dependent destruction STATE.
  - (* choose *)
    right.
    esplits.
    + ss.
    + econs 2; [|refl]. econs.
      * econs 2; [|econs 1]. econs. refl.
      * ss.
    + econs 2. econs 2; [|econs 1]. econs. refl.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
  - (* read *)
    right.
    exploit sim_local_read; try exact LOCAL1; eauto; try refl. i. des.
    esplits.
    + ss.
    + econs 2; [|refl]. econs.
      * econs 2; [|econs 2]; eauto. econs. refl.
      * ss.
    + econs 2. econs 2; [|econs 1]. econs. refl.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
  - (* update-read *)
    right.
    exploit sim_local_read; try exact LOCAL1; eauto; try refl. i. des.
    esplits.
    + ss.
    + econs 2; [|refl]. econs.
      * econs 2; [|econs 2]; eauto. econs; eauto.
      * ss.
    + econs 2. econs 2; [|econs 1]. econs. refl.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
  - (* write *)
    right.
    exploit sim_local_write; try exact LOCAL1; eauto; try refl. i. des.
    esplits.
    + ss.
    + econs 2; [|refl]. econs.
      * econs 2; [|econs 3]; eauto. econs. refl.
      * ss.
    + econs 2. econs 2; [|econs 1]. econs. refl.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
  - (* update *)
    right.
    exploit sim_local_update; try exact LOCAL1; eauto; try refl. i. des.
    esplits.
    + ss.
    + econs 2; [|refl]. econs.
      * econs 2; [|econs 4]; eauto. econs; eauto.
      * ss.
    + econs 2. econs 2; [|econs 1]. econs. refl.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
  - (* fence *)
    right.
    exploit sim_local_fence; try exact LOCAL1; eauto; try refl. i. des.
    esplits.
    + ss.
    + econs 2; [|refl]. econs.
      * econs 2; [|econs 5]; eauto. econs. refl.
      * ss.
    + econs 2. econs 2; [|econs 1]. econs. refl.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
  - (* syscall *)
    ss.
  - (* failure *)
    left.
    econs.
    + refl.
    + econs 2; [|econs 7]; eauto. econs.
    + ss.
  - (* racy-read *)
    right.
    exploit sim_local_racy_read; try exact LOCAL1; eauto; try refl. i. des.
    esplits.
    + ss.
    + econs 2; [|refl]. econs.
      * econs 2; [|econs 8]; eauto. econs. refl.
      * ss.
    + econs 2. econs 2; [|econs 1]. econs. refl.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
  - (* racy-update-read *)
    right.
    exploit sim_local_racy_read; try exact LOCAL1; eauto; try refl. i. des.
    esplits.
    + ss.
    + econs 2; [|refl]. econs.
      * econs 2; [|econs 8]; eauto. econs; eauto.
      * ss.
    + econs 2. econs 2; [|econs 1]. econs. refl.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_itree_ret|]; ss.
  - (* write *)
    left.
    exploit sim_local_racy_write; try exact LOCAL1; eauto; try refl. i. des.
    econs.
    + refl.
    + econs 2; [|econs 9]; eauto. econs. refl.
    + ss.
  - (* update *)
    left.
    exploit sim_local_racy_update; try exact LOCAL1; eauto; try refl. i. des.
    econs.
    + refl.
    + econs 2; [|econs 10]; eauto. econs; eauto.
    + ss.
Qed.
