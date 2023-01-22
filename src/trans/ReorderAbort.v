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

Require Import SimLocal.
Require Import SimMemory.
Require Import SimGlobal.
Require Import SimThread.
Require Import Compatibility.

Require Import ITreeLang.
Require Import ITreeLib.

Set Implicit Arguments.


Variant reorder_abort: forall R (i2:MemE.t R), Prop :=
| reorder_abort_load
    l2 o2
    (ORD2: Ordering.le o2 Ordering.relaxed):
    reorder_abort (MemE.read l2 o2)
| reorder_abort_store
    l2 v2 o2
    (ORD21: Ordering.le o2 Ordering.acqrel)
    (ORD22: Ordering.le Ordering.plain o2):
    reorder_abort (MemE.write l2 v2 o2)
| reorder_abort_fence
    or2 ow2
    (ORDR2: Ordering.le or2 Ordering.relaxed)
    (ORDW2: Ordering.le ow2 Ordering.acqrel):
    reorder_abort (MemE.fence or2 ow2)
| reorder_abort_choose:
    reorder_abort MemE.choose
.

Variant sim_abort:
  forall R (st_src:itree MemE.t (void * R)%type) (lc_src:Local.t) (gl1_src:Global.t), Prop :=
| sim_abort_intro
    R (i2: MemE.t R)
    lc1_src gl1_src
    (REORDER: reorder_abort i2)
    (LC_WF_SRC: Local.wf lc1_src gl1_src)
    (GL_WF_SRC: Global.wf gl1_src):
    @sim_abort
      R (Vis i2 (fun v2 => Vis (MemE.abort) (fun v1 => Ret (v1, v2)))) lc1_src gl1_src
.

Lemma sim_abort_steps_failure
      R
      st1_src lc1_src gl1_src
      (SIM: @sim_abort R st1_src lc1_src gl1_src):
  Thread.steps_failure (Thread.mk (lang (void * R)%type) st1_src lc1_src gl1_src).
Proof.
  destruct SIM. destruct REORDER.
  - (* load *)
    exploit progress_read_step; try exact LC_WF_SRC; eauto. i. des.
    econs.
    + econs 2; [|refl]. econs.
      * econs 2; [|econs 2]; eauto. econs. refl.
      * ss.
    + econs 2; [|econs 7]; eauto. econs.
    + ss.
  - (* store *)
    exploit progress_write_step; try apply Time.incr_spec; eauto. i. des.
    econs.
    + econs 2; [|refl]. econs.
      * econs 2; [|econs 3]; eauto. econs. refl.
      * ss.
    + econs 2; [|econs 7]; eauto. econs.
    + ss.
  - (* fence *)
    exploit progress_fence_step.
    { instantiate (2:=ow2). destruct ow2; ss. }
    i. des.
    econs.
    + econs 2; [|refl]. econs.
      * econs 2; [|econs 5]; eauto. econs. refl.
      * ss.
    + econs 2; [|econs 7]; eauto. econs.
    + ss.
  - (* choose *)
    econs.
    + econs 2; [|econs 1]. econs.
      * econs 2; [|econs 1]. econs. refl.
      * ss.
    + econs 2; [|econs 7]; eauto. econs.
    + ss.
  Unshelve. econs 2.
Qed.
