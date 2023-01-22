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


Variant reorder: forall R0 R1 (i1: MemE.t R0) (i2: MemE.t R1), Prop :=
| reorder_intro_load
    R1 l1 o1 (i2: MemE.t R1)
    (REORDER: reorder_load l1 o1 i2):
    reorder (MemE.read l1 o1) i2
| reorder_intro_fence
    R1 or1 ow1 (i2: MemE.t R1)
    (REORDER: reorder_fence or1 ow1 i2):
    reorder (MemE.fence or1 ow1) i2
| reorder_intro_abort
    R1 (i2: MemE.t R1)
    (REORDER: reorder_abort i2):
    reorder MemE.abort i2
.

Lemma reorder_sim_itree R0 R1
      (i1: MemE.t R0) (i2: MemE.t R1) (REORDER: reorder i1 i2):
  sim_itree eq
            (r2 <- ITree.trigger i2;; r1 <- ITree.trigger i1;; Ret (r1, r2))
            (r1 <- ITree.trigger i1;; r2 <- ITree.trigger i2;; Ret (r1, r2)).
Proof.
  replace (r2 <- ITree.trigger i2;; r1 <- ITree.trigger i1;; Ret (r1, r2)) with
      (Vis i2 (fun r2 => Vis i1 (fun r1 => Ret (r1, r2)))).
  2:{ unfold ITree.trigger. grind. repeat f_equal. extensionality r2. grind.
      repeat f_equal. extensionality r1. grind. }
  replace (r1 <- ITree.trigger i1;; r2 <- ITree.trigger i2;; Ret (r1, r2)) with
      (Vis i1 (fun r1 => Vis i2 (fun r2 => Ret (r1, r2)))).
  2:{ unfold ITree.trigger. grind. repeat f_equal. extensionality r2. grind.
      repeat f_equal. extensionality r1. grind. }
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { inv TERMINAL_TGT. eapply f_equal with (f:=observe) in H; ss. }
  { right. esplits; eauto. inv LOCAL. congr. }
  inv STEP_TGT; [|destruct REORDER; ss; dependent destruction STATE; inv LOCAL0]; ss; clarify.
  - (* internal *)
    right.
    exploit sim_local_internal; eauto. i. des.
    esplits; try apply GL2; eauto.
    inv LOCAL0; ss.
  - (* load *)
    right.
    exploit sim_local_read; eauto; try refl. i. des.
    esplits; try apply GLOBAL; eauto; ss.
    left. eapply paco9_mon; [apply sim_load_sim_thread|]; ss.
    econs; eauto.
    eapply Local.read_step_future; eauto.
  - (* racy read *)
    right.
    exploit sim_local_racy_read; eauto; try refl. i. des.
    esplits; try apply GLOBAL; eauto; ss.
    left. eapply paco9_mon; [apply sim_load_sim_thread|]; ss.
    econs 2; eauto.
  - (* fence *)
    right.
    exploit sim_local_fence; eauto; try refl. i. des.
    exploit Local.fence_step_future; try exact LOCAL1; eauto. i. des.
    assert (GLOBAL3: sim_global gl1_src gl3_tgt).
    { etrans; [|eauto]. inv STEP_SRC. inv GLOBAL2.
      econs; ss; try refl.
      apply TViewFacts.write_fence_sc_incr.
    }
    esplits.
    + ss.
    + refl.
    + econs 1.
    + ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_fence_sim_thread|]; ss.
      econs; eauto.
  - (* abort *)
    left.
    eapply sim_abort_steps_failure.
    econs; eauto.
Qed.
