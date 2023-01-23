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

Require Import ITreeLang.
Require Import ITreeLib.

Set Implicit Arguments.


Lemma intro_choose_sim_itree (v: Const.t):
  sim_itree eq
            (Ret tt)
            (ITree.trigger MemE.choose;; Ret tt).
Proof.
  unfold trigger. rewrite bind_vis.
  pcofix CIH. ii. pfold. ii. splits; i.
  { inv TERMINAL_TGT. ss. }
  { right. esplits; eauto.
    rewrite sim_local_promises_bot; eauto.
  }
  ii. right.
  inv STEP_TGT; ss.
  - (* internal *)
    exploit sim_local_internal; eauto. i. des.
    esplits; try apply GL2; eauto. inv LOCAL0; ss.
  - (* choose *)
    inv LOCAL0; dependent destruction STATE.
    esplits; [|refl|econs 1|..]; ss.
    left. rewrite bind_ret_l. eapply paco9_mon; [apply sim_itree_ret|]; ss.
Qed.
