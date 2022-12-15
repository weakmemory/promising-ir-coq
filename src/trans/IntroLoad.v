From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
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


Lemma intro_load_sim_itree
      loc ord:
  sim_itree eq
            (Ret tt)
            (ITree.trigger (MemE.read loc ord);; Ret tt).
Proof.
  unfold trigger. rewrite bind_vis.
  pcofix CIH. ii. subst. pfold. ii. splits; i.
  { inv TERMINAL_TGT. eapply f_equal with (f:=observe) in H; ss. }
  { right. esplits; eauto.
    rewrite sim_local_promises_bot; eauto.
  }
  ii. right.
  inv STEP_TGT; ss.
  - (* internal *)
    exploit sim_local_internal; eauto. i. des.
    esplits; try exact GL2; eauto. inv LOCAL0; ss.
  - (* load *)
    dependent destruction STATE.
    esplits; [|refl|econs 1|..]; eauto.
    + destruct e_tgt; ss.
    + destruct e_tgt; ss.
    + by inv LOCAL0.
    + left. rewrite bind_ret_l. eapply paco9_mon; [apply sim_itree_ret|]; ss.
      inv LOCAL. inv LOCAL0; ss. inv LOCAL. econs; ss.
      etrans; eauto. apply TViewFacts.read_tview_incr.
Qed.
