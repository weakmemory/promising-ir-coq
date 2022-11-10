Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
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
Require Import SimMemory.
Require Import SimGlobal.

Set Implicit Arguments.


Variant sim_local (lc_src lc_tgt: Local.t): Prop :=
| sim_local_intro
    (TVIEW: TView.le (Local.tview lc_src) (Local.tview lc_tgt))
    (PROMISES: Local.promises lc_src = Local.promises lc_tgt)
    (RESERVES: Local.reserves lc_src = Local.reserves lc_tgt)
.
#[export] Hint Constructors sim_local: core.

Global Program Instance sim_local_PreOrder: PreOrder sim_local.
Next Obligation.
  ii. destruct x. econs; refl.
Qed.
Next Obligation.
  ii. destruct x, y, z. inv H. inv H0. ss. subst.
  econs; ss. etrans; eauto.
Qed.

Lemma sim_local_promises_bot
      lc_src lc_tgt
      (SIM: sim_local lc_src lc_tgt):
  Local.promises lc_src = BoolMap.bot <->
  Local.promises lc_tgt = BoolMap.bot.
Proof.
  inv SIM. rewrite PROMISES. ss.
Qed.

Lemma sim_local_is_terminal
      lc_src lc_tgt
      (SIM: sim_local lc_src lc_tgt):
  Local.is_terminal lc_src <-> Local.is_terminal lc_tgt.
Proof.
  exploit sim_local_promises_bot; eauto. i. des.
  split; i; inv H; eauto.
Qed.

Lemma sim_local_internal
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      lc2_tgt gl2_tgt
      e
      (STEP_TGT: Local.internal_step e lc1_tgt gl1_tgt lc2_tgt gl2_tgt)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GL1: sim_global gl1_src gl1_tgt)
      (WF1_SRC: Local.wf lc1_src gl1_src)
      (WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL1_SRC: Global.wf gl1_src)
      (GL1_TGT: Global.wf gl1_tgt):
  exists lc2_src gl2_src,
    <<STEP_SRC: Local.internal_step e lc1_src gl1_src lc2_src gl2_src >> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
    <<GL2: sim_global gl2_src gl2_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  { inv LOCAL. inv GL1. inv PROMISE. esplits; eauto.
    { econs 1; eauto. econs; eauto. econs; eauto.
      { rewrite PROMISES. eauto. }
      { rewrite PROMISES0. eauto. }
    }
    { econs; eauto. }
    { econs; eauto. }
  }
  { inv LOCAL. inv RESERVE. inv GL1.
    hexploit sim_memory_add_exist; eauto. i. des. esplits.
    { econs 2. econs; eauto. econs; eauto.
      rewrite RESERVES. eauto.
    }
    { econs; eauto. }
    { econs; eauto. }
  }
  { inv LOCAL. inv CANCEL. inv GL1.
    hexploit Memory.remove_exists.
    { eapply WF1_SRC. rewrite RESERVES. eapply Memory.remove_get0. eauto. }
    i. des.
    hexploit sim_memory_remove; try exact MEMORY; eauto.
    i. esplits.
    { econs 3. econs; eauto. econs; eauto.
      rewrite RESERVES. eauto.
    }
    { econs; eauto. }
    { econs; eauto. }
  }
Qed.
