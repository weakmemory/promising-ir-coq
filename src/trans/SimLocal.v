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
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (WF1_SRC: Local.wf lc1_src gl1_src)
      (WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL1_SRC: Global.wf gl1_src)
      (GL1_TGT: Global.wf gl1_tgt)
      (STEP_TGT: Local.internal_step e lc1_tgt gl1_tgt lc2_tgt gl2_tgt):
  exists lc2_src gl2_src,
    <<STEP_SRC: Local.internal_step e lc1_src gl1_src lc2_src gl2_src >> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
    <<GL2: sim_global gl2_src gl2_tgt>>.
Proof.
  inv LOCAL1. inv GLOBAL1. inv STEP_TGT.
  { inv LOCAL. inv PROMISE. esplits; eauto.
    { econs 1; eauto. econs; eauto. econs; eauto.
      { rewrite PROMISES. eauto. }
      { rewrite PROMISES0. eauto. }
    }
    { econs; eauto. }
    { econs; eauto. }
  }
  { inv LOCAL. inv RESERVE.
    hexploit sim_memory_add_exists; eauto. i. des. esplits.
    { econs 2. econs; eauto. econs; eauto.
      rewrite RESERVES. eauto.
    }
    { econs; eauto. }
    { econs; eauto. }
  }
  { inv LOCAL. inv CANCEL.
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

Lemma sim_local_read
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      lc2_tgt
      loc ts val released_tgt ord_src ord_tgt
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (ORD: Ordering.le ord_src ord_tgt)
      (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF1_TGT: Global.wf gl1_tgt)
      (STEP_TGT: Local.read_step lc1_tgt gl1_tgt loc ts val released_tgt ord_tgt lc2_tgt):
  exists released_src lc2_src,
    <<REL: View.opt_le released_src released_tgt>> /\
    <<STEP_SRC: Local.read_step lc1_src gl1_src loc ts val released_src ord_src lc2_src>> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>>.
Proof.
  inv LOCAL1. inv GLOBAL1. inv STEP_TGT.
  exploit sim_memory_get; try apply GET; eauto. i. des.
  inv MSG. esplits; eauto.
  - econs; eauto; (try by etrans; eauto).
    eapply TViewFacts.readable_mon; eauto. apply TVIEW.
  - econs; eauto. s. apply TViewFacts.read_tview_mon; auto.
    + apply LC_WF1_TGT.
    + inv GL_WF1_TGT. inv MEM_CLOSED.
      exploit CLOSED; eauto. i. des. inv MSG_WF. auto.
Qed.

Lemma ord_implb
      ord_src ord_tgt ord
      (ORD: Ordering.le ord_src ord_tgt):
  implb (Ordering.le ord_tgt ord) (Ordering.le ord_src ord).
Proof.
  destruct ord_src, ord_tgt, ord; ss.
Qed.

Lemma sim_local_fulfill
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      loc ord_src ord_tgt prm2 gprm2
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (ORD: Ordering.le ord_src ord_tgt)
      (FULFILL_TGT: Promises.fulfill lc1_tgt.(Local.promises) gl1_tgt.(Global.promises) loc ord_tgt prm2 gprm2):
  Promises.fulfill lc1_src.(Local.promises) gl1_src.(Global.promises) loc ord_src prm2 gprm2.
Proof.
  destruct lc1_src, lc1_tgt, gl1_src, gl1_tgt.
  inv LOCAL1. inv GLOBAL1. ss. subst.
  inv FULFILL_TGT; eauto.
Qed.

Lemma sim_local_write
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      lc2_tgt gl2_tgt
      loc from to val releasedm_src releasedm_tgt released_tgt ord_src ord_tgt
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (ORD: Ordering.le ord_src ord_tgt)
      (LC_WF1_SRC: Local.wf lc1_src gl1_src)
      (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (RELM: View.opt_le releasedm_src releasedm_tgt)
      (RELM_WF_SRC: View.opt_wf releasedm_src)
      (RELM_WF_TGT: View.opt_wf releasedm_tgt)
      (STEP_TGT: Local.write_step lc1_tgt gl1_tgt loc from to val releasedm_tgt released_tgt ord_tgt lc2_tgt gl2_tgt):
  exists released_src lc2_src gl2_src,
    <<STEP_SRC: Local.write_step lc1_src gl1_src loc from to val releasedm_src released_src ord_src lc2_src gl2_src>> /\
    <<RELEASED: View.opt_le released_src released_tgt>> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
    <<GLOBAL2: sim_global gl2_src gl2_tgt>>.
Proof.
  inv STEP_TGT.
  exploit sim_local_fulfill; eauto. intro FULFILL_SRC.
  assert (RELT_LE:
   View.opt_le
     (TView.write_released (Local.tview lc1_src) loc to releasedm_src ord_src)
     (TView.write_released (Local.tview lc1_tgt) loc to releasedm_tgt ord_tgt)).
  { apply TViewFacts.write_released_mon; ss.
    - apply LOCAL1.
    - apply LC_WF1_TGT.
  }
  assert (RELT_WF:
   View.opt_wf (TView.write_released (Local.tview lc1_src) loc to releasedm_src ord_src)).
  { unfold TView.write_released. condtac; econs.
    repeat (try condtac; viewtac; try apply LC_WF1_SRC).
  }
  exploit sim_memory_add_exists; try exact WRITE.
  { econs 1. exact RELT_WF. }
  { econs 1; try exact RELT_LE; try refl.
    eapply ord_implb. eassumption.
  }
  { apply GLOBAL1. }
  i. des. esplits.
  - econs; eauto.
    eapply TViewFacts.writable_mon; try exact WRITABLE; eauto. apply LOCAL1.
  - ss.
  - econs; eauto; s; try apply LOCAL1.
    apply TViewFacts.write_tview_mon; ss; try apply LOCAL1.
    apply LC_WF1_TGT.
  - econs; ss; try apply GLOBAL1.
Qed.

Lemma sim_local_update
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      loc ts1 val1 released1_tgt ord1_src ord1_tgt lc2_tgt
      from2 to2 val2 released2_tgt ord2_src ord2_tgt lc3_tgt gl3_tgt
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (ORD1: Ordering.le ord1_src ord1_tgt)
      (ORD2: Ordering.le ord2_src ord2_tgt)
      (LC_WF1_SRC: Local.wf lc1_src gl1_src)
      (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF1_SRC: Global.wf gl1_src)
      (GL_WF1_TGT: Global.wf gl1_tgt)
      (STEP1_TGT: Local.read_step lc1_tgt gl1_tgt loc ts1 val1 released1_tgt ord1_tgt lc2_tgt)
      (STEP2_TGT: Local.write_step lc2_tgt gl1_tgt loc from2 to2 val2
                    released1_tgt released2_tgt ord2_tgt lc3_tgt gl3_tgt):
  exists released1_src released2_src lc2_src lc3_src gl3_src,
    <<STEP1_SRC: Local.read_step lc1_src gl1_src loc ts1 val1 released1_src ord1_src lc2_src>> /\
    <<STEP2_SRC: Local.write_step lc2_src gl1_src loc from2 to2 val2 
                   released1_src released2_src ord2_src lc3_src gl3_src>> /\
    <<REL1: View.opt_le released1_src released1_tgt>> /\
    <<REL2: View.opt_le released2_src released2_tgt>> /\
    <<LOCAL3: sim_local lc3_src lc3_tgt>> /\
    <<GLOBAL3: sim_global gl3_src gl3_tgt>>.
Proof.
  exploit sim_local_read; try exact STEP1_TGT; eauto. i. des.
  exploit Local.read_step_future; try exact STEP1_TGT; eauto. i. des.
  exploit Local.read_step_future; try exact STEP_SRC; eauto. i. des.
  hexploit sim_local_write; eauto. i. des.
  esplits; eauto.
Qed.

Lemma sim_local_fence
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      lc2_tgt gl2_tgt
      ordr_src ordw_src
      ordr_tgt ordw_tgt
      (STEP_TGT: Local.fence_step lc1_tgt gl1_tgt ordr_tgt ordw_tgt lc2_tgt gl2_tgt)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (LC_WF1_SRC: Local.wf lc1_src gl1_src)
      (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
      (ORDR: Ordering.le ordr_src ordr_tgt)
      (ORDW: Ordering.le ordw_src ordw_tgt):
  exists lc2_src gl2_src,
    <<STEP_SRC: Local.fence_step lc1_src gl1_src ordr_src ordw_src lc2_src gl2_src>> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
    <<GLOBAL2: sim_global gl2_src gl2_tgt>>.
Proof.
  inv GLOBAL1. inv STEP_TGT.
  esplits; eauto.
  - econs; eauto. i.
    erewrite sim_local_promises_bot; eauto.
  - econs; try apply LOCAL1. s.
    apply TViewFacts.write_fence_tview_mon; auto; try refl; cycle 1.
    { eapply TViewFacts.read_fence_future; apply LC_WF1_SRC. }
    apply TViewFacts.read_fence_tview_mon; auto; try refl.
    + apply LOCAL1.
    + apply LC_WF1_TGT.
  - econs; ss.
    apply TViewFacts.write_fence_sc_mon; auto; try refl.
    apply TViewFacts.read_fence_tview_mon; auto; try refl.
    + apply LOCAL1.
    + apply LC_WF1_TGT.
Qed.

Lemma sim_local_is_racy
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      loc to ord_src ord_tgt
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (ORD: Ordering.le ord_src ord_tgt)
      (RACE_TGT: Local.is_racy lc1_tgt gl1_tgt loc to ord_tgt):
  <<RACE_SRC: Local.is_racy lc1_src gl1_src loc to ord_src>>.
Proof.
  inv LOCAL1. inv GLOBAL1.
  inv RACE_TGT; [econs 1; congr|].
  exploit sim_memory_get; eauto. i. des. inv MSG0.
  econs; eauto.
  - eapply TViewFacts.racy_view_mon; eauto. apply TVIEW.
  - i. exploit MSG; try by destruct ord_src, ord_tgt; ss.
    i. subst. destruct na1; ss.
Qed.

Lemma sim_local_racy_read
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      loc to val ord_src ord_tgt
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (ORD: Ordering.le ord_src ord_tgt)
      (STEP_TGT: Local.racy_read_step lc1_tgt gl1_tgt loc to val ord_tgt):
  <<STEP_SRC: Local.racy_read_step lc1_src gl1_src loc to val ord_src>>.
Proof.
  inv STEP_TGT.
  exploit sim_local_is_racy; eauto.
Qed.

Lemma sim_local_racy_write
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      loc to ord_src ord_tgt
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (ORD: Ordering.le ord_src ord_tgt)
      (STEP_TGT: Local.racy_write_step lc1_tgt gl1_tgt loc to ord_tgt):
  <<STEP_SRC: Local.racy_write_step lc1_src gl1_src loc to ord_src>>.
Proof.
  inv STEP_TGT.
  exploit sim_local_is_racy; eauto.
Qed.

Lemma sim_local_racy_update
      lc1_src gl1_src
      lc1_tgt gl1_tgt
      loc to ordr_src ordw_src ordr_tgt ordw_tgt
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (GLOBAL1: sim_global gl1_src gl1_tgt)
      (ORDR: Ordering.le ordr_src ordr_tgt)
      (ORDW: Ordering.le ordw_src ordw_tgt)
      (STEP_TGT: Local.racy_update_step lc1_tgt gl1_tgt loc to ordr_tgt ordw_tgt):
  <<STEP_SRC: Local.racy_update_step lc1_src gl1_src loc to ordr_src ordw_src>>.
Proof.
  inv STEP_TGT; eauto.
  exploit sim_local_is_racy; try exact RACE; eauto.
Qed.

Lemma sim_local_program_step
      lang
      th1_src
      th1_tgt th2_tgt e_tgt
      (STATE1: (Thread.state th1_src) = (Thread.state th1_tgt))
      (LOCAL1: sim_local (Thread.local th1_src) (Thread.local th1_tgt))
      (GLOBAL1: sim_global (Thread.global th1_src) (Thread.global th1_tgt))
      (LC_WF1_SRC: Local.wf (Thread.local th1_src) (Thread.global th1_src))
      (LC_WF1_TGT: Local.wf (Thread.local th1_tgt) (Thread.global th1_tgt))
      (GL_WF1_SRC: Global.wf (Thread.global th1_src))
      (GL_WF1_TGT: Global.wf (Thread.global th1_tgt))
      (STEP_TGT: @Thread.step lang e_tgt th1_tgt th2_tgt)
      (EVENT: ThreadEvent.is_program e_tgt):
  exists e_src th2_src,
    <<STEP_SRC: @Thread.step lang e_src th1_src th2_src>> /\
    <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
    <<STATE2: (Thread.state th2_src) = (Thread.state th2_tgt)>> /\
    <<LOCAL2: sim_local (Thread.local th2_src) (Thread.local th2_tgt)>> /\
    <<GLOBAL2: sim_global (Thread.global th2_src) (Thread.global th2_tgt)>>.
Proof.
  destruct th1_src as [st1_src lc1_src gl1_src],
      th1_tgt as [st1_tgt lc1_tgt gl1_tgt]. ss. subst.
  inv STEP_TGT; ss.
  { exploit sim_local_internal; eauto. i. des.
    esplits; eauto.
  }
  inv LOCAL; ss.
  - esplits; (try by econs; [|econs 1]; eauto); ss.
  - exploit sim_local_read; eauto; try refl. i. des.
    esplits; (try by econs; [|econs 2]; eauto); ss.
  - exploit sim_local_write; eauto; try refl. i. des.
    esplits; (try by econs; [|econs 3]; eauto); ss.
  - exploit sim_local_update; eauto; try refl. i. des.
    esplits; (try by econs; [|econs 4]; eauto); ss.
  - exploit sim_local_fence; eauto; try refl. i. des.
    esplits; (try by econs; [|econs 5]; eauto); ss.
  - exploit sim_local_fence; eauto; try refl. i. des.
    esplits; (try by econs; [|econs 6]; eauto); ss.
  - esplits; (try by econs; [|econs 7]; eauto); ss.
  - exploit sim_local_racy_read; eauto; try refl. i. des.
    esplits; (try by econs; [|econs 8]; eauto); ss.
  - exploit sim_local_racy_write; eauto; try refl. i. des.
    esplits; (try by econs; [|econs 9]; eauto); ss.
  - exploit sim_local_racy_update; eauto; try refl. i. des.
    esplits; (try by econs; [|econs 10]; eauto); ss.
Qed.
