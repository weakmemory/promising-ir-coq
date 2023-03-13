Require Import RelationClasses.
Require Import Program.

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
Require Import Cell.
Require Import Memory.
(* Require Import MemoryFacts. *)
Require Import TView.
Require Import BoolMap.
Require Import Promises.
Require Import Local.
Require Import Global.
Require Import Thread.
Require Import Configuration.
Require Import Behavior.

Require Import Cover.
Require Import MemoryProps.
Require Import LowerMemory.
(* Require Import FulfillStep. *)
(* Require Import ReorderStepPromise. *)
(* Require Import Pred. *)
(* Require Import Trace. *)

Require Import LowerMemory.

Require Import Delayed.
Require Import LowerStep.
Require Import Owned.

Set Implicit Arguments.


Section DStep.
  Variable lang: language.

  (** delayed steps *)

  Variant dstep (e: ThreadEvent.t) (e1 e4: Thread.t lang): Prop :=
  | dstep_intro
      e2 e3
      (PROMISES: rtc (@Thread.internal_step _) e1 e2)
      (LOWERS: rtc (tau lower_step) e2 e3)
      (STEP_RELEASE: Thread.step e e3 e4)
      (EVENT_RELEASE: release_event e)
  .

  Variant dsteps: forall (e: MachineEvent.t) (e1 e2: Thread.t lang), Prop :=
  | dsteps_promises
      e1 e2 e3
      (DSTEPS: rtc (tau dstep) e1 e2)
      (PROMISES: rtc (@Thread.internal_step _) e2 e3):
    dsteps MachineEvent.silent e1 e3
  | dsteps_step
      e te e1 e2 e3
      (DSTEPS: rtc (tau dstep) e1 e2)
      (DSTEP: dstep te e2 e3)
      (EVENT: e = ThreadEvent.get_machine_event te):
    dsteps e e1 e3
  .

  Definition delayed_consistent (e1: Thread.t lang): Prop :=
    exists e e2,
      (<<DSTEPS: dsteps
                   e (Thread.mk _ (Thread.state e1) (Thread.local e1) (Global.cap_of (Thread.global e1))) e2>>) /\
      ((<<FAILURE: e = MachineEvent.failure>>) \/
       (exists e3,
           (<<SILENT: e = MachineEvent.silent>>) /\
           (<<STEPS: rtc (tau lower_step) e2 e3>>) /\
           (<<PROMISES: Local.promises (Thread.local e3) = BoolMap.bot>>))).

  Lemma dstep_future
        e e1 e2
        (STEP: dstep e e1 e2)
        (LC_WF1: Local.wf e1.(Thread.local) e1.(Thread.global))
        (GL_WF1: Global.wf e1.(Thread.global)):
    (<<LC_WF2: Local.wf e2.(Thread.local) e2.(Thread.global)>>) /\
      (<<GL_WF2: Global.wf e2.(Thread.global)>>) /\
      (<<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>>) /\
      (<<GL_FUTURE: Global.future e1.(Thread.global) e2.(Thread.global)>>).
  Proof.
    inv STEP.
    hexploit Thread.rtc_internal_step_future; eauto. i. des.
    hexploit lower_steps_future; eauto. i. des.
    hexploit Thread.step_future; eauto. i. des. splits; auto.
    { etrans; eauto. etrans; eauto. }
    { etrans; eauto. etrans; eauto. }
  Qed.

  Lemma rtc_dstep_future
        e1 e2
        (STEPS: rtc (tau dstep) e1 e2)
        (LC_WF1: Local.wf e1.(Thread.local) e1.(Thread.global))
        (GL_WF1: Global.wf e1.(Thread.global)):
    (<<LC_WF2: Local.wf e2.(Thread.local) e2.(Thread.global)>>) /\
      (<<GL_WF2: Global.wf e2.(Thread.global)>>) /\
      (<<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>>) /\
      (<<GL_FUTURE: Global.future e1.(Thread.global) e2.(Thread.global)>>).
  Proof.
    induction STEPS.
    { splits; auto; try by refl. }
    { inv H. hexploit dstep_future; eauto. i. des.
      hexploit IHSTEPS; eauto. i. des. splits; auto; try by (etrans; eauto). }
  Qed.

  Lemma dsteps_future
        e e1 e2
        (STEPS: dsteps e e1 e2)
        (LC_WF1: Local.wf e1.(Thread.local) e1.(Thread.global))
        (GL_WF1: Global.wf e1.(Thread.global)):
    (<<LC_WF2: Local.wf e2.(Thread.local) e2.(Thread.global)>>) /\
      (<<GL_WF2: Global.wf e2.(Thread.global)>>) /\
      (<<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>>) /\
      (<<GL_FUTURE: Global.future e1.(Thread.global) e2.(Thread.global)>>).
  Proof.
    inv STEPS.
    { hexploit rtc_dstep_future; eauto. i. des.
      hexploit Thread.rtc_internal_step_future; eauto. i. des.
      esplits; eauto; try by (etrans; eauto).
    }
    { hexploit rtc_dstep_future; eauto. i. des.
      hexploit dstep_future; eauto. i. des.
      esplits; eauto; try by (etrans; eauto).
    }
  Qed.

  Lemma dstep_rtc_all_step
        e e1 e2
        (STEP: dstep e e1 e2):
    rtc (@Thread.all_step lang) e1 e2.
  Proof.
    inv STEP.
    etrans.
    { eapply rtc_implies; try eapply PROMISES.
      i. inv H. econs; eauto.
    }
    etrans.
    { instantiate (1:=e3). clear - LOWERS. induction LOWERS; auto.
      transitivity y; auto.
      inv H. eapply lower_step_step; eauto.
    }
    econs 2; eauto. econs; eauto.
  Qed.

  Lemma dstep_rtc_tau_step
        e e1 e2
        (STEP: dstep e e1 e2)
        (SILENT: ThreadEvent.get_machine_event e = MachineEvent.silent):
    rtc (@Thread.tau_step lang) e1 e2.
  Proof.
    inv STEP.
    etrans.
    { eapply rtc_implies; try eapply PROMISES.
      i. inv H. econs; eauto. inv LOCAL; ss.
    }
    etrans.
    { instantiate (1:=e3). clear - LOWERS. induction LOWERS; auto.
      transitivity y; auto.
      eapply tau_lower_step_tau_step; eauto.
    }
    econs 2; eauto. econs; eauto.
  Qed.

  Lemma rtc_dstep_rtc_tau_step
        e1 e2
        (STEP: rtc (tau dstep) e1 e2):
    rtc (@Thread.tau_step lang) e1 e2.
  Proof.
    induction STEP; eauto. inv H.
    exploit dstep_rtc_tau_step; eauto. i.
    etrans; eauto.
  Qed.

  Lemma dsteps_rtc_all_step
        e e1 e2
        (STEP: dsteps e e1 e2):
    rtc (@Thread.all_step lang) e1 e2.
  Proof.
    inv STEP.
    - exploit rtc_dstep_rtc_tau_step; eauto. i.
      etrans.
      + eapply rtc_implies; try eapply x0.
        i. inv H. econs. eauto.
      + eapply rtc_implies; try eapply PROMISES.
        i. inv H. econs; eauto.
    - exploit rtc_dstep_rtc_tau_step; eauto. i.
      exploit dstep_rtc_all_step; eauto. i.
      etrans; [|eauto].
      eapply rtc_implies; try eapply x0.
      i. inv H. econs. eauto.
  Qed.

  Lemma dsteps_rtc_tau_step
        e e1 e2
        (STEP: dsteps e e1 e2)
        (SILENT: e = MachineEvent.silent):
    rtc (@Thread.tau_step lang) e1 e2.
  Proof.
    inv STEP.
    - exploit rtc_dstep_rtc_tau_step; eauto. i.
      etrans; eauto.
      eapply rtc_implies; try eapply PROMISES.
      i. inv H0. econs; eauto. inv LOCAL; ss.
    - exploit rtc_dstep_rtc_tau_step; eauto. i.
      exploit dstep_rtc_tau_step; eauto. i.
      etrans; eauto.
  Qed.

  Lemma dsteps_plus_step
        e e1 e3
        (STEP: dsteps e e1 e3):
    e = MachineEvent.silent /\ e1 = e3 \/
    exists e2 te,
      (<<STEPS: rtc (@Thread.tau_step lang) e1 e2>>) /\
      (<<STEP: Thread.step te e2 e3>>) /\
      (<<EVENT: ThreadEvent.get_machine_event te = e>>).
  Proof.
    inv STEP.
    { exploit rtc_dstep_rtc_tau_step; eauto. i.
      exploit rtc_implies; try eapply PROMISES.
      { i. instantiate (1 := @Thread.tau_step lang).
        inv H. econs; eauto. inv LOCAL; ss.
      }
      i. rewrite x1 in x0. clear e2 DSTEPS PROMISES x1.
      exploit rtc_tail; try exact x0. i. des; eauto.
      right. inv x2. esplits; eauto.
    }
    { exploit rtc_dstep_rtc_tau_step; eauto. i.
      inv DSTEP.
      exploit rtc_implies; try eapply PROMISES; i.
      { i. instantiate (1 := @Thread.tau_step lang).
        inv H. econs; eauto. inv LOCAL; ss.
      }
      exploit rtc_implies; try eapply LOWERS; i.
      { i. instantiate (1 := rtc (@Thread.tau_step lang)).
        eapply tau_lower_step_tau_step; eauto.
      }
      eapply rtc_join in x2.
      rewrite x2 in x1. rewrite x1 in x0.
      clear x1 x2 DSTEPS PROMISES LOWERS.
      right. esplits; eauto.
    }
  Qed.

  Lemma interal_steps_lower_steps_dstep_dstep th0 th1 th2 th3 e
        (INTERNALS: rtc (@Thread.internal_step _) th0 th1)
        (LOWERS: rtc (tau lower_step) th1 th2)
        (STEP: dstep e th2 th3)
        (LOCAL: Local.wf th0.(Thread.local) th0.(Thread.global))
        (GLOBAL: Global.wf th0.(Thread.global))
    :
    dstep e th0 th3.
  Proof.
    hexploit Thread.rtc_internal_step_future; eauto. i. des.
    inv STEP. hexploit reorder_lower_steps_internal_steps; eauto.
    i. des. econs.
    { etrans; eauto. }
    { etrans; eauto. }
    { eauto. }
    { eauto. }
  Qed.

  Lemma interal_steps_lower_steps_dsteps_dsteps th0 th1 th2 th3 e
        (INTERNALS: rtc (@Thread.internal_step _) th0 th1)
        (LOWERS: rtc (tau lower_step) th1 th2)
        (STEP: dsteps e th2 th3)
        (LOCAL: Local.wf th0.(Thread.local) th0.(Thread.global))
        (GLOBAL: Global.wf th0.(Thread.global))
        (EVENT: e <> MachineEvent.silent)
    :
    dsteps e th0 th3.
  Proof.
    inv STEP; ss. inv DSTEPS.
    { econs 2.
      { refl. }
      { eapply interal_steps_lower_steps_dstep_dstep; eauto. }
      { auto. }
    }
    { econs 2.
      { econs 2; [|eauto]. inv H. econs; [|eauto].
        eapply interal_steps_lower_steps_dstep_dstep; eauto.
      }
      { eauto. }
      { auto. }
    }
  Qed.

  Lemma failure_dfailure th0
        (FAILURE: Thread.steps_failure th0)
        (LOCAL: Local.wf th0.(Thread.local) th0.(Thread.global))
        (GLOBAL: Global.wf th0.(Thread.global))
    :
    exists th1, (<<FAILURE: dsteps MachineEvent.failure th0 th1>>).
  Proof.
    inv FAILURE. revert e th3 STEP_FAILURE EVENT_FAILURE LOCAL GLOBAL.
    induction STEPS; i.
    { esplits. econs.
      { refl. }
      { econs.
        { refl. }
        { refl. }
        { eauto. }
        destruct e; ss.
      }
      { auto. }
    }
    inv H. hexploit Thread.step_future; eauto. i. des.
    hexploit IHSTEPS; eauto. i. des.
    destruct (classic (release_event e0)).
    { esplits. inv FAILURE; ss. econs; [|eauto|eauto].
      econs 2; [|eauto]. econs; [|eapply EVENT]. econs.
      { refl. }
      { refl. }
      { eauto. }
      { eauto. }
    }
    hexploit split_step; eauto. i. des.
    { esplits. eapply interal_steps_lower_steps_dsteps_dsteps; eauto. ss. }
    { esplits. econs 2.
      { refl. }
      econs.
      { refl. }
      { refl. }
      { eauto. }
      { destruct e_race; ss. }
      { eauto. }
    }
  Qed.

  Lemma tau_dsteps_dsteps_dsteps th0 th1 th2 e
        (STEP0: dsteps MachineEvent.silent th0 th1)
        (STEP1: dsteps e th1 th2)
    :
    dsteps e th0 th2.
  Proof.
    inv STEP0; inv STEP1.
    { inv DSTEPS0.
      { econs 1; [eauto|]. etrans; eauto. }
      { inv H. inv TSTEP. econs 1; [|eauto].
        etrans; eauto. econs 2; [|eauto].
        econs; [|eauto]. econs.
        { etrans; eauto. }
        { eauto. }
        { eauto. }
        { eauto. }
      }
    }
    { inv DSTEPS0.
      { inv DSTEP. econs 2; [eauto| |eauto].
        econs; [|eauto|eauto|eauto]. etrans; eauto.
      }
      { inv H. inv TSTEP. econs 2; [|eauto|eauto].
        etrans; eauto. econs 2; [|eauto].
        econs; eauto. econs; [|eauto|eauto|eauto]. etrans; eauto.
      }
    }
    { econs 1; [|eapply PROMISES]. etrans; eauto. }
    { econs 2; [|eapply DSTEP0|]; auto. etrans; eauto. }
  Qed.

  Lemma rtc_tau_dstep_dsteps_dsteps th0 th1 th2 e
        (STEP0: rtc (tau dstep) th0 th1)
        (STEP1: dsteps e th1 th2)
    :
    dsteps e th0 th2.
  Proof.
    eapply tau_dsteps_dsteps_dsteps; [|eauto].
    econs 1; eauto.
  Qed.


  (** steps to delayed steps *)

  Variant delayed_thread (th_delayed th: Thread.t lang): Prop :=
  | delayed_thread_intro
      (DELAYED: delayed
                  _
                  (Thread.state th_delayed) (Thread.state th)
                  (Thread.local th_delayed) (Thread.local th)
                  (Thread.global th_delayed) (Thread.global th))
  .


  Lemma internal_step_strong_le
        th1 th2
        (STEP: @Thread.internal_step lang th1 th2)
        (LC_WF1: Local.wf (Thread.local th1) (Thread.global th1))
        (GL_WF1: Global.wf (Thread.global th1)):
    Global.strong_le (Thread.global th1) (Thread.global th2).
  Proof.
    inv STEP. hexploit Local.internal_step_strong_le; eauto.
    i. des. splits; auto.
  Qed.

  Lemma rtc_internal_step_strong_le
        th1 th2
        (STEPS: rtc (@Thread.internal_step lang) th1 th2)
        (LC_WF1: Local.wf (Thread.local th1) (Thread.global th1))
        (GL_WF1: Global.wf (Thread.global th1)):
    Global.strong_le (Thread.global th1) (Thread.global th2).
  Proof.
    revert LC_WF1 GL_WF1. induction STEPS; i.
    { refl. }
    hexploit internal_step_strong_le; eauto. i.
    hexploit Thread.internal_step_future; eauto. i. des.
    etrans; eauto.
  Qed.

  Lemma lower_step_strong_le
        e th1 th2
        (STEP: lower_step e th1 th2)
        (LC_WF1: Local.wf (Thread.local th1) (Thread.global th1))
        (GL_WF1: Global.wf (Thread.global th1)):
    (<<LE: Global.strong_le (Thread.global th1) (Thread.global th2)>>) \/
      exists e_race th2',
        (<<STEP: @Thread.step lang e_race th1 th2'>>) /\
          (<<RELEASE: release_event e_race>>) /\
          (<<EVENT: ThreadEvent.get_program_event e_race = ThreadEvent.get_program_event e>>) /\
          (<<RACE: ThreadEvent.get_machine_event e_race = MachineEvent.failure>>).
  Proof.
    inv STEP. des; subst.
    { inv STEP0. hexploit Local.program_step_strong_le; eauto. i. des; auto.
      right. esplits.
      { econs 2; [|eauto]; eauto. rewrite EVENT. eauto. }
      { destruct e_race; ss. }
      { eauto. }
      { auto. }
    }
    { inv STEP; [|inv LOCAL].
      hexploit Local.internal_step_strong_le; eauto.
      i. des. splits; auto.
      inv STEP0. hexploit Local.program_step_strong_le; eauto. i. des.
      { left. etrans; eauto. }
      right. inv LOCAL. inv LOCAL1. ss. inv CANCEL.
      inv STEP; ss. inv LOCAL. clarify. esplits.
      { econs 2; cycle 1.
        { eapply Local.program_step_racy_write. econs; eauto.
          instantiate (1:=Ordering.na). instantiate (1:=to0). instantiate (1:=loc).
          inv RACE0.
          { econs 1; eauto. }
          { econs 2; eauto. erewrite Memory.remove_o in GET; eauto.
            des_ifs. eauto.
          }
        }
        { eauto. }
      }
      { ss. }
      { eauto. }
      { eauto. }
    }
  Qed.

  Lemma rtc_tau_lower_step_strong_le
        th1 th2
        (STEPS: rtc (tau (@lower_step lang)) th1 th2)
        (LC_WF1: Local.wf (Thread.local th1) (Thread.global th1))
        (GL_WF1: Global.wf (Thread.global th1)):
    (<<LE: Global.strong_le (Thread.global th1) (Thread.global th2)>>) \/
      exists e_race th1' th2',
        (<<STEPS: rtc (tau (@lower_step lang)) th1 th1'>>) /\
          (<<STEP: @Thread.step lang e_race th1' th2'>>) /\
          (<<RELEASE: release_event e_race>>) /\
          (<<RACE: ThreadEvent.get_machine_event e_race = MachineEvent.failure>>).
  Proof.
    revert LC_WF1 GL_WF1. induction STEPS; i.
    { left. r. refl. }
    { inv H. hexploit lower_step_strong_le; eauto. i. des.
      2:{ right. esplits; eauto. }
      hexploit lower_step_future; eauto. i. des.
      hexploit IHSTEPS; eauto. i. des.
      { left. r. etrans; eauto. }
      { right. esplits.
        { econs 2; eauto. }
        { eauto. }
        { eauto. }
        { eauto. }
      }
    }
  Qed.

  Lemma dstep_strong_le
        th1 th2 e
        (STEP: dstep e th1 th2)
        (LC_WF1: Local.wf (Thread.local th1) (Thread.global th1))
        (GL_WF1: Global.wf (Thread.global th1)):
    (<<LE: Global.strong_le (Thread.global th1) (Thread.global th2)>>) \/
      exists e_race th2',
        (<<STEP: dstep e_race th1 th2'>>) /\
          (<<RACE: ThreadEvent.get_machine_event e_race = MachineEvent.failure>>).
  Proof.
    inv STEP.
    hexploit rtc_internal_step_strong_le; eauto. i. des.
    hexploit Thread.rtc_internal_step_future; eauto. i. des.
    hexploit rtc_tau_lower_step_strong_le; eauto. i. des; cycle 1.
    { right. esplits; [..|eauto]. econs; eauto. }
    hexploit lower_steps_future; eauto. i. des.
    hexploit Thread.step_strong_le; eauto. i. des.
    { left. r. etrans; eauto. etrans; eauto. }
    { right. esplits; eauto. econs; eauto. destruct e_race; ss. }
  Qed.

  Lemma rtc_tau_dstep_strong_le
        th1 th2
        (STEPS: rtc (tau dstep) th1 th2)
        (LC_WF1: Local.wf (Thread.local th1) (Thread.global th1))
        (GL_WF1: Global.wf (Thread.global th1)):
    (<<LE: Global.strong_le (Thread.global th1) (Thread.global th2)>>) \/
      exists e_race th1' th2',
        (<<STEPS: rtc (tau dstep) th1 th1'>>) /\
          (<<STEP: dstep e_race th1' th2'>>) /\
          (<<RACE: ThreadEvent.get_machine_event e_race = MachineEvent.failure>>).
  Proof.
    revert LC_WF1 GL_WF1. induction STEPS; i.
    { left. r. refl. }
    inv H. hexploit dstep_strong_le; eauto. i. des; cycle 1.
    { right. esplits; eauto. }
    hexploit dstep_future; eauto. i. des.
    hexploit IHSTEPS; eauto. i. des.
    { left. r. etrans; eauto. }
    { right. esplits; [..|eauto|eauto]. econs 2; eauto. }
  Qed.

  Lemma dsteps_strong_le
        th1 th2 e
        (STEPS: dsteps e th1 th2)
        (LC_WF1: Local.wf (Thread.local th1) (Thread.global th1))
        (GL_WF1: Global.wf (Thread.global th1)):
    (<<LE: Global.strong_le (Thread.global th1) (Thread.global th2)>>) \/
      exists th2',
          (<<STEPS: dsteps MachineEvent.failure th1 th2'>>).
  Proof.
    inv STEPS.
    { hexploit rtc_tau_dstep_strong_le; eauto. i. des.
      { hexploit rtc_dstep_future; eauto. i. des.
        hexploit rtc_internal_step_strong_le; eauto.
        i. left. r. etrans; eauto.
      }
      { right. esplits. eapply rtc_tau_dstep_dsteps_dsteps.
        { eauto. }
        { econs 2; eauto. }
      }
    }
    { hexploit rtc_tau_dstep_strong_le; eauto. i. des.
      { hexploit rtc_dstep_future; eauto. i. des.
        hexploit dstep_strong_le; eauto.
        i. des.
        { left. r. etrans; eauto. }
        { right. esplits. econs 2; eauto. }
      }
      { right. esplits. econs 2; eauto. }
    }
  Qed.

  Lemma dsteps_promises_minus
        e th1 th2
        (STEP: dsteps e th1 th2):
    BoolMap.minus (Global.promises (Thread.global th1)) (Local.promises (Thread.local th1)) =
      BoolMap.minus (Global.promises (Thread.global th2)) (Local.promises (Thread.local th2)).
  Proof.
    eapply Thread.rtc_all_step_promises_minus.
    eapply dsteps_rtc_all_step; eauto.
  Qed.

  Lemma delayed_thread_delayed_global th_src0 th_tgt0
        (DELAYED: delayed_thread th_src0 th_tgt0)
        (LOCALSRC0: Local.wf th_src0.(Thread.local) th_src0.(Thread.global))
        (LOCALTGT0: Local.wf th_tgt0.(Thread.local) th_tgt0.(Thread.global))
        (GLOBALSRC0: Global.wf th_src0.(Thread.global))
        (GLOBALTGT0: Global.wf th_tgt0.(Thread.global))
    :
    delayed_global_private th_src0.(Thread.local) th_tgt0.(Thread.local) th_src0.(Thread.global) th_tgt0.(Thread.global).
  Proof.
    inv DELAYED. hexploit delayed_sync; eauto. i. des.
    eapply lower_steps_delayed_preserve; eauto.
  Qed.

  Lemma delayed_thread_step th_src0 th_tgt0 th_tgt1 e
        (STEP: Thread.step e th_tgt0 th_tgt1)
        (DELAYED: delayed_thread th_src0 th_tgt0)
        (LOCALSRC: Local.wf th_src0.(Thread.local) th_src0.(Thread.global))
        (LOCALTGT: Local.wf th_tgt0.(Thread.local) th_tgt0.(Thread.global))
        (GLOBALSRC: Global.wf th_src0.(Thread.global))
        (GLOBALTGT: Global.wf th_tgt0.(Thread.global))
        (CONSISTENT: ThreadEvent.get_machine_event e <> MachineEvent.failure -> rtc_consistent th_tgt1)
    :
    exists th_src1,
      ((<<STEP: dsteps (ThreadEvent.get_machine_event e) th_src0 th_src1>>) /\
         (<<DELAYED: delayed_thread th_src1 th_tgt1>>) /\
         (<<GLOBAL: delayed_global_public th_src1.(Thread.global) th_tgt1.(Thread.global)>>) /\
         (<<FUTURESRC: owned_future_global_promises
                         (BoolMap.minus th_src0.(Thread.global).(Global.promises) th_src0.(Thread.local).(Local.promises))
                         th_src0.(Thread.global) th_src1.(Thread.global)>>) /\
         (<<FUTURETGT: owned_future_global_promises
                         (BoolMap.minus th_src0.(Thread.global).(Global.promises) th_src0.(Thread.local).(Local.promises))
                         th_tgt0.(Thread.global) th_tgt1.(Thread.global)>>)) \/
        (<<FAILURE: dsteps MachineEvent.failure th_src0 th_src1>>)
  .
  Proof.
    inv DELAYED. destruct th_src0, th_tgt0, th_tgt1; ss.
    destruct (classic (release_event e)).
    { hexploit delayed_step_release; eauto. i. des.
      { esplits. left. esplits.
        { econs 2; [refl|..|].
          { econs; eauto. }
          { auto. }
        }
        { econs; eauto. }
        { eapply delayed_global_private_to_public; eauto. }
        { eauto. }
        { eauto. }
      }
      { hexploit failure_dfailure; eauto. i. des.
        esplits. right. eauto.
      }
    }
    { hexploit delayed_step_non_release; eauto. i. des.
      { esplits. left. esplits.
        { rewrite SILENT. econs 1; [refl|..]. eauto. }
        { econs; eauto. }
        { eapply delayed_global_private_to_public; eauto. }
        { eauto. }
        { eauto. }
      }
      { hexploit failure_dfailure; eauto. i. des.
        esplits. right. eauto.
      }
    }
  Qed.

  Lemma delayed_thread_bot th_src0 th_tgt0
        (DELAYED: delayed_thread th_src0 th_tgt0)
        (LOCALSRC: Local.wf th_src0.(Thread.local) th_src0.(Thread.global))
        (LOCALTGT: Local.wf th_tgt0.(Thread.local) th_tgt0.(Thread.global))
        (GLOBALSRC: Global.wf th_src0.(Thread.global))
        (GLOBALTGT: Global.wf th_tgt0.(Thread.global))
        (TERMINAL: Local.promises th_tgt0.(Thread.local) = BoolMap.bot)
    :
    exists th_src1,
      ((<<STEPS: rtc (tau lower_step) th_src0 th_src1>>) /\
         (<<GLOBAL: delayed_global_public th_src1.(Thread.global) th_tgt0.(Thread.global)>>) /\
         (<<FUTURESRC: owned_future_global_promises
                         (BoolMap.minus th_src0.(Thread.global).(Global.promises) th_src0.(Thread.local).(Local.promises))
                         th_src0.(Thread.global) th_src1.(Thread.global)>>) /\
         (<<STATE: th_src1.(Thread.state) = th_tgt0.(Thread.state)>>) /\
         (<<TERMINAL: Local.promises th_src1.(Thread.local) = BoolMap.bot>>)) \/
        (<<FAILURE: dsteps MachineEvent.failure th_src0 th_src1>>)
  .
  Proof.
    inv DELAYED. destruct th_src0, th_tgt0; ss.
    hexploit delayed_sync; eauto. i. des.
    esplits. left. esplits; eauto.
    { eapply delayed_global_private_to_public; eauto. }
    { eapply SimLocal.sim_local_is_terminal; eauto. }
  Qed.

  Lemma delayed_thread_steps th_src0 th_tgt0 th_tgt1
        (STEPS: rtc (@Thread.tau_step _) th_tgt0 th_tgt1)
        (DELAYED: delayed_thread th_src0 th_tgt0)
        (LOCALSRC: Local.wf th_src0.(Thread.local) th_src0.(Thread.global))
        (LOCALTGT: Local.wf th_tgt0.(Thread.local) th_tgt0.(Thread.global))
        (GLOBALSRC: Global.wf th_src0.(Thread.global))
        (GLOBALTGT: Global.wf th_tgt0.(Thread.global))
        (CONSISTENT: rtc_consistent th_tgt1)
      :
    exists th_src1,
      ((<<STEP: dsteps MachineEvent.silent th_src0 th_src1>>) /\
         (<<DELAYED: delayed_thread th_src1 th_tgt1>>) /\
         (<<GLOBAL: delayed_global_public th_src1.(Thread.global) th_tgt1.(Thread.global)>>) /\
         (<<FUTURESRC: owned_future_global_promises
                         (BoolMap.minus th_src0.(Thread.global).(Global.promises) th_src0.(Thread.local).(Local.promises))
                         th_src0.(Thread.global) th_src1.(Thread.global)>>) /\
         (<<FUTURETGT: owned_future_global_promises
                         (BoolMap.minus th_src0.(Thread.global).(Global.promises) th_src0.(Thread.local).(Local.promises))
                         th_tgt0.(Thread.global) th_tgt1.(Thread.global)>>)) \/
        (<<FAILURE: dsteps MachineEvent.failure th_src0 th_src1>>)
  .
  Proof.
    revert th_src0 DELAYED LOCALSRC LOCALTGT GLOBALSRC GLOBALTGT CONSISTENT.
    induction STEPS; i.
    { esplits. left. esplits; eauto.
      { econs 1; eauto. }
      { eapply delayed_global_private_to_public; eauto.
        eapply delayed_thread_delayed_global; eauto. }
      { refl. }
      { refl. }
    }
    inv H. hexploit Thread.step_future; eauto. i. des.
    hexploit Thread.step_promises_minus; eauto. i.
    hexploit delayed_thread_step; eauto.
    { i. eapply tau_steps_rtc_consistent; eauto. }
    i. des; cycle 1.
    { esplits. right. esplits; eauto. }
    hexploit dsteps_future; eauto. i. des.
    hexploit dsteps_promises_minus; eauto. i.
    rewrite EVENT in *.
    hexploit IHSTEPS; eauto. i. des; cycle 1.
    { esplits. right. eapply tau_dsteps_dsteps_dsteps; eauto. }
    esplits. left. esplits.
    { eapply tau_dsteps_dsteps_dsteps; eauto. }
    { eauto. }
    { eauto. }
    { etrans; eauto. rewrite H0. auto. }
    { etrans; eauto. rewrite H0. auto. }
  Qed.

  Lemma delayed_thread_future th_src0 th_tgt0 gl_src1 gl_tgt1
        (DELAYED: delayed_thread th_src0 th_tgt0)
        (GLOBAL: delayed_global_public gl_src1 gl_tgt1)
        (LOCALSRC0: Local.wf th_src0.(Thread.local) th_src0.(Thread.global))
        (LOCALTGT0: Local.wf th_tgt0.(Thread.local) th_tgt0.(Thread.global))
        (GLOBALSRC0: Global.wf th_src0.(Thread.global))
        (GLOBALTGT0: Global.wf th_tgt0.(Thread.global))
        (LOCALSRC1: Local.wf th_src0.(Thread.local) gl_src1)
        (LOCALTGT1: Local.wf th_tgt0.(Thread.local) gl_tgt1)
        (GLOBALSRC1: Global.wf gl_src1)
        (GLOBALTGT1: Global.wf gl_tgt1)
        (FUTURESRC: Global.strong_le th_src0.(Thread.global) gl_src1)
        (FUTURETGT: Global.le th_tgt0.(Thread.global) gl_tgt1)
        (OWNEDSRC: owned_future_global_promises th_src0.(Thread.local).(Local.promises) th_src0.(Thread.global) gl_src1)
        (OWNEDTGT: owned_future_global_promises th_src0.(Thread.local).(Local.promises) th_tgt0.(Thread.global) gl_tgt1)
    :
    (<<DELAYED: delayed_thread (Thread.mk _ th_src0.(Thread.state) th_src0.(Thread.local) gl_src1) (Thread.mk _ th_tgt0.(Thread.state) th_tgt0.(Thread.local) gl_tgt1)>>) \/
      exists th_src1, (<<FAILURE: dsteps MachineEvent.failure (Thread.mk _ th_src0.(Thread.state) th_src0.(Thread.local) gl_src1) th_src1>>).
  Proof.
    hexploit delayed_thread_delayed_global; eauto. i.
    inv DELAYED. hexploit delayed_future; eauto. i. des; cycle 1.
    { hexploit failure_dfailure; eauto. }
    left. r. econs; eauto.
  Qed.

  Lemma delayed_thread_consistent th_src0 th_tgt0
        (DELAYED: delayed_thread th_src0 th_tgt0)
        (LOCALSRC: Local.wf th_src0.(Thread.local) th_src0.(Thread.global))
        (LOCALTGT: Local.wf th_tgt0.(Thread.local) th_tgt0.(Thread.global))
        (GLOBALSRC: Global.wf th_src0.(Thread.global))
        (GLOBALTGT: Global.wf th_tgt0.(Thread.global))
        (CONSISTENT: Thread.consistent th_tgt0)
    :
    delayed_consistent th_src0.
  Proof.
    hexploit delayed_global_public_cap; eauto.
    { eapply delayed_global_private_to_public.
      eapply delayed_thread_delayed_global; eauto.
    }
    intros CAP.
    pose proof (Local.cap_wf LOCALSRC) as LOCALSRC1.
    pose proof (Local.cap_wf LOCALTGT) as LOCALTGT1.
    pose proof (Global.cap_wf GLOBALSRC) as GLOBALSRC1.
    pose proof (Global.cap_wf GLOBALTGT) as GLOBALTGT1.
    hexploit delayed_thread_future; eauto.
    { eapply Global.cap_strong_le; eauto. }
    { eapply Global.cap_le; eauto. }
    { eapply cap_owned_future_global_promises; eauto. }
    { eapply cap_owned_future_global_promises; eauto. }
    i. des; cycle 1.
    { r. esplits; eauto. }
    inv CONSISTENT.
    { inv FAILURE.
      hexploit Thread.rtc_tau_step_future; eauto. i. des.
      hexploit delayed_thread_steps; eauto.
      { eapply failure_rtc_consistent. econs; eauto. }
      i. des; ss; cycle 1.
      { r. esplits; eauto. }
      hexploit dsteps_future; eauto. i. des; s.
      hexploit delayed_thread_step; eauto.
      { i. ss. }
      i. des.
      { r. esplits.
        { eapply tau_dsteps_dsteps_dsteps; eauto. }
        { eauto. }
      }
      { r. esplits.
        { eapply tau_dsteps_dsteps_dsteps; eauto. }
        { eauto. }
      }
    }
    hexploit Thread.rtc_tau_step_future; eauto. i. des.
    hexploit delayed_thread_steps; eauto.
    { eapply bot_rtc_consistent; eauto. }
    i. des; cycle 1; ss.
    { r. esplits; eauto. }
    hexploit dsteps_future; eauto. i. des; ss.
    hexploit delayed_thread_bot; eauto. i. des.
    { r. esplits.
      { eauto. }
      { right. esplit; eauto. }
    }
    { r. esplits.
      { eapply tau_dsteps_dsteps_dsteps; eauto. }
      { eauto. }
    }
  Qed.

  Lemma delayed_thread_steps_full th_src0 th_tgt0
        gl_src1 gl_tgt1 th_tgt1 th_tgt2 e_tgt
        (DELAYED: delayed_thread th_src0 th_tgt0)
        (STEPS: rtc (@Thread.tau_step _) (Thread.mk _ th_tgt0.(Thread.state) th_tgt0.(Thread.local) gl_tgt1) th_tgt1)
        (STEP1: Thread.step e_tgt th_tgt1 th_tgt2)
        (GLOBAL: delayed_global_public gl_src1 gl_tgt1)
        (LOCALSRC: Local.wf th_src0.(Thread.local) th_src0.(Thread.global))
        (LOCALTGT: Local.wf th_tgt0.(Thread.local) th_tgt0.(Thread.global))
        (GLOBALSRC: Global.wf th_src0.(Thread.global))
        (GLOBALTGT: Global.wf th_tgt0.(Thread.global))
        (LOCALSRC1: Local.wf th_src0.(Thread.local) gl_src1)
        (LOCALTGT1: Local.wf th_tgt0.(Thread.local) gl_tgt1)
        (GLOBALSRC1: Global.wf gl_src1)
        (GLOBALTGT1: Global.wf gl_tgt1)
        (FUTURESRC: Global.strong_le th_src0.(Thread.global) gl_src1)
        (FUTURETGT: Global.le th_tgt0.(Thread.global) gl_tgt1)
        (OWNEDSRC: owned_future_global_promises th_src0.(Thread.local).(Local.promises) th_src0.(Thread.global) gl_src1)
        (OWNEDTGT: owned_future_global_promises th_src0.(Thread.local).(Local.promises) th_tgt0.(Thread.global) gl_tgt1)
        (CONSISTENT: ThreadEvent.get_machine_event e_tgt <> MachineEvent.failure -> Thread.consistent th_tgt2)
      :
    exists th_src1,
      ((<<STEP: dsteps (ThreadEvent.get_machine_event e_tgt) (Thread.mk _ th_src0.(Thread.state) th_src0.(Thread.local) gl_src1) th_src1>>) /\
         (<<DELAYED: delayed_thread th_src1 th_tgt2>>) /\
         (<<GLOBAL: delayed_global_public th_src1.(Thread.global) th_tgt2.(Thread.global)>>) /\
         (<<CONSISTENT: ThreadEvent.get_machine_event e_tgt <> MachineEvent.failure -> delayed_consistent th_src1>>) /\
         (<<FUTURESRC: owned_future_global_promises
                         (BoolMap.minus gl_src1.(Global.promises) th_src0.(Thread.local).(Local.promises))
                         gl_src1 th_src1.(Thread.global)>>) /\
         (<<FUTURETGT: owned_future_global_promises
                         (BoolMap.minus gl_src1.(Global.promises) th_src0.(Thread.local).(Local.promises))
                         gl_tgt1 th_tgt2.(Thread.global)>>)) \/
        (<<FAILURE: dsteps MachineEvent.failure (Thread.mk _ th_src0.(Thread.state) th_src0.(Thread.local) gl_src1) th_src1>>)
  .
  Proof.
    hexploit delayed_thread_future; eauto. i. des; cycle 1.
    { esplits; eauto. }
    hexploit Thread.rtc_tau_step_future; eauto. i. des.
    hexploit Thread.step_future; eauto. i. des.
    hexploit delayed_thread_steps; eauto.
    { eapply tau_steps_rtc_consistent; eauto.
      eapply step_rtc_consistent; eauto.
      i. eapply consistent_rtc_consistent. eapply CONSISTENT.
      rewrite H. ss.
    }
    i. des; eauto. hexploit dsteps_future; eauto. i. des.
    hexploit dsteps_promises_minus; eauto. i. ss.
    hexploit delayed_thread_step; eauto.
    { i. eapply consistent_rtc_consistent. eapply CONSISTENT; auto. }
    i. des; cycle 1.
    { esplits. right. eapply tau_dsteps_dsteps_dsteps; eauto. }
    { hexploit dsteps_future; eauto. i. des.
      esplits. left. esplits.
      { eapply tau_dsteps_dsteps_dsteps; eauto. }
      { eauto. }
      { eauto. }
      { i. eapply delayed_thread_consistent; eauto. }
      { etrans; eauto. rewrite H. auto. }
      { etrans; eauto. rewrite H. auto. }
    }
  Qed.

  Lemma delayed_thread_steps_terminal th_src0 th_tgt0
        gl_src1 gl_tgt1
        (DELAYED: delayed_thread th_src0 th_tgt0)
        (TERMINAL: Local.is_terminal th_tgt0.(Thread.local))
        (LANG: Language.is_terminal _ th_tgt0.(Thread.state))
        (GLOBAL: delayed_global_public gl_src1 gl_tgt1)
        (LOCALSRC: Local.wf th_src0.(Thread.local) th_src0.(Thread.global))
        (LOCALTGT: Local.wf th_tgt0.(Thread.local) th_tgt0.(Thread.global))
        (GLOBALSRC: Global.wf th_src0.(Thread.global))
        (GLOBALTGT: Global.wf th_tgt0.(Thread.global))
        (LOCALSRC1: Local.wf th_src0.(Thread.local) gl_src1)
        (LOCALTGT1: Local.wf th_tgt0.(Thread.local) gl_tgt1)
        (GLOBALSRC1: Global.wf gl_src1)
        (GLOBALTGT1: Global.wf gl_tgt1)
        (FUTURESRC: Global.strong_le th_src0.(Thread.global) gl_src1)
        (FUTURETGT: Global.le th_tgt0.(Thread.global) gl_tgt1)
        (OWNEDSRC: owned_future_global_promises th_src0.(Thread.local).(Local.promises) th_src0.(Thread.global) gl_src1)
        (OWNEDTGT: owned_future_global_promises th_src0.(Thread.local).(Local.promises) th_tgt0.(Thread.global) gl_tgt1)
    :
    exists th_src1,
      ((<<STEPS: rtc (tau lower_step) (Thread.mk _ th_src0.(Thread.state) th_src0.(Thread.local) gl_src1) th_src1>>) /\
         (<<GLOBAL: delayed_global_public th_src1.(Thread.global) gl_tgt1>>) /\
         (<<FUTURESRC: owned_future_global_promises
                         (BoolMap.minus gl_src1.(Global.promises) th_src0.(Thread.local).(Local.promises))
                         gl_src1 th_src1.(Thread.global)>>) /\
        (<<TERMINAL: Local.is_terminal th_src1.(Thread.local)>>) /\
        (<<LANG: Language.is_terminal _ th_src1.(Thread.state)>>)) \/
        (<<FAILURE: dsteps MachineEvent.failure (Thread.mk _ th_src0.(Thread.state) th_src0.(Thread.local) gl_src1) th_src1>>).
  Proof.
    hexploit delayed_thread_future; eauto. i. des; cycle 1.
    { esplits; eauto. }
    hexploit delayed_thread_bot; eauto.
    { eapply TERMINAL. }
    i. des; cycle 1.
    { esplits; eauto. }
    esplits. left. esplits; eauto.
    { rewrite STATE. auto. }
  Qed.

  Lemma delayed_thread_init st:
    delayed_thread (Thread.mk _ st Local.init Global.init) (Thread.mk _ st Local.init Global.init).
  Proof.
    econs; ss. r. esplits.
    { refl. }
    { refl. }
    econs.
    { refl. }
    { refl. }
    { ii. erewrite ! Memory.bot_get.
      destruct (Memory.get loc to Memory.init) as [[]|]; econs. refl.
    }
  Qed.

  Lemma delayed_global_public_init
    :
    delayed_global_public Global.init Global.init.
  Proof.
    econs.
    { refl. }
    { refl. }
    { ii. destruct (Memory.get loc to Memory.init) as [[]|]; econs. refl. }
  Qed.

  Variant past_delayed_thread: Thread.t lang -> Thread.t lang -> Prop :=
  | past_delayed_thread_intro
      st_src lc_src st_tgt lc_tgt gl_src gl_tgt
      gl_src0 gl_tgt0
      (DELAYED:
        delayed_thread (Thread.mk lang st_src lc_src gl_src0)
                       (Thread.mk lang st_tgt lc_tgt gl_tgt0))
      (FUTURESRC: Global.strong_le gl_src0 gl_src)
      (FUTURETGT: Global.le gl_tgt0 gl_tgt)
      (OWNEDSRC: owned_future_global_promises lc_src.(Local.promises) gl_src0 gl_src)
      (OWNEDTGT: owned_future_global_promises lc_src.(Local.promises) gl_tgt0 gl_tgt)
      (LOCALSRC: Local.wf lc_src gl_src0)
      (LOCALTGT: Local.wf lc_tgt gl_tgt0)
      (GLOBALSRC: Global.wf gl_src0)
      (GLOBALTGT: Global.wf gl_tgt0)
    :
    past_delayed_thread (Thread.mk lang st_src lc_src gl_src)
                        (Thread.mk lang st_tgt lc_tgt gl_tgt)
  .

  Lemma delayed_consistent_consistent
        e
        (CONSISTENT: delayed_consistent e):
    (<<CONSISTENT: Thread.consistent e>>).
  Proof.
    rr in CONSISTENT. des.
    { left.
      exploit dsteps_plus_step; eauto. i. des; subst; ss.
      econs; eauto.
    }
    { exploit dsteps_rtc_tau_step; eauto. i.
      esplits; try exact PROMISES. econs 2; [|eauto].
      etrans; eauto. eapply rtc_join.
      eapply rtc_implies; try exact STEPS.
      eapply tau_lower_step_tau_step.
    }
  Qed.

End DStep.


Module DConfiguration.
  Variant step: forall (e: MachineEvent.t) (tid: Ident.t) (c1 c2: Configuration.t), Prop :=
  | step_intro
      e tid c1 lang st1 lc1 st2 lc2 gl2
      (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
      (DSTEPS: dsteps e (Thread.mk _ st1 lc1 (Configuration.global c1))
                      (Thread.mk _ st2 lc2 gl2))
      (CONSISTENT: e <> MachineEvent.failure ->
                   delayed_consistent (Thread.mk _ st2 lc2 gl2)):
      step e tid c1
           (Configuration.mk (IdentMap.add tid (existT _ _ st2, lc2) (Configuration.threads c1)) gl2)
  .

  Variant terminal_step: forall (tid: Ident.t) (c1 c2: Configuration.t), Prop :=
  | terminal_step_intro
      tid c1 lang st1 lc1 st2 lc2 gl2
      (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
      (STEPS: rtc (tau lower_step)
                  (Thread.mk _ st1 lc1 (Configuration.global c1))
                  (Thread.mk _ st2 lc2 gl2))
      (TERMINAL: Language.is_terminal _ st2)
      (PROMISES: Local.is_terminal lc2):
      terminal_step tid c1
                    (Configuration.mk
                       (IdentMap.add tid (existT _ _ st2, lc2) (Configuration.threads c1))
                       gl2)
  .

  Inductive terminal_steps: forall (tids: list Ident.t) (c1 c2: Configuration.t), Prop :=
  | terminal_steps_nil
      c
      (TERMINAL: Configuration.is_terminal c):
      terminal_steps [] c c
  | terminal_steps_failure
      tid c1 c2 tids c3
      (NOTIN: ~ List.In tid tids)
      (STEP: step MachineEvent.failure tid c1 c2):
      terminal_steps (tid :: tids) c1 c3
  | terminal_steps_cons
      tid c1 c2 tids c3
      (NOTIN: ~ List.In tid tids)
      (STEP: terminal_step tid c1 c2)
      (STEPS: terminal_steps tids c2 c3):
      terminal_steps (tid :: tids) c1 c3
  .

  Lemma step_step
        e tid c1 c2
        (STEP: step e tid c1 c2):
    Configuration.opt_step e tid c1 c2.
  Proof.
    inv STEP.
    exploit dsteps_plus_step; eauto. i. des.
    - inv x1. destruct c1 as [threads sc mem]. ss.
      rewrite IdentMap.gsident; eauto.
    - subst. econs 2. econs; eauto. i.
      hexploit CONSISTENT; eauto. i.
      eapply delayed_consistent_consistent; eauto.
  Qed.

  Lemma terminal_step_step
        tid c1 c2
        (STEP: terminal_step tid c1 c2):
    Configuration.opt_step MachineEvent.silent tid c1 c2.
  Proof.
    inv STEP.
    exploit rtc_tail; eauto. i. des.
    - inv x1. inv TSTEP. destruct a2. ss.
      rewrite <- EVENT. des; clarify.
      { econs 2. econs; [eauto|..].
        + eapply rtc_join.
          eapply rtc_implies; try apply x0.
          eapply tau_lower_step_tau_step; eauto.
        + inv STEP. econs 2; eauto.
        + ii. econs 2; eauto. ss. inv PROMISES. auto.
      }
      { econs 2. econs; [eauto|..].
        + etrans.
          { eapply rtc_join.
            eapply rtc_implies; try apply x0.
            eapply tau_lower_step_tau_step; eauto.
          }
          { econs 2; [|refl]. econs; eauto. }
        + inv STEP. econs 2; eauto.
        + ii. econs 2; eauto. ss. inv PROMISES. auto.
      }
    - inv x0. destruct c1 as [threads sc mem]. ss.
      rewrite IdentMap.gsident; eauto.
  Qed.

  Lemma step_future c0 c1 e tid
        (STEP: step e tid c0 c1)
        (WF: Configuration.wf c0)
    :
      (<<WF2: Configuration.wf c1>>) /\
      (<<MEM_FUTURE: Global.future (Configuration.global c0) (Configuration.global c1)>>).
  Proof.
    inv WF. inv WF0. inv STEP; s.
    exploit THREADS; ss; eauto. i.
    hexploit dsteps_future; eauto. s. i. des.
    eapply dsteps_rtc_all_step in DSTEPS.
    splits; eauto. econs; ss. econs.
    - i. erewrite IdentMap.gsspec in *. des_ifs.
      + eapply inj_pair2 in H0. subst.
        exploit THREADS; try apply TH1; eauto. i.
        exploit Thread.rtc_all_step_disjoint; eauto. i. des. ss.
        symmetry. auto.
      + eapply inj_pair2 in H0. subst.
        exploit THREADS; try apply TH2; eauto. i. des.
        exploit Thread.rtc_all_step_disjoint; eauto. i. des.
        auto.
      + eapply DISJOINT; [|eauto|eauto]. auto.
    - i. erewrite IdentMap.gsspec in *. des_ifs.
      exploit THREADS; try apply TH; eauto. i.
      exploit Thread.rtc_all_step_disjoint; eauto. i. des.
      auto.
    - i. destruct (Local.promises lc2 loc) eqn:LGET.
      + exists tid, lang, st2, lc2. splits; ss.
        rewrite IdentMap.Facts.add_o. condtac; ss.
      + exploit Thread.rtc_all_step_promises_minus; try exact DSTEPS. s. i.
        eapply equal_f in x1.
        revert x1. unfold BoolMap.minus. rewrite GET, LGET. s. i.
        destruct (Global.promises (Configuration.global c0) loc) eqn:GET1; ss.
        destruct (Local.promises lc1 loc) eqn:LGET1; ss.
        exploit PROMISES; eauto. i. des.
        exists tid0, lang0, st, lc. splits; ss.
        rewrite IdentMap.Facts.add_o. condtac; ss. subst. congr.
  Qed.

  Lemma terminal_step_future c0 c1 tid
        (STEP: terminal_step tid c0 c1)
        (WF: Configuration.wf c0)
    :
      (<<WF2: Configuration.wf c1>>) /\
      (<<MEM_FUTURE: Global.future (Configuration.global c0) (Configuration.global c1)>>).
  Proof.
    inv WF. inv WF0. inv STEP; s.
    exploit THREADS; ss; eauto. i.
    exploit rtc_join.
    { eapply rtc_implies; [|apply STEPS].
      apply tau_lower_step_tau_step.
    }
    i. exploit Thread.rtc_tau_step_future; eauto. s. i. des.
    splits; eauto. econs; ss. econs.
    - i. erewrite IdentMap.gsspec in *. des_ifs.
      + eapply inj_pair2 in H0. subst.
        exploit THREADS; try apply TH1; eauto. i.
        exploit Thread.rtc_tau_step_disjoint; eauto. i. des. ss.
        symmetry. auto.
      + eapply inj_pair2 in H0. subst.
        exploit THREADS; try apply TH2; eauto. i. des.
        exploit Thread.rtc_tau_step_disjoint; eauto. i. des.
        auto.
      + eapply DISJOINT; [|eauto|eauto]. auto.
    - i. erewrite IdentMap.gsspec in *. des_ifs.
      exploit THREADS; try apply TH; eauto. i.
      exploit Thread.rtc_tau_step_disjoint; eauto. i. des.
      auto.
    - i. destruct (Local.promises lc2 loc) eqn:LGET.
      + exists tid, lang, st2, lc2. splits; ss.
        rewrite IdentMap.Facts.add_o. condtac; ss.
      + exploit Thread.rtc_tau_step_promises_minus; try exact x1. s. i.
        eapply equal_f in x2.
        revert x2. unfold BoolMap.minus. rewrite GET, LGET. s. i.
        destruct (Global.promises (Configuration.global c0) loc) eqn:GET1; ss.
        destruct (Local.promises lc1 loc) eqn:LGET1; ss.
        exploit PROMISES; eauto. i. des.
        exists tid0, lang0, st, lc. splits; ss.
        rewrite IdentMap.Facts.add_o. condtac; ss. subst. congr.
  Qed.

  Variant delayed_sl (gl_src gl_tgt: Global.t):
    forall (sl_src sl_tgt: {lang: language & Language.state lang} * Local.t), Prop :=
  | delayed_sl_intro
      lang st_src lc_src st_tgt lc_tgt
      (DELAYED:
        past_delayed_thread (Thread.mk lang st_src lc_src gl_src)
                       (Thread.mk lang st_tgt lc_tgt gl_tgt))
    :
    delayed_sl gl_src gl_tgt
          (existT _ lang st_src, lc_src)
          (existT _ lang st_tgt, lc_tgt)
  .

  Lemma delayed_sl_init lang st
    :
    delayed_sl Global.init Global.init (existT _ lang st, Local.init) (existT _ lang st, Local.init).
  Proof.
    econs.
    { econs.
      { eapply delayed_thread_init. }
      { refl. }
      { refl. }
      { refl. }
      { refl. }
      { eapply Local.init_wf. }
      { eapply Local.init_wf. }
      { eapply Global.init_wf. }
      { eapply Global.init_wf. }
    }
  Qed.

  Variant delayed_conf: forall (c_src c_tgt: Configuration.t), Prop :=
  | delayed_conf_intro
      ths_src gl_src
      ths_tgt gl_tgt
      (THS: forall tid,
          option_rel
            (delayed_sl gl_src gl_tgt)
            (IdentMap.find tid ths_src)
            (IdentMap.find tid ths_tgt))
      (GLOBAL: delayed_global_public gl_src gl_tgt)
    :
    delayed_conf (Configuration.mk ths_src gl_src)
                 (Configuration.mk ths_tgt gl_tgt)
  .

  Lemma delayed_conf_init s:
    delayed_conf (Configuration.init s) (Configuration.init s).
  Proof.
    econs.
    { i. unfold Threads.init.
      rewrite IdentMap.Facts.map_o. unfold option_map. des_ifs.
      ss. eapply delayed_sl_init.
    }
    { eapply delayed_global_public_init. }
  Qed.

  Lemma delayed_conf_step
        c1_src c1_tgt
        e tid c2_tgt
        (SIM: delayed_conf c1_src c1_tgt)
        (WF1_SRC: Configuration.wf c1_src)
        (WF1_TGT: Configuration.wf c1_tgt)
        (STEP: Configuration.step e tid c1_tgt c2_tgt):
    (exists c2_src,
        (<<STEP_SRC: step e tid c1_src c2_src>>) /\
          (<<SIM: delayed_conf c2_src c2_tgt>>)) \/
    (exists c2_src,
        (<<STEP_SRC: step MachineEvent.failure tid c1_src c2_src>>)).
  Proof.
    destruct c1_src as [ths1_src gl1_src],
             c1_tgt as [ths1_tgt gl1_tgt].
    inv SIM. inv STEP. ss.
    dup THS. specialize (THS tid). rewrite TID in THS.
    destruct (IdentMap.find tid ths1_src) as [[[lang_src st1_src] lc1_src]|] eqn:FIND_SRC; ss.
    inv THS. Configuration.simplify.
    dup WF1_SRC. inv WF1_SRC. ss.
    inv WF. exploit THREADS; eauto. intro WF1_SRC.
    clear DISJOINT THREADS.
    inv WF1_TGT. ss.
    inv WF. exploit THREADS; eauto. intro WF1_TGT.
    clear DISJOINT THREADS.
    inv DELAYED.
    hexploit Thread.rtc_tau_step_future; eauto. i. des.
    hexploit Thread.step_future; eauto. i. des.
    hexploit delayed_thread_steps_full; eauto. i. des; cycle 1.
    { destruct th_src1. right. esplits. econs; eauto. ss. }
    hexploit dsteps_future; eauto. i. des. ss.
    destruct th_src1.
    hexploit dsteps_strong_le; eauto. i. des; ss; cycle 1.
    { destruct th2'. right. esplits. econs; eauto. ss. }
    left. esplits.
    { econs; eauto. }
    { econs; eauto. i. rewrite ! IdentMap.gsspec. des_ifs.
      { econs; eauto. econs; eauto.
        { refl. }
        { refl. }
        { refl. }
        { refl. }
      }
      { specialize (THS0 tid0). ss. unfold option_rel in THS0. des_ifs.
        des. ss. inv THS0; ss. destruct lc1_src, lc_src.
        inv DELAYED1; ss. econs. econs; eauto.
        { etrans; eauto. }
        { etrans; eauto. eapply Global.future_le. etrans; eauto. }
        { etrans; eauto.
          eapply owned_future_global_promises_mon; eauto.
          eapply other_promise_included; eauto.
        }
        { etrans; eauto.
          eapply owned_future_global_promises_mon; eauto.
          eapply other_promise_included; eauto.
        }
      }
    }
  Qed.

  Lemma delayed_conf_terminal
        c_src c_tgt
        (LD: delayed_conf c_src c_tgt)
        (WF_SRC: Configuration.wf c_src)
        (WF_TGT: Configuration.wf c_tgt)
        (TERMINAL: Configuration.is_terminal c_tgt):
    exists c1_src,
      (<<STEP: terminal_steps
                 (IdentSet.elements (Threads.tids (Configuration.threads c_src)))
                 c_src c1_src>>).
  Proof.
    destruct c_src as [ths_src gl_src],
             c_tgt as [ths_tgt gl_tgt]. ss.
    remember (Threads.tids ths_src) as tids eqn:TIDS_SRC.
    assert (NOTIN: forall tid lang_src st_src lc_src
                     (FIND: IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src))
                     (TID: ~ List.In tid (IdentSet.elements tids)),
               Language.is_terminal _ st_src /\ Local.is_terminal lc_src).
    { i. destruct (IdentSet.mem tid tids) eqn:MEM.
      - exfalso. apply TID. rewrite IdentSet.mem_spec in MEM.
        rewrite <- IdentSet.elements_spec1 in MEM.
        clear - MEM. induction MEM; [econs 1|econs 2]; auto.
      - rewrite TIDS_SRC in MEM. rewrite Threads.tids_o in MEM.
        destruct (IdentMap.find tid ths_src) eqn:IFIND; [inv MEM|]. ss.
    }
    assert (IN: forall tid (TID: List.In tid (IdentSet.elements tids)),
               exists lang st_src lc_src st_tgt lc_tgt,
                 (<<FIND_SRC: IdentMap.find tid ths_src = Some (existT _ lang st_src, lc_src)>>) /\
                 (<<FIND_TGT: IdentMap.find tid ths_tgt = Some (existT _ lang st_tgt, lc_tgt)>>) /\
                 (<<LD_THREAD: past_delayed_thread
                                 (Thread.mk _ st_src lc_src gl_src)
                                 (Thread.mk _ st_tgt lc_tgt gl_tgt)>>)).
    { i. destruct (IdentSet.mem tid tids) eqn:MEM.
      - subst. dup MEM. rewrite Threads.tids_o in MEM0.
        inv LD. specialize (THS tid).
        destruct (IdentMap.find tid ths_src) as [[[lang_src st_src] lc_src]|] eqn:FIND_SRC; ss.
        destruct (IdentMap.find tid ths_tgt) as [[[lang_tgt st_tgt] lc_tgt]|] eqn:FIND_TGT; ss.
        inv THS. Configuration.simplify.
        esplits; eauto.
      - exfalso. subst.
        assert (SetoidList.InA eq tid (IdentSet.elements (Threads.tids ths_src))).
        { clear - TID. induction (IdentSet.elements (Threads.tids ths_src)); eauto. }
        rewrite IdentSet.elements_spec1 in H.
        rewrite <- IdentSet.mem_spec in H. congr.
    }
    assert (TIDS_MEM: forall tid, List.In tid (IdentSet.elements tids) -> IdentSet.mem tid tids = true).
    { i. rewrite IdentSet.mem_spec.
      rewrite <- IdentSet.elements_spec1.
      eapply SetoidList.In_InA; auto.
    }
    assert (NODUP: List.NoDup (IdentSet.elements tids)).
    { specialize (IdentSet.elements_spec2w tids). i.
      clear - H. induction H; econs; eauto.
    }
    assert (GLOBAL: delayed_global_public gl_src gl_tgt).
    { inv LD. eauto. }
    clear LD.
    revert NOTIN IN TIDS_MEM NODUP GLOBAL.
    revert ths_src gl_src WF_SRC TIDS_SRC WF_TGT.
    induction (IdentSet.elements tids); i.
    { esplits; [econs 1|..]. ii. eauto. }
    exploit (IN a); try by econs 1. i. des.
    exploit TERMINAL; eauto. i. des. inv THREAD.
    inv LD_THREAD.
    exploit delayed_thread_steps_terminal; try exact DELAYED; eauto; s.
    { eapply WF_SRC; eauto. }
    { eapply WF_TGT; eauto. }
    { eapply WF_SRC; eauto. }
    { eapply WF_TGT; eauto. }
    i. des; cycle 1.
    { destruct th_src1. esplits. econs 2; eauto.
      { inv NODUP. auto. }
      { econs; eauto. ss. }
    }
    hexploit lower_steps_future; eauto.
    { eapply WF_SRC; eauto. }
    { eapply WF_SRC; eauto. }
    i. des. ss.
    destruct th_src1 as [st1 lc1 gl1]. ss.
    hexploit rtc_tau_lower_step_strong_le; eauto.
    { eapply WF_SRC; eauto. }
    { eapply WF_SRC; eauto. }
    i. des; cycle 1.
    { destruct th1', th2'. esplits. econs 2; eauto.
      { inv NODUP. auto. }
      { econs; eauto.
        { econs; eauto. econs; eauto. }
        { ss. }
      }
    }
    assert (STEP_SRC: terminal_step
                        a
                        (Configuration.mk ths_src gl_src)
                        (Configuration.mk
                           (IdentMap.add a (existT _ _ st1, lc1) ths_src) gl1)).
    { econs; eauto. }
    exploit terminal_step_future; eauto. s. i. des.
    exploit IHl; try exact WF2; ss; eauto; i.
    { rewrite Threads.tids_add. rewrite IdentSet.add_mem; eauto. }
    { rewrite IdentMap.gsspec in FIND. revert FIND. condtac; ss; i.
      - subst. Configuration.simplify.
      - eapply NOTIN; eauto. ii. des; ss. subst. ss.
    }
    { exploit IN; eauto. i. des. inv NODUP.
      rewrite IdentMap.gso; try by (ii; subst; ss).
      esplits; eauto.
      inv LD_THREAD. destruct lc_src0, lc_src. ss. econs; eauto.
      { etrans; eauto. }
      { etrans; eauto.
        eapply owned_future_global_promises_mon; eauto.
        eapply other_promise_included; eauto.
        ii. subst. ss.
      }
    }
    { inv NODUP. ss. }
    des. esplits.
    econs 3; eauto. inv NODUP. ss.
    Unshelve. all: ss.
  Qed.

  Inductive delayed_behaviors:
    forall (conf:Configuration.t) (b:list Event.t) (f: bool), Prop :=
  | delayed_behaviors_nil
      c1 c2
      (STEP: terminal_steps
               (IdentSet.elements (Threads.tids (Configuration.threads c1)))
               c1 c2):
      delayed_behaviors c1 nil true
  | delayed_behaviors_syscall
      e1 e2 tid c1 c2 beh f
      (STEP: step (MachineEvent.syscall e2) tid c1 c2)
      (NEXT: delayed_behaviors c2 beh f)
      (EVENT: Event.le e1 e2):
      delayed_behaviors c1 (e1::beh) f
  | delayed_behaviors_failure
      tid c1 c2 beh f
      (STEP: step MachineEvent.failure tid c1 c2):
      delayed_behaviors c1 beh f
  | delayed_behaviors_tau
      tid c1 c2 beh f
      (STEP: step MachineEvent.silent tid c1 c2)
      (NEXT: delayed_behaviors c2 beh f):
      delayed_behaviors c1 beh f
  | delayed_behaviors_partial_term
      c:
      delayed_behaviors c [] false
  .

  Lemma delayed_conf_behavior
        c_src c_tgt
        (LD: delayed_conf c_src c_tgt)
        (WF_SRC: Configuration.wf c_src)
        (WF_tgt: Configuration.wf c_tgt):
    behaviors Configuration.step c_tgt <2= delayed_behaviors c_src.
  Proof.
    i. revert c_src LD WF_SRC. induction PR; i.
    - exploit delayed_conf_terminal; eauto. i. des.
      econs 1; eauto.
    - exploit delayed_conf_step; eauto. i. des; cycle 1.
      { eapply delayed_behaviors_failure; eauto. }
      exploit step_future; eauto. i. des.
      exploit Configuration.step_future; try exact STEP; eauto. i. des.
      econs 2; eauto.
    - exploit delayed_conf_step; eauto. i. des; cycle 1.
      { eapply delayed_behaviors_failure; eauto. }
      econs 3; eauto.
    - exploit delayed_conf_step; eauto. i. des; cycle 1.
      { eapply delayed_behaviors_failure; eauto. }
      exploit step_future; eauto. i. des.
      exploit Configuration.step_future; try exact STEP_SRC; eauto. i. des.
      econs 4; eauto.
    - econs 5.
  Qed.

  Lemma delayed_refinement
        s
    :
    behaviors Configuration.step (Configuration.init s) <2= delayed_behaviors (Configuration.init s).
  Proof.
    exploit delayed_conf_init; eauto. i.
    eapply delayed_conf_behavior; eauto.
    { eapply Configuration.init_wf. }
    { eapply Configuration.init_wf. }
  Qed.
End DConfiguration.
