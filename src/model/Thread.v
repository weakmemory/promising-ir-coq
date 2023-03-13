Require Import Bool.
Require Import RelationClasses.

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
Require Import TView.
Require Import Global.
Require Import Local.

Set Implicit Arguments.


Variant tau T (step: forall (e:ThreadEvent.t) (th1 th2:T), Prop) (th1 th2:T): Prop :=
| tau_intro
    e
    (TSTEP: step e th1 th2)
    (EVENT: ThreadEvent.get_machine_event e = MachineEvent.silent)
.
#[export] Hint Constructors tau: core.

Variant union E T (step: forall (e:E) (th1 th2:T), Prop) (th1 th2:T): Prop :=
| union_intro
    e
    (USTEP: step e th1 th2)
.
#[export] Hint Constructors union: core.

Variant pstep E T (step: forall (e: E) (th1 th2: T), Prop) (P: E -> Prop) (th1 th2: T): Prop :=
| pstep_intro
    e
    (STEP: step e th1 th2)
    (EVENT: P e)
.
#[export] Hint Constructors pstep: core.

Lemma tau_mon T (step1 step2: forall (e:ThreadEvent.t) (th1 th2:T), Prop)
      (STEP: step1 <3= step2):
  tau step1 <2= tau step2.
Proof.
  i. inv PR. econs; eauto.
Qed.

Lemma union_mon E T (step1 step2: forall (e:E) (th1 th2:T), Prop)
      (STEP: step1 <3= step2):
  union step1 <2= union step2.
Proof.
  i. inv PR. econs; eauto.
Qed.

Lemma pstep_mon E T (step1 step2: forall (e:E) (th1 th2:T), Prop) P1 P2
      (STEP: step1 <3= step2)
      (P: P1 <1= P2):
  pstep step1 P1 <2= pstep step2 P2.
Proof.
  i. inv PR. econs; eauto.
Qed.

Lemma tau_union: tau <4= (@union ThreadEvent.t).
Proof.
  ii. inv PR. econs. eauto.
Qed.

Lemma pstep_union E T step P:
  @pstep E T step P <2= @union E T step.
Proof.
  i. inv PR. eauto.
Qed.


Module Thread.
  Section Thread.
    Variable (lang: language).

    Structure t := mk {
      state: (Language.state lang);
      local: Local.t;
      global: Global.t;
    }.

    Variant step: forall (e: ThreadEvent.t) (th1 th2: t), Prop :=
    | step_internal
        e st lc1 gl1 lc2 gl2
        (LOCAL: Local.internal_step e lc1 gl1 lc2 gl2):
      step e (mk st lc1 gl1) (mk st lc2 gl2)
    | step_program
        e st1 lc1 gl1 st2 lc2 gl2
        (STATE: Language.step lang (ThreadEvent.get_program_event e) st1 st2)
        (LOCAL: Local.program_step e lc1 gl1 lc2 gl2):
      step e (mk st1 lc1 gl1) (mk st2 lc2 gl2)
    .
    Hint Constructors step: core.

    Definition tau_step := tau step.
    Hint Unfold tau_step: core.

    Definition all_step := union step.
    Hint Unfold all_step: core.

    Variant opt_step: forall (e:ThreadEvent.t) (th1 th2:t), Prop :=
      | step_none
          th:
        opt_step ThreadEvent.silent th th
      | step_some
          e th1 th2
          (STEP: step e th1 th2):
        opt_step e th1 th2
    .
    Hint Constructors opt_step: core.

    Variant internal_step: forall (th1 th2: t), Prop :=
    | interal_step_intro
        e st lc1 gl1 lc2 gl2
        (LOCAL: Local.internal_step e lc1 gl1 lc2 gl2):
      internal_step (mk st lc1 gl1) (mk st lc2 gl2)
    .
    Hint Constructors internal_step: core.

    Variant program_step: forall (e: ThreadEvent.t) (th1 th2: t), Prop :=
    | program_step_intro
        e st1 lc1 gl1 st2 lc2 gl2
        (STATE: Language.step lang (ThreadEvent.get_program_event e) st1 st2)
        (LOCAL: Local.program_step e lc1 gl1 lc2 gl2):
      program_step e (mk st1 lc1 gl1) (mk st2 lc2 gl2)
    .
    Hint Constructors program_step: core.

    Lemma tau_opt_tau
          th1 th2 th3 e
          (STEPS: rtc tau_step th1 th2)
          (STEP: opt_step e th2 th3)
          (EVENT: ThreadEvent.get_machine_event e = MachineEvent.silent):
      rtc tau_step th1 th3.
    Proof.
      induction STEPS.
      - inv STEP; eauto.
      - exploit IHSTEPS; eauto.
    Qed.

    Lemma tau_opt_all
          th1 th2 th3 e
          (STEPS: rtc tau_step th1 th2)
          (STEP: opt_step e th2 th3):
      rtc all_step th1 th3.
    Proof.
      induction STEPS.
      - inv STEP; eauto.
      - exploit IHSTEPS; eauto. i.
        econs 2; eauto.
        inv H. econs. eauto.
    Qed.


    (* consistency *)

    Definition cap_of (th: t): t :=
      mk (state th) (local th) (Global.cap_of (global th)).

    Variant steps_failure (th1: t): Prop :=
      | steps_failure_intro
          e th2 th3
          (STEPS: rtc tau_step th1 th2)
          (STEP_FAILURE: step e th2 th3)
          (EVENT_FAILURE: ThreadEvent.get_machine_event e = MachineEvent.failure)
    .

    Variant consistent (th: t): Prop :=
      | consistent_failure
          (FAILURE: steps_failure (cap_of th))
      | consistent_fulfill
          th2
          (STEPS: rtc tau_step (cap_of th) th2)
          (PROMISES: Local.promises (Thread.local th2) = BoolMap.bot)
    .

    Lemma cap_wf
          th
          (LC_WF: Local.wf (local th) (global th))
          (GL_WF: Global.wf (global th)):
      (<<LC_WF_CAP: Local.wf (local (cap_of th)) (global (cap_of th))>>) /\
      (<<GL_WF_CAP: Global.wf (global (cap_of th))>>).
    Proof.
      exploit Local.cap_wf; eauto.
      exploit Global.cap_wf; eauto.
    Qed.

    (* step_future *)

    Lemma step_future
          e th1 th2
          (STEP: step e th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.future (global th1) (global th2)>>.
    Proof.
      inv STEP; ss.
      - eauto using Local.internal_step_future.
      - eauto using Local.program_step_future.
    Qed.

    Lemma opt_step_future
          e th1 th2
          (STEP: opt_step e th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.future (global th1) (global th2)>>.
    Proof.
      inv STEP; eauto using step_future.
      esplits; eauto; refl.
    Qed.

    Lemma rtc_all_step_future
          th1 th2
          (STEP: rtc all_step th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.future (global th1) (global th2)>>.
    Proof.
      revert LC_WF1. induction STEP; i.
      - splits; ss; refl.
      - inv H. exploit step_future; eauto. i. des.
        exploit IHSTEP; eauto. i. des.
        splits; ss; etrans; eauto.
    Qed.

    Lemma rtc_tau_step_future
          th1 th2
          (STEP: rtc tau_step th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.future (global th1) (global th2)>>.
    Proof.
      apply rtc_all_step_future; auto.
      eapply rtc_implies; [|eauto].
      apply tau_union.
    Qed.

    Lemma internal_step_future
          th1 th2
          (STEP: internal_step th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.future (global th1) (global th2)>>.
    Proof.
      inv STEP; ss.
      eauto using Local.internal_step_future.
    Qed.

    Lemma rtc_internal_step_future
          th1 th2
          (STEP: rtc internal_step th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.future (global th1) (global th2)>>.
    Proof.
      revert LC_WF1. induction STEP; i.
      - splits; ss; refl.
      - exploit internal_step_future; eauto. i. des.
        exploit IHSTEP; eauto. i. des.
        splits; ss; etrans; eauto.
    Qed.

    Lemma program_step_future
          e th1 th2
          (STEP: program_step e th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.future (global th1) (global th2)>>.
    Proof.
      inv STEP; ss.
      eauto using Local.program_step_future.
    Qed.

    Lemma rtc_program_step_future
          th1 th2
          (STEP: rtc (tau program_step) th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.future (global th1) (global th2)>>.
    Proof.
      revert LC_WF1. induction STEP; i.
      - splits; ss; refl.
      - inv H. exploit program_step_future; eauto. i. des.
        exploit IHSTEP; eauto. i. des.
        splits; ss; etrans; eauto.
    Qed.


    (* step_inhabited *)

    Lemma step_inhabited
          e th1 th2
          (STEP: step e th1 th2)
          (INHABITED1: Memory.inhabited (Global.memory (global th1))):
      <<INHABITED2: Memory.inhabited (Global.memory (global th2))>>.
    Proof.
      inv STEP.
      - eapply Local.internal_step_inhabited; eauto.
      - eapply Local.program_step_inhabited; eauto.
    Qed.


    (* step_disjoint *)

    Lemma step_disjoint
          e th1 th2 lc
          (STEP: step e th1 th2)
          (DISJOINTH1: Local.disjoint (local th1) lc)
          (LC_WF: Local.wf lc (global th1)):
      <<DISJOINTH2: Local.disjoint (local th2) lc>> /\
      <<LC_WF: Local.wf lc (global th2)>>.
    Proof.
      inv STEP.
      - eapply Local.internal_step_disjoint; eauto.
      - eapply Local.program_step_disjoint; eauto.
    Qed.

    Lemma opt_step_disjoint
          e th1 th2 lc
          (STEP: opt_step e th1 th2)
          (DISJOINTH1: Local.disjoint (local th1) lc)
          (LC_WF: Local.wf lc (global th1)):
      <<DISJOINTH2: Local.disjoint (local th2) lc>> /\
      <<LC_WF: Local.wf lc (global th2)>>.
    Proof.
      inv STEP.
      - esplits; eauto.
      - eapply step_disjoint; eauto.
    Qed.

    Lemma rtc_all_step_disjoint
          th1 th2 lc
          (STEP: rtc all_step th1 th2)
          (DISJOINTH1: Local.disjoint (local th1) lc)
          (LC_WF: Local.wf lc (global th1)):
      <<DISJOINTH2: Local.disjoint (local th2) lc>> /\
      <<LC_WF: Local.wf lc (global th2)>>.
    Proof.
      revert DISJOINTH1 LC_WF. induction STEP; eauto. i.
      inv H. exploit step_disjoint; eauto. i. des. eauto.
    Qed.

    Lemma rtc_tau_step_disjoint
          th1 th2 lc
          (STEP: rtc tau_step th1 th2)
          (DISJOINTH1: Local.disjoint (local th1) lc)
          (LC_WF: Local.wf lc (global th1)):
      <<DISJOINTH2: Local.disjoint (local th2) lc>> /\
      <<LC_WF: Local.wf lc (global th2)>>.
    Proof.
      eapply rtc_all_step_disjoint; cycle 1; eauto.
      eapply rtc_implies; [|eauto].
      apply tau_union.
    Qed.

    Lemma program_step_promises
          e th1 th2
          (STEP: Thread.step e th1 th2)
          (EVENT: ThreadEvent.is_program e):
      BoolMap.le (Local.promises (local th2)) (Local.promises (local th1)) /\
      BoolMap.le (Global.promises (global th2)) (Global.promises (global th1)).
    Proof.
      inv STEP; try by (inv LOCAL; ss).
      eapply Local.program_step_promises; eauto.
    Qed.

    Lemma step_promises_minus
          e th1 th2
          (STEP: step e th1 th2):
      BoolMap.minus (Global.promises (Thread.global th1)) (Local.promises (Thread.local th1)) =
      BoolMap.minus (Global.promises (Thread.global th2)) (Local.promises (Thread.local th2)).
    Proof.
      inv STEP; s.
      - eapply Local.internal_step_promises_minus; eauto.
      - eapply Local.program_step_promises_minus; eauto.
    Qed.

    Lemma rtc_all_step_promises_minus
          th1 th2
          (STEPS: rtc all_step th1 th2):
      BoolMap.minus (Global.promises (Thread.global th1)) (Local.promises (Thread.local th1)) =
      BoolMap.minus (Global.promises (Thread.global th2)) (Local.promises (Thread.local th2)).
    Proof.
      induction STEPS; ss. inv H.
      exploit step_promises_minus; eauto. i. congr.
    Qed.

    Lemma rtc_tau_step_promises_minus
          th1 th2
          (STEPS: rtc tau_step th1 th2):
      BoolMap.minus (Global.promises (Thread.global th1)) (Local.promises (Thread.local th1)) =
      BoolMap.minus (Global.promises (Thread.global th2)) (Local.promises (Thread.local th2)).
    Proof.
      apply rtc_all_step_promises_minus.
      eapply rtc_implies; try exact STEPS.
      apply tau_union.
    Qed.


    (* step_strong_le *)

    Lemma step_strong_le
          e th1 th2
          (STEP: step e th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.strong_le (global th1) (global th2)>>
      \/
      exists e_race th2',
        <<STEP: step e_race th1 th2'>> /\
        <<EVENT: ThreadEvent.get_program_event e_race = ThreadEvent.get_program_event e>> /\
        <<RACE: ThreadEvent.get_machine_event e_race = MachineEvent.failure>>
    .
    Proof.
      inv STEP; ss.
      - eauto using Local.internal_step_strong_le.
      - hexploit Local.program_step_strong_le; eauto. i. des.
        { left. esplits; eauto. }
        { right. exists e_race. esplits; eauto. econs 2; eauto.
          rewrite EVENT. eauto.
        }
    Qed.

    Lemma opt_step_strong_le
          e th1 th2
          (STEP: opt_step e th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.strong_le (global th1) (global th2)>>
      \/
      exists e_race th2',
        <<STEP: step e_race th1 th2'>> /\
        <<EVENT: ThreadEvent.get_program_event e_race = ThreadEvent.get_program_event e>> /\
        <<RACE: ThreadEvent.get_machine_event e_race = MachineEvent.failure>>
    .
    Proof.
      inv STEP; eauto using step_strong_le.
      left. esplits; eauto; refl.
    Qed.

    Lemma rtc_tau_step_strong_le
          th1 th2
          (STEP: rtc tau_step th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.strong_le (global th1) (global th2)>>
          \/
      <<FAILURE: steps_failure th1>>
    .
    Proof.
      revert LC_WF1. induction STEP; i.
      - left. splits; ss; refl.
      - inv H. exploit step_strong_le; eauto. i. des.
        2:{ right. repeat red. econs; [refl| |]; eauto. }
        exploit IHSTEP; eauto. i. des.
        { left. splits; auto; etrans; eauto. }
        { inv FAILURE. right. econs.
          { econs 2.
            { econs; eauto. }
            { eauto. }
          }
          { eauto. }
          { eauto. }
        }
    Qed.


    (* internal and program step *)

    Lemma internal_step_tau_thread_step
          th1 th2
          (STEP: internal_step th1 th2)
      :
      tau_step th1 th2.
    Proof.
      inv STEP. econs 1; eauto. inv LOCAL; ss.
    Qed.

    Lemma program_step_thread_step
          e th1 th2
          (STEP: program_step e th1 th2)
      :
      step e th1 th2.
    Proof.
      inv STEP. econs 2; eauto.
    Qed.

    Lemma rtc_internal_step_rtc_tau_thread_step
          th1 th2
          (STEPS: rtc internal_step th1 th2)
      :
      rtc tau_step th1 th2.
    Proof.
      induction STEPS; eauto. econs 2; [|eauto].
      eapply internal_step_tau_thread_step; eauto.
    Qed.

    Lemma rtc_tau_program_step_rtc_tau_thread_step
          th1 th2
          (STEPS: rtc (tau program_step) th1 th2)
      :
      rtc tau_step th1 th2.
    Proof.
      induction STEPS; eauto. econs 2; [|eauto].
      inv H. econs; eauto. eapply program_step_thread_step; eauto.
    Qed.

  End Thread.
End Thread.
#[export] Hint Constructors Thread.step: core.
#[export] Hint Constructors Thread.opt_step: core.
#[export] Hint Constructors Thread.steps_failure: core.
#[export] Hint Constructors Thread.consistent: core.
