From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.
From PromisingLib Require Import Event.

Require Import Time.
Require Import View.
Require Import BoolMap.
Require Import Promises.
Require Import Reserves.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Global.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Set Implicit Arguments.


Module PFConfiguration.
  Variant step: forall (e: MachineEvent.t) (tid: Ident.t) (c1 c2: Configuration.t), Prop :=
  | step_intro
      e tid c1 lang st1 lc1 e2 st3 lc3 gl3
      (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
      (STEPS: rtc (Thread.pf_tau_step (Global.max_reserved (Configuration.global c1)))
                  (Thread.mk _ st1 lc1 (Configuration.global c1)) e2)
      (STEP: Thread.step (Global.max_reserved (Configuration.global c1)) true e
                         e2 (Thread.mk _ st3 lc3 gl3)):
      step (ThreadEvent.get_machine_event_pf e) tid
           c1
           (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) (Configuration.threads c1)) gl3)
  .
  #[global] Hint Constructors step: core.

  Variant normal_step (c1 c2: Configuration.t): Prop :=
  | normal_step_intro
      e tid
      (STEP: step e tid c1 c2)
      (EVENT: e <> MachineEvent.failure)
  .
  #[global] Hint Constructors normal_step: core.

  Variant all_step (c1 c2: Configuration.t): Prop :=
  | all_step_intro
      e tid
      (STEP: step e tid c1 c2)
  .
  #[global] Hint Constructors all_step: core.

  Variant opt_step: forall (e: MachineEvent.t) (tid: Ident.t) (c1 c2: Configuration.t), Prop :=
  | step_none
      tid c:
      opt_step MachineEvent.silent tid c c
  | step_some
      e tid c1 c2
      (STEP: step e tid c1 c2):
      opt_step e tid c1 c2
  .
  #[global] Hint Constructors opt_step: core.

  Definition tau_step := union (step MachineEvent.silent).

  Variant steps_failure (c1: Configuration.t): Prop :=
  | steps_failure_intro
      tid c2 c3
      (STEPS: rtc tau_step c1 c2)
      (FAILURE: step MachineEvent.failure tid c2 c3)
  .
  #[global] Hint Constructors steps_failure: core.

  Lemma step_future
        e tid c1 c2
        (STEP: step e tid c1 c2)
        (WF1: Configuration.wf c1):
    <<WF2: Configuration.wf c2>> /\
    <<GL_FUTURE: Global.future (Configuration.global c1) (Configuration.global c2)>>.
  Proof.
    inv WF1. inv WF. inv STEP; s.
    exploit THREADS; ss; eauto. i.
    exploit Thread.rtc_tau_step_future;
      try eapply rtc_implies; try eapply STEPS; eauto.
    { i. inv H. econs; eauto. }
    s. i. des.
    exploit Thread.step_future; eauto. s. i. des.
    splits; try by etrans; eauto.
    econs; ss. econs.
    - i. Configuration.simplify.
      + exploit THREADS; try apply TH1; eauto. i. des.
        exploit Thread.rtc_tau_step_disjoint;
          try eapply rtc_implies; try eapply STEPS; eauto.
        { i. inv H. econs; eauto. }
        s. i. des.
        exploit Thread.step_disjoint; eauto. s. i. des.
        symmetry. auto.
      + exploit THREADS; try apply TH2; eauto. i. des.
        exploit Thread.rtc_tau_step_disjoint;
          try eapply rtc_implies; try eapply STEPS; eauto.
        { i. inv H. econs; eauto. }
        s. i. des.
        exploit Thread.step_disjoint; eauto. i. des.
        auto.
      + eapply DISJOINT; [|eauto|eauto]. auto.
    - i. Configuration.simplify.
      exploit THREADS; try apply TH; eauto. i.
      exploit Thread.rtc_tau_step_disjoint;
        try eapply rtc_implies; try eapply STEPS; eauto.
      { i. inv H. econs; eauto. }
      s. i. des.
      exploit Thread.step_disjoint; eauto. s. i. des.
      auto.
  Qed.

  Lemma opt_step_future
        e tid c1 c2
        (STEP: opt_step e tid c1 c2)
        (WF1: Configuration.wf c1):
    <<WF2: Configuration.wf c2>> /\
    <<GL_FUTURE: Global.future (Configuration.global c1) (Configuration.global c2)>>.
  Proof.
    inv STEP.
    - splits; auto; refl.
    - eapply step_future; eauto.
  Qed.

  Lemma normal_step_future
        c1 c2
        (STEP: normal_step c1 c2)
        (WF1: Configuration.wf c1):
    <<WF2: Configuration.wf c2>> /\
    <<GL_FUTURE: Global.future (Configuration.global c1) (Configuration.global c2)>>.
  Proof.
    inv STEP. eauto using step_future.
  Qed.

  Lemma all_step_future
        c1 c2
        (STEP: all_step c1 c2)
        (WF1: Configuration.wf c1):
    <<WF2: Configuration.wf c2>> /\
    <<GL_FUTURE: Global.future (Configuration.global c1) (Configuration.global c2)>>.
  Proof.
    inv STEP. eauto using step_future.
  Qed.

  Lemma rtc_step_future
        c1 c2
        (STEPS: rtc tau_step c1 c2)
        (WF1: Configuration.wf c1):
    <<WF2: Configuration.wf c2>> /\
    <<GL_FUTURE: Global.future (Configuration.global c1) (Configuration.global c2)>>.
  Proof.
    induction STEPS; i.
    - splits; auto; refl.
    - inv H.
      exploit step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      splits; eauto; etrans; eauto.
  Qed.

  Lemma rtc_normal_step_future
        c1 c2
        (STEPS: rtc normal_step c1 c2)
        (WF1: Configuration.wf c1):
    <<WF2: Configuration.wf c2>> /\
    <<GL_FUTURE: Global.future (Configuration.global c1) (Configuration.global c2)>>.
  Proof.
    induction STEPS; i.
    - splits; auto; refl.
    - inv H.
      exploit step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      splits; eauto; etrans; eauto.
  Qed.

  Lemma rtc_all_step_future
        c1 c2
        (STEPS: rtc all_step c1 c2)
        (WF1: Configuration.wf c1):
    <<WF2: Configuration.wf c2>> /\
    <<GL_FUTURE: Global.future (Configuration.global c1) (Configuration.global c2)>>.
  Proof.
    induction STEPS; i.
    - splits; auto; refl.
    - inv H.
      exploit step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      splits; eauto; etrans; eauto.
  Qed.
End PFConfiguration.
