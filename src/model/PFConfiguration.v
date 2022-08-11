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
  Variant estep: forall (e: ThreadEvent.t) (tid: Ident.t) (c1 c2: Configuration.t), Prop :=
    | estep_intro
        e tid c1 lang st1 lc1 st2 lc2 gl2
        (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
        (STEP: Thread.step TimeMap.bot true e
                           (Thread.mk _ st1 lc1 (Configuration.global c1))
                           (Thread.mk _ st2 lc2 gl2)):
      estep e tid
            c1
            (Configuration.mk (IdentMap.add tid (existT _ _ st2, lc2) (Configuration.threads c1)) gl2)
  .
  #[global] Hint Constructors estep: core.

  Variant all_step (c1 c2: Configuration.t): Prop :=
    | all_step_intro
        e tid
        (STEP: estep e tid c1 c2)
  .
  #[global] Hint Constructors all_step: core.

  Lemma estep_future
        e tid c1 c2
        (STEP: estep e tid c1 c2)
        (WF1: Configuration.wf c1):
    <<WF2: Configuration.wf c2>> /\
    <<GL_FUTURE: Global.future (Configuration.global c1) (Configuration.global c2)>>.
  Proof.
    inv WF1. inv WF. inv STEP; s.
    exploit THREADS; ss; eauto. i.
    exploit Thread.step_future; eauto. s. i. des.
    splits; eauto.
    econs; ss. econs.
    - i. Configuration.simplify.
      + exploit THREADS; try apply TH1; eauto. i. des.
        exploit Thread.step_disjoint; eauto. s. i. des.
        symmetry. auto.
      + exploit THREADS; try apply TH2; eauto. i. des.
        exploit Thread.step_disjoint; eauto. i. des.
        auto.
      + eapply DISJOINT; [|eauto|eauto]. auto.
    - i. Configuration.simplify.
      exploit THREADS; try apply TH; eauto. i.
      exploit Thread.step_disjoint; eauto. s. i. des.
      auto.
    - i. destruct (Local.promises lc2 loc) eqn:LGET.
      + exists tid, lang, st2, lc2. splits; ss.
        rewrite IdentMap.Facts.add_o. condtac; ss.
      + exploit Thread.step_promises_minus; try exact STEP0. s. i.
        eapply equal_f in x1.
        revert x1. unfold BoolMap.minus. rewrite GET, LGET. s. i.
        destruct (Global.promises (Configuration.global c1) loc) eqn:GET1; ss.
        destruct (Local.promises lc1 loc) eqn:LGET1; ss.
        exploit PROMISES; eauto. i. des.
        exists tid0, lang0, st, lc. splits; ss.
        rewrite IdentMap.Facts.add_o. condtac; ss. subst. congr.
    - i. destruct (Local.reserves lc2 loc) eqn:LGET.
      + exists tid, lang, st2, lc2. splits; ss.
        rewrite IdentMap.Facts.add_o. condtac; ss.
      + exploit Thread.step_reserves_minus; try exact STEP0. s. i.
        eapply equal_f in x1.
        revert x1. unfold BoolMap.minus. rewrite GET, LGET. s. i.
        destruct (Global.reserves (Configuration.global c1) loc) eqn:GET1; ss.
        destruct (Local.reserves lc1 loc) eqn:LGET1; ss.
        exploit RESERVES; eauto. i. des.
        exists tid0, lang0, st, lc. splits; ss.
        rewrite IdentMap.Facts.add_o. condtac; ss. subst. congr.
  Qed.

  Lemma all_step_future
        c1 c2
        (STEP: all_step c1 c2)
        (WF1: Configuration.wf c1):
    <<WF2: Configuration.wf c2>> /\
    <<GL_FUTURE: Global.future (Configuration.global c1) (Configuration.global c2)>>.
  Proof.
    inv STEP. eauto using estep_future.
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
      exploit estep_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      splits; eauto; etrans; eauto.
  Qed.

  Section PFConfiguration.
    Variable get_machine_event: ThreadEvent.t -> MachineEvent.t.

    Variant step: forall (e: MachineEvent.t) (tid: Ident.t) (c1 c2: Configuration.t), Prop :=
      | step_intro
          e tid c1 c2
          (STEP: estep e tid c1 c2):
        step (get_machine_event e) tid c1 c2
    .

    Variant normal_step (c1 c2: Configuration.t): Prop :=
      | normal_step_intro
          e tid
          (STEP: step e tid c1 c2)
          (EVENT: e <> MachineEvent.failure)
    .

    Variant opt_step: forall (e: MachineEvent.t) (tid: Ident.t) (c1 c2: Configuration.t), Prop :=
      | step_none
          tid c:
        opt_step MachineEvent.silent tid c c
      | step_some
          e tid c1 c2
          (STEP: step e tid c1 c2):
        opt_step e tid c1 c2
    .

    Definition tau_step := union (step MachineEvent.silent).

    Variant steps_failure (c1: Configuration.t): Prop :=
      | steps_failure_intro
          tid c2 c3
          (STEPS: rtc tau_step c1 c2)
          (FAILURE: step MachineEvent.failure tid c2 c3)
    .

    Lemma step_future
          e tid c1 c2
          (STEP: step e tid c1 c2)
          (WF1: Configuration.wf c1):
      <<WF2: Configuration.wf c2>> /\
      <<GL_FUTURE: Global.future (Configuration.global c1) (Configuration.global c2)>>.
    Proof.
      inv STEP. eauto using estep_future.
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

    Lemma rtc_tau_step_future
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

    Lemma program_step_step
          c1 tid lang st1 lc1
          e th2
          (FIND: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
          (STEP: Thread.step TimeMap.bot true e
                             (Thread.mk _ st1 lc1 (Configuration.global c1)) th2):
      step (get_machine_event e) tid
           c1
           (Configuration.mk
              (IdentMap.add tid (existT _ _ (Thread.state th2), Thread.local th2) (Configuration.threads c1))
              (Thread.global th2)).
    Proof.
      destruct th2. ss. econs. econs; eauto.
    Qed.
  End PFConfiguration.

  Lemma opt_program_step_opt_step
        c1 tid lang st1 lc1
        e th2
        (FIND: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
        (STEP: Thread.opt_step TimeMap.bot true e
                               (Thread.mk _ st1 lc1 (Configuration.global c1)) th2):
    opt_step ThreadEvent.get_machine_event_pf
             (ThreadEvent.get_machine_event_pf e) tid
             c1
             (Configuration.mk
                (IdentMap.add tid (existT _ _ (Thread.state th2), Thread.local th2) (Configuration.threads c1))
                (Thread.global th2)).
  Proof.
    destruct th2. ss. inv STEP.
    - destruct c1; ss.
      rewrite IdentMap.gsident; ss. econs.
    - econs 2. econs; eauto.
  Qed.

  Lemma rtc_program_step_rtc_step
        c1 tid lang st1 lc1
        th2
        (FIND: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
        (STEPS: rtc (tau (Thread.step TimeMap.bot true))
                    (Thread.mk _ st1 lc1 (Configuration.global c1)) th2):
    (<<STEPS: rtc (tau_step ThreadEvent.get_machine_event_pf)
                  c1
                  (Configuration.mk
                     (IdentMap.add tid (existT _ _ (Thread.state th2), Thread.local th2) (Configuration.threads c1))
                     (Thread.global th2))>>) \/
    exists c2 c3,
      (<<STEPS: rtc (tau_step ThreadEvent.get_machine_event_pf) c1 c2>>) /\
      (<<STEP: step ThreadEvent.get_machine_event_pf MachineEvent.failure tid c2 c3>>).
  Proof.
    destruct c1 as [ths1 gl1]. ss.
    remember (Thread.mk _ st1 lc1 gl1) as th1.
    replace st1 with (Thread.state th1) in FIND by (subst; ss).
    replace lc1 with (Thread.local th1) in FIND by (subst; ss).
    replace gl1 with (Thread.global th1) by (subst; ss).
    clear gl1 st1 lc1 Heqth1. revert ths1 FIND.
    induction STEPS; i; subst; ss.
    { left. rewrite IdentMap.gsident; ss. auto. }
    destruct x, y. inv H. ss.
    destruct (ThreadEvent.get_machine_event_pf e) eqn: PF_EVENT; cycle 1.
    { destruct e; ss. }
    { right. esplits; [refl|].
      rewrite <- PF_EVENT. econs. econs; eauto.
    }
    exploit (@program_step_step
               ThreadEvent.get_machine_event_pf (Configuration.mk ths1 global)); eauto. s. i.
    exploit (IHSTEPS
               (IdentMap.add tid (existT (Language.state (E:=ProgramEvent.t)) lang state0, local0) ths1));
      try apply IdentMap.gss.
    i. des.
    - rewrite IdentMap.add_add_eq in *.
      left. econs 2; eauto. econs. rewrite <- PF_EVENT. eauto.
    - right. esplits; try exact STEP.
      econs 2; eauto. econs. rewrite <- PF_EVENT. eauto.
  Qed.
End PFConfiguration.
#[export] Hint Constructors PFConfiguration.step: core.
#[export] Hint Constructors PFConfiguration.normal_step: core.
#[export] Hint Constructors PFConfiguration.opt_step: core.
#[export] Hint Constructors PFConfiguration.steps_failure: core.
