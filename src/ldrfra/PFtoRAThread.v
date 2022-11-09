Require Import Lia.
Require Import Bool.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
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
Require Import Thread.

Require Import OrdStep.
Require Import Writes.
Require Import WStep.
Require Import Stable.
Require Import PFtoRASim.

Set Implicit Arguments.


Module PFtoRAThread.
  Section PFtoRAThread.
    Variable lang: language.
    Variable L: Loc.t -> bool.

    (* well-formedness *)

    Variant wf_pf (e: Thread.t lang): Prop :=
    | wf_pf_intro
        (WF_LC: Local.wf (Thread.local e) (Thread.global e))
        (WF_GL: Global.wf (Thread.global e))
        (PRM: Local.promises (Thread.local e) = BoolMap.bot)
        (GPRM: Global.promises (Thread.global e) = BoolMap.bot)
    .
    Hint Constructors wf_pf: core.

    Variant wf_ra (rels: Writes.t) (e: Thread.t lang): Prop :=
    | wf_ra_intro
        (WF_LC: Local.wf (Thread.local e) (Thread.global e))
        (WF_GL: Global.wf (Thread.global e))
        (PRM: Local.promises (Thread.local e) = BoolMap.bot)
        (GPRM: Global.promises (Thread.global e) = BoolMap.bot)
        (RELS: Writes.wf L rels (Global.memory (Thread.global e)))
    .
    Hint Constructors wf_ra: core.

    Lemma step_pf_future
          e e1 e2
          (WF1: wf_pf e1)
          (STEP: Thread.step e e1 e2)
          (EVENT: ThreadEvent.is_program e):
      <<WF2_PF: wf_pf e2>>.
    Proof.
      inv WF1.
      exploit Thread.step_future; eauto. i. des.
      inv STEP; [inv LOCAL|]; ss.
      exploit Local.program_step_promises; eauto. i. des.
      econs; eauto; s.
      - apply BoolMap.antisym; try apply BoolMap.bot_spec.
        rewrite <- PRM. ss.
      - apply BoolMap.antisym; try apply BoolMap.bot_spec.
        rewrite <- GPRM. ss.
    Qed.

    Lemma step_ra_future
          ordr ordw rels1 rels2 e e1 e2
          (WF1: wf_ra rels1 e1)
          (ORDC: Ordering.le Ordering.plain ordw)
          (STEP: WThread.step L ordr ordw rels1 rels2 e e1 e2):
      <<WF2_APF: wf_ra rels2 e2>>.
    Proof.
      inv WF1.
      hexploit WThread.step_future; eauto. i. des.
      inv STEP.
      hexploit Writes.step_wf; eauto. i.
      exploit OrdThread.step_promises; eauto. i. des.
      econs; ss.
      - apply BoolMap.antisym; try apply BoolMap.bot_spec.
        rewrite <- PRM. ss.
      - apply BoolMap.antisym; try apply BoolMap.bot_spec.
        rewrite <- GPRM. ss.
    Qed.

    Lemma opt_step_pf_future
          e e1 e2
          (WF1: wf_pf e1)
          (STEP: Thread.opt_step e e1 e2)
          (EVENT: ThreadEvent.is_program e):
      <<WF2_PF: wf_pf e2>>.
    Proof.
      inv STEP; eauto using step_pf_future.
    Qed.

    Lemma opt_step_ra_future
          ordr ordw rels1 rels2 e e1 e2
          (WF1: wf_ra rels1 e1)
          (ORD: Ordering.le Ordering.plain ordw)
          (STEP: WThread.opt_step L ordr ordw rels1 rels2 e e1 e2):
      <<WF2_APF: wf_ra rels2 e2>>.
    Proof.
      inv STEP; eauto using step_ra_future.
    Qed.


    (* sim_thread *)

    Variant sim_thread (rels: Writes.t) (e_pf e_ra: Thread.t lang): Prop :=
    | sim_thread_intro
        (SIM_RA: PFtoRASim.sim_thread L rels e_ra e_pf)
        (NORMAL_PF: Normal.normal_thread L e_pf)
        (NORMAL_RA: Normal.normal_thread L e_ra)
        (STABLE_RA: Stable.stable_thread L rels e_ra)
    .

    Lemma sim_thread_step_aux
          rels1 e1_pf e1_ra
          e_pf e2_pf
          (SIM1: sim_thread rels1 e1_pf e1_ra)
          (WF1_PF: wf_pf e1_pf)
          (WF1_RA: wf_ra rels1 e1_ra)
          (STEP_PF: Thread.step e_pf e1_pf e2_pf)
          (EVENT: ThreadEvent.is_program e_pf):
      (exists e_ra e2_ra,
          (<<STEP_RA: OrdThread.step L Ordering.acqrel Ordering.acqrel e_ra e1_ra e2_ra>>) /\
          (<<EVENT_RA: PFtoRASim.sim_event e_ra e_pf>>) /\
          (<<SIM2: sim_thread (Writes.append L e_ra rels1) e2_pf e2_ra>>)) \/
      (<<RACE: RARaceW.ra_race L rels1 (Local.tview (Thread.local e1_ra)) (ThreadEvent.get_program_event e_pf)>>).
    Proof.
      (* normal step *)
      inv WF1_PF. inv WF1_RA.
      hexploit PFtoRASim.thread_step;
        try exact STEP_PF; try eapply SIM1; eauto.
      i. des; eauto.
      left. unguard. des. esplits; eauto. econs; ss.
    Qed.

    Lemma sim_event_ra_writes_append
          e_pf e_ra
          (SIM: PFtoRASim.sim_event e_ra e_pf):
      forall rels, Writes.append L e_pf rels = Writes.append L e_ra rels.
    Proof.
      inv SIM; ss.
    Qed.

    Lemma sim_thread_step
          rels1 e1_pf e1_ra
          e_pf e2_pf
          (SIM1: sim_thread rels1 e1_pf e1_ra)
          (WF1_PF: wf_pf e1_pf)
          (WF1_RA: wf_ra rels1 e1_ra)
          (STEP: Thread.step e_pf e1_pf e2_pf)
          (EVENT: ThreadEvent.is_program e_pf):
      (exists rels2 e_ra e2_ra,
          (<<STEP_RA: WThread.step L Ordering.acqrel Ordering.acqrel rels1 rels2 e_ra e1_ra e2_ra>>) /\
          (<<EVENT_RA: PFtoRASim.sim_event e_ra e_pf>>) /\
          (<<SIM2: sim_thread rels2 e2_pf e2_ra>>)) \/
      (exists e st2,
          (<<STEP: lang.(Language.step) e e1_ra.(Thread.state) st2>>) /\
          (<<RACE: RARaceW.ra_race L rels1 (Local.tview (Thread.local e1_ra)) e>>)).
    Proof.
      exploit sim_thread_step_aux; eauto. i. des.
      { left. esplits; eauto. econs. eauto. }
      right.
      inv SIM1. inv SIM_RA.
      destruct e1_pf, e1_ra. ss. subst.
      inv STEP; [inv LOCAL0|]; ss.
      esplits; eauto.
    Qed.

    (* Lemma sim_thread_opt_step *)
    (*       views1 rels1 e1_pf e1_j e1_apf e1_ra *)
    (*       e_pf e2_pf *)
    (*       (SIM1: sim_thread views1 rels1 e1_pf e1_j e1_apf e1_ra) *)
    (*       (WF1_PF: wf_pf e1_pf) *)
    (*       (WF1_J: wf_j views1 e1_j) *)
    (*       (WF1_APF: wf_ra rels1 e1_apf) *)
    (*       (WF1_RA: wf_ra rels1 e1_ra) *)
    (*       (STEP: Thread.opt_step e_pf e1_pf e2_pf) *)
    (*       (PF: PF.pf_event L e_pf) *)
    (*       (CONS: Local.promise_consistent (Thread.local e2_pf)): *)
    (*   (exists views2 rels2 e_j e2_j e_apf e2_apf e_ra e2_ra, *)
    (*       (<<STEP_J: JThread.opt_step e_j e1_j e2_j views1 views2>>) /\ *)
    (*       (<<STEP_APF: WThread.opt_step L Ordering.na Ordering.plain rels1 rels2 e_apf e1_apf e2_apf>>) /\ *)
    (*       (<<STEP_RA: WThread.opt_step L Ordering.acqrel Ordering.acqrel rels1 rels2 e_ra e1_ra e2_ra>>) /\ *)
    (*       (<<EVENT_J: JSim.sim_event e_j e_pf>>) /\ *)
    (*       (<<EVENT_APF: PFtoAPFSim.sim_event e_apf e_j>>) /\ *)
    (*       (<<EVENT_RA: APFtoRASim.sim_event e_ra e_apf>>) /\ *)
    (*       (<<SIM2: sim_thread views2 rels2 e2_pf e2_j e2_apf e2_ra>>)) \/ *)
    (*   (exists e st2, *)
    (*       (<<CONS: Local.promise_consistent (Thread.local e1_ra)>>) /\ *)
    (*       (<<STEP: lang.(Language.step) e e1_ra.(Thread.state) st2>>) /\ *)
    (*       (<<RACE: RARaceW.ra_race L rels1 (Local.tview (Thread.local e1_ra)) e>>)). *)
    (* Proof. *)
    (*   inv STEP. *)
    (*   - left. esplits; eauto; try econs 1; econs. *)
    (*   - exploit sim_thread_step; eauto. i. des. *)
    (*     + left. esplits; (try by econs 2; eauto); ss. *)
    (*     + right. eauto. *)
    (* Qed. *)

    (* Lemma sim_thread_steps *)
    (*       views1 rels1 e1_pf e1_j e1_apf e1_ra *)
    (*       tr e2_pf *)
    (*       (SIM1: sim_thread views1 rels1 e1_pf e1_j e1_apf e1_ra) *)
    (*       (WF1_PF: wf_pf e1_pf) *)
    (*       (WF1_J: wf_j views1 e1_j) *)
    (*       (WF1_APF: wf_ra rels1 e1_apf) *)
    (*       (WF1_RA: wf_ra rels1 e1_ra) *)
    (*       (STEPS: Trace.steps tr e1_pf e2_pf) *)
    (*       (SILENT: List.Forall (fun the => ThreadEvent.get_machine_event (snd the) = MachineEvent.silent) tr) *)
    (*       (PF: List.Forall (compose (PF.pf_event L) snd) tr) *)
    (*       (CONS: Local.promise_consistent (Thread.local e2_pf)): *)
    (*   (exists views2 rels2 e2_j e2_apf e2_ra, *)
    (*       (<<STEPS_J: JThread.rtc_tau e1_j e2_j views1 views2>>) /\ *)
    (*       (<<STEPS_APF: WThread.tau_steps L Ordering.na Ordering.plain rels1 rels2 e1_apf e2_apf>>) /\ *)
    (*       (<<STEPS_RA: WThread.tau_steps L Ordering.acqrel Ordering.acqrel rels1 rels2 e1_ra e2_ra>>) /\ *)
    (*       (<<SIM2: sim_thread views2 rels2 e2_pf e2_j e2_apf e2_ra>>)) \/ *)
    (*   (exists rels2 e2_ra e st3, *)
    (*       (<<STEPS_RA: WThread.tau_steps L Ordering.acqrel Ordering.acqrel rels1 rels2 e1_ra e2_ra>>) /\ *)
    (*       (<<CONS_RA: Local.promise_consistent (Thread.local e2_ra)>>) /\ *)
    (*       (<<STEP_RA: lang.(Language.step) e e2_ra.(Thread.state) st3>>) /\ *)
    (*       (<<RACE: RARaceW.ra_race L rels2 (Local.tview (Thread.local e2_ra)) e>>)). *)
    (* Proof. *)
    (*   revert views1 rels1 e1_j e1_apf e1_ra SIM1 WF1_PF WF1_J WF1_APF WF1_RA SILENT PF CONS. *)
    (*   induction STEPS; i; ss. *)
    (*   { left. esplits; eauto; econs 1; eauto. } *)
    (*   subst. exploit sim_thread_step; try exact SIM1; eauto. *)
    (*   { ii. inv PF. exploit H1; ss; eauto. } *)
    (*   { exploit Thread.step_future; try exact STEP; try apply WF1_PF. i. des. *)
    (*     eapply rtc_tau_step_promise_consistent; try eapply Trace.silent_steps_tau_steps; eauto. *)
    (*     inv SILENT. ss. *)
    (*   } *)
    (*   i. des. *)
    (*   - exploit step_pf_future; eauto. i. des. *)
    (*     exploit step_j_future; eauto. i. des. *)
    (*     exploit step_ra_future; try exact WF1_APF; eauto; ss. i. des. *)
    (*     exploit step_ra_future; try exact WF1_RA; eauto; ss. i. des. *)
    (*     exploit IHSTEPS; eauto. *)
    (*     { inv SILENT. ss. } *)
    (*     { inv PF. ss. } *)
    (*     i. des. *)
    (*     + left. esplits; try exact SIM0; eauto. *)
    (*       * econs 2; [eauto|..]; eauto. *)
    (*         inv SILENT. ss. inv EVENT_J; ss. *)
    (*       * econs 2; [eauto|..]; eauto. *)
    (*         inv SILENT. ss. inv EVENT_J; inv EVENT_APF; ss. *)
    (*       * econs 2; [eauto|..]; eauto. *)
    (*         inv SILENT. ss. inv EVENT_J; inv EVENT_APF; inv EVENT_RA; ss. *)
    (*     + right. esplits; eauto. *)
    (*       econs 2; [eauto|..]; eauto. *)
    (*       inv SILENT. ss. inv EVENT_J; inv EVENT_APF; inv EVENT_RA; ss. *)
    (*   - right. esplits; eauto. econs 1. *)
    (* Qed. *)
  End PFtoRAThread.
End PFtoRAThread.
