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
Require Import Configuration.
Require Import PFConfiguration.
Require Import Behavior.

Require Import OrdStep.
Require Import Writes.
Require Import WStep.
Require Import Stable.
Require Import PFtoRASim.
Require Import PFtoRAThread.

Set Implicit Arguments.


Module PFtoRA.
  Section PFtoRA.
    Variable L: Loc.t -> bool.

    (* well-formedness *)

    Variant wf_pf (c: Configuration.t): Prop :=
    | wf_pf_intro
        (WF: Configuration.wf c)
        (PRM: forall tid lang st lc
                (TH: IdentMap.find tid (Configuration.threads c) = Some (existT _ lang st, lc)),
            Local.promises lc = BoolMap.bot)
        (GPRM: Global.promises (Configuration.global c) = BoolMap.bot)
    .

    Variant wf_ra (rels: Writes.t) (c: Configuration.t): Prop :=
    | wf_ra_intro
        (WF: Configuration.wf c)
        (RELS: Writes.wf L rels (Global.memory (Configuration.global c)))
        (PRM: forall tid lang st lc
                (TH: IdentMap.find tid (Configuration.threads c) = Some (existT _ lang st, lc)),
            Local.promises lc = BoolMap.bot)
        (GPRM: Global.promises (Configuration.global c) = BoolMap.bot)
    .

    Lemma wf_pf_thread
          c tid lang st lc
          (WF: wf_pf c)
          (FIND: IdentMap.find tid (Configuration.threads c) = Some (existT _ lang st, lc)):
      PFtoRAThread.wf_pf (Thread.mk _ st lc (Configuration.global c)).
    Proof.
      inv WF. inv WF0. inv WF.
      econs; eauto.
    Qed.

    Lemma wf_ra_thread
          rels c tid lang st lc
          (WF: wf_ra rels c)
          (FIND: IdentMap.find tid (Configuration.threads c) = Some (existT _ lang st, lc)):
      PFtoRAThread.wf_ra L rels (Thread.mk _ st lc (Configuration.global c)).
    Proof.
      inv WF. inv WF0. inv WF.
      econs; eauto.
    Qed.

    Lemma step_pf_future
          e tid c1 c2
          (WF1: wf_pf c1)
          (STEP: PFConfiguration.estep e tid c1 c2):
      <<WF2: wf_pf c2>>.
    Proof.
      exploit PFConfiguration.estep_future; try apply WF1; eauto. i. des.
      inv STEP. ss.
      exploit wf_pf_thread; eauto. i.
      exploit PFtoRAThread.step_pf_future; eauto. i. des. inv x1. ss.
      econs; ss. i. Configuration.simplify.
      inv WF1. eauto.
    Qed.

    Lemma step_ra_future
          ordr ordw
          e tid rels1 rels2 c1 c2
          (WF1: wf_ra rels1 c1)
          (ORD: Ordering.le Ordering.plain ordw)
          (STEP: WConfiguration.step L ordr ordw e tid rels1 rels2 c1 c2):
      <<WF2: wf_ra rels2 c2>>.
    Proof.
      exploit WConfiguration.step_future; try eapply WF1; eauto. i. des.
      inv STEP. ss.
      exploit wf_ra_thread; eauto. i.
      hexploit WThread.step_writes_wf; eauto; try apply x0. s. i.
      exploit PFtoRAThread.step_ra_future; eauto. i. des. inv x1. ss.
      econs; ss. i. Configuration.simplify; ss.
      inv WF1. eauto.
    Qed.

    Lemma steps_pf_future
          c1 c2
          (WF1: wf_pf c1)
          (STEPS: rtc (PFConfiguration.all_step) c1 c2):
      <<WF2: wf_pf c2>>.
    Proof.
      induction STEPS; ss. inv H.
      exploit step_pf_future; eauto.
    Qed.

    Lemma steps_ra_future
          ordr ordw
          rels1 rels2 c1 c2
          (WF1: wf_ra rels1 c1)
          (ORD: Ordering.le Ordering.plain ordw)
          (STEPS: WConfiguration.steps L ordr ordw rels1 rels2 c1 c2):
      <<WF2: wf_ra rels2 c2>>.
    Proof.
      induction STEPS; ss.
      exploit step_ra_future; eauto.
    Qed.


    (* sim *)

    Variant sim_thread_sl (rels: Writes.t) (gl_pf gl_ra: Global.t):
      forall (sl_pf sl_ra: {lang: language & Language.state lang} * Local.t), Prop :=
    | sim_thread_sl_intro
        lang st_pf lc_pf st_ra lc_ra
        (SIM: PFtoRAThread.sim_thread L rels
                                      (Thread.mk lang st_pf lc_pf gl_pf)
                                      (Thread.mk lang st_ra lc_ra gl_ra)):
        sim_thread_sl rels gl_pf gl_ra
                      (existT _ lang st_pf, lc_pf) (existT _ lang st_ra, lc_ra)
    .

    Variant sim_conf (rels: Writes.t): forall (c_pf c_ra: Configuration.t), Prop :=
    | sim_conf_intro
        ths_pf gl_pf
        ths_ra gl_ra
        (THS: forall tid,
            option_rel
              (sim_thread_sl rels gl_pf gl_ra)
              (IdentMap.find tid ths_pf)
              (IdentMap.find tid ths_ra)):
        sim_conf rels
                 (Configuration.mk ths_pf gl_pf)
                 (Configuration.mk ths_ra gl_ra)
    .

    Lemma init_wf_pf syn:
      wf_pf (Configuration.init syn).
    Proof.
      econs; eauto using Configuration.init_wf.
      i. ss.
      unfold Threads.init in *.
      rewrite IdentMap.Facts.map_o in *.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid syn); inv TH.
      apply inj_pair2 in H1. subst. ss.
    Qed.

    Lemma init_wf_ra syn:
      wf_ra [] (Configuration.init syn).
    Proof.
      econs; eauto using Configuration.init_wf; i; ss.
      - econs; i; ss.
        unfold Memory.get, Memory.init, Cell.get, Cell.init in *. ss.
        apply DOMap.singleton_find_inv in GET. des. inv GET0. ss.
      -unfold Threads.init in *.
        rewrite IdentMap.Facts.map_o in *.
        destruct (@UsualFMapPositive.UsualPositiveMap'.find
                    (@sigT _ (@Language.syntax ProgramEvent.t)) tid syn); inv TH.
        apply inj_pair2 in H1. subst. ss.
    Qed.

    Lemma init_sim_conf syn:
      sim_conf [] (Configuration.init syn) (Configuration.init syn).
    Proof.
      econs; ss. i. unfold option_rel.
      destruct (IdentMap.find tid (Threads.init syn)) as [[[lang st] lc]|] eqn:FIND; ss.
      unfold Threads.init in *.
      rewrite IdentMap.Facts.map_o in *.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid syn); inv FIND.
      apply inj_pair2 in H1. subst.
      econs. econs; ss.
      (* - econs; ss; try refl. econs; try refl. ii. *)
      (*   rewrite Memory.bot_get. ss. *)
      (* - econs; ss. econs; ss; eauto. i. *)
      (*   unfold Memory.get, Memory.init, Cell.get, Cell.init in *. ss. *)
      (*   apply DOMap.singleton_find_inv in GET. des. inv GET0. ss. *)
      - econs; ss.
        + econs; ss. econs; ss. i. condtac; ss. refl.
        + econs; ss; i.
          * unfold Memory.get, Memory.init, Cell.get, Cell.init in *. ss.
            apply DOMap.singleton_find_inv in GET_SRC. des. inv GET_SRC0.
            esplits; ss. econs; ss. condtac; ss.
          * unfold Memory.get, Memory.init, Cell.get, Cell.init in *. ss.
            apply DOMap.singleton_find_inv in GET_TGT. des. inv GET_TGT0.
            esplits; ss. econs; ss. condtac; ss.
          * unfold Memory.get, Memory.init, Cell.get, Cell.init in *. ss.
            apply DOMap.singleton_find_inv in GET_TGT. des. inv GET_TGT0. ss.
      - econs; ss. ii.
        unfold Memory.get, Memory.init, Cell.get, Cell.init in *. ss.
        apply DOMap.singleton_find_inv in GET. des. inv GET0.
      - econs; ss. ii.
        unfold Memory.get, Memory.init, Cell.get, Cell.init in *. ss.
        apply DOMap.singleton_find_inv in GET. des. inv GET0.
      - econs; ss. ii. des; ss.
        unfold Memory.get, Memory.init, Cell.get, Cell.init in *. ss.
        apply DOMap.singleton_find_inv in GET. des. inv GET1.
    Qed.

    Lemma sim_conf_terminal
          rels c_pf c_ra
          (WF_RA: wf_ra rels c_ra)
          (SIM: sim_conf rels c_pf c_ra)
          (TERMINAL: Configuration.is_terminal c_pf):
      Configuration.is_terminal c_ra.
    Proof.
      ii. inv SIM. specialize (THS tid).
      unfold option_rel in *. ss. des_ifs.
      destruct p as [[]]. inv THS.
      Configuration.simplify.
      inv SIM. inv SIM_RA. ss. subst.
      exploit TERMINAL; eauto. i. des.
      split; ss.
      inv WF_RA. eauto.
    Qed.


    (* step *)

    Lemma sim_conf_step
          rels1 c1_pf c1_ra
          tid e_pf c2_pf
          (SIM1: sim_conf rels1 c1_pf c1_ra)
          (WF1_PF: wf_pf c1_pf)
          (WF1_RA: wf_ra rels1 c1_ra)
          (STEP: PFConfiguration.estep e_pf tid c1_pf c2_pf):
      (exists e_ra rels2 c2_ra,
          (<<STEP_RA: WConfiguration.step L Ordering.acqrel Ordering.acqrel
                                          e_ra tid rels1 rels2 c1_ra c2_ra>>) /\
          (<<EVENT_RA: PFtoRASim.sim_event e_ra e_pf>>) /\
          (<<SIM2: sim_conf rels2 c2_pf c2_ra>>)) \/
      (<<RACE: RARaceW.ra_race_steps L Ordering.acqrel Ordering.acqrel rels1 c1_ra>>).
    Proof.
      dup SIM1. inv SIM0. inv STEP. ss.
      dup THS. specialize (THS0 tid). unfold option_rel in THS0. des_ifs.
      inv THS0. apply inj_pair2 in H1. subst.
      exploit wf_pf_thread; eauto. s. i.
      exploit wf_ra_thread; try exact WF1_RA; eauto. s. i.
      exploit PFtoRAThread.sim_thread_step; eauto. i. des; cycle 1.
      { right. unfold RARaceW.ra_race_steps.
        esplits; [econs 1|..]; eauto.
      }
      destruct e2_ra as [st2_ra lc2_ra gl2_ra].
      left. esplits.
      - econs; eauto.
      - ss.
      - econs; ss. i.
        repeat rewrite IdentMap.gsspec. condtac; ss.
        specialize (THS tid0). unfold option_rel in THS. des_ifs. inv THS. ss.
        inv SIM0. econs. econs; s.
        + inv SIM_RA. ss. subst.
          inv SIM2. inv SIM_RA. ss.
        + econs; try apply SIM2; try apply NORMAL_PF.
        + econs; try apply SIM2; try apply NORMAL_RA.
        + econs; s; try apply SIM2; try apply STABLE_RA.
          exploit WThread.step_future; try exact STEP_RA; try apply x1. s. i. des.
          exploit wf_ra_thread; try exact WF1_RA; try eapply Heq2. s. i.
          exploit Stable.future_stable_tview;
            try eapply STABLE_RA; try apply x2; try apply GL_FUTURE; eauto.
    Qed.

    Lemma sim_conf_steps
          rels1 c1_pf c1_ra
          c2_pf
          (SIM1: sim_conf rels1 c1_pf c1_ra)
          (WF1_PF: wf_pf c1_pf)
          (WF1_RA: wf_ra rels1 c1_ra)
          (STEPS: rtc PFConfiguration.all_step c1_pf c2_pf):
      (exists rels2 c2_ra,
          (<<STEPS_RA: WConfiguration.steps L Ordering.acqrel Ordering.acqrel rels1 rels2 c1_ra c2_ra>>) /\
          (<<SIM2: sim_conf rels2 c2_pf c2_ra>>)) \/
      (<<RACE: RARaceW.ra_race_steps L Ordering.acqrel Ordering.acqrel rels1 c1_ra>>).
    Proof.
      revert rels1  c1_ra SIM1 WF1_PF WF1_RA.
      induction STEPS; i.
      { left. esplits; try by econs 1. ss. }
      inv H. exploit sim_conf_step; eauto. i. des; eauto.
      exploit step_pf_future; eauto. i. des.
      exploit step_ra_future; try exact STEP_RA; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      - left. esplits; (try by econs 2; eauto); ss.
      - right. unfold RARaceW.ra_race_steps in *. des.
        esplits; [econs 2; eauto|..]; eauto.
    Qed.


    (* behaviors *)

    Lemma sim_conf_behavior
          rels c_pf c_ra
          (SIM: sim_conf rels c_pf c_ra)
          (WF_PF: wf_pf c_pf)
          (WF_RA: wf_ra rels c_ra)
          (RACEFREE: RARaceW.racefree L Ordering.acqrel Ordering.acqrel rels c_ra):
      behaviors (PFConfiguration.step ThreadEvent.get_machine_event_pf) c_pf <2=
      behaviors (@OrdConfiguration.step L Ordering.acqrel Ordering.acqrel) c_ra.
    Proof.
      i. revert rels  c_ra SIM WF_PF WF_RA RACEFREE.
      induction PR; i.
      - econs 1. eapply sim_conf_terminal; eauto.
      - inv STEP. exploit sim_conf_step; eauto. i. des.
        + exploit WConfiguration.step_ord_step; eauto. i.
          inv EVENT_RA; ss. inv H0.
          econs 2.
          { replace (MachineEvent.syscall e2) with
              (ThreadEvent.get_machine_event_pf (ThreadEvent.syscall e2)) by ss.
            econs; eauto.
          }
          { hexploit RARaceW.step_racefree; eauto. i.
            exploit step_pf_future; eauto. i. des.
            exploit step_ra_future; try exact STEP_RA; eauto.
          }
          { ss. }
        + exfalso. unfold RARaceW.ra_race_steps in *. des. eauto.
      - inv STEP. exploit sim_conf_step; eauto. i. des.
        + exploit WConfiguration.step_ord_step; eauto. i.
          econs 3.
          replace MachineEvent.failure with (ThreadEvent.get_machine_event_pf e_ra); [econs; eauto|].
          inv EVENT_RA; ss.
        + exfalso. unfold RARaceW.ra_race_steps in *. des. eauto.
      - inv STEP. exploit sim_conf_step; eauto. i. des.
        + exploit WConfiguration.step_ord_step; eauto. i.
          econs 4.
          { replace MachineEvent.silent with (ThreadEvent.get_machine_event_pf e_ra); cycle 1.
            { inv EVENT_RA; ss. }
            econs; eauto.
          }
          hexploit RARaceW.step_racefree; eauto. i.
          exploit step_pf_future; eauto. i. des.
          exploit step_ra_future; try exact STEP_RA; eauto.
        + exfalso. unfold RARaceW.ra_race_steps in *. des. eauto.
      - econs 5.
    Qed.
  End PFtoRA.
End PFtoRA.
