Require Import RelationClasses.
Require Import Coq.Logic.PropExtensionality.

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
Require Import Thread.
Require Import Configuration.
Require Import PFConfiguration.
Require Import Behavior.

Require Import PFConsistent.
Require Import FutureCertify.
Require Import SrcToIRThread.

Set Implicit Arguments.


Module SrcToIR.
  Variant sim_thread_sl (gl_src gl_ir: Global.t):
    forall (sl_src sl_ir: {lang: language & Language.state lang} * Local.t), Prop :=
    | sim_thread_sl_intro
        lang
        st_src lc_src
        st_ir lc_ir
        (THREAD: SrcToIRThread.sim_thread (Thread.mk _ st_src lc_src gl_src) (Thread.mk _ st_ir lc_ir gl_ir))
        (CONS: exists gl_past,
            (<<FUTURE: Global.future gl_past gl_ir>>) /\
            (<<LC_WF: Local.wf lc_ir gl_past>>) /\
            (<<GL_WF: Global.wf gl_past>>) /\
            (<<CONS: PFConsistent.spf_consistent (Thread.mk _ st_ir lc_ir gl_past)>>))
      :
      sim_thread_sl gl_src gl_ir (existT _ lang st_src, lc_src) (existT _ lang st_ir, lc_ir)
  .

  Lemma sim_thread_sl_future
        gl_src gl_ir lang_src st_src lc_src lang_ir st_ir lc_ir
        gl_future_src gl_future_ir
        (GL_FUTURE_IR: Global.future gl_ir gl_future_ir)
        (SC: Global.sc gl_future_src = Global.sc gl_future_ir)
        (GPROMISES: Global.promises gl_future_src = BoolMap.bot)
        (MEMORY: SrcToIRThread.sim_memory (Global.memory gl_future_src) (Global.memory gl_future_ir))
        (SIM: sim_thread_sl gl_src gl_ir
                            (existT _ lang_src st_src, lc_src)
                            (existT _ lang_ir st_ir, lc_ir)):
    sim_thread_sl gl_future_src gl_future_ir
                  (existT _ lang_src st_src, lc_src)
                  (existT _ lang_ir st_ir, lc_ir).
  Proof.
    inv SIM. Configuration.simplify. econs.
    - inv THREAD. ss.
    - des. exists gl_past.
      splits; ss; try by (etrans; eauto).
  Qed.

  Variant sim_conf: forall (c_src c_ir: Configuration.t), Prop :=
    | sim_conf_intro
        ths_src gl_src
        ths_ir gl_ir
        (THS: forall tid,
            option_rel
              (sim_thread_sl gl_src gl_ir)
              (IdentMap.find tid ths_src)
              (IdentMap.find tid ths_ir)):
      sim_conf (Configuration.mk ths_src gl_src) (Configuration.mk ths_ir gl_ir)
  .

  Lemma init_sim_conf prog: sim_conf (Configuration.init prog) (Configuration.init prog).
  Proof.
    econs. i.
    unfold Threads.init. rewrite IdentMap.Facts.map_o.
    destruct (@UsualFMapPositive.UsualPositiveMap'.find
                (@sigT _ (@Language.syntax ProgramEvent.t)) tid prog); ss.
    econs; ss.
    - econs; ss. apply SrcToIRThread.init_sim_memory.
    - exists Global.init. splits.
      + refl.
      + apply Local.init_wf.
      + apply Global.init_wf.
      + econs 2; s; try refl.
  Qed.

  Lemma sim_conf_terminal
        c1_src c1_ir
        (SIM: sim_conf c1_src c1_ir)
        (TERMINAL: Configuration.is_terminal c1_ir):
    Configuration.is_terminal c1_src.
  Proof.
    inv SIM. ii. ss.
    specialize (THS tid). rewrite FIND in THS.
    destruct (IdentMap.find tid ths_ir) as [[[lang_ir st_ir] lc_ir]|] eqn:FIND_IR; ss.
    inv THS. Configuration.simplify.
    inv THREAD. ss. subst. splits; ss.
    exploit TERMINAL; eauto. i. des. ss.
  Qed.

  Lemma is_racy_promise_is_racy
        lang e (th1 th2: Thread.t lang)
        (STEP: Thread.step e th1 th2)
        (EVENT: ThreadEvent.is_racy_promise e):
    exists loc,
      (<<LOC: ThreadEvent.is_accessing_loc loc e>>) /\
      (<<GET: Global.promises (Thread.global th1) loc = true>>) /\
      (<<GETP: Local.promises (Thread.local th1) loc = false>>).
  Proof.
    inv STEP; inv LOCAL; ss.
    - inv LOCAL0. inv RACE; ss. eauto.
    - inv LOCAL0. inv RACE; ss. eauto.
    - inv LOCAL0; des.
      + destruct ordr; ss.
      + destruct ordw; ss.
      + inv RACE; ss. eauto.
  Qed.

  Lemma disjoint_minus_le_r
        bm1 bm2 gbm
        (LE1: BoolMap.le bm1 gbm)
        (LE2: BoolMap.le bm2 gbm)
        (DISJOINT: BoolMap.disjoint bm1 bm2):
    BoolMap.le bm2 (BoolMap.minus gbm bm1).
  Proof.
    ii. exploit LE2; eauto. i.
    unfold BoolMap.minus. rewrite x0. s.
    destruct (bm1 loc) eqn:GET1; ss.
    exploit DISJOINT; eauto.
  Qed.

  Lemma sim_conf_step
        c1_src c1_ir
        e tid c2_ir
        (SIM: sim_conf c1_src c1_ir)
        (WF1_SRC: Configuration.wf c1_src)
        (WF1_IR: Configuration.wf c1_ir)
        (STEP: Configuration.step e tid c1_ir c2_ir):
    (exists c_src tid' c2_src,
        (<<STEPS_SRC: rtc (PFConfiguration.tau_step ThreadEvent.get_machine_event_pf)
                         c1_src c_src>>) /\
        (<<STEP_SRC: PFConfiguration.step ThreadEvent.get_machine_event_pf
                                         MachineEvent.failure tid' c_src c2_src>>)) \/
    (exists c_src c2_src,
        (<<STEPS_SRC: rtc (PFConfiguration.tau_step ThreadEvent.get_machine_event_pf)
                         c1_src c_src>>) /\
        (<<STEP_SRC: PFConfiguration.opt_step ThreadEvent.get_machine_event_pf
                                             e tid c_src c2_src>>) /\
        ((<<SIM2: sim_conf c2_src c2_ir>>) \/
         exists c3_src tid' c4_src,
           (<<STEPS2_SRC: rtc (PFConfiguration.tau_step ThreadEvent.get_machine_event_pf)
                             c2_src c3_src>>) /\
           (<<STEP2_SRC: PFConfiguration.step ThreadEvent.get_machine_event_pf
                                             MachineEvent.failure tid' c3_src c4_src>>))).
  Proof.
    destruct c1_src as [ths1_src gl1_src], c1_ir as [ths1_ir gl1_ir].
    inv STEP. dup SIM. inv SIM0. ss.
    rename st1 into st1_ir, lc1 into lc1_ir.
    specialize (THS tid). rewrite TID in *.
    destruct (IdentMap.find tid ths1_src) as [[[lang_src st1_src] lc1_src]|] eqn:FIND_SRC; ss.
    inv THS. Configuration.simplify. clear CONS.

    exploit SrcToIRThread.plus_step_cases; try exact STEPS; eauto. i. des; cycle 1.
    { (* race with a promise *)
      left. clear e0 th2 st3 lc3 gl3 STEPS STEP0 CONSISTENT.
      exploit SrcToIRThread.sim_thread_rtc_step; try exact STEPS0; eauto. i. des.
      exploit is_racy_promise_is_racy; try exact STEP_RACE; ss. i. des.
      exploit Thread.rtc_tau_step_promises_minus;
        try eapply rtc_implies; try exact STEPS0; s.
      { i. inv H. des. econs; eauto. }
      unfold BoolMap.minus. i.
      eapply equal_f in x0.
      rewrite GET, GETP in x0. ss.
      destruct (Global.promises gl1_ir loc) eqn:GPROMISED; ss.
      destruct (Local.promises lc1_ir loc) eqn:PROMISED; ss.
      dup WF1_IR. inv WF1_IR0. inv WF. ss.
      exploit (PROMISES loc); ss.
      clear DISJOINT THREADS PROMISES. i. des.
      destruct (classic (tid = tid0)).
      { subst. rewrite TID in *. Configuration.simplify. congr. }
      dup SIM. inv SIM0. specialize (THS tid0). rewrite TH in *.
      destruct (IdentMap.find tid0 ths1_src) as [[[lang0_src st0_src] lc0_src]|] eqn:FIND0_SRC; ss.
      inv THS. Configuration.simplify. des.
      exploit FutureCertify.spf_consistent_certify; try exact CONS; eauto. s. intro CERTIFY.

      dup WF1_IR. inv WF1_IR0. inv WF. ss.
      exploit DISJOINT; try exact H; eauto. i.
      exploit THREADS; try exact TID. i.
      exploit THREADS; try exact TH. i.
      clear DISJOINT THREADS PROMISES.
      dup WF1_SRC. inv WF1_SRC0. inv WF. ss.
      exploit DISJOINT; try exact H; eauto. i.
      exploit THREADS; try exact FIND_SRC. i.
      exploit THREADS; try exact FIND0_SRC. i.
      clear DISJOINT THREADS PROMISES.
      exploit Thread.rtc_tau_step_future; try eapply rtc_implies; try exact STEPS0; ss.
      { i. inv H0. des. econs; eauto. }
      i. des.
      exploit Thread.rtc_tau_step_future; try eapply rtc_implies; try exact STEPS_SRC; ss.
      { i. inv H0. des. econs; eauto. }
      i. des.
      exploit Thread.rtc_tau_step_disjoint; try eapply rtc_implies; try exact STEPS0; eauto.
      { i. inv H0. des. econs; eauto. }
      i. des.
      exploit Thread.rtc_tau_step_disjoint; try eapply rtc_implies; try exact STEPS_SRC; eauto.
      { i. inv H0. des. econs; eauto. }
      i. des.
      exploit (@FutureCertify.future_certify lang0 (Thread.mk _ st0_src lc0_src (Thread.global th2_src)));
        try exact CERTIFY; ss; (try by inv THREAD0; ss); (try by inv SIM2; ss); try apply SIM2.
      { eapply Memory.future_messages_le. etrans; try apply FUTURE. apply GL_FUTURE. }
      { apply LC_WF1. }
      intro CERTIFY_SRC.
      exploit (@PFConfiguration.rtc_program_step_rtc_step (Configuration.mk ths1_src gl1_src));
        try eapply STEPS_SRC; eauto. s. i. des; eauto.

      inv CERTIFY_SRC.
      - exploit (@PFConfiguration.plus_program_step_plus_step
                   (Configuration.mk
                      (IdentMap.add tid (existT _ lang (Thread.state th2_src), Thread.local th2_src) ths1_src)
                      (Thread.global th2_src))); s.
        { erewrite IdentMap.gso; try eapply FIND0_SRC. auto. }
        { eapply rtc_implies; try exact STEPS1.
          i. inv H0. des. econs; eauto.
          inv EVENT. inv EVENT0. destruct e1; ss.
        }
        { eassumption. }
        { destruct e0; ss. }
        i. des; try by destruct e0; ss.
        esplits; try exact STEP. etrans; eauto.
      - destruct th2_src as [st2_src lc2_src gl2_src]. ss.
        assert (RACE: exists e th3_src,
                     Thread.step e
                                 (Thread.mk _ st2_src lc2_src (Thread.global th2)) th3_src /\
                     ThreadEvent.is_racy e /\
                     ~ ThreadEvent.is_racy_promise e).
        { exploit Thread.rtc_all_step_future; try eapply rtc_implies; try exact STEPS1; ss.
          { i. inv H0. econs; eauto. }
          i. des.
          inv STEP_FULFILL; inv LOCAL. inv LOCAL0. ss.
          exploit Memory.add_get0; try exact WRITE. i. des.
          inv SIM2. ss. subst.
          inv STEP_RACE; inv LOCAL; ss; subst.
          - esplits.
            + econs 2; cycle 1.
              * econs 8. econs. econs 2; try apply GET2; ss.
                eapply TimeFacts.le_lt_lt; try exact TO.
                inv LC_WF0. inv TVIEW_CLOSED. inv CUR.
                exploit Memory.future_closed_timemap; try exact PLN; try apply GL_FUTURE1. i. des.
                eapply Memory.max_ts_spec. eauto.
              * ss. eauto.
            + ss.
            + ss.
          - esplits.
            + econs 2; cycle 1.
              * econs 9. econs. econs 2; try apply GET2; ss.
                eapply TimeFacts.le_lt_lt; try exact TO.
                inv LC_WF0. inv TVIEW_CLOSED. inv CUR.
                exploit Memory.future_closed_timemap; try exact PLN; try apply GL_FUTURE1. i. des.
                eapply Memory.max_ts_spec. eauto.
              * ss. eauto.
            + ss.
            + ss.
          - esplits.
            + econs 2; cycle 1.
              * econs 10. econs 3. econs 2; try apply GET2; ss.
                eapply TimeFacts.le_lt_lt; try exact TO.
                inv LC_WF0. inv TVIEW_CLOSED. inv CUR.
                exploit Memory.future_closed_timemap; try exact PLN; try apply GL_FUTURE1. i. des.
                eapply Memory.max_ts_spec. eauto.
              * ss. eauto.
            + ss.
            + ss.
        }
        des. destruct th3_src.
        exploit (@PFConfiguration.plus_program_step_plus_step
                   (Configuration.mk
                      (IdentMap.add tid (existT _ lang st2_src, lc2_src) ths1_src) gl2_src)); s.
        { erewrite IdentMap.gso; try eapply FIND0_SRC. auto. }
        { eapply rtc_implies; try exact STEPS1.
          i. inv H0. des. econs; eauto.
          inv EVENT. inv EVENT0. destruct e1; ss.
        }
        { eassumption. }
        { ss. }
        s. i. des; cycle 1.
        { esplits; try exact STEP. etrans; eauto. }
        esplits.
        + etrans; [eauto|]. eapply rtc_n1; [eauto|]. econs. exact STEP.
        + replace MachineEvent.failure with (ThreadEvent.get_machine_event_pf e0); cycle 1.
          { destruct e0; ss. }
          econs. econs; s.
          * rewrite IdentMap.gso; try by apply IdentMap.gss. ss.
          * eassumption.
          * destruct e0; ss.
    }

    exploit SrcToIRThread.sim_thread_rtc_step; try exact STEPS0; eauto. i. des.
    exploit SrcToIRThread.sim_thread_step; try exact STEP0; eauto. i. des.
    exploit (@PFConfiguration.opt_plus_program_step_opt_plus_step (Configuration.mk ths1_src gl1_src));
      try exact STEPS_SRC; eauto. s. i. des; try by left; eauto.
    right.
    assert (ThreadEvent.get_machine_event e0 = ThreadEvent.get_machine_event_pf e_src).
    { unguard. des; subst; ss; destruct e0; ss. }
    rewrite H.
    esplits; try exact STEPS1; eauto.
    exploit CONSISTENT; try by (destruct e0; ss; congr). i.
    dup WF1_IR. inv WF1_IR0. inv WF. ss.
    exploit THREADS; try exact TID. intro LC_WF.
    clear DISJOINT THREADS PROMISES.
    exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
    exploit Thread.step_future; try exact STEP0; eauto. s. i. des.
    exploit PFConsistent.consistent_pf_consistent; try exact x0; eauto. i.
    exploit PFConsistent.pf_consistent_spf_consistent; try exact x1. i. des.
    { (* certification with no race *)
      left. clear x0 x1.
      destruct th2_src, th2_src0. ss.
      econs. i.
      destruct (classic (tid = tid0)).
      - subst. repeat rewrite IdentMap.gss. s. econs; ss.
        esplits; try exact SPF_CONS; ss; try refl.
      - repeat (rewrite IdentMap.gso; auto).
        dup SIM. inv SIM1. specialize (THS tid0).
        destruct (IdentMap.find tid0 ths1_src) as [[[lang0_src st0_src] lc0_src]|] eqn:FIND0_SRC;
          destruct (IdentMap.find tid0 ths1_ir) as [[[lang0_ir st0_ir] lc0_ir]|] eqn:FIND0_IR; ss.
        eapply sim_thread_sl_future; try exact THS; try apply SIM0; try by (etrans; eauto).
    }

    (* race with a promise during certification *)
    right. clear H c2 STEPS1 STEP EVENT0 x0 x1.
    inv SPF_RACE. ss.
    exploit SrcToIRThread.sim_thread_cap; try exact SIM0. i.
    exploit SrcToIRThread.sim_thread_rtc_step; try eapply rtc_implies; try exact STEPS1; eauto.
    { i. inv H. des. inv EVENT0. inv EVENT2. econs; eauto. }
    i. des.
    exploit is_racy_promise_is_racy; try exact STEP_RACE; ss. i. des.
    exploit Thread.rtc_all_step_promises_minus; try eapply rtc_implies; try exact STEPS1.
    { i. inv H. des. econs; eauto. }
    exploit Thread.rtc_all_step_promises_minus.
    { eapply rtc_n1.
      - eapply rtc_implies; try exact STEPS. i. inv H. econs; eauto.
      - econs. exact STEP0.
    }
    unfold BoolMap.minus. s. i.
    rewrite x2 in x1. clear x2.
    eapply equal_f in x1.
    rewrite GET, GETP in x1. ss.
    destruct (Global.promises gl1_ir loc) eqn:GPROMISED; ss.
    destruct (Local.promises lc1_ir loc) eqn:PROMISED; ss.
    clear x1.
    dup WF1_IR. inv WF1_IR0. inv WF. ss.
    exploit (PROMISES loc); ss.
    clear GL_WF DISJOINT THREADS PROMISES. i. des.
    destruct (classic (tid = tid0)).
    { subst. rewrite TID in *. Configuration.simplify. congr. }
    dup SIM. inv SIM3. specialize (THS tid0). rewrite TH in *.
    destruct (IdentMap.find tid0 ths1_src) as [[[lang0_src st0_src] lc0_src]|] eqn:FIND0_SRC; ss.
    inv THS. Configuration.simplify. des.
    exploit FutureCertify.spf_consistent_certify; try exact CONS; eauto. intro CERTIFY.

    dup WF1_IR. inv WF1_IR0. inv WF. ss.
    exploit DISJOINT; try exact H; eauto. i.
    exploit THREADS; try exact TID. i.
    exploit THREADS; try exact TH. i.
    clear DISJOINT THREADS PROMISES.
    dup WF1_SRC. inv WF1_SRC0. inv WF. ss.
    exploit DISJOINT; try exact H; eauto. i.
    exploit THREADS; try exact FIND_SRC. i.
    exploit THREADS; try exact FIND0_SRC. i.
    clear DISJOINT THREADS PROMISES.
    exploit rtc_implies; [eauto|..].
    { etrans.
      - eapply Thread.tau_opt_all; try exact STEP_SRC.
        eapply rtc_implies; try exact STEPS_SRC. i. inv H0. des. econs; eauto.
      - eapply rtc_implies; try exact STEPS_SRC0. i. inv H0. des. econs; eauto.
    }
    intro STEP_SRC_ALL.
    exploit Thread.rtc_all_step_future; try exact STEP_SRC_ALL; eauto. s. i. des.
    exploit Thread.rtc_all_step_disjoint; try exact STEP_SRC_ALL; eauto. s. i. des.
    exploit (@FutureCertify.future_certify lang0 (Thread.mk _ st0_src lc0_src (Thread.global th2_src1)));
      try exact CERTIFY; ss; (try by inv THREAD0; ss); (try by inv SIM1; ss); try apply SIM1.
    { etrans.
      - eapply Memory.future_messages_le.
        etrans; [apply FUTURE|].
        etrans; [apply GL_FUTURE|].
        apply GL_FUTURE0.
      - exploit Thread.rtc_all_step_future; try eapply rtc_implies; try exact STEPS1; eauto.
        { i. inv H0. econs; eauto. }
        { apply Local.cap_wf; ss. }
        { apply Global.cap_wf; ss. }
        s. i. des.
        etrans; [|eapply Memory.future_messages_le; apply GL_FUTURE2].
        apply Memory.cap_messages_le.
        apply Memory.cap_of_cap.
    }
    { exploit Thread.rtc_all_step_disjoint.
      { etrans; [eapply rtc_implies; try exact STEPS|].
        { i. inv H0. econs. eauto. }
        econs 2; try refl. econs. eauto.
      }
      { eauto. }
      { ss. }
      s. i. des.
      exploit Local.cap_wf; try exact LC_WF5. i.
      exploit Thread.rtc_all_step_disjoint; try eapply rtc_implies; try exact STEPS1.
      { i. inv H0. econs; eauto. }
      { eauto. }
      { ss. }
      i. des. apply LC_WF6.
    }
    intro CERTIFY_SRC.
    destruct th2_src0. ss.
    exploit (@PFConfiguration.rtc_program_step_rtc_step
               (Configuration.mk (IdentMap.add tid (existT _ lang state, local) ths1_src) global));
      try exact STEPS_SRC0; s; try apply IdentMap.gss.
    i. des; eauto.

    inv CERTIFY_SRC.
    - exploit (@PFConfiguration.plus_program_step_plus_step
                 (Configuration.mk
                    (IdentMap.add tid (existT _ lang (Thread.state th2_src1), Thread.local th2_src1) ths1_src)
                    (Thread.global th2_src1))); s.
      { erewrite IdentMap.gso; try eapply FIND0_SRC. auto. }
      { eapply rtc_implies; try exact STEPS3.
        i. inv H0. des. econs; eauto.
        inv EVENT0. inv EVENT2. destruct e2; ss.
      }
      { eassumption. }
      { destruct e1; ss. }
      i. des; try by destruct e1; ss.
      esplits; try exact STEP. etrans; [eauto|].
      rewrite IdentMap.add_add_eq. ss.
    - destruct th2_src1 as [st2_src lc2_src gl2_src]. ss.
      assert (RACE: exists e th3_src,
                 Thread.step e
                             (Thread.mk _ st2_src lc2_src (Thread.global th4)) th3_src /\
                 ThreadEvent.is_racy e /\
                 ~ ThreadEvent.is_racy_promise e).
      { exploit Thread.rtc_all_step_future; try eapply rtc_implies; try exact STEPS3; ss.
        { i. inv H0. econs; eauto. }
        i. des.
        inv STEP_FULFILL; inv LOCAL. inv LOCAL0. ss.
        exploit Memory.add_get0; try exact WRITE. i. des.
        inv SIM1. ss. subst.
        inv STEP_RACE; inv LOCAL; ss; subst.
        - esplits.
          + econs 2; cycle 1.
            * econs 8. econs.
              econs 2; try apply GET2; ss.
              eapply TimeFacts.le_lt_lt; try exact TO.
              inv LC_WF3. inv TVIEW_CLOSED. inv CUR.
              exploit Memory.future_closed_timemap; try exact PLN; try apply GL_FUTURE2. i. des.
              eapply Memory.max_ts_spec. eauto.
           * ss. eauto.
          + ss.
          + ss.
        - esplits.
          + econs 2; cycle 1.
            * econs 9. econs. econs 2; try apply GET2; ss.
              eapply TimeFacts.le_lt_lt; try exact TO.
              inv LC_WF3. inv TVIEW_CLOSED. inv CUR.
              exploit Memory.future_closed_timemap; try exact PLN; try apply GL_FUTURE2. i. des.
              eapply Memory.max_ts_spec. eauto.
            * ss. eauto.
          + ss.
          + ss.
        - esplits.
          + econs 2; cycle 1.
            * econs 10. econs 3. econs 2; try apply GET2; ss.
              eapply TimeFacts.le_lt_lt; try exact TO.
              inv LC_WF3. inv TVIEW_CLOSED. inv CUR.
              exploit Memory.future_closed_timemap; try exact PLN; try apply GL_FUTURE2. i. des.
              eapply Memory.max_ts_spec. eauto.
            * ss. eauto.
          + ss.
          + ss.
      }
      des. destruct th3_src.
      exploit (@PFConfiguration.plus_program_step_plus_step
                 (Configuration.mk
                    (IdentMap.add tid (existT _ lang st2_src, lc2_src) ths1_src) gl2_src)); s.
      { erewrite IdentMap.gso; try eapply FIND0_SRC. auto. }
      { eapply rtc_implies; try exact STEPS3.
        i. inv H0. des. econs; eauto.
        inv EVENT0. inv EVENT2. destruct e1; ss.
      }
      { eassumption. }
      { ss. }
      s. i. des; cycle 1.
      { esplits; try exact STEP. etrans; [eauto|].
        rewrite IdentMap.add_add_eq. ss.
      }
      esplits.
      + etrans; [eauto|].
        rewrite IdentMap.add_add_eq.
        eapply rtc_n1; [eauto|]. econs. exact STEP.
      + replace MachineEvent.failure with (ThreadEvent.get_machine_event_pf e1); cycle 1.
        { destruct e1; ss. }
        econs. econs; s.
        * rewrite IdentMap.gso; try by apply IdentMap.gss. ss.
        * eassumption.
        * destruct e1; ss.
  Qed.

  Theorem src_to_ir prog:
    behaviors Configuration.step (Configuration.init prog) <2=
    behaviors (PFConfiguration.step ThreadEvent.get_machine_event_pf) (Configuration.init prog).
  Proof.
    i. remember (Configuration.init prog) as c_ir in PR.
    specialize (init_sim_conf prog). intro SIM.
    specialize (Configuration.init_wf prog). intro WF_IR.
    rewrite <- Heqc_ir in WF_IR.
    rewrite <- Heqc_ir in SIM at 2.
    clear Heqc_ir.
    specialize (Configuration.init_wf prog). intro WF_SRC.
    remember (Configuration.init prog) as c_src.
    clear Heqc_src.
    revert c_src WF_SRC SIM.
    induction PR; i.
    - econs. eauto using sim_conf_terminal.
    - exploit sim_conf_step; try exact SIM; eauto. i. des.
      + eapply rtc_tau_step_behavior; try exact STEPS_SRC.
        econs 3; eauto.
      + exploit Configuration.step_future; try exact STEP; ss. i. des.
        exploit PFConfiguration.rtc_tau_step_future; try exact STEPS_SRC; ss. i. des.
        exploit PFConfiguration.opt_step_future; try exact STEP_SRC; ss. i. des.
        eapply rtc_tau_step_behavior; try exact STEPS_SRC.
        inv STEP_SRC. econs 2; eauto.
      + eapply rtc_tau_step_behavior; try exact STEPS_SRC.
        inv STEP_SRC. econs 2; eauto.
        eapply rtc_tau_step_behavior; try exact STEPS2_SRC.
        econs 3; eauto.
    - exploit sim_conf_step; try exact SIM; eauto. i. des.
      + eapply rtc_tau_step_behavior; try exact STEPS_SRC.
        econs 3; eauto.
      + eapply rtc_tau_step_behavior; try exact STEPS_SRC.
        inv STEP_SRC. econs 3; eauto.
      + eapply rtc_tau_step_behavior; try exact STEPS_SRC.
        inv STEP_SRC. econs 3; eauto.
    - exploit sim_conf_step; try exact SIM; eauto. i. des.
      + eapply rtc_tau_step_behavior; try exact STEPS_SRC.
        econs 3; eauto.
      + exploit Configuration.step_future; try exact STEP; ss. i. des.
        exploit PFConfiguration.rtc_tau_step_future; try exact STEPS_SRC; ss. i. des.
        exploit PFConfiguration.opt_step_future; try exact STEP_SRC; ss. i. des.
        eapply rtc_tau_step_behavior; try exact STEPS_SRC.
        inv STEP_SRC; auto. econs 4; eauto.
      + eapply rtc_tau_step_behavior.
        { etrans; try exact STEPS_SRC.
          inv STEP_SRC; [refl|]. econs 2; eauto.
        }
        eapply rtc_tau_step_behavior; try exact STEPS2_SRC.
        econs 3; eauto.
    - econs 5.
  Qed.
End SrcToIR.
