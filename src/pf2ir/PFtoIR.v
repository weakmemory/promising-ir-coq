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
Require Import Reserves.
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
Require Import PFtoIRThread.

Set Implicit Arguments.


Module PFtoIR.
  Definition future_reserved (rsv: BoolMap.t) (reserved: TimeMap.t) (mem1 mem2: Memory.t): Prop :=
    forall loc from to msg
      (RESERVED: rsv loc = true)
      (GET1: Memory.get loc to mem1 = None)
      (GET2: Memory.get loc to mem2 = Some (from, msg)),
      Time.lt (reserved loc) from.

  Lemma future_reserved_trans
        rsv reserved
        mem1 mem2 mem3
        (FUTURE12: Memory.future mem1 mem2)
        (FUTURE23: Memory.future mem2 mem3)
        (RESERVED12: future_reserved rsv reserved mem1 mem2)
        (RESERVED23: future_reserved rsv reserved mem2 mem3):
    future_reserved rsv reserved mem1 mem3.
  Proof.
    ii. destruct (Memory.get loc to mem2) as [[]|] eqn:GET; eauto 2.
    exploit Memory.future_get1; try exact FUTURE23; try exact GET. i. des.
    rewrite x0 in *. clarify. eauto.
  Qed.

  Lemma future_reserved_mon
        rsv1 rsv2 reserved1 reserved2 mem1 mem2
        (RESERVES_LE: BoolMap.le rsv2 rsv1)
        (RESERVED_LE: TimeMap.le reserved2 reserved1)
        (RESERVED: future_reserved rsv1 reserved1 mem1 mem2):
    future_reserved rsv2 reserved2 mem1 mem2.
  Proof.
    ii. exploit RESERVED; eauto. i.
    eapply TimeFacts.le_lt_lt; eauto.
  Qed.

  Lemma step_future_reserved
        rsv
        lang reserved pf e (th1 th2: Thread.t lang)
        (RESERVED: BoolMap.le rsv (BoolMap.minus (Global.reserves (Thread.global th1))
                                                 (Local.reserves (Thread.local th1))))
        (STEP: Thread.step reserved pf e th1 th2):
    future_reserved rsv reserved
                    (Global.memory (Thread.global th1)) (Global.memory (Thread.global th2)).
  Proof.
    ii. inv STEP; inv LOCAL; ss; try congr; try by (inv LOCAL0; ss; congr).
    - inv LOCAL0. ss.
      revert GET2. erewrite Memory.add_o; eauto. condtac; ss; try congr.
      i. des. inv GET2.
      exploit RESERVED; eauto.
      unfold BoolMap.minus.
      destruct (Global.reserves gl1 loc0), (Local.reserves lc1 loc0); ss. i. eauto.
    - inv LOCAL1. inv LOCAL2. ss.
      revert GET2. erewrite Memory.add_o; eauto. condtac; ss; try congr.
      i. des. inv GET2.
      exploit RESERVED; eauto.
      unfold BoolMap.minus.
      destruct (Global.reserves gl1 loc0), (Local.reserves lc1 loc0); ss. i. eauto.
  Qed.

  Lemma rtc_all_step_future_reserved
        rsv
        lang reserved (th1 th2: Thread.t lang)
        (LC_WF: Local.wf (Thread.local th1) (Thread.global th1))
        (GL_WF: Global.wf (Thread.global th1))
        (RESERVED: BoolMap.le rsv (BoolMap.minus (Global.reserves (Thread.global th1))
                                                 (Local.reserves (Thread.local th1))))
        (STEPS: rtc (@Thread.all_step lang reserved) th1 th2):
    future_reserved rsv reserved
                    (Global.memory (Thread.global th1)) (Global.memory (Thread.global th2)).
  Proof.
    revert RESERVED. induction STEPS; i.
    { ii. congr. }
    inv H. inv USTEP.
    hexploit step_future_reserved; try exact STEP; eauto. i.
    exploit Thread.step_future; try exact STEP0; eauto. i. des.
    exploit Thread.rtc_all_step_future; try exact STEPS; eauto. i. des.
    exploit Thread.step_reserves_minus; eauto. i.
    rewrite x1 in *.
    hexploit IHSTEPS; eauto. i.
    eapply future_reserved_trans; try exact H; ss;
      try apply GL_FUTURE; try apply GL_FUTURE0.
  Qed.

  Lemma rtc_tau_step_future_reserved
        rsv
        lang reserved (th1 th2: Thread.t lang)
        (LC_WF: Local.wf (Thread.local th1) (Thread.global th1))
        (GL_WF: Global.wf (Thread.global th1))
        (RESERVED: BoolMap.le rsv (BoolMap.minus (Global.reserves (Thread.global th1))
                                                 (Local.reserves (Thread.local th1))))
        (STEPS: rtc (@Thread.tau_step lang reserved) th1 th2):
    future_reserved rsv reserved
                    (Global.memory (Thread.global th1)) (Global.memory (Thread.global th2)).
  Proof.
    eapply rtc_all_step_future_reserved; eauto.
    eapply rtc_implies; try exact STEPS.
    i. inv H. inv TSTEP. econs; eauto.
  Qed.

  Variant sim_thread_sl (gl_pf gl_ir: Global.t):
    forall (sl_pf sl_ir: {lang: language & Language.state lang} * Local.t), Prop :=
    | sim_thread_sl_intro
        lang
        st_pf lc_pf
        st_ir lc_ir
        (THREAD: PFtoIRThread.sim_thread (Thread.mk _ st_pf lc_pf gl_pf) (Thread.mk _ st_ir lc_ir gl_ir))
        (CONS: exists gl_past,
            (<<FUTURE: Global.future gl_past gl_ir>>) /\
            (<<RESERVED: future_reserved
                           (Local.reserves lc_ir) (Memory.max_timemap (Global.memory gl_past))
                           (Global.memory gl_past) (Global.memory gl_ir)>>) /\
            (<<LC_WF: Local.wf lc_ir gl_past>>) /\
            (<<GL_WF: Global.wf gl_past>>) /\
            (<<CONS: PFConsistent.spf_consistent (Thread.mk _ st_ir lc_ir gl_past)>>))
      :
      sim_thread_sl gl_pf gl_ir (existT _ lang st_pf, lc_pf) (existT _ lang st_ir, lc_ir)
  .

  Lemma sim_thread_sl_future
        gl_pf gl_ir lang_pf st_pf lc_pf lang_ir st_ir lc_ir
        gl_future_pf gl_future_ir
        (GL_FUTURE_IR: Global.future gl_ir gl_future_ir)
        (RESERVED: future_reserved (Local.reserves lc_ir)
                                   (Memory.max_timemap (Global.memory gl_ir))
                                   (Global.memory gl_ir) (Global.memory gl_future_ir))
        (SC: Global.sc gl_future_pf = Global.sc gl_future_ir)
        (GPROMISES: Global.promises gl_future_pf = BoolMap.bot)
        (GRESERVES: Global.reserves gl_future_pf = BoolMap.bot)
        (MEMORY: Global.memory gl_future_pf = Global.memory gl_future_ir)
        (SIM: sim_thread_sl gl_pf gl_ir
                            (existT _ lang_pf st_pf, lc_pf)
                            (existT _ lang_ir st_ir, lc_ir)):
    sim_thread_sl gl_future_pf gl_future_ir
                  (existT _ lang_pf st_pf, lc_pf)
                  (existT _ lang_ir st_ir, lc_ir).
  Proof.
    inv SIM. Configuration.simplify. econs.
    - inv THREAD. ss.
    - des. exists gl_past.
      splits; ss; try by (etrans; eauto).
      eapply future_reserved_trans; try exact RESERVED0;
        try apply FUTURE; try apply GL_FUTURE_IR.
      eapply future_reserved_mon; try exact RESERVED; try refl.
      eapply Memory.future_max_timemap; try apply GL_WF.
      apply FUTURE.
  Qed.

  Variant sim_conf: forall (c_pf c_ir: Configuration.t), Prop :=
    | sim_conf_intro
        ths_pf gl_pf
        ths_ir gl_ir
        (THS: forall tid,
            option_rel
              (sim_thread_sl gl_pf gl_ir)
              (IdentMap.find tid ths_pf)
              (IdentMap.find tid ths_ir)):
      sim_conf (Configuration.mk ths_pf gl_pf) (Configuration.mk ths_ir gl_ir)
  .

  Lemma init_sim_conf prog: sim_conf (Configuration.init prog) (Configuration.init prog).
  Proof.
    econs. i.
    unfold Threads.init. rewrite IdentMap.Facts.map_o.
    destruct (@UsualFMapPositive.UsualPositiveMap'.find
                (@sigT _ (@Language.syntax ProgramEvent.t)) tid prog); ss.
    econs; ss.
    exists Global.init. splits.
    - refl.
    - ii. ss.
    - apply Local.init_wf.
    - apply Global.init_wf.
    - econs 2; s; try refl.
  Qed.

  Lemma sim_conf_terminal
        c1_pf c1_ir
        (SIM: sim_conf c1_pf c1_ir)
        (TERMINAL: Configuration.is_terminal c1_ir):
    Configuration.is_terminal c1_pf.
  Proof.
    inv SIM. ii. ss.
    specialize (THS tid). rewrite FIND in THS.
    destruct (IdentMap.find tid ths_ir) as [[[lang_ir st_ir] lc_ir]|] eqn:FIND_IR; ss.
    inv THS. Configuration.simplify.
    inv THREAD. ss. subst. splits; ss.
    exploit TERMINAL; eauto. i. des. ss.
  Qed.

  Lemma is_racy_promise_is_racy
        lang released pf e (th1 th2: Thread.t lang)
        (STEP: Thread.step released pf e th1 th2)
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
        c1_pf c1_ir
        e tid c2_ir
        (SIM: sim_conf c1_pf c1_ir)
        (WF1_PF: Configuration.wf c1_pf)
        (WF1_IR: Configuration.wf c1_ir)
        (STEP: Configuration.step e tid c1_ir c2_ir):
    (exists c_pf tid' c2_pf,
        (<<STEPS_PF: rtc (PFConfiguration.tau_step ThreadEvent.get_machine_event_pf)
                         c1_pf c_pf>>) /\
        (<<STEP_PF: PFConfiguration.step ThreadEvent.get_machine_event_pf
                                         MachineEvent.failure tid' c_pf c2_pf>>)) \/
    (exists c_pf c2_pf,
        (<<STEPS_PF: rtc (PFConfiguration.tau_step ThreadEvent.get_machine_event_pf)
                         c1_pf c_pf>>) /\
        (<<STEP_PF: PFConfiguration.opt_step ThreadEvent.get_machine_event_pf
                                             e tid c_pf c2_pf>>) /\
        ((<<SIM2: sim_conf c2_pf c2_ir>>) \/
         exists c3_pf tid' c4_pf,
           (<<STEPS2_PF: rtc (PFConfiguration.tau_step ThreadEvent.get_machine_event_pf)
                             c2_pf c3_pf>>) /\
           (<<STEP2_PF: PFConfiguration.step ThreadEvent.get_machine_event_pf
                                             MachineEvent.failure tid' c3_pf c4_pf>>))).
  Proof.
    destruct c1_pf as [ths1_pf gl1_pf], c1_ir as [ths1_ir gl1_ir].
    inv STEP. dup SIM. inv SIM0. ss.
    rename st1 into st1_ir, lc1 into lc1_ir.
    specialize (THS tid). rewrite TID in *.
    destruct (IdentMap.find tid ths1_pf) as [[[lang_pf st1_pf] lc1_pf]|] eqn:FIND_PF; ss.
    inv THS. Configuration.simplify. clear CONS.

    exploit PFtoIRThread.rtc_tau_step_cases; try exact STEPS. i. des; cycle 1.
    { (* race with a promise *)
      left.
      exploit PFtoIRThread.sim_thread_rtc_step; try exact STEPS0; eauto. i. des.
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
      clear DISJOINT THREADS PROMISES RESERVES. i. des.
      destruct (classic (tid = tid0)).
      { subst. rewrite TID in *. Configuration.simplify. congr. }
      dup SIM. inv SIM0. specialize (THS tid0). rewrite TH in *.
      destruct (IdentMap.find tid0 ths1_pf) as [[[lang0_pf st0_pf] lc0_pf]|] eqn:FIND0_PF; ss.
      inv THS. Configuration.simplify. des.
      exploit FutureCertify.spf_consistent_certify; try exact CONS; eauto. s. intro CERTIFY.

      dup WF1_IR. inv WF1_IR0. inv WF. ss.
      exploit DISJOINT; try exact H; eauto. i.
      exploit THREADS; try exact TID. i.
      exploit THREADS; try exact TH. i.
      clear DISJOINT THREADS PROMISES RESERVES.
      dup WF1_PF. inv WF1_PF0. inv WF. ss.
      exploit DISJOINT; try exact H; eauto. i.
      exploit THREADS; try exact FIND_PF. i.
      exploit THREADS; try exact FIND0_PF. i.
      clear DISJOINT THREADS PROMISES RESERVES.
      exploit Thread.rtc_tau_step_future; try eapply rtc_implies; try exact STEPS_PF; ss.
      { i. inv H0. econs; eauto. }
      i. des.
      exploit Thread.rtc_tau_step_disjoint; try eapply rtc_implies;
        try exact STEPS_PF; ss; try exact x1; eauto.
      { i. inv H0. econs; eauto. }
      i. des.
      replace (Global.memory gl_past) with
        (Global.memory (Thread.global (Thread.fully_reserved (Thread.mk _ st lc gl_past))))
        in CERTIFY at 1 by ss.
      exploit (@FutureCertify.future_certify lang0 (Thread.mk _ st0_pf lc0_pf (Thread.global th2_pf)));
        try exact CERTIFY; ss; (try by inv THREAD0; ss); (try by inv SIM2; ss).
      { etrans; try apply GL_FUTURE.
        inv THREAD0. ss. rewrite MEMORY. apply FUTURE.
      }
      { eapply future_reserved_trans; try eapply RESERVED.
        - apply FUTURE.
        - inv THREAD0. ss. rewrite <- MEMORY. apply GL_FUTURE.
        - hexploit rtc_all_step_future_reserved; try eapply rtc_implies; try exact STEPS0; ss.
          { i. inv H0. econs; eauto. }
          inv SIM2. rewrite MEMORY. i.
          eapply future_reserved_mon; try exact H0.
          + eapply disjoint_minus_le_r; try apply x1; try apply x2; try apply x3.
          + eapply Memory.future_max_timemap; try apply FUTURE; try apply GL_WF0.
      }
      { apply Local.fully_reserved_wf. ss. }
      { apply Global.fully_reserved_wf. ss. }
      instantiate (1:=TimeMap.bot). intro CERTIFY_PF.
      exploit (@PFConfiguration.rtc_program_step_rtc_step (Configuration.mk ths1_pf gl1_pf));
        try eapply STEPS_PF; eauto. s. i. des; eauto.
      inv CERTIFY_PF.
      - destruct pf1; try by (inv STEP_FAILURE; inv LOCAL; ss).
        exploit (@PFConfiguration.plus_program_step_plus_step
                   (Configuration.mk
                      (IdentMap.add tid (existT _ lang (Thread.state th2_pf), Thread.local th2_pf) ths1_pf)
                      (Thread.global th2_pf))); s.
        { erewrite IdentMap.gso; try eapply FIND0_PF. auto. }
        { eapply rtc_implies; try exact STEPS2.
          i. inv H0. des. econs; eauto.
          inv EVENT0. destruct e2; ss.
        }
        { eassumption. }
        i. des; try by destruct e1; ss.
        esplits; try exact STEP. etrans; eauto.
      - destruct th2_pf as [st2_pf lc2_pf gl2_pf]. ss.
        assert (RACE: exists e th3_pf,
                     Thread.step TimeMap.bot true e
                                 (Thread.mk _ st2_pf lc2_pf (Thread.global th3)) th3_pf /\
                     ThreadEvent.is_racy e /\
                     ~ ThreadEvent.is_racy_promise e).
        { exploit Thread.rtc_all_step_future; try eapply rtc_implies; try exact STEPS2; ss.
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
                etrans; [|eapply Memory.future_max_ts]; try apply GL_FUTURE0; try apply GL_WF3.
                inv LC_WF2. inv TVIEW_CLOSED. inv CUR. specialize (PLN loc). des.
                eapply Memory.max_ts_spec; eauto.
              * ss. eauto.
            + ss.
            + ss.
          - esplits.
            + econs 2; cycle 1.
              * econs 9. econs. econs 2; try apply GET2; ss.
                eapply TimeFacts.le_lt_lt; try exact TO.
                etrans; [|eapply Memory.future_max_ts]; try apply GL_FUTURE0; try apply GL_WF3.
                inv LC_WF2. inv TVIEW_CLOSED. inv CUR. specialize (PLN loc). des.
                eapply Memory.max_ts_spec; eauto.
              * ss. eauto.
            + ss.
            + ss.
          - esplits.
            + econs 2; cycle 1.
              * econs 10. econs 3. econs 2; try apply GET2; ss.
                eapply TimeFacts.le_lt_lt; try exact TO.
                etrans; [|eapply Memory.future_max_ts]; try apply GL_FUTURE0; try apply GL_WF3.
                inv LC_WF2. inv TVIEW_CLOSED. inv CUR. specialize (PLN loc). des.
                eapply Memory.max_ts_spec; eauto.
              * ss. eauto.
            + ss.
            + ss.
        }
        des. destruct th3_pf.
        destruct pf1; try by (inv STEP_FULFILL; inv LOCAL; ss).
        exploit (@PFConfiguration.plus_program_step_plus_step
                   (Configuration.mk
                      (IdentMap.add tid (existT _ lang st2_pf, lc2_pf) ths1_pf) gl2_pf)); s.
        { erewrite IdentMap.gso; try eapply FIND0_PF. auto. }
        { eapply rtc_implies; try exact STEPS2.
          i. inv H0. des. econs; eauto.
          inv EVENT0. destruct e1; ss.
        }
        { eassumption. }
        s. i. des; cycle 1.
        { esplits; try exact STEP. etrans; eauto. }
        esplits.
        + etrans; [eauto|]. eapply rtc_n1; [eauto|]. econs. exact STEP.
        + replace MachineEvent.failure with (ThreadEvent.get_machine_event_pf e1); cycle 1.
          { destruct e1; ss. }
          econs. econs; s.
          * rewrite IdentMap.gso; try by apply IdentMap.gss. ss.
          * eassumption.
    }

    destruct (classic (ThreadEvent.is_racy_promise e0)).
    { (* race with a promise *)
      left.
      exploit PFtoIRThread.sim_thread_rtc_step; try exact STEPS0; eauto. i. des.
      exploit is_racy_promise_is_racy; try exact STEP0; ss. i. des.
      exploit Thread.rtc_tau_step_promises_minus; try exact STEPS.
      unfold BoolMap.minus. s. i.
      eapply equal_f in x0.
      rewrite GET, GETP in x0. ss.
      destruct (Global.promises gl1_ir loc) eqn:GPROMISED; ss.
      destruct (Local.promises lc1_ir loc) eqn:PROMISED; ss.
      dup WF1_IR. inv WF1_IR0. inv WF. ss.
      exploit (PROMISES loc); ss.
      clear GL_WF DISJOINT THREADS PROMISES RESERVES. i. des.
      destruct (classic (tid = tid0)).
      { subst. rewrite TID in *. Configuration.simplify. congr. }
      dup SIM. inv SIM0. specialize (THS tid0). rewrite TH in *.
      destruct (IdentMap.find tid0 ths1_pf) as [[[lang0_pf st0_pf] lc0_pf]|] eqn:FIND0_PF; ss.
      inv THS. Configuration.simplify. des.
      exploit FutureCertify.spf_consistent_certify; try exact CONS; eauto. s. intro CERTIFY.

      dup WF1_IR. inv WF1_IR0. inv WF. ss.
      exploit DISJOINT; try exact H; eauto. i.
      exploit THREADS; try exact TID. i.
      exploit THREADS; try exact TH. i.
      clear DISJOINT THREADS PROMISES RESERVES.
      dup WF1_PF. inv WF1_PF0. inv WF. ss.
      exploit DISJOINT; try exact H; eauto. i.
      exploit THREADS; try exact FIND_PF. i.
      exploit THREADS; try exact FIND0_PF. i.
      clear DISJOINT THREADS PROMISES RESERVES.
      exploit Thread.rtc_tau_step_future; try eapply rtc_implies; try exact STEPS_PF; ss.
      { i. inv H1. econs; eauto. }
      i. des.
      exploit Thread.rtc_tau_step_disjoint; try eapply rtc_implies;
        try exact STEPS_PF; ss; try exact x1; eauto.
      { i. inv H1. econs; eauto. }
      i. des.
      replace (Global.memory gl_past) with
        (Global.memory (Thread.global (Thread.fully_reserved (Thread.mk _ st lc gl_past))))
        in CERTIFY at 1 by ss.
      exploit (@FutureCertify.future_certify lang0 (Thread.mk _ st0_pf lc0_pf (Thread.global th2_pf)));
        try exact CERTIFY; ss; (try by inv THREAD0; ss); (try by inv SIM2; ss).
      { etrans; try apply GL_FUTURE.
        inv THREAD0. ss. rewrite MEMORY. apply FUTURE.
      }
      { eapply future_reserved_trans; try eapply RESERVED.
        - apply FUTURE.
        - inv THREAD0. ss. rewrite <- MEMORY. apply GL_FUTURE.
        - hexploit rtc_all_step_future_reserved; try eapply rtc_implies; try exact STEPS0; ss.
          { i. inv H1. econs; eauto. }
          inv SIM2. rewrite MEMORY. i.
          eapply future_reserved_mon; try exact H1.
          + eapply disjoint_minus_le_r; try apply x1; try apply x2; try apply x3.
          + eapply Memory.future_max_timemap; try apply FUTURE; try apply GL_WF.
      }
      { apply Local.fully_reserved_wf. ss. }
      { apply Global.fully_reserved_wf. ss. }
      instantiate (1:=TimeMap.bot). intro CERTIFY_PF.
      exploit (@PFConfiguration.rtc_program_step_rtc_step (Configuration.mk ths1_pf gl1_pf));
        try eapply STEPS_PF; eauto. s. i. des; eauto.
      inv CERTIFY_PF.
      - destruct pf0; try by (inv STEP_FAILURE; inv LOCAL; ss).
        exploit (@PFConfiguration.plus_program_step_plus_step
                   (Configuration.mk
                      (IdentMap.add tid (existT _ lang (Thread.state th2_pf), Thread.local th2_pf) ths1_pf)
                      (Thread.global th2_pf))); s.
        { erewrite IdentMap.gso; try eapply FIND0_PF. auto. }
        { eapply rtc_implies; try exact STEPS2.
          i. inv H1. des. econs; eauto.
          inv EVENT0. destruct e1; ss.
        }
        { eassumption. }
        i. des; try by destruct e; ss.
        esplits; try exact STEP. etrans; eauto.
      - destruct th2_pf as [st2_pf lc2_pf gl2_pf]. ss.
        assert (RACE: exists e th3_pf,
                     Thread.step TimeMap.bot true e
                                 (Thread.mk _ st2_pf lc2_pf (Thread.global th0)) th3_pf /\
                     ThreadEvent.is_racy e /\
                     ~ ThreadEvent.is_racy_promise e).
        { exploit Thread.rtc_all_step_future; try eapply rtc_implies; try exact STEPS2; ss.
          { i. inv H1. econs; eauto. }
          i. des.
          inv STEP_FULFILL; inv LOCAL. inv LOCAL0. ss.
          exploit Memory.add_get0; try exact WRITE. i. des.
          inv SIM2. ss. subst.
          inv STEP0; inv LOCAL; ss; subst.
          - esplits.
            + econs 2; cycle 1.
              * econs 8. econs.
                econs 2; try apply GET2; ss.
                eapply TimeFacts.le_lt_lt; try exact TO.
                etrans; [|eapply Memory.future_max_ts]; try apply GL_FUTURE0; try apply GL_WF2.
                inv LC_WF2. inv TVIEW_CLOSED. inv CUR. specialize (PLN loc). des.
                eapply Memory.max_ts_spec; eauto.
              * ss. eauto.
            + ss.
            + ss.
          - esplits.
            + econs 2; cycle 1.
              * econs 9. econs. econs 2; try apply GET2; ss.
                eapply TimeFacts.le_lt_lt; try exact TO.
                etrans; [|eapply Memory.future_max_ts]; try apply GL_FUTURE0; try apply GL_WF2.
                inv LC_WF2. inv TVIEW_CLOSED. inv CUR. specialize (PLN loc). des.
                eapply Memory.max_ts_spec; eauto.
              * ss. eauto.
            + ss.
            + ss.
          - esplits.
            + econs 2; cycle 1.
              * econs 10. econs 3. econs 2; try apply GET2; ss.
                eapply TimeFacts.le_lt_lt; try exact TO.
                etrans; [|eapply Memory.future_max_ts]; try apply GL_FUTURE0; try apply GL_WF2.
                inv LC_WF2. inv TVIEW_CLOSED. inv CUR. specialize (PLN loc). des.
                eapply Memory.max_ts_spec; eauto.
              * ss. eauto.
            + ss.
            + ss.
        }
        des. destruct th3_pf.
        destruct pf0; try by (inv STEP_FULFILL; inv LOCAL; ss).
        exploit (@PFConfiguration.plus_program_step_plus_step
                   (Configuration.mk
                      (IdentMap.add tid (existT _ lang st2_pf, lc2_pf) ths1_pf) gl2_pf)); s.
        { erewrite IdentMap.gso; try eapply FIND0_PF. auto. }
        { eapply rtc_implies; try exact STEPS2.
          i. inv H1. des. econs; eauto.
          inv EVENT0. destruct e1; ss.
        }
        { eassumption. }
        s. i. des; cycle 1.
        { esplits; try exact STEP. etrans; eauto. }
        esplits.
        + etrans; [eauto|]. eapply rtc_n1; [eauto|]. econs. exact STEP.
        + replace MachineEvent.failure with (ThreadEvent.get_machine_event_pf e); cycle 1.
          { destruct e; ss. }
          econs. econs; s.
          * rewrite IdentMap.gso; try by apply IdentMap.gss. ss.
          * eassumption.
    }

    exploit PFtoIRThread.sim_thread_rtc_step; try exact STEPS0; eauto. i. des.
    exploit PFtoIRThread.sim_thread_step; try exact STEP0; eauto. i. des.
    exploit (@PFConfiguration.opt_plus_program_step_opt_plus_step (Configuration.mk ths1_pf gl1_pf));
      try exact STEPS_PF; eauto. s. i. des; try by left; eauto.
    right.
    unguard. des; try congr. rewrite <- EVENT1.
    esplits; try exact STEPS1; eauto.
    exploit CONSISTENT; try by destruct e0. i.
    exploit PFConsistent.consistent_pf_consistent; try exact x0. i.
    exploit PFConsistent.pf_consistent_spf_consistent; try exact x1. i. des.
    { (* normal step *)
      left. clear x0 x1.
      destruct th2_pf, th2_pf0. ss.
      econs. i.
      dup WF1_IR. inv WF1_IR0. inv WF. ss.
      exploit THREADS; try exact TID. intro LC_WF.
      clear DISJOINT PROMISES RESERVES THREADS.
      exploit Thread.rtc_tau_step_future; try exact STEPS; ss. i. des.
      exploit Thread.step_future; try exact STEP0; ss. i. des.
      destruct (classic (tid = tid0)).
      - subst. repeat rewrite IdentMap.gss. s. econs; ss.
        esplits; try exact SPF_CONS; ss; try refl. ii. congr.
      - repeat (rewrite IdentMap.gso; auto).
        dup SIM. inv SIM1. specialize (THS tid0).
        destruct (IdentMap.find tid0 ths1_pf) as [[[lang0_pf st0_pf] lc0_pf]|] eqn:FIND0_PF;
          destruct (IdentMap.find tid0 ths1_ir) as [[[lang0_ir st0_ir] lc0_ir]|] eqn:FIND0_IR; ss.
        eapply sim_thread_sl_future; try exact THS; try apply SIM0; try by (etrans; eauto).
        hexploit rtc_all_step_future_reserved; cycle 3.
        { eapply rtc_n1.
          - eapply rtc_implies; try exact STEPS. apply tau_union.
          - econs. econs. eauto.
        }
        { eauto. }
        { ss. }
        { ss. }
        { inv WF1_IR. inv WF. ss.
          exploit DISJOINT; try exact H0; eauto. i. inv x0.
          exploit THREADS; try exact FIND0_IR. i. inv x0.
          ii. unfold BoolMap.minus.
          exploit RESERVES0; try exact LHS. i. rewrite x0. s.
          destruct (Local.reserves lc1_ir loc) eqn:RSV; ss.
          exploit RESERVES_DISJOINT; eauto.
        }
    }

    (* race with a promise during certification *)
    right. clear H c2 STEPS1 STEP EVENT0 x0 x1.
    inv SPF_RACE. ss.
    exploit PFtoIRThread.sim_thread_fully_reserved; try exact SIM0. i.
    exploit PFtoIRThread.sim_thread_rtc_step; try eapply rtc_implies; try exact STEPS1; eauto.
    { i. inv H. des. inv EVENT2. econs; eauto. }
    i. des.
    exploit is_racy_promise_is_racy; try exact STEP_RACE; ss. i. des.
    exploit Thread.rtc_all_step_promises_minus; try eapply rtc_implies; try exact STEPS1.
    { i. inv H. des. inv EVENT2. econs; eauto. }
    exploit Thread.rtc_all_step_promises_minus.
    { eapply rtc_n1.
      - eapply rtc_implies; try exact STEPS. i. inv H. econs; eauto.
      - econs. econs. exact STEP0.
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
    clear GL_WF DISJOINT THREADS PROMISES RESERVES. i. des.
    destruct (classic (tid = tid0)).
    { subst. rewrite TID in *. Configuration.simplify. congr. }
    dup SIM. inv SIM3. specialize (THS tid0). rewrite TH in *.
    destruct (IdentMap.find tid0 ths1_pf) as [[[lang0_pf st0_pf] lc0_pf]|] eqn:FIND0_PF; ss.
    inv THS. Configuration.simplify. des.
    exploit FutureCertify.spf_consistent_certify; try exact CONS; eauto. s. intro CERTIFY.

    dup WF1_IR. inv WF1_IR0. inv WF. ss.
    exploit DISJOINT; try exact H; eauto. i.
    exploit THREADS; try exact TID. i.
    exploit THREADS; try exact TH. i.
    clear DISJOINT THREADS PROMISES RESERVES.
    dup WF1_PF. inv WF1_PF0. inv WF. ss.
    exploit DISJOINT; try exact H; eauto. i.
    exploit THREADS; try exact FIND_PF. i.
    exploit THREADS; try exact FIND0_PF. i.
    clear DISJOINT THREADS PROMISES RESERVES.
    exploit rtc_implies; [eauto|..].
    { etrans.
      - eapply Thread.tau_opt_all; try exact STEP_PF.
        eapply rtc_implies; try exact STEPS_PF. i. inv H0. econs; eauto.
      - eapply rtc_implies; try exact STEPS_PF0. i. inv H0. econs; eauto.
    }
    intro STEP_PF_ALL.
    exploit Thread.rtc_all_step_future; try exact STEP_PF_ALL; eauto. s. i. des.
    exploit Thread.rtc_all_step_disjoint; try exact STEP_PF_ALL; eauto. s. i. des.
    replace (Global.memory gl_past) with
      (Global.memory (Thread.global (Thread.fully_reserved (Thread.mk _ st lc gl_past))))
      in CERTIFY at 1 by ss.
    exploit (@FutureCertify.future_certify lang0 (Thread.mk _ st0_pf lc0_pf (Thread.global th2_pf1)));
      try exact CERTIFY; ss; (try by inv THREAD0; ss); (try by inv SIM1; ss).
    { etrans; try apply GL_FUTURE.
      inv THREAD0. ss. rewrite MEMORY. apply FUTURE.
    }
    { eapply future_reserved_trans; try eapply RESERVED.
      { apply FUTURE. }
      { inv THREAD0. ss. rewrite <- MEMORY. apply GL_FUTURE. }
      exploit Thread.rtc_all_step_future;
        try eapply rtc_n1; try eapply rtc_implies; try exact STEPS; ss.
      { i. inv H0. econs. eauto. }
      { econs. econs. apply STEP0. }
      s. i. des.
      exploit Thread.rtc_all_step_future; try eapply rtc_implies; try exact STEPS1; ss.
      { i. inv H0. econs; eauto. }
      { apply Local.fully_reserved_wf. ss. }
      { apply Global.fully_reserved_wf. ss. }
      i. des.
      hexploit rtc_all_step_future_reserved;
        try eapply rtc_n1; try eapply rtc_implies; try exact STEPS; ss.
      { i. inv H0. econs. eauto. }
      { econs. econs. apply STEP0. }
      s. i.
      hexploit rtc_all_step_future_reserved;
        try eapply rtc_implies; try exact STEPS1; ss.
      { apply Local.fully_reserved_wf. ss. }
      { apply Global.fully_reserved_wf. ss. }
      { i. inv H1. econs; eauto. }
      i.
      eapply future_reserved_trans; try eapply future_reserved_mon; try eapply H0; ss.
      { apply GL_FUTURE0. }
      { inv SIM1. rewrite MEMORY. apply GL_FUTURE1. }
      { eapply disjoint_minus_le_r; try apply x1; try apply x2; try apply x3. }
      { apply Memory.future_max_timemap; try apply FUTURE. apply GL_WF. }
      { instantiate (1:=Memory.max_timemap (Global.memory gl_past)). refl. }
      inv SIM1. rewrite MEMORY.
      eapply future_reserved_mon; try exact H1.
      + exploit Thread.rtc_all_step_disjoint;
          try eapply rtc_n1; try eapply rtc_implies; try exact STEPS; ss.
        { i. inv H2. econs. eauto. }
        { econs. econs. apply STEP0. }
        { eauto. }
        { eauto. }
        s. i. des.
        eapply disjoint_minus_le_r; try apply BoolMap.top_spec. apply DISJOINTH0.
      + eapply Memory.future_max_timemap; try apply GL_WF.
        etrans; try apply FUTURE. apply GL_FUTURE0.
    }
    { apply Local.fully_reserved_wf. ss. }
    { apply Global.fully_reserved_wf. ss. }
    instantiate (1:=TimeMap.bot). intro CERTIFY_PF.
    destruct th2_pf0. ss.
    exploit (@PFConfiguration.rtc_program_step_rtc_step
               (Configuration.mk (IdentMap.add tid (existT _ lang state, local) ths1_pf) global));
      try exact STEPS_PF0; s; try apply IdentMap.gss.
    i. des; eauto.
    inv CERTIFY_PF.
    - destruct pf1; try by (inv STEP_FAILURE; inv LOCAL; ss).
      exploit (@PFConfiguration.plus_program_step_plus_step
                 (Configuration.mk
                    (IdentMap.add tid (existT _ lang (Thread.state th2_pf1), Thread.local th2_pf1) ths1_pf)
                    (Thread.global th2_pf1))); s.
      { erewrite IdentMap.gso; try eapply FIND0_PF. auto. }
      { eapply rtc_implies; try exact STEPS3.
        i. inv H0. des. econs; eauto.
        inv EVENT2. destruct e2; ss.
      }
      { eassumption. }
      i. des; try by destruct e1; ss.
      esplits; try exact STEP. etrans; [eauto|].
      rewrite IdentMap.add_add_eq. ss.
    - destruct th2_pf1 as [st2_pf lc2_pf gl2_pf]. ss.
      assert (RACE: exists e th3_pf,
                 Thread.step TimeMap.bot true e
                             (Thread.mk _ st2_pf lc2_pf (Thread.global th4)) th3_pf /\
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
              etrans; [|eapply Memory.future_max_ts]; try apply GL_FUTURE0; try apply GL_WF2.
              inv LC_WF2. inv TVIEW_CLOSED. inv CUR. specialize (PLN loc). des.
              eapply Memory.max_ts_spec; eauto.
            * ss. eauto.
          + ss.
          + ss.
        - esplits.
          + econs 2; cycle 1.
            * econs 9. econs. econs 2; try apply GET2; ss.
              eapply TimeFacts.le_lt_lt; try exact TO.
              etrans; [|eapply Memory.future_max_ts]; try apply GL_FUTURE0; try apply GL_WF2.
              inv LC_WF2. inv TVIEW_CLOSED. inv CUR. specialize (PLN loc). des.
              eapply Memory.max_ts_spec; eauto.
            * ss. eauto.
          + ss.
          + ss.
        - esplits.
          + econs 2; cycle 1.
            * econs 10. econs 3. econs 2; try apply GET2; ss.
              eapply TimeFacts.le_lt_lt; try exact TO.
              etrans; [|eapply Memory.future_max_ts]; try apply GL_FUTURE0; try apply GL_WF2.
              inv LC_WF2. inv TVIEW_CLOSED. inv CUR. specialize (PLN loc). des.
              eapply Memory.max_ts_spec; eauto.
            * ss. eauto.
          + ss.
          + ss.
      }
      des. destruct th3_pf.
      destruct pf1; try by (inv STEP_FULFILL; inv LOCAL; ss).
      exploit (@PFConfiguration.plus_program_step_plus_step
                 (Configuration.mk
                    (IdentMap.add tid (existT _ lang st2_pf, lc2_pf) ths1_pf) gl2_pf)); s.
      { erewrite IdentMap.gso; try eapply FIND0_PF. auto. }
      { eapply rtc_implies; try exact STEPS3.
        i. inv H0. des. econs; eauto.
        inv EVENT2. destruct e1; ss.
      }
      { eassumption. }
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
  Qed.

  Theorem pf_to_ir prog:
    behaviors Configuration.step (Configuration.init prog) <2=
    behaviors (PFConfiguration.step ThreadEvent.get_machine_event_pf) (Configuration.init prog).
  Proof.
    i. remember (Configuration.init prog) as c_ir in PR.
    specialize (init_sim_conf prog). intro SIM.
    specialize (Configuration.init_wf prog). intro WF_IR.
    rewrite <- Heqc_ir in WF_IR.
    rewrite <- Heqc_ir in SIM at 2.
    clear Heqc_ir.
    specialize (Configuration.init_wf prog). intro WF_PF.
    remember (Configuration.init prog) as c_pf.
    clear Heqc_pf.
    revert c_pf WF_PF SIM.
    induction PR; i.
    - econs. eauto using sim_conf_terminal.
    - exploit sim_conf_step; try exact SIM; eauto. i. des.
      + eapply rtc_tau_step_behavior; try exact STEPS_PF.
        econs 3; eauto.
      + exploit Configuration.step_future; try exact STEP; ss. i. des.
        exploit PFConfiguration.rtc_tau_step_future; try exact STEPS_PF; ss. i. des.
        exploit PFConfiguration.opt_step_future; try exact STEP_PF; ss. i. des.
        eapply rtc_tau_step_behavior; try exact STEPS_PF.
        inv STEP_PF. econs 2; eauto.
      + eapply rtc_tau_step_behavior; try exact STEPS_PF.
        inv STEP_PF. econs 2; eauto.
        eapply rtc_tau_step_behavior; try exact STEPS2_PF.
        econs 3; eauto.
    - exploit sim_conf_step; try exact SIM; eauto. i. des.
      + eapply rtc_tau_step_behavior; try exact STEPS_PF.
        econs 3; eauto.
      + eapply rtc_tau_step_behavior; try exact STEPS_PF.
        inv STEP_PF. econs 3; eauto.
      + eapply rtc_tau_step_behavior; try exact STEPS_PF.
        inv STEP_PF. econs 3; eauto.
    - exploit sim_conf_step; try exact SIM; eauto. i. des.
      + eapply rtc_tau_step_behavior; try exact STEPS_PF.
        econs 3; eauto.
      + exploit Configuration.step_future; try exact STEP; ss. i. des.
        exploit PFConfiguration.rtc_tau_step_future; try exact STEPS_PF; ss. i. des.
        exploit PFConfiguration.opt_step_future; try exact STEP_PF; ss. i. des.
        eapply rtc_tau_step_behavior; try exact STEPS_PF.
        inv STEP_PF; auto. econs 4; eauto.
      + eapply rtc_tau_step_behavior.
        { etrans; try exact STEPS_PF.
          inv STEP_PF; [refl|]. econs 2; eauto.
        }
        eapply rtc_tau_step_behavior; try exact STEPS2_PF.
        econs 3; eauto.
    - econs 5.
  Qed.
End PFtoIR.
