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
Set Nested Proofs Allowed.


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

  Lemma future_reserved_incr
        rsv reserved1 reserved2 mem1 mem2
        (INCR: TimeMap.le reserved2 reserved1)
        (RESERVED: future_reserved rsv reserved1 mem1 mem2):
    future_reserved rsv reserved2 mem1 mem2.
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
    ii. inv STEP; inv STEP0; ss; try congr; try by (inv LOCAL; ss; congr).
    - inv LOCAL. ss.
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
      eapply future_reserved_incr; try exact RESERVED.
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
    inv STEP; inv STEP0; ss.
    - inv LOCAL. inv RACE; ss. eauto.
    - inv LOCAL. inv RACE; ss. eauto.
    - inv LOCAL; des.
      + destruct ordr; ss.
      + destruct ordw; ss.
      + inv RACE; ss. eauto.
  Qed.

  Lemma sim_conf_step
        c1_pf c1_ir
        e tid c2_ir
        (SIM: sim_conf c1_pf c1_ir)
        (WF1_PF: Configuration.wf c1_pf)
        (WF1_IR: Configuration.wf c1_ir)
        (STEP: Configuration.step e tid c1_ir c2_ir):
    (exists c_pf c2_pf,
        (<<STEPS_PF: rtc (PFConfiguration.tau_step ThreadEvent.get_machine_event_pf)
                         c1_pf c_pf>>) /\
        (<<STEP_PF: PFConfiguration.step ThreadEvent.get_machine_event_pf
                                         MachineEvent.failure tid c_pf c2_pf>>)) \/
    (exists c_pf c2_pf,
        (<<STEPS_PF: rtc (PFConfiguration.tau_step ThreadEvent.get_machine_event_pf)
                         c1_pf c_pf>>) /\
        (<<STEP_PF: PFConfiguration.opt_step ThreadEvent.get_machine_event_pf
                                             e tid c_pf c2_pf>>) /\
        (<<SIM2: sim_conf c2_pf c2_ir>>)).
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
      clear GL_WF DISJOINT THREADS PROMISES RESERVES. i. des.
      destruct (classic (tid = tid0)).
      { subst. rewrite TID in *. Configuration.simplify. congr. }
      dup SIM. inv SIM0. specialize (THS tid0). rewrite TH in *.
      destruct (IdentMap.find tid0 ths1_pf) as [[[lang0_pf st0_pf] lc0_pf]|] eqn:FIND0_PF; ss.
      inv THS. Configuration.simplify. des.
      exploit FutureCertify.spf_consistent_certify; try exact CONS; ss.
    }

    destruct (classic (ThreadEvent.is_racy_promise e0)).
    { (* race with a promise *)
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
      admit.
    }

    exploit PFtoIRThread.sim_thread_rtc_step; try exact STEPS0; eauto. i. des.
    exploit PFtoIRThread.sim_thread_step; try exact STEP0; eauto. i. des.
    exploit (@PFConfiguration.rtc_program_step_rtc_step (Configuration.mk ths1_pf gl1_pf));
      try exact STEPS_PF; eauto. s. i. des; eauto.
    unguard. des; cycle 1.
    { (* failure *)
      left.
      inv STEP_PF; ss. destruct th2_pf.
      esplits; eauto.
      rewrite <- EVENT.
      eapply PFConfiguration.program_step_step; s; eauto.
      rewrite IdentMap.gss. refl.
    }

    exploit CONSISTENT; try by destruct e0. i.
    exploit PFConsistent.consistent_pf_consistent; try exact x0. i.
    exploit PFConsistent.pf_consistent_spf_consistent; try exact x1. i. des.
    { (* normal step *)
      clear x0 x1.
      right. destruct th2_pf, th2_pf0. ss.
      esplits; try exact STEPS1.
      - rewrite <- EVENT0.
        eapply PFConfiguration.opt_program_step_opt_step; s; eauto.
        apply IdentMap.gss.
      - ss. econs. i.
        dup WF1_IR. inv WF1_IR0. inv WF. ss.
        exploit THREADS; try exact TID. intro LC_WF.
        clear DISJOINT PROMISES RESERVES THREADS.
        exploit Thread.rtc_tau_step_future; try exact STEPS; ss. i. des.
        exploit Thread.step_future; try exact STEP0; ss. i. des.
        destruct (classic (tid = tid0)).
        + subst. repeat rewrite IdentMap.gss. s. econs; ss.
          esplits; try exact SPF_CONS; ss; try refl. ii. congr.
        + repeat (rewrite IdentMap.gso; auto).
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
    inv SPF_RACE. ss.
    admit.
  Admitted.

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
    - exploit sim_conf_step; try exact SIM; eauto. i. des.
      + eapply rtc_tau_step_behavior; try exact STEPS_PF.
        econs 3; eauto.
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
    - econs 5.
  Qed.
End PFtoIR.
