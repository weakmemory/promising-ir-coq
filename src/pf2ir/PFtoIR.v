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
    ii. destruct (Memory.get loc to mem2) as [[]|] eqn:GET; eauto.
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
        (STATE: st_pf = st_ir)
        (TVIEW: Local.tview lc_pf = Local.tview lc_ir)
        (PROMISES: Local.promises lc_pf = BoolMap.bot)
        (RESERVES: Local.reserves lc_pf = BoolMap.bot)
        (SC: Global.sc gl_pf = Global.sc gl_ir)
        (GPROMISES: Global.promises gl_pf = BoolMap.bot)
        (GRESERVES: Global.reserves gl_pf = BoolMap.bot)
        (MEMORY: Global.memory gl_pf = Global.memory gl_ir)
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
    inv THS. Configuration.simplify. splits; ss.
    exploit TERMINAL; eauto. i. des. ss.
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
  Admitted.

  Theorem pf_to_ir prog:
    behaviors Configuration.step (Configuration.init prog) <2=
    behaviors (PFConfiguration.step ThreadEvent.get_machine_event_pf) (Configuration.init prog).
  Proof.
  Admitted.
End PFtoIR.
