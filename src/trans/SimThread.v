Require Import RelationClasses.

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
Require Import BoolMap.
Require Import Promises.
Require Import Reserves.
Require Import Cell.
Require Import Memory.
Require Import Global.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import SimLocal.
Require Import SimMemory.
Require Import SimGlobal.

Set Implicit Arguments.


Section SimulationThread.
  Definition SIM_TERMINAL (lang_src lang_tgt:language) :=
    forall (st_src:(Language.state lang_src)) (st_tgt:(Language.state lang_tgt)), Prop.

  Definition SIM_THREAD :=
    forall (lang_src lang_tgt:language) (sim_terminal: SIM_TERMINAL lang_src lang_tgt)
      (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (gl0_src:Global.t)
      (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (gl0_tgt:Global.t), Prop.

  Definition _sim_thread_step
             (lang_src lang_tgt:language)
             (sim_thread:
               forall (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (gl0_src:Global.t)
                 (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (gl0_tgt:Global.t), Prop)
             reserved_src st1_src lc1_src gl1_src
             reserved_tgt st1_tgt lc1_tgt gl1_tgt
    :=
    forall pf_tgt e_tgt st3_tgt lc3_tgt gl3_tgt
      (STEP_TGT: Thread.step reserved_tgt pf_tgt e_tgt
                             (Thread.mk _ st1_tgt lc1_tgt gl1_tgt)
                             (Thread.mk _ st3_tgt lc3_tgt gl3_tgt)),
      (<<FAILURE: Thread.steps_failure reserved_src (Thread.mk _ st1_src lc1_src gl1_src)>>) \/
      exists e_src st2_src lc2_src gl2_src st3_src lc3_src gl3_src,
        (<<FAILURE: ThreadEvent.get_machine_event e_tgt <> MachineEvent.failure>>) /\
        (<<STEPS: rtc (@Thread.tau_step _ reserved_src)
                      (Thread.mk _ st1_src lc1_src gl1_src)
                      (Thread.mk _ st2_src lc2_src gl2_src)>>) /\
        (<<STEP_SRC: Thread.opt_step reserved_src e_src
                                     (Thread.mk _ st2_src lc2_src gl2_src)
                                     (Thread.mk _ st3_src lc3_src gl3_src)>>) /\
        (<<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>>) /\
        (<<GLOBAL3: sim_global gl3_src gl3_tgt>>) /\
        (<<SIM: sim_thread st3_src lc3_src gl3_src st3_tgt lc3_tgt gl3_tgt>>).

  Definition _sim_thread
             (sim_thread: SIM_THREAD)
             (lang_src lang_tgt:language)
             (sim_terminal: SIM_TERMINAL lang_src lang_tgt)
             (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (gl0_src:Global.t)
             (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (gl0_tgt:Global.t): Prop :=
    forall reserved_src reserved_tgt
      gl1_src gl1_tgt
      (RESERVED: OptTimeMap.le reserved_src reserved_tgt)
      (GLOBAL: sim_global gl1_src gl1_tgt)
      (GL_FUTURE_SRC: Global.future gl0_src gl1_src)
      (GL_FUTURE_TGT: Global.future gl0_tgt gl1_tgt)
      (LC_WF_SRC: Local.wf lc1_src gl1_src)
      (LC_WF_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF_SRC: Global.wf gl1_src)
      (GL_WF_TGT: Global.wf gl1_tgt),
      (<<TERMINAL:
        forall (TERMINAL_TGT: (Language.is_terminal lang_tgt) st1_tgt),
          (<<FAILURE: Thread.steps_failure reserved_src (Thread.mk _ st1_src lc1_src gl1_src)>>) \/
          exists st2_src lc2_src gl2_src,
            (<<STEPS: rtc (@Thread.tau_step _ reserved_src)
                          (Thread.mk _ st1_src lc1_src gl1_src)
                          (Thread.mk _ st2_src lc2_src gl2_src)>>) /\
            (<<GLOBAL: sim_global gl2_src gl1_tgt>>) /\
            (<<TERMINAL_SRC: (Language.is_terminal lang_src) st2_src>>) /\
            (<<LOCAL: sim_local lc2_src lc1_tgt>>) /\
            (<<TERMINAL: sim_terminal st2_src st1_tgt>>)>>) /\
      (<<PROMISES:
        forall (PROMISES_TGT: Local.promises lc1_tgt = BoolMap.bot),
          (<<FAILURE: Thread.steps_failure reserved_src (Thread.mk _ st1_src lc1_src gl1_src)>>) \/
          exists st2_src lc2_src gl2_src,
            (<<STEPS: rtc (@Thread.tau_step _ reserved_src)
                          (Thread.mk _ st1_src lc1_src gl1_src)
                          (Thread.mk _ st2_src lc2_src gl2_src)>>) /\
            (<<PROMISES_SRC: Local.promises lc2_src = BoolMap.bot>>)>>) /\
      (<<STEP: _sim_thread_step _ _ (@sim_thread lang_src lang_tgt sim_terminal)
                                reserved_src st1_src lc1_src gl1_src
                                reserved_tgt st1_tgt lc1_tgt gl1_tgt>>).

  Lemma _sim_thread_mon: monotone9 _sim_thread.
  Proof.
    ii. exploit IN; eauto. i. des.
    splits; eauto. ii.
    exploit STEP; eauto. i. des; eauto.
    right. esplits; eauto.
  Qed.
  #[local] Hint Resolve _sim_thread_mon: paco.

  Definition sim_thread: SIM_THREAD := paco9 _sim_thread bot9.

  Lemma sim_thread_mon
        (lang_src lang_tgt:language)
        (sim_terminal1 sim_terminal2: SIM_TERMINAL lang_src lang_tgt)
        (SIM: sim_terminal1 <2= sim_terminal2):
    sim_thread sim_terminal1 <6= sim_thread sim_terminal2.
  Proof.
    pcofix CIH. i. punfold PR. pfold. ii.
    exploit PR; eauto. i. des.
    splits; auto.
    - i. exploit TERMINAL; eauto. i. des; eauto.
      right. esplits; eauto.
    - ii. exploit STEP; eauto. i. des; eauto.
      inv SIM0; [|done].
      right. esplits; eauto.
  Qed.
End SimulationThread.
#[export] Hint Resolve _sim_thread_mon: paco.


Lemma sim_thread_step
      lang_src lang_tgt
      reserved_src reserved_tgt
      sim_terminal
      pf_tgt e_tgt
      st1_src lc1_src gl1_src
      st1_tgt lc1_tgt gl1_tgt
      st3_tgt lc3_tgt gl3_tgt
      (STEP: @Thread.step lang_tgt reserved_tgt pf_tgt e_tgt
                          (Thread.mk _ st1_tgt lc1_tgt gl1_tgt)
                          (Thread.mk _ st3_tgt lc3_tgt gl3_tgt))
      (RESERVED: OptTimeMap.le reserved_src reserved_tgt)
      (GLOBAL: sim_global gl1_src gl1_tgt)
      (LC_WF_SRC: Local.wf lc1_src gl1_src)
      (LC_WF_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF_SRC: Global.wf gl1_src)
      (GL_WF_TGT: Global.wf gl1_tgt)
      (SIM: sim_thread sim_terminal st1_src lc1_src gl1_src st1_tgt lc1_tgt gl1_tgt):
  (<<FAILURE: Thread.steps_failure reserved_src (Thread.mk lang_src st1_src lc1_src gl1_src)>>) \/
  exists e_src st2_src lc2_src gl2_src st3_src lc3_src gl3_src,
    (<<FAILURE: ThreadEvent.get_machine_event e_tgt <> MachineEvent.failure>>) /\
    (<<STEPS: rtc (@Thread.tau_step lang_src reserved_src)
                  (Thread.mk _ st1_src lc1_src gl1_src)
                  (Thread.mk _ st2_src lc2_src gl2_src)>>) /\
    (<<STEP: Thread.opt_step reserved_src e_src
                             (Thread.mk _ st2_src lc2_src gl2_src)
                             (Thread.mk _ st3_src lc3_src gl3_src)>>) /\
    (<<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>>) /\
    (<<GLOBAL: sim_global gl3_src gl3_tgt>>) /\
    (<<LC_WF_SRC: Local.wf lc3_src gl3_src>>) /\
    (<<LC_WF_TGT: Local.wf lc3_tgt gl3_tgt>>) /\
    (<<GL_WF_SRC: Global.wf gl3_src>>) /\
    (<<GL_WF_TGT: Global.wf gl3_tgt>>) /\
    (<<SIM: sim_thread sim_terminal st3_src lc3_src gl3_src st3_tgt lc3_tgt gl3_tgt>>).
Proof.
  hexploit step_promise_consistent; eauto. s. i.
  punfold SIM. exploit SIM; eauto; try refl. i. des.
  exploit Thread.step_future; eauto. s. i. des.
  exploit STEP0; eauto. i. des; eauto.
  inv SIM0; [|done]. right.
  exploit Thread.rtc_tau_step_future; eauto. s. i. des.
  exploit Thread.opt_step_future; eauto. s. i. des.
  esplits; eauto.
Qed.

Lemma sim_thread_opt_step
      lang_src lang_tgt
      sim_terminal
      e_tgt
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      st3_tgt lc3_tgt sc3_tgt mem3_tgt
      (STEP: @Thread.opt_step lang_tgt e_tgt
                              (Thread.mk _ st1_tgt lc1_tgt sc1_tgt mem1_tgt)
                              (Thread.mk _ st3_tgt lc3_tgt sc3_tgt mem3_tgt))
      (SC: TimeMap.le sc1_src sc1_tgt)
      (MEMORY: sim_memory mem1_src mem1_tgt)
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed mem1_tgt)
      (CONS_TGT: Local.promise_consistent lc3_tgt)
      (SIM: sim_thread sim_terminal st1_src lc1_src sc1_src mem1_src st1_tgt lc1_tgt sc1_tgt mem1_tgt):
  <<FAILURE: Thread.steps_failure (Thread.mk lang_src st1_src lc1_src sc1_src mem1_src)>> \/
  exists e_src st2_src lc2_src sc2_src mem2_src st3_src lc3_src sc3_src mem3_src,
    <<FAILURE: ThreadEvent.get_machine_event e_tgt <> MachineEvent.failure>> /\
    <<STEPS: rtc (@Thread.tau_step lang_src)
                 (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                 (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
    <<STEP: Thread.opt_step e_src
                            (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                            (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>> /\
    <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
    <<SC: TimeMap.le sc3_src sc3_tgt>> /\
    <<MEMORY: sim_memory mem3_src mem3_tgt>> /\
    <<WF_SRC: Local.wf lc3_src mem3_src>> /\
    <<WF_TGT: Local.wf lc3_tgt mem3_tgt>> /\
    <<SC_SRC: Memory.closed_timemap sc3_src mem3_src>> /\
    <<SC_TGT: Memory.closed_timemap sc3_tgt mem3_tgt>> /\
    <<MEM_SRC: Memory.closed mem3_src>> /\
    <<MEM_TGT: Memory.closed mem3_tgt>> /\
    <<SIM: sim_thread sim_terminal st3_src lc3_src sc3_src mem3_src st3_tgt lc3_tgt sc3_tgt mem3_tgt>>.
Proof.
  inv STEP.
  - right. esplits; eauto; ss. econs 1.
  - eapply sim_thread_step; eauto.
Qed.

Lemma sim_thread_rtc_step
      lang_src lang_tgt
      sim_terminal
      st1_src lc1_src sc1_src mem1_src
      e1_tgt e2_tgt
      (STEPS: rtc (@Thread.tau_step lang_tgt) e1_tgt e2_tgt)
      (SC: TimeMap.le sc1_src (Thread.sc e1_tgt))
      (MEMORY: sim_memory mem1_src (Thread.memory e1_tgt))
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed (Thread.memory e1_tgt))
      (CONS_TGT: Local.promise_consistent (Thread.local e2_tgt))
      (SIM: sim_thread sim_terminal st1_src lc1_src sc1_src mem1_src (Thread.state e1_tgt) (Thread.local e1_tgt) (Thread.sc e1_tgt) (Thread.memory e1_tgt)):
  <<FAILURE: Thread.steps_failure (Thread.mk lang_src st1_src lc1_src sc1_src mem1_src)>> \/
  exists st2_src lc2_src sc2_src mem2_src,
    <<STEPS: rtc (@Thread.tau_step lang_src)
                 (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                 (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
    <<SC: TimeMap.le sc2_src (Thread.sc e2_tgt)>> /\
    <<MEMORY: sim_memory mem2_src (Thread.memory e2_tgt)>> /\
    <<WF_SRC: Local.wf lc2_src mem2_src>> /\
    <<WF_TGT: Local.wf (Thread.local e2_tgt) (Thread.memory e2_tgt)>> /\
    <<SC_SRC: Memory.closed_timemap sc2_src mem2_src>> /\
    <<SC_TGT: Memory.closed_timemap (Thread.sc e2_tgt) (Thread.memory e2_tgt)>> /\
    <<MEM_SRC: Memory.closed mem2_src>> /\
    <<MEM_TGT: Memory.closed (Thread.memory e2_tgt)>> /\
    <<SIM: sim_thread sim_terminal st2_src lc2_src sc2_src mem2_src (Thread.state e2_tgt) (Thread.local e2_tgt) (Thread.sc e2_tgt) (Thread.memory e2_tgt)>>.
Proof.
  revert SC MEMORY WF_SRC WF_TGT SC_SRC SC_TGT MEM_SRC MEM_TGT SIM.
  revert st1_src lc1_src sc1_src mem1_src.
  induction STEPS; i.
  { right. esplits; eauto. }
  inv H. inv TSTEP. destruct x, y. ss.
  exploit Thread.step_future; eauto. s. i. des.
  hexploit rtc_tau_step_promise_consistent; eauto. s. i.
  exploit sim_thread_step; eauto. i. des; eauto.
  exploit IHSTEPS; eauto. i. des.
  - left. inv FAILURE0. des.
    unfold Thread.steps_failure. esplits; [|eauto|eauto].
    etrans; eauto. etrans; eauto. inv STEP0; eauto.
    econs 2; eauto. econs.
    + econs. eauto.
    + destruct e, e_src; ss.
  - right. destruct z. ss.
    esplits; try apply MEMORY1; eauto.
    etrans; [eauto|]. etrans; [|eauto]. inv STEP0; eauto.
    econs 2; eauto. econs.
    + econs. eauto.
    + destruct e, e_src; ss.
Qed.

Lemma sim_thread_plus_step
      lang_src lang_tgt
      sim_terminal
      pf_tgt e_tgt
      st1_src lc1_src sc1_src mem1_src
      e1_tgt e2_tgt e3_tgt
      (STEPS: rtc (@Thread.tau_step lang_tgt) e1_tgt e2_tgt)
      (STEP: @Thread.step lang_tgt pf_tgt e_tgt e2_tgt e3_tgt)
      (SC: TimeMap.le sc1_src (Thread.sc e1_tgt))
      (MEMORY: sim_memory mem1_src (Thread.memory e1_tgt))
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed (Thread.memory e1_tgt))
      (CONS_TGT: Local.promise_consistent (Thread.local e3_tgt))
      (SIM: sim_thread sim_terminal st1_src lc1_src sc1_src mem1_src (Thread.state e1_tgt) (Thread.local e1_tgt) (Thread.sc e1_tgt) (Thread.memory e1_tgt)):
  <<FAILURE: Thread.steps_failure (Thread.mk lang_src st1_src lc1_src sc1_src mem1_src)>> \/
  exists e_src st2_src lc2_src sc2_src mem2_src st3_src lc3_src sc3_src mem3_src,
    <<FAILURE: ThreadEvent.get_machine_event e_tgt <> MachineEvent.failure>> /\
    <<STEPS: rtc (@Thread.tau_step lang_src)
                 (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                 (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
    <<STEP: Thread.opt_step e_src
                            (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                            (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>> /\
    <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
    <<SC: TimeMap.le sc3_src (Thread.sc e3_tgt)>> /\
    <<MEMORY: sim_memory mem3_src (Thread.memory e3_tgt)>> /\
    <<WF_SRC: Local.wf lc3_src mem3_src>> /\
    <<WF_TGT: Local.wf (Thread.local e3_tgt) (Thread.memory e3_tgt)>> /\
    <<SC_SRC: Memory.closed_timemap sc3_src mem3_src>> /\
    <<SC_TGT: Memory.closed_timemap (Thread.sc e3_tgt) (Thread.memory e3_tgt)>> /\
    <<MEM_SRC: Memory.closed mem3_src>> /\
    <<MEM_TGT: Memory.closed (Thread.memory e3_tgt)>> /\
    <<SIM: sim_thread sim_terminal st3_src lc3_src sc3_src mem3_src (Thread.state e3_tgt) (Thread.local e3_tgt) (Thread.sc e3_tgt) (Thread.memory e3_tgt)>>.
Proof.
  destruct e1_tgt, e2_tgt, e3_tgt. ss.
  exploit Thread.rtc_tau_step_future; eauto. s. i. des.
  hexploit step_promise_consistent; eauto. s. i.
  exploit sim_thread_rtc_step; eauto. s. i. des; eauto.
  exploit Thread.rtc_tau_step_future; try exact STEPS0; eauto. s. i. des.
  exploit sim_thread_step; try exact STEP; try exact SIM0; eauto. s. i. des.
  - left. inv FAILURE. des.
    unfold Thread.steps_failure. esplits; [|eauto|eauto].
    etrans; eauto.
  - right. rewrite STEPS1 in STEPS0.
    esplits; try exact STEPS0; try exact STEP0; eauto.
Qed.

Lemma sim_thread_future
      lang_src lang_tgt
      sim_terminal
      st_src lc_src sc1_src sc2_src mem1_src mem2_src
      st_tgt lc_tgt sc1_tgt sc2_tgt mem1_tgt mem2_tgt
      (SIM: @sim_thread lang_src lang_tgt sim_terminal st_src lc_src sc1_src mem1_src st_tgt lc_tgt sc1_tgt mem1_tgt)
      (SC_FUTURE_SRC: TimeMap.le sc1_src sc2_src)
      (SC_FUTURE_TGT: TimeMap.le sc1_tgt sc2_tgt)
      (MEM_FUTURE_SRC: Memory.future_weak mem1_src mem2_src)
      (MEM_FUTURE_TGT: Memory.future_weak mem1_tgt mem2_tgt):
  sim_thread sim_terminal st_src lc_src sc2_src mem2_src st_tgt lc_tgt sc2_tgt mem2_tgt.
Proof.
  pfold. ii.
  punfold SIM. exploit SIM; (try by etrans; eauto); eauto.
Qed.


Lemma sim_thread_consistent
      lang_src lang_tgt
      sim_terminal
      st_src lc_src sc_src mem_src
      st_tgt lc_tgt sc_tgt mem_tgt
      (SIM: sim_thread sim_terminal st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt)
      (SC: TimeMap.le sc_src sc_tgt)
      (MEMORY: sim_memory mem_src mem_tgt)
      (WF_SRC: Local.wf lc_src mem_src)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (SC_SRC: Memory.closed_timemap sc_src mem_src)
      (SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_SRC: Memory.closed mem_src)
      (MEM_TGT: Memory.closed mem_tgt)
      (CONSISTENT: Thread.consistent (Thread.mk lang_tgt st_tgt lc_tgt sc_tgt mem_tgt)):
  Thread.consistent (Thread.mk lang_src st_src lc_src sc_src mem_src).
Proof.
  hexploit consistent_promise_consistent; eauto. s. i.
  generalize SIM. intro X.
  punfold X. exploit X; eauto; try refl. i. des.
  ii. ss.
  exploit Memory.cap_exists; try exact MEM_TGT. i. des.
  exploit cap_property; try exact CAP; eauto. i. des.
  exploit cap_property; try exact CAP0; eauto. i. des.
  exploit sim_memory_cap; try exact MEMORY; eauto. i. des.
  exploit CONSISTENT; eauto. s. i. des.
  - left. inv FAILURE. des.
    exploit sim_thread_future; try exact SIM; try exact FUTURE; try exact FUTURE0; try refl. i.
    exploit sim_thread_plus_step; try exact STEPS; try exact FAILURE; try exact x2; eauto; try refl.
    { inv STEP_FAILURE; inv STEP0; ss. inv LOCAL; ss; inv LOCAL0; ss. }
    i. des; ss.
  - hexploit Local.bot_promise_consistent; eauto. i.
    exploit sim_thread_future; try exact SIM; try exact FUTURE; try exact FUTURE0; try refl. i.
    exploit sim_thread_rtc_step; try apply STEPS; try exact x1; eauto; try refl. i. des; eauto.
    destruct e2. ss.
    punfold SIM0. exploit SIM0; eauto; try refl. i. des.
    exploit PROMISES1; eauto. i. des.
    + left. unfold Thread.steps_failure in *. des.
      esplits; [|eauto|eauto]. etrans; eauto.
    + right. eexists (Thread.mk _ _ _ _ _). splits; [|eauto].
      etrans; eauto.
Qed.
