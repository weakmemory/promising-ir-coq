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
             st1_src lc1_src gl1_src
             st1_tgt lc1_tgt gl1_tgt
    :=
    forall e_tgt st3_tgt lc3_tgt gl3_tgt
      (STEP_TGT: Thread.step e_tgt
                             (Thread.mk _ st1_tgt lc1_tgt gl1_tgt)
                             (Thread.mk _ st3_tgt lc3_tgt gl3_tgt)),
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st1_src lc1_src gl1_src)>>) \/
      exists e_src st2_src lc2_src gl2_src st3_src lc3_src gl3_src,
        (<<FAILURE: ThreadEvent.get_machine_event e_tgt <> MachineEvent.failure>>) /\
        (<<STEPS: rtc (@Thread.tau_step _)
                      (Thread.mk _ st1_src lc1_src gl1_src)
                      (Thread.mk _ st2_src lc2_src gl2_src)>>) /\
        (<<STEP_SRC: Thread.opt_step e_src
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
    forall
      gl1_src gl1_tgt
      (GLOBAL: sim_global gl1_src gl1_tgt)
      (GL_FUTURE_SRC: Global.strong_le gl0_src gl1_src)
      (GL_FUTURE_TGT: Global.le gl0_tgt gl1_tgt)
      (LC_WF_SRC: Local.wf lc1_src gl1_src)
      (LC_WF_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF_SRC: Global.wf gl1_src)
      (GL_WF_TGT: Global.wf gl1_tgt),
      (<<TERMINAL:
        forall (TERMINAL_TGT: (Language.is_terminal lang_tgt) st1_tgt),
          (<<FAILURE: Thread.steps_failure (Thread.mk _ st1_src lc1_src gl1_src)>>) \/
          exists st2_src lc2_src gl2_src,
            (<<STEPS: rtc (@Thread.tau_step _)
                          (Thread.mk _ st1_src lc1_src gl1_src)
                          (Thread.mk _ st2_src lc2_src gl2_src)>>) /\
            (<<GLOBAL: sim_global gl2_src gl1_tgt>>) /\
            (<<TERMINAL_SRC: (Language.is_terminal lang_src) st2_src>>) /\
            (<<LOCAL: sim_local lc2_src lc1_tgt>>) /\
            (<<TERMINAL: sim_terminal st2_src st1_tgt>>)>>) /\
      (<<PROMISES:
        forall (PROMISES_TGT: Local.promises lc1_tgt = BoolMap.bot),
          (<<FAILURE: Thread.steps_failure (Thread.mk _ st1_src lc1_src gl1_src)>>) \/
          exists st2_src lc2_src gl2_src,
            (<<STEPS: rtc (@Thread.tau_step _)
                          (Thread.mk _ st1_src lc1_src gl1_src)
                          (Thread.mk _ st2_src lc2_src gl2_src)>>) /\
            (<<PROMISES_SRC: Local.promises lc2_src = BoolMap.bot>>)>>) /\
      (<<STEP: _sim_thread_step _ _ (@sim_thread lang_src lang_tgt sim_terminal)
                                st1_src lc1_src gl1_src
                                st1_tgt lc1_tgt gl1_tgt>>).

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
      sim_terminal
      e_tgt
      st1_src lc1_src gl1_src
      st1_tgt lc1_tgt gl1_tgt
      st3_tgt lc3_tgt gl3_tgt
      (STEP: @Thread.step lang_tgt e_tgt
                          (Thread.mk _ st1_tgt lc1_tgt gl1_tgt)
                          (Thread.mk _ st3_tgt lc3_tgt gl3_tgt))
      (GLOBAL: sim_global gl1_src gl1_tgt)
      (LC_WF_SRC: Local.wf lc1_src gl1_src)
      (LC_WF_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF_SRC: Global.wf gl1_src)
      (GL_WF_TGT: Global.wf gl1_tgt)
      (SIM: sim_thread sim_terminal st1_src lc1_src gl1_src st1_tgt lc1_tgt gl1_tgt):
  (<<FAILURE: Thread.steps_failure (Thread.mk lang_src st1_src lc1_src gl1_src)>>) \/
  exists e_src st2_src lc2_src gl2_src st3_src lc3_src gl3_src,
    (<<FAILURE: ThreadEvent.get_machine_event e_tgt <> MachineEvent.failure>>) /\
    (<<STEPS: rtc (@Thread.tau_step lang_src)
                  (Thread.mk _ st1_src lc1_src gl1_src)
                  (Thread.mk _ st2_src lc2_src gl2_src)>>) /\
    (<<STEP: Thread.opt_step e_src
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
  punfold SIM. exploit SIM; eauto; try refl. i. des.
  exploit STEP0; eauto. i. des; eauto.
  inv SIM0; [|done]. right.
  exploit Thread.step_future; eauto. s. i. des.
  exploit Thread.rtc_tau_step_future; eauto. s. i. des.
  exploit Thread.opt_step_future; eauto. s. i. des.
  esplits; eauto.
Qed.

Lemma sim_thread_opt_step
      lang_src lang_tgt
      sim_terminal
      e_tgt
      st1_src lc1_src gl1_src
      st1_tgt lc1_tgt gl1_tgt
      st3_tgt lc3_tgt gl3_tgt
      (STEP: @Thread.opt_step lang_tgt e_tgt
                              (Thread.mk _ st1_tgt lc1_tgt gl1_tgt)
                              (Thread.mk _ st3_tgt lc3_tgt gl3_tgt))
      (GLOBAL: sim_global gl1_src gl1_tgt)
      (LC_WF_SRC: Local.wf lc1_src gl1_src)
      (LC_WF_TGT: Local.wf lc1_tgt gl1_tgt)
      (GL_WF_SRC: Global.wf gl1_src)
      (GL_WF_TGT: Global.wf gl1_tgt)
      (SIM: sim_thread sim_terminal st1_src lc1_src gl1_src st1_tgt lc1_tgt gl1_tgt):
  (<<FAILURE: Thread.steps_failure (Thread.mk lang_src st1_src lc1_src gl1_src)>>) \/
  exists e_src st2_src lc2_src gl2_src st3_src lc3_src gl3_src,
    (<<FAILURE: ThreadEvent.get_machine_event e_tgt <> MachineEvent.failure>>) /\
    (<<STEPS: rtc (@Thread.tau_step lang_src)
                  (Thread.mk _ st1_src lc1_src gl1_src)
                  (Thread.mk _ st2_src lc2_src gl2_src)>>) /\
    (<<STEP: Thread.opt_step e_src
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
  inv STEP.
  - right. esplits; eauto; ss.
  - eapply sim_thread_step; eauto.
Qed.

Lemma sim_thread_rtc_step
      lang_src lang_tgt
      sim_terminal
      st1_src lc1_src gl1_src
      th1_tgt th2_tgt
      (STEPS: rtc (@Thread.tau_step lang_tgt) th1_tgt th2_tgt)
      (GLOBAL: sim_global gl1_src (Thread.global th1_tgt))
      (LC_WF_SRC: Local.wf lc1_src gl1_src)
      (LC_WF_TGT: Local.wf (Thread.local th1_tgt) (Thread.global th1_tgt))
      (GL_WF_SRC: Global.wf gl1_src)
      (GL_WF_TGT: Global.wf (Thread.global th1_tgt))
      (SIM: sim_thread sim_terminal
                       st1_src lc1_src gl1_src
                       (Thread.state th1_tgt) (Thread.local th1_tgt) (Thread.global th1_tgt)):
  (<<FAILURE: Thread.steps_failure (Thread.mk lang_src st1_src lc1_src gl1_src)>>) \/
  exists st2_src lc2_src gl2_src,
    (<<STEPS: rtc (@Thread.tau_step lang_src)
                  (Thread.mk _ st1_src lc1_src gl1_src)
                  (Thread.mk _ st2_src lc2_src gl2_src)>>) /\
    (<<GLOBAL: sim_global gl2_src (Thread.global th2_tgt)>>) /\
    (<<LC_WF_SRC: Local.wf lc2_src gl2_src>>) /\
    (<<LC_WF_TGT: Local.wf (Thread.local th2_tgt) (Thread.global th2_tgt)>>) /\
    (<<GL_WF_SRC: Global.wf gl2_src>>) /\
    (<<GL_WF_TGT: Global.wf (Thread.global th2_tgt)>>) /\
    (<<SIM: sim_thread sim_terminal
                       st2_src lc2_src gl2_src
                       (Thread.state th2_tgt) (Thread.local th2_tgt) (Thread.global th2_tgt)>>).
Proof.
  revert GLOBAL LC_WF_SRC LC_WF_TGT GL_WF_SRC GL_WF_TGT SIM.
  revert st1_src lc1_src gl1_src.
  induction STEPS; i.
  { right. esplits; eauto. }
  inv H. destruct x, y. ss.
  exploit Thread.step_future; eauto. s. i. des.
  exploit sim_thread_step; eauto. i. des; eauto.
  exploit IHSTEPS; eauto. i. des.
  - left. inv FAILURE0. des.
    econs; [|eauto|eauto].
    etrans; eauto. inv STEP; eauto.
    econs 2; eauto. econs.
    + eauto.
    + destruct e, e_src; ss.
  - right. destruct z. ss.
    esplits; try apply GLOBAL1; eauto.
    etrans; [eauto|]. etrans; [|eauto]. inv STEP; eauto.
    econs 2; eauto. econs.
    + eauto.
    + destruct e, e_src; ss.
Qed.

Lemma sim_thread_plus_step
      lang_src lang_tgt
      sim_terminal
      e_tgt
      st1_src lc1_src gl1_src
      th1_tgt th2_tgt th3_tgt
      (STEPS: rtc (@Thread.tau_step lang_tgt) th1_tgt th2_tgt)
      (STEP: @Thread.step lang_tgt e_tgt th2_tgt th3_tgt)
      (GLOBAL: sim_global gl1_src (Thread.global th1_tgt))
      (LC_WF_SRC: Local.wf lc1_src gl1_src)
      (LC_WF_TGT: Local.wf (Thread.local th1_tgt) (Thread.global th1_tgt))
      (GL_WF_SRC: Global.wf gl1_src)
      (GL_WF_TGT: Global.wf (Thread.global th1_tgt))
      (SIM: sim_thread sim_terminal
                       st1_src lc1_src gl1_src
                       (Thread.state th1_tgt) (Thread.local th1_tgt) (Thread.global th1_tgt)):
  (<<FAILURE: Thread.steps_failure (Thread.mk lang_src st1_src lc1_src gl1_src)>>) \/
  exists e_src st2_src lc2_src gl2_src st3_src lc3_src gl3_src,
    (<<STEPS: rtc (@Thread.tau_step lang_src)
                  (Thread.mk _ st1_src lc1_src gl1_src)
                  (Thread.mk _ st2_src lc2_src gl2_src)>>) /\
    (<<STEP: Thread.opt_step e_src
                             (Thread.mk _ st2_src lc2_src gl2_src)
                             (Thread.mk _ st3_src lc3_src gl3_src)>>) /\
    (<<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>>) /\
    (<<GLOBAL: sim_global gl3_src (Thread.global th3_tgt)>>) /\
    (<<LC_WF_SRC: Local.wf lc3_src gl3_src>>) /\
    (<<LC_WF_TGT: Local.wf (Thread.local th3_tgt) (Thread.global th3_tgt)>>) /\
    (<<GL_WF_SRC: Global.wf gl3_src>>) /\
    (<<GL_WF_TGT: Global.wf (Thread.global th3_tgt)>>) /\
    (<<SIM: sim_thread sim_terminal
                       st3_src lc3_src gl3_src
                       (Thread.state th3_tgt) (Thread.local th3_tgt) (Thread.global th3_tgt)>>).
Proof.
  destruct th1_tgt, th2_tgt, th3_tgt. ss.
  exploit Thread.rtc_tau_step_future; eauto. s. i. des.
  exploit sim_thread_rtc_step; eauto. s. i. des; eauto.
  exploit Thread.rtc_tau_step_future; try exact STEPS0; eauto. s. i. des.
  exploit sim_thread_step; try exact STEP; try exact SIM0; eauto. s. i. des.
  - left. inv FAILURE. des.
    econs; [|eauto|eauto].
    etrans; eauto.
  - right. rewrite STEPS1 in STEPS0.
    esplits; try exact STEPS0; try exact STEP0; eauto.
Qed.

Lemma sim_thread_steps_failure
      lang_src lang_tgt
      sim_terminal
      e_src e_tgt
      (FAILURE: Thread.steps_failure e_tgt)
      (GLOBAL: sim_global (Thread.global e_src) (Thread.global e_tgt))
      (LC_WF_SRC: Local.wf (Thread.local e_src) (Thread.global e_src))
      (LC_WF_TGT: Local.wf (Thread.local e_tgt) (Thread.global e_tgt))
      (GL_WF_SRC: Global.wf (Thread.global e_src))
      (GL_WF_TGT: Global.wf (Thread.global e_tgt))
      (SIM: @sim_thread lang_src lang_tgt sim_terminal
                        (Thread.state e_src) (Thread.local e_src) (Thread.global e_src)
                        (Thread.state e_tgt) (Thread.local e_tgt) (Thread.global e_tgt)):
  (<<FAILURE: Thread.steps_failure e_src>>).
Proof.
  destruct e_src, e_tgt. ss. inv FAILURE.
  exploit sim_thread_plus_step; eauto. i. des; eauto.
  rewrite EVENT_FAILURE in *. inv STEP; ss.
  esplits; eauto.
Qed.

Lemma sim_thread_future
      lang_src lang_tgt
      sim_terminal
      st_src lc_src gl1_src gl2_src
      st_tgt lc_tgt gl1_tgt gl2_tgt
      (SIM: @sim_thread lang_src lang_tgt sim_terminal st_src lc_src gl1_src st_tgt lc_tgt gl1_tgt)
      (GL_FUTURE_SRC: Global.strong_le gl1_src gl2_src)
      (GL_FUTURE_TGT: Global.le gl1_tgt gl2_tgt):
  sim_thread sim_terminal st_src lc_src gl2_src st_tgt lc_tgt gl2_tgt.
Proof.
  pfold. ii.
  punfold SIM. exploit SIM; (try by etrans; eauto); eauto.
Qed.

Lemma sim_thread_cap
      lang_src lang_tgt
      sim_terminal
      st_src lc_src gl_src
      st_tgt lc_tgt gl_tgt
      (SIM: @sim_thread lang_src lang_tgt sim_terminal st_src lc_src gl_src st_tgt lc_tgt gl_tgt):
  sim_thread sim_terminal
             st_src lc_src (Global.cap_of gl_src)
             st_tgt lc_tgt (Global.cap_of gl_tgt).
Proof.
  eapply sim_thread_future; eauto.
  { eapply Global.cap_strong_le; eauto. }
  { eapply Global.cap_le; eauto. }
Qed.

Lemma sim_thread_consistent
      lang_src lang_tgt
      sim_terminal
      st_src lc_src gl_src
      st_tgt lc_tgt gl_tgt
      (SIM: sim_thread sim_terminal st_src lc_src gl_src st_tgt lc_tgt gl_tgt)
      (GLOBAL: sim_global gl_src gl_tgt)
      (LC_WF_SRC: Local.wf lc_src gl_src)
      (LC_WF_TGT: Local.wf lc_tgt gl_tgt)
      (GL_WF_SRC: Global.wf gl_src)
      (GL_WF_TGT: Global.wf gl_tgt)
      (CONSISTENT: Thread.consistent (Thread.mk lang_tgt st_tgt lc_tgt gl_tgt)):
  Thread.consistent (Thread.mk lang_src st_src lc_src gl_src).
Proof.
  generalize SIM. intro X.
  exploit sim_memory_max_timemap; try eapply GLOBAL; try apply GL_WF_SRC; try apply GL_WF_TGT. i.
  exploit Local.cap_wf; try exact LC_WF_SRC. i.
  exploit Local.cap_wf; try exact LC_WF_TGT. i.
  exploit Global.cap_wf; try exact GL_WF_SRC. i.
  exploit Global.cap_wf; try exact GL_WF_TGT. i.
  hexploit sim_thread_cap; eauto. intros CAP.
  hexploit sim_global_cap; eauto. intros GL.
  inv CONSISTENT.
  - exploit sim_thread_steps_failure; try exact x2; eauto; s; eauto.
  - exploit sim_thread_rtc_step; eauto.
    i. des; eauto. destruct th2. ss.
    punfold SIM0. exploit SIM0; try exact x0; eauto; try refl. i. des.
    exploit PROMISES0; eauto. i. des.
    + econs 1. inv FAILURE.
      econs; [|eauto|eauto]. etrans; eauto.
    + econs 2; [etrans; eauto|]. ss.
Qed.
