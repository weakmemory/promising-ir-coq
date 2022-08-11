From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
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
Require Import Behavior.

Set Implicit Arguments.


Section Simulation.
  Definition SIM := forall (c1_src c1_tgt: Configuration.t), Prop.

  Definition _sim (sim: SIM) (c1_src c1_tgt:Configuration.t): Prop :=
    forall (WF_SRC: Configuration.wf c1_src)
      (WF_TGT: Configuration.wf c1_tgt),
      (<<TERMINAL:
        forall (TERMINAL_TGT: Configuration.is_terminal c1_tgt),
          (<<FAILURE: Configuration.steps_failure c1_src>>) \/
          exists c2_src,
            (<<STEPS_SRC: rtc Configuration.tau_step c1_src c2_src>>) /\
            (<<TERMINAL_SRC: Configuration.is_terminal c2_src>>)>>) /\
      (<<STEP:
        forall e tid_tgt c3_tgt
          (STEP_TGT: Configuration.step e tid_tgt c1_tgt c3_tgt),
          (<<FAILURE: Configuration.steps_failure c1_src>>) \/
          exists tid_src c2_src c3_src,
            (<<STEPS_SRC: rtc Configuration.tau_step c1_src c2_src>>) /\
            (<<STEP_SRC: Configuration.opt_step e tid_src c2_src c3_src>>) /\
            (<<SIM: sim c3_src c3_tgt>>)>>)
  .

  Lemma _sim_mon: monotone2 _sim.
  Proof.
    ii. exploit IN; eauto. i. des.
    econs; eauto. ii.
    exploit STEP; eauto. i. des; eauto.
    right. esplits; eauto.
  Qed.
  Hint Resolve _sim_mon: paco.

  Definition sim: SIM := paco2 _sim bot2.
End Simulation.
#[export] Hint Resolve _sim_mon: paco.


Lemma sim_adequacy
      c_src c_tgt
      (WF_SRC: Configuration.wf c_src)
      (WF_TGT: Configuration.wf c_tgt)
      (SIM: sim c_src c_tgt):
  behaviors Configuration.step c_tgt <2= behaviors Configuration.step c_src.
Proof.
  i. revert c_src WF_SRC WF_TGT SIM.
  induction PR; i.
  - punfold SIM0. exploit SIM0; eauto. i. des.
    hexploit TERMINAL0; eauto. i. des.
    + inv FAILURE.
      eapply rtc_tau_step_behavior; eauto. econs 3; eauto.
    + eapply rtc_tau_step_behavior; eauto. econs 1; eauto.
  - punfold SIM0. exploit SIM0; eauto. i. des.
    exploit STEP0; eauto. i. des.
    + inv FAILURE.
      eapply rtc_tau_step_behavior; eauto. econs 3; eauto.
    + exploit Configuration.step_future; try exact STEP; eauto. i. des.
      exploit Configuration.rtc_tau_step_future; try exact STEPS_SRC; eauto. i. des.
      exploit Configuration.opt_step_future; try exact STEP_SRC; eauto. i. des.
      eapply rtc_tau_step_behavior; eauto.
      inv SIM1; [|done]. inv STEP_SRC. econs 2; eauto.
  - punfold SIM0. exploit SIM0; eauto. i. des.
    exploit STEP0; eauto. i. des.
    + inv FAILURE.
      eapply rtc_tau_step_behavior; eauto. econs 3; eauto.
    + inv STEP_SRC.
      eapply rtc_tau_step_behavior; eauto. econs 3; eauto.
  - punfold SIM0. exploit SIM0; eauto. i. des.
    exploit STEP0; eauto. i. des.
    + inv FAILURE.
      eapply rtc_tau_step_behavior; eauto. econs 3; eauto.
    + exploit Configuration.step_future; try exact STEP; eauto. i. des.
      exploit Configuration.rtc_tau_step_future; try exact STEPS_SRC; eauto. i. des.
      exploit Configuration.opt_step_future; try exact STEP_SRC; eauto. i. des.
      eapply rtc_tau_step_behavior; eauto.
      inv SIM1; [|done]. inv STEP_SRC; eauto. econs 4; eauto.
  - econs 5.
Qed.
