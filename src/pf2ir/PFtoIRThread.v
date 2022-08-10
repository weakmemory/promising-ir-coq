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

Set Implicit Arguments.


Module PFtoIRThread.
  Section PFtoIRThread.
    Variable lang: language.

    Variant sim_thread (th_pf th_ir: Thread.t lang): Prop :=
      | sim_thread_intro
          (STATE: Thread.state th_pf = Thread.state th_ir)
          (TVIEW: Local.tview (Thread.local th_pf) = Local.tview (Thread.local th_ir))
          (PROMISES: Local.promises (Thread.local th_pf) = BoolMap.bot)
          (RESERVES: Local.reserves (Thread.local th_pf) = BoolMap.bot)
          (SC: Global.sc (Thread.global th_pf) = Global.sc (Thread.global th_ir))
          (GPROMISES: Global.promises (Thread.global th_pf) = BoolMap.bot)
          (GRESERVES: Global.reserves (Thread.global th_pf) = BoolMap.bot)
          (MEMORY: Global.memory (Thread.global th_pf) = Global.memory (Thread.global th_ir))
    .
    #[local] Hint Constructors sim_thread: core.

    Lemma sim_thread_internal_step
          th1_pf th1_ir
          reserved e th2_ir
          (SIM1: sim_thread th1_pf th1_ir)
          (STEP: Thread.step reserved false e th1_ir th2_ir):
      <<SIM2: sim_thread th1_pf th2_ir>>.
    Proof.
      inv SIM1. inv STEP. inv STEP0; inv LOCAL; ss.
    Qed.

    Lemma sim_thread_program_step
          th1_pf th1_ir
          reserved e th2_ir
          (SIM1: sim_thread th1_pf th1_ir)
          (STEP: Thread.step reserved true e th1_ir th2_ir)
          (PF: ~ ThreadEvent.is_racy_promise e):
      exists th2_pf,
        (<<STEP_PF: Thread.step TimeMap.bot true e th1_pf th2_pf>>) /\
        (<<SIM2: sim_thread th2_pf th2_ir>>).
    Proof.
      destruct th1_ir as [st1_ir [tview1_ir prm1_ir rsv1_ir] [sc1_ir gprm1_ir grsv1_ir mem1_ir]],
          th1_pf as [st1_pf [tview1_pf prm1_pf rsv1_pf] [sc1_pf gprm1_pf grsv1_pf mem1_pf]].
      inv SIM1. ss. subst.
      inv STEP. inv STEP0; ss.
      - esplits; [econs; [|econs 1]|]; eauto.
      - inv LOCAL. ss.
        esplits; [econs; [|econs 2]|]; eauto.
      - inv LOCAL. ss.
        esplits; [econs; [|econs 3]|]; eauto.
        + econs; ss; try by intuition. eauto.
        + ss.
      - inv LOCAL1. inv LOCAL2. ss.
        esplits; [econs; [|econs 4]|]; eauto.
        + econs; ss; try by intuition. eauto.
        + ss.
      - inv LOCAL.
        esplits; [econs; [|econs 5]|]; eauto.
      - inv LOCAL.
        esplits; [econs; [|econs 6]|]; eauto.
      - esplits; [econs; [|econs 7]|]; eauto.
      - destruct to; ss. inv LOCAL. inv RACE. ss.
        esplits; [econs; [|econs 8]|]; eauto.
      - destruct to; ss. inv LOCAL. inv RACE. ss.
        esplits; [econs; [|econs 9]|]; eauto.
      - destruct to; ss.
        + inv LOCAL. inv RACE. ss.
          esplits; [econs; [|econs 10]|]; eauto.
        + esplits; [econs; [|econs 10]|]; eauto.
          apply not_and_or in PF. des.
          * econs 1. destruct ordr; ss.
          * econs 2. destruct ordw; ss.
    Qed.

    Lemma rtc_tau_step_cases
          reserved th1 th2
          (STEPS: rtc (@Thread.tau_step lang reserved) th1 th2):
      (<<STEPS: rtc (pstep (Thread.step_allpf reserved) (strict_pf /1\ ThreadEvent.is_silent)) th1 th2>>) \/
      exists th pf e th2,
        (<<STEPS: rtc (pstep (Thread.step_allpf reserved) (strict_pf /1\ ThreadEvent.is_silent)) th1 th>>) /\
        (<<STEP_RACE: Thread.step reserved pf e th th2>>) /\
        (<<EVENT_RACE: ThreadEvent.is_racy_promise e>>).
    Proof.
      induction STEPS; eauto.
      inv H. inv TSTEP.
      destruct (classic (strict_pf e)).
      - des.
        + left. econs 2; eauto.
        + right. esplits; try exact STEP_RACE; eauto.
      - right. esplits; try exact STEP; eauto.
        apply NNPP in H. ss.
    Qed.

    Lemma sim_thread_rtc_step
          th1_pf th1_ir
          reserved th2_ir
          (SIM1: sim_thread th1_pf th1_ir)
          (STEPS: rtc (pstep (Thread.step_allpf reserved) (strict_pf /1\ ThreadEvent.is_silent)) th1_ir th2_ir):
      exists th2_pf,
        (<<STEP_PF: rtc (tau (Thread.step TimeMap.bot true)) th1_pf th2_pf>>) /\
        (<<SIM2: sim_thread th2_pf th2_ir>>).
    Proof.
      revert th1_pf SIM1.
      induction STEPS; i; eauto.
      inv H. inv STEP. des.
      destruct pf.
      - exploit sim_thread_program_step; eauto. i. des.
        exploit IHSTEPS; eauto. i. des.
        esplits; [econs 2|]; eauto.
      - exploit sim_thread_internal_step; eauto.
    Qed.
  End PFtoIRThread.
End PFtoIRThread.
