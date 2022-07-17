Require Import Bool.
Require Import RelationClasses.

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

Set Implicit Arguments.


Variant tau T (step: forall (e:ThreadEvent.t) (th1 th2:T), Prop) (th1 th2:T): Prop :=
| tau_intro
    e
    (TSTEP: step e th1 th2)
    (EVENT: ThreadEvent.get_machine_event e = MachineEvent.silent)
.
#[export] Hint Constructors tau: core.

Variant union E T (step: forall (e:E) (th1 th2:T), Prop) (th1 th2:T): Prop :=
| union_intro
    e
    (USTEP: step e th1 th2)
.
#[export] Hint Constructors union: core.

Lemma tau_mon T (step1 step2: forall (e:ThreadEvent.t) (th1 th2:T), Prop)
      (STEP: step1 <3= step2):
  tau step1 <2= tau step2.
Proof.
  i. inv PR. econs; eauto.
Qed.

Lemma union_mon E T (step1 step2: forall (e:E) (th1 th2:T), Prop)
      (STEP: step1 <3= step2):
  union step1 <2= union step2.
Proof.
  i. inv PR. econs; eauto.
Qed.

Lemma tau_union: tau <4= (@union ThreadEvent.t).
Proof.
  ii. inv PR. econs. eauto.
Qed.


Module Thread.
  Section Thread.
    Variable (lang: language).
    Variable (reserved: OptTimeMap.t).

    Structure t := mk {
      state: (Language.state lang);
      local: Local.t;
      global: Global.t;
    }.

    Variant step: forall (pf: bool) (e: ThreadEvent.t) (th1 th2: t), Prop :=
    | step_internal
        e st lc1 gl1 lc2 gl2
        (STEP: Local.internal_step e lc1 gl1 lc2 gl2):
      step false e (mk st lc1 gl1) (mk st lc2 gl2)
    | step_program
        e sth1 lc1 gl1 sth2 lc2 gl2
        (STATE: Language.step lang (ThreadEvent.get_program_event e) sth1 sth2)
        (STEP: Local.program_step reserved e lc1 gl1 lc2 gl2):
        step true e (mk sth1 lc1 gl1) (mk sth2 lc2 gl2)
    .
    #[local] Hint Constructors step: core.

    Variant step_allpf (e:ThreadEvent.t) (th1 th2:t): Prop :=
    | step_nopf_intro
        pf
        (STEP: step pf e th1 th2)
    .
    #[local] Hint Constructors step_allpf: core.

    Lemma allpf pf: step pf <3= step_allpf.
    Proof.
      i. econs. eauto.
    Qed.

    Definition pf_tau_step := tau (step true).
    Hint Unfold pf_tau_step: core.

    Definition tau_step := tau step_allpf.
    Hint Unfold tau_step: core.

    Definition all_step := union step_allpf.
    Hint Unfold all_step: core.

    Variant opt_step: forall (e:ThreadEvent.t) (th1 th2:t), Prop :=
    | step_none
        e:
        opt_step ThreadEvent.silent e e
    | step_some
        pf e th1 th2
        (STEP: step pf e th1 th2):
        opt_step e th1 th2
    .
    #[local] Hint Constructors opt_step: core.

    Lemma tau_opt_tau
          th1 th2 th3 e
          (STEPS: rtc tau_step th1 th2)
          (STEP: opt_step e th2 th3)
          (EVENT: ThreadEvent.get_machine_event e = MachineEvent.silent):
      rtc tau_step th1 th3.
    Proof.
      induction STEPS.
      - inv STEP; eauto.
      - exploit IHSTEPS; eauto.
    Qed.

    Lemma tau_opt_all
          th1 th2 th3 e
          (STEPS: rtc tau_step th1 th2)
          (STEP: opt_step e th2 th3):
      rtc all_step th1 th3.
    Proof.
      induction STEPS.
      - inv STEP; eauto.
      - exploit IHSTEPS; eauto. i.
        econs 2; eauto.
        inv H. inv TSTEP. econs. econs. eauto.
    Qed.


    Variant steps_failure (th1: t): Prop :=
    | steps_failure_intro
        pf e th2 th3
        (STEPS: rtc tau_step th1 th2)
        (STEP_FAILURE: step pf e th2 th3)
        (EVENT_FAILURE: ThreadEvent.get_machine_event e = MachineEvent.failure)
    .


    (* step_future *)

    Lemma step_future
          pf e th1 th2
          (STEP: step pf e th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.future (global th1) (global th2)>>.
    Proof.
      inv STEP; ss.
      - eapply Local.internal_step_future; eauto.
      - eapply Local.program_step_future; eauto.
    Qed.

    Lemma opt_step_future
          e th1 th2
          (STEP: opt_step e th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.future (global th1) (global th2)>>.
    Proof.
      inv STEP.
      - esplits; eauto; refl.
      - eapply step_future; eauto.
    Qed.

    Lemma rtc_all_step_future
          th1 th2
          (STEP: rtc all_step th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.future (global th1) (global th2)>>.
    Proof.
      revert LC_WF1. induction STEP.
      - i. splits; ss; refl.
      - i. inv H. inv USTEP.
        exploit step_future; eauto. i. des.
        exploit IHSTEP; eauto. i. des.
        splits; ss; etrans; eauto.
    Qed.

    Lemma rtc_tau_step_future
          th1 th2
          (STEP: rtc tau_step th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.future (global th1) (global th2)>>.
    Proof.
      apply rtc_all_step_future; auto.
      eapply rtc_implies; [|eauto].
      apply tau_union.
    Qed.

    Lemma step_nonpf_future
          e th1 th2
          (STEP: step false e th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.future (global th1) (global th2)>> /\
      <<STATE: (state th1) = (state th2)>>.
    Proof.
      exploit step_future; eauto. i. des.
      inv STEP. inv STEP0; esplits; ss.
    Qed.

    Lemma rtc_step_nonpf_future
          th1 th2
          (STEP: rtc (union (step false)) th1 th2)
          (LC_WF1: Local.wf (local th1) (global th1))
          (GL_WF1: Global.wf (global th1)):
      <<LC_WF2: Local.wf (local th2) (global th2)>> /\
      <<GL_WF2: Global.wf (global th2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\
      <<GL_FUTURE: Global.future (global th1) (global th2)>> /\
      <<STATE: (state th1) = (state th2)>>.
    Proof.
      revert LC_WF1. induction STEP.
      - i. splits; ss; refl.
      - inv H. i. exploit step_nonpf_future; eauto. i. des.
        exploit IHSTEP; eauto. i. des.
        splits; ss; etrans; eauto.
    Qed.


    (* step_inhabited *)

    Lemma step_inhabited
          pf e th1 th2
          (STEP: step pf e th1 th2)
          (INHABITED1: Memory.inhabited (Global.memory (global th1))):
      <<INHABITED2: Memory.inhabited (Global.memory (global th2))>>.
    Proof.
      inv STEP.
      - eapply Local.internal_step_inhabited; eauto.
      - eapply Local.program_step_inhabited; eauto.
    Qed.


    (* step_disjoint *)

    Lemma step_disjoint
          pf e th1 th2 lc
          (STEP: step pf e th1 th2)
          (DISJOINTH1: Local.disjoint (local th1) lc)
          (LC_WF: Local.wf lc (global th1)):
      <<DISJOINTH2: Local.disjoint (local th2) lc>> /\
      <<LC_WF: Local.wf lc (global th2)>>.
    Proof.
      inv STEP.
      - eapply Local.internal_step_disjoint; eauto.
      - eapply Local.program_step_disjoint; eauto.
    Qed.

    Lemma opt_step_disjoint
          e th1 th2 lc
          (STEP: opt_step e th1 th2)
          (DISJOINTH1: Local.disjoint (local th1) lc)
          (LC_WF: Local.wf lc (global th1)):
      <<DISJOINTH2: Local.disjoint (local th2) lc>> /\
      <<LC_WF: Local.wf lc (global th2)>>.
    Proof.
      inv STEP.
      - esplits; eauto.
      - eapply step_disjoint; eauto.
    Qed.

    Lemma rtc_all_step_disjoint
          th1 th2 lc
          (STEP: rtc all_step th1 th2)
          (DISJOINTH1: Local.disjoint (local th1) lc)
          (LC_WF: Local.wf lc (global th1)):
      <<DISJOINTH2: Local.disjoint (local th2) lc>> /\
      <<LC_WF: Local.wf lc (global th2)>>.
    Proof.
      revert DISJOINTH1 LC_WF. induction STEP; eauto. i.
      inv H. inv USTEP.
      exploit step_disjoint; eauto. i. des.
      exploit IHSTEP; eauto.
    Qed.

    Lemma rtc_tau_step_disjoint
          th1 th2 lc
          (STEP: rtc tau_step th1 th2)
          (DISJOINTH1: Local.disjoint (local th1) lc)
          (LC_WF: Local.wf lc (global th1)):
      <<DISJOINTH2: Local.disjoint (local th2) lc>> /\
      <<LC_WF: Local.wf lc (global th2)>>.
    Proof.
      eapply rtc_all_step_disjoint; cycle 1; eauto.
      eapply rtc_implies; [|eauto].
      apply tau_union.
    Qed.

    (* Lemma program_step_promises_bot *)
    (*       e th1 th2 *)
    (*       (STEP: program_step e th1 th2) *)
    (*       (PROMISES: (Local.promises (local th1)) = Memory.bot): *)
    (*   (Local.promises (local th2)) = Memory.bot. *)
    (* Proof. *)
    (*   inv STEP. eapply Local.program_step_promises_bot; eauto. *)
    (* Qed. *)


    (* reserve & cancel steps *)

    (* Variant reserve_step (th1 th2:t): Prop := *)
    (* | reserve_step_intro *)
    (*     pf loc from to *)
    (*     (STEP: step pf (ThreadEvent.promise loc from to Message.reserve Memory.op_kind_add) th1 th2) *)
    (* . *)
    (* Hint Constructors reserve_step: core. *)

    (* Variant cancel_step (th1 th2:t): Prop := *)
    (* | cancel_step_intro *)
    (*     pf loc from to *)
    (*     (STEP: step pf (ThreadEvent.promise loc from to Message.reserve Memory.op_kind_cancel) th1 th2) *)
    (* . *)
    (* Hint Constructors cancel_step: core. *)

    (* Lemma reserve_step_tau_step th1 th2 *)
    (*       (RESERVE: reserve_step th1 th2) *)
    (*   : *)
    (*     tau_step th1 th2. *)
    (* Proof. *)
    (*   inv RESERVE. econs; eauto. *)
    (* Qed. *)

    (* Lemma cancel_step_tau_step th1 th2 *)
    (*       (CANCEL: cancel_step th1 th2) *)
    (*   : *)
    (*     tau_step th1 th2. *)
    (* Proof. *)
    (*   inv CANCEL. econs; eauto. *)
    (* Qed. *)

    (* Lemma reservation_event_reserve_or_cancel_step *)
    (*       (th1 th2: t) pf e *)
    (*       (RESERVATION: ThreadEvent.is_reservation_event e) *)
    (*       (STEP: step pf e th1 th2): *)
    (*     reserve_step th1 th2 \/ cancel_step th1 th2. *)
    (* Proof. *)
    (*   dup STEP. inv STEP. *)
    (*   - inv STEP1. inv LOCAL. ss. des_ifs. inv PROMISE; ss; eauto. *)
    (*   - inv STEP1. inv LOCAL; ss. *)
    (* Qed. *)

    (* Lemma rtc_reserve_step_future *)
    (*       th1 th2 *)
    (*       (STEP: rtc reserve_step th1 th2) *)
    (*       (WF1: Local.wf (local th1) (memory th1)) *)
    (*       (SC1: Memory.closed_timemap (sc th1) (memory th1)) *)
    (*       (CLOSED1: Memory.closed (memory th1)): *)
    (*   <<WF2: Local.wf (local th2) (memory th2)>> /\ *)
    (*   <<SC2: Memory.closed_timemap (sc th2) (memory th2)>> /\ *)
    (*   <<CLOSED2: Memory.closed (memory th2)>> /\ *)
    (*   <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\ *)
    (*   <<SC_FUTURE: TimeMap.le (sc th1) (sc th2)>> /\ *)
    (*   <<MEM_FUTURE: Memory.future (memory th1) (memory th2)>>. *)
    (* Proof. *)
    (*   apply rtc_all_step_future; auto. *)
    (*   eapply rtc_implies; [|eauto]. *)
    (*   i. inv H. eauto. *)
    (* Qed. *)

    (* Lemma rtc_cancel_step_future *)
    (*       th1 th2 *)
    (*       (STEP: rtc cancel_step th1 th2) *)
    (*       (WF1: Local.wf (local th1) (memory th1)) *)
    (*       (SC1: Memory.closed_timemap (sc th1) (memory th1)) *)
    (*       (CLOSED1: Memory.closed (memory th1)): *)
    (*   <<WF2: Local.wf (local th2) (memory th2)>> /\ *)
    (*   <<SC2: Memory.closed_timemap (sc th2) (memory th2)>> /\ *)
    (*   <<CLOSED2: Memory.closed (memory th2)>> /\ *)
    (*   <<TVIEW_FUTURE: TView.le (Local.tview (local th1)) (Local.tview (local th2))>> /\ *)
    (*   <<SC_FUTURE: TimeMap.le (sc th1) (sc th2)>> /\ *)
    (*   <<MEM_FUTURE: Memory.future (memory th1) (memory th2)>>. *)
    (* Proof. *)
    (*   apply rtc_all_step_future; auto. *)
    (*   eapply rtc_implies; [|eauto]. *)
    (*   i. inv H. eauto. *)
    (* Qed. *)
  End Thread.


  (* consistency *)

  Variant consistent {lang: language} (th: t lang): Prop :=
  | consistent_failure
      (FAILURE: @steps_failure lang (Global.max_reserved (global th)) th)
  | consistent_promises
      th2
      (STEPS: rtc (@tau_step lang (Global.max_reserved (global th))) th th2)
      (PROMISES: Local.promises (Thread.local th2) = BoolMap.bot)
  .
End Thread.
#[export] Hint Constructors Thread.step: core.
#[export] Hint Constructors Thread.step_allpf: core.
#[export] Hint Constructors Thread.opt_step: core.
#[export] Hint Constructors Thread.steps_failure: core.
#[export] Hint Constructors Thread.consistent: core.
