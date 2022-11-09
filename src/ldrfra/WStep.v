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

Require Import OrdStep.
Require Import Writes.

Set Implicit Arguments.


Module WThread.
  Section WThread.
    Variable lang: language.
    Variable L: Loc.t -> bool.
    Variable ordcr: Ordering.t.
    Variable ordcw: Ordering.t.

    Variant step rels1: forall (rels2: Writes.t) (e: ThreadEvent.t) (e1 e2: Thread.t lang), Prop :=
    | step_intro
        e e1 e2
        (STEP: @OrdThread.step lang L ordcr ordcw e e1 e2):
        step rels1 (Writes.append L e rels1) e e1 e2
    .

    (* Inducitve steps rels1: forall (rels2: Writes.t) (e1 e2: Thread.t lang), Prop := *)
    (* | steps_refl *)
    (*     e: *)
    (*     steps rels1 rels1 e e *)
    (* | steps_step *)
    (*     rels2 rels3 e e1 e2 e3 *)
    (*     (STEP: step rels1 rels2 e e1 e2) *)
    (*     (STEPS: steps rels2 rels3 e2 e3): *)
    (*     steps rels1 rels3 e1 e3 *)
    (* . *)
    (* Hint Constructors steps: core. *)

    (* Inductive tau_steps rels1: forall (rels2: Writes.t) (e1 e2: Thread.t lang), Prop := *)
    (* | tau_steps_refl *)
    (*     e: *)
    (*     tau_steps rels1 rels1 e e *)
    (* | tau_steps_step *)
    (*     rels2 rels3 e e1 e2 e3 *)
    (*     (STEP: step rels1 rels2 e e1 e2) *)
    (*     (SILENT: ThreadEvent.get_machine_event e = MachineEvent.silent) *)
    (*     (STEPS: tau_steps rels2 rels3 e2 e3): *)
    (*     tau_steps rels1 rels3 e1 e3 *)
    (* . *)
    (* Hint Constructors tau_steps: core. *)

    Variant opt_step rels1: forall (rels2: Writes.t) (e: ThreadEvent.t) (e1 e2: Thread.t lang), Prop :=
    | step_none
        e:
        opt_step rels1 rels1 ThreadEvent.silent e e
    | step_some
        rels2 e e1 e2
        (STEP: step rels1 rels2 e e1 e2):
        opt_step rels1 rels2 e e1 e2
    .
    Hint Constructors opt_step: core.


    Lemma step_ord_step
          rels1 rels2 e e1 e2
          (STEP: step rels1 rels2 e e1 e2):
      OrdThread.step L ordcr ordcw e e1 e2.
    Proof.
      inv STEP. eauto.
    Qed.

    Lemma opt_step_ord_opt_step
          rels1 rels2 e e1 e2
          (STEP: opt_step rels1 rels2 e e1 e2):
      OrdThread.opt_step L ordcr ordcw e e1 e2.
    Proof.
      inv STEP; [econs 1|].
      exploit step_ord_step; eauto. i. des.
      econs 2. eauto.
    Qed.

    (* Lemma steps_ord_steps *)
    (*       rels1 rels2 e1 e2 *)
    (*       (STEPS: steps rels1 rels2 e1 e2): *)
    (*   rtc (OrdThread.all_step L ordcr ordcw) e1 e2. *)
    (* Proof. *)
    (*   induction STEPS; eauto. *)
    (*   exploit step_ord_step; eauto. i. des. *)
    (*   econs 2; eauto. econs. econs. eauto. *)
    (* Qed. *)

    (* Lemma tau_steps_ord_tau_steps *)
    (*       rels1 rels2 e1 e2 *)
    (*       (STEPS: tau_steps rels1 rels2 e1 e2): *)
    (*   rtc (@OrdThread.tau_step lang L ordcr ordcw) e1 e2. *)
    (* Proof. *)
    (*   induction STEPS; eauto. *)
    (*   inv STEP; ss. *)
    (*   econs 2; eauto. econs; eauto. econs. eauto. *)
    (* Qed. *)

    (* Lemma ord_tau_steps_tau_steps *)
    (*       e1 e2 *)
    (*       (STEPS: rtc (@OrdThread.tau_step lang L ordcr ordcw) e1 e2): *)
    (*   forall rels1, exists rels2, *)
    (*       tau_steps rels1 rels2 e1 e2. *)
    (* Proof. *)
    (*   induction STEPS; eauto. inv H. inv TSTEP. i. *)
    (*   specialize (IHSTEPS (Writes.append L e rels1)). des. *)
    (*   esplits. econs 2; eauto. econs; eauto. *)
    (* Qed. *)

    (* Lemma tau_steps_steps *)
    (*       rels1 rels2 e1 e2 *)
    (*       (STEPS: tau_steps rels1 rels2 e1 e2): *)
    (*   steps rels1 rels2 e1 e2. *)
    (* Proof. *)
    (*   induction STEPS; eauto. *)
    (* Qed. *)

    (* Lemma reserve_steps_tau_steps *)
    (*       rels e1 e2 *)
    (*       (STEPS: rtc (@Thread.reserve_step _) e1 e2): *)
    (*   tau_steps rels rels e1 e2. *)
    (* Proof. *)
    (*   induction STEPS; eauto. *)
    (*   inv H. inv STEP; [|inv STEP0; inv LOCAL]. *)
    (*   econs 2; eauto. *)
    (*   - replace rels with *)
    (*         (Writes.append *)
    (*            L (ThreadEvent.promise loc from to Message.reserve Memory.op_kind_add) rels) *)
    (*         at 2 by ss. *)
    (*     econs. econs 1; eauto. *)
    (*     ii. inv PROMISE. ss. *)
    (*   - ss. *)
    (* Qed. *)

    (* Lemma cancel_steps_tau_steps *)
    (*       rels e1 e2 *)
    (*       (STEPS: rtc (@Thread.cancel_step _) e1 e2): *)
    (*   tau_steps rels rels e1 e2. *)
    (* Proof. *)
    (*   induction STEPS; eauto. *)
    (*   inv H. inv STEP; [|inv STEP0; inv LOCAL]. *)
    (*   econs 2; eauto. *)
    (*   - replace rels with *)
    (*         (Writes.append *)
    (*            L (ThreadEvent.promise loc from to Message.reserve Memory.op_kind_cancel) rels) *)
    (*         at 2 by ss. *)
    (*     econs. econs 1; eauto. *)
    (*     ii. inv PROMISE; ss. *)
    (*   - ss. *)
    (* Qed. *)

    (* Lemma tau_steps_rtc_tau_step *)
    (*       rels1 rels2 e1 e2 *)
    (*       (STEPS: tau_steps rels1 rels2 e1 e2): *)
    (*   rtc (@OrdThread.tau_step lang L ordcr ordcw) e1 e2. *)
    (* Proof. *)
    (*   induction STEPS; eauto. *)
    (*   econs 2; eauto. inv STEP; ss. *)
    (*   econs; eauto. econs. eauto. *)
    (* Qed. *)

    (* Lemma opt_step_steps *)
    (*       rels1 rels2 e e1 e2 *)
    (*       (STEP: opt_step rels1 rels2 e e1 e2): *)
    (*   steps rels1 rels2 e1 e2. *)
    (* Proof. *)
    (*   inv STEP; eauto. *)
    (* Qed. *)

    (* Lemma steps_trans *)
    (*       rels1 rels2 rels3 e1 e2 e3 *)
    (*       (STEPS1: steps rels1 rels2 e1 e2) *)
    (*       (STEPS2: steps rels2 rels3 e2 e3): *)
    (*   steps rels1 rels3 e1 e3. *)
    (* Proof. *)
    (*   revert rels3 e3 STEPS2. *)
    (*   induction STEPS1; i; eauto. *)
    (* Qed. *)

    (* Lemma tau_steps_trans *)
    (*       rels1 rels2 rels3 e1 e2 e3 *)
    (*       (STEPS1: tau_steps rels1 rels2 e1 e2) *)
    (*       (STEPS2: tau_steps rels2 rels3 e2 e3): *)
    (*   tau_steps rels1 rels3 e1 e3. *)
    (* Proof. *)
    (*   revert rels3 e3 STEPS2. *)
    (*   induction STEPS1; i; eauto. *)
    (* Qed. *)

    Lemma step_future
          rels1 rels2 e e1 e2
          (STEP: step rels1 rels2 e e1 e2)
          (LC_WF1: Local.wf (Thread.local e1) (Thread.global e1))
          (GL_WF1: Global.wf (Thread.global e1)):
      <<LC_WF2: Local.wf (Thread.local e2) (Thread.global e2)>> /\
      <<GL_WF2: Global.wf (Thread.global e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>> /\
      <<GL_FUTURE: Global.future (Thread.global e1) (Thread.global e2)>>.
    Proof.
      inv STEP; eauto using OrdThread.step_future.
    Qed.

    Lemma opt_step_future
          rels1 rels2 e e1 e2
          (STEP: opt_step rels1 rels2 e e1 e2)
          (LC_WF1: Local.wf (Thread.local e1) (Thread.global e1))
          (GL_WF1: Global.wf (Thread.global e1)):
      <<LC_WF2: Local.wf (Thread.local e2) (Thread.global e2)>> /\
      <<GL_WF2: Global.wf (Thread.global e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>> /\
      <<GL_FUTURE: Global.future (Thread.global e1) (Thread.global e2)>>.
    Proof.
      inv STEP.
      - esplits; eauto; refl.
      - inv STEP0; eauto using OrdThread.step_future.
    Qed.

    (* Lemma steps_future *)
    (*       rels1 rels2 e1 e2 *)
    (*       (STEPS: steps rels1 rels2 e1 e2) *)
    (*       (WF1: Local.wf (Thread.local e1) (Thread.memory e1)) *)
    (*       (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1)) *)
    (*       (CLOSED1: Memory.closed (Thread.memory e1)): *)
    (*   <<WF2: Local.wf (Thread.local e2) (Thread.memory e2)>> /\ *)
    (*   <<SC2: Memory.closed_timemap (Thread.sc e2) (Thread.memory e2)>> /\ *)
    (*   <<CLOSED2: Memory.closed (Thread.memory e2)>> /\ *)
    (*   <<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>> /\ *)
    (*   <<SC_FUTURE: TimeMap.le (Thread.sc e1) (Thread.sc e2)>> /\ *)
    (*   <<MEM_FUTURE: Memory.future (Thread.memory e1) (Thread.memory e2)>>. *)
    (* Proof. *)
    (*   revert WF1 SC1 CLOSED1. induction STEPS; i. *)
    (*   - splits; ss; refl. *)
    (*   - exploit step_future; eauto. i. des. *)
    (*     exploit IHSTEPS; eauto. i. des. *)
    (*     splits; ss; etrans; eauto. *)
    (* Qed. *)

    Lemma step_disjoint
          rels1 rels2 e e1 e2 lc
          (STEP: step rels1 rels2 e e1 e2)
          (LC_WF1: Local.wf (Thread.local e1) (Thread.global e1))
          (GL_WF1: Global.wf (Thread.global e1))
          (DISJOINT1: Local.disjoint (Thread.local e1) lc)
          (LC_WF: Local.wf lc (Thread.global e1)):
      <<DISJOINT2: Local.disjoint (Thread.local e2) lc>> /\
      <<LC_WF: Local.wf lc (Thread.global e2)>>.
    Proof.
      inv STEP; eauto using OrdThread.step_disjoint.
    Qed.

    Lemma opt_step_disjoint
          rels1 rels2 e e1 e2 lc
          (STEP: opt_step rels1 rels2 e e1 e2)
          (LC_WF1: Local.wf (Thread.local e1) (Thread.global e1))
          (GL_WF1: Global.wf (Thread.global e1))
          (DISJOINT1: Local.disjoint (Thread.local e1) lc)
          (LC_WF: Local.wf lc (Thread.global e1)):
      <<DISJOINT2: Local.disjoint (Thread.local e2) lc>> /\
      <<LC_WF: Local.wf lc (Thread.global e2)>>.
    Proof.
      inv STEP; eauto.
      inv STEP0; eauto using OrdThread.step_disjoint.
    Qed.


    (* Writes.wf *)

    Lemma step_writes_wf
          rels1 rels2 e e1 e2
          (ORDCW: Ordering.le Ordering.plain ordcw)
          (RELS1: Writes.wf L rels1 (Global.memory (Thread.global e1)))
          (STEP: step rels1 rels2 e e1 e2):
      Writes.wf L rels2 (Global.memory (Thread.global e2)).
    Proof.
      inv STEP. eapply Writes.step_wf; eauto.
    Qed.

    (* Lemma steps_writes_wf *)
    (*       rels1 rels2 e1 e2 *)
    (*       (ORDCW: Ordering.le Ordering.plain ordcw) *)
    (*       (RELS1: Writes.wf L rels1 (Thread.memory e1)) *)
    (*       (STEPS: steps rels1 rels2 e1 e2): *)
    (*   Writes.wf L rels2 (Thread.memory e2). *)
    (* Proof. *)
    (*   induction STEPS; eauto. *)
    (*   apply IHSTEPS. eapply step_writes_wf; eauto. *)
    (* Qed. *)

    (* Lemma step_rels_disjoint *)
    (*       rels1 rels2 e e1 e2 promises *)
    (*       (RELS1: Writes.wf L rels1 (Local.promises (Thread.local e1)) (Thread.memory e1)) *)
    (*       (STEP: step rels1 rels2 e e1 e2) *)
    (*       (DISJOINT: Memory.disjoint (Local.promises (Thread.local e1)) promises) *)
    (*       (LE: Memory.le promises (Thread.memory e1)) *)
    (*       (RELS: Writes.wf L rels1 promises (Thread.memory e1)): *)
    (*   Writes.wf L rels2 promises (Thread.memory e2). *)
    (* Proof. *)
    (*   inv STEP. eauto using Writes.step_disjoint. *)
    (* Qed. *)

    (* Lemma steps_rels_disjoint *)
    (*       rels1 rels2 e1 e2 lc *)
    (*       (RELS1: Writes.wf L rels1 (Local.promises (Thread.local e1)) (Thread.memory e1)) *)
    (*       (STEPS: steps rels1 rels2 e1 e2) *)
    (*       (WF1: Local.wf (Thread.local e1) (Thread.memory e1)) *)
    (*       (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1)) *)
    (*       (CLOSED1: Memory.closed (Thread.memory e1)) *)
    (*       (DISJOINT: Local.disjoint (Thread.local e1) lc) *)
    (*       (WF: Local.wf lc (Thread.memory e1)) *)
    (*       (RELS: Writes.wf L rels1 (Local.promises lc) (Thread.memory e1)): *)
    (*   Writes.wf L rels2 (Local.promises lc) (Thread.memory e2). *)
    (* Proof. *)
    (*   induction STEPS; ss. *)
    (*   hexploit step_rels_disjoint; eauto; try apply DISJOINT; try apply WF. i. *)
    (*   hexploit step_writes_wf; eauto. i. *)
    (*   inv STEP. *)
    (*   exploit OrdThread.step_future; eauto. i. des. *)
    (*   exploit OrdThread.step_disjoint; eauto. i. des. *)
    (*   eapply IHSTEPS; eauto. *)
    (* Qed. *)

    Lemma step_rels_incl
          rels1 rels2 e e1 e2
          (STEP: step rels1 rels2 e e1 e2):
      rels2 = rels1 \/ exists a, rels2 = a :: rels1.
    Proof.
      inv STEP. unfold Writes.append. des_ifs; eauto.
    Qed.
  End WThread.
End WThread.


Module WConfiguration.
  Section WConfiguration.
    Variable L: Loc.t -> bool.
    Variable ordcr ordcw: Ordering.t.

    Variant step:
      forall (e: ThreadEvent.t) (tid: Ident.t) (rels1 rels2: Writes.t) (c1 c2: Configuration.t), Prop :=
    | step_intro
        rels1 rels2
        e tid c1 lang st1 lc1 st2 lc2 gl2
        (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
        (STEP: WThread.step L ordcr ordcw rels1 rels2 e
                            (Thread.mk _ st1 lc1 (Configuration.global c1))
                            (Thread.mk _ st2 lc2 gl2)):
        step e tid rels1 rels2
             c1 (Configuration.mk (IdentMap.add tid (existT _ _ st2, lc2) (Configuration.threads c1)) gl2)
    .

    Inductive steps rels1: forall (rels2: Writes.t) (c1 c2: Configuration.t), Prop :=
    | steps_refl
        c:
        steps rels1 rels1 c c
    | steps_step
        rels2 rels3 e tid c1 c2 c3
        (STEP: step e tid rels1 rels2 c1 c2)
        (STEPS: steps rels2 rels3 c2 c3):
        steps rels1 rels3 c1 c3
    .
    Hint Constructors steps: core.

    Lemma steps_trans
          rels1 rels2 rels3 c1 c2 c3
          (STEPS1: steps rels1 rels2 c1 c2)
          (STEPS2: steps rels2 rels3 c2 c3):
      steps rels1 rels3 c1 c3.
    Proof.
      revert c3 STEPS2. induction STEPS1; i; eauto.
    Qed.

    Lemma step_ord_step
          e tid rels1 rels2 c1 c2
          (STEP: step e tid rels1 rels2 c1 c2):
      OrdConfiguration.estep L ordcr ordcw e tid c1 c2.
    Proof.
      inv STEP. econs; eauto. inv STEP0. ss.
    Qed.

    Lemma steps_ord_steps
          rels1 rels2 c1 c2
          (STEPS: steps rels1 rels2 c1 c2):
      rtc (@OrdConfiguration.all_step L ordcr ordcw) c1 c2.
    Proof.
      induction STEPS; eauto.
      exploit step_ord_step; eauto. i. econs 2; eauto.
      econs. eauto.
    Qed.

    Lemma step_future
          e tid rels1 rels2 c1 c2
          (WF1: Configuration.wf c1)
          (STEP: step e tid rels1 rels2 c1 c2):
      <<WF2: Configuration.wf c2>> /\
      <<GL_FUTURE: Global.future (Configuration.global c1) (Configuration.global c2)>>.
    Proof.
      apply step_ord_step in STEP.
      eapply OrdConfiguration.estep_future; eauto.
    Qed.

    Lemma steps_future
          rels1 rels2 c1 c2
          (WF1: Configuration.wf c1)
          (STEPS: steps rels1 rels2 c1 c2):
      <<WF2: Configuration.wf c2>> /\
      <<GL_FUTURE: Global.future (Configuration.global c1) (Configuration.global c2)>>.
    Proof.
      induction STEPS; ss.
      - split; ss. econs; refl.
      - exploit step_future; eauto. i. des.
        exploit IHSTEPS; eauto. i. des.
        splits; ss; etrans; eauto.
    Qed.

    Lemma step_rels
          e tid rels1 rels2 c1 c2
          (STEP: WConfiguration.step e tid rels1 rels2 c1 c2):
      rels2 = Writes.append L e rels1.
    Proof.
      unfold Writes.append.
      inv STEP. inv STEP0; ss.
    Qed.

    Lemma step_rels_incl
          e tid rels1 rels2 c1 c2
          (STEP: step e tid rels1 rels2 c1 c2):
      rels2 = rels1 \/ exists a, rels2 = a :: rels1.
    Proof.
      inv STEP. inv STEP0; eauto. inv STEP.
      unfold Writes.append. des_ifs; eauto.
    Qed.

    Lemma steps_rels_incl
          rels1 rels2 c1 c2
          (STEPS: steps rels1 rels2 c1 c2):
      exists rels, rels2 = rels ++ rels1.
    Proof.
      induction STEPS.
      - exists []. ss.
      - des. exploit step_rels_incl; eauto. i. des; subst.
        + exists rels. ss.
        + exists (rels ++ [a]). rewrite <- List.app_assoc. ss.
    Qed.
  End WConfiguration.
End WConfiguration.


Module RARaceW.
  Section RARaceW.
    Variable L: Loc.t -> bool.
    Variable ordcr ordcw: Ordering.t.

    Definition wr_race (rels: Writes.t) (tview: TView.t) (loc: Loc.t) (ord: Ordering.t): Prop :=
      exists to ordw,
        (<<LOC: L loc>>) /\
        (<<HIGHER: Time.lt ((View.rlx (TView.cur tview)) loc) to>>) /\
        (<<IN: List.In (loc, to, ordw) rels>>) /\
        ((<<ORDW: Ordering.le ordw Ordering.strong_relaxed>>) \/
         (<<ORDR: Ordering.le ord Ordering.strong_relaxed>>)).

    Definition ww_race (rels: Writes.t) (tview: TView.t) (loc: Loc.t) (ord: Ordering.t): Prop :=
      exists to ordw,
        (<<LOC: L loc>>) /\
        (<<HIGHER: Time.lt ((View.rlx (TView.cur tview)) loc) to>>) /\
        (<<IN: List.In (loc, to, ordw) rels>>) /\
        ((<<ORDW1: Ordering.le ordw Ordering.na>>) \/
         (<<ORDW2: Ordering.le ord Ordering.na>>)).

    Definition ra_race (rels: Writes.t) (tview: TView.t) (e: ProgramEvent.t): Prop :=
      (exists loc val ord,
          (<<READ: ProgramEvent.is_reading e = Some (loc, val, ord)>>) /\
          (<<WRRACE: wr_race rels tview loc ord>>)) \/
      (exists loc val ord,
          (<<WRITE: ProgramEvent.is_writing e = Some (loc, val, ord)>>) /\
          (<<WWRACE: ww_race rels tview loc ord>>)).

    Definition ra_race_steps (rels: Writes.t) (c: Configuration.t): Prop :=
      exists tid rels2 c2 lang st2 lc2 e st3,
        (<<STEPS: WConfiguration.steps L ordcr ordcw rels rels2 c c2>>) /\
        (<<TID: IdentMap.find tid (Configuration.threads c2) = Some (existT _ lang st2, lc2)>>) /\
        (<<THREAD_STEP: lang.(Language.step) e st2 st3>>) /\
        (<<RARACE: ra_race rels2 (Local.tview lc2) e>>).

    Definition racefree (rels: Writes.t) (c: Configuration.t): Prop :=
      forall tid rels2 c2 lang st2 lc2 e st3
        (STEPS: WConfiguration.steps L ordcr ordcw rels rels2 c c2)
        (TID: IdentMap.find tid (Configuration.threads c2) = Some (existT _ lang st2, lc2))
        (THREAD_STEP: lang.(Language.step) e st2 st3)
        (RARACE: ra_race rels2 (Local.tview lc2) e),
        False.

    Definition racefree_syn (syn: Threads.syntax): Prop :=
      racefree [] (Configuration.init syn).

    Lemma step_racefree
          e tid rels1 rels2 c1 c2
          (RACEFREE: racefree rels1 c1)
          (STEP: WConfiguration.step L ordcr ordcw e tid rels1 rels2 c1 c2):
      racefree rels2 c2.
    Proof.
      ii. eapply RACEFREE; eauto. econs 2; eauto.
    Qed.
  End RARaceW.
End RARaceW.
