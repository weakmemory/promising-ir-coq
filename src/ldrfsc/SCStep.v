Require Import Lia.
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
Require Import Cell.
Require Import Memory.
Require Import Global.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import BoolMap.
Require Import Promises.

Require Import OrdStep.

Set Implicit Arguments.




(** L-SC machine **)
Module SCLocal.
  Section SCLocal.
    Variable L: Loc.t -> bool.

    Definition non_maximal (lc: Local.t) (mem: Memory.t) (loc: Loc.t): Prop :=
      exists to from msg,
        (<<GET: Memory.get loc to mem = Some (from, msg)>>) /\
        (<<NRESERVE: msg <> Message.reserve>>) /\
        (<<TS: Time.lt ((TView.cur (Local.tview lc)).(View.rlx) loc) to>>)
    .

    Inductive read_step (lc1:Local.t) (gl1:Global.t) (loc:Loc.t) (to:Time.t) (val:Const.t) (released:option View.t) (ord:Ordering.t) (lc2:Local.t): Prop :=
    | read_step_intro
        ord'
        (ORD: ord' = if L loc then Ordering.join ord Ordering.acqrel else ord)
        (STEP: Local.read_step lc1 gl1 loc to val released ord' lc2)
        (MAXIMAL: forall (LOC: L loc)
                         from' to' val' released' na
                         (GET: Memory.get loc to' gl1.(Global.memory) = Some (from', Message.message val' released' na)),
            Time.le to' to)
    .
    Hint Constructors read_step: core.

    Inductive write_step (lc1:Local.t) (gl1:Global.t)
              (loc:Loc.t) (from to:Time.t)
              (val:Const.t) (releasedm released:option View.t) (ord:Ordering.t)
              (lc2:Local.t) (gl2:Global.t): Prop :=
    | write_step_intro
        ord'
        (ORD: ord' = if L loc then Ordering.join ord Ordering.acqrel else ord)
        (STEP: Local.write_step lc1 gl1 loc from to val releasedm released ord' lc2 gl2)
        (MAXIMAL: forall (LOC: L loc)
                         from' to' val' released' na
                         (GET: Memory.get loc to' gl1.(Global.memory) = Some (from', Message.message val' released' na)),
            Time.lt to' to)
    .
    Hint Constructors write_step: core.

    Variant program_step:
      forall (e: ThreadEvent.t) (lc1: Local.t) (gl1: Global.t) (lc2: Local.t) (gl2: Global.t), Prop :=
      | program_step_silent
          lc1 gl1:
        program_step ThreadEvent.silent lc1 gl1 lc1 gl1
      | program_step_read
          lc1 gl1
          loc to val released ord lc2
          (LOCAL: read_step lc1 gl1 loc to val released ord lc2):
        program_step (ThreadEvent.read loc to val released ord) lc1 gl1 lc2 gl1
      | program_step_write
          lc1 gl1
          loc from to val released ord lc2 gl2
          (LOCAL: write_step lc1 gl1 loc from to val None released ord lc2 gl2):
        program_step (ThreadEvent.write loc from to val released ord) lc1 gl1 lc2 gl2
      | program_step_update
          lc1 gl1
          loc ordr ordw
          tsr valr releasedr releasedw lc2
          tsw valw lc3 gl3
          (LOCAL1: read_step lc1 gl1 loc tsr valr releasedr ordr lc2)
          (LOCAL2: write_step lc2 gl1 loc tsr tsw valw releasedr releasedw ordw lc3 gl3):
        program_step (ThreadEvent.update loc tsr tsw valr valw releasedr releasedw ordr ordw)
                     lc1 gl1 lc3 gl3
      | program_step_fence
          lc1 gl1
          ordr ordw lc2 gl2
          (LOCAL: Local.fence_step lc1 gl1 ordr ordw lc2 gl2):
        program_step (ThreadEvent.fence ordr ordw) lc1 gl1 lc2 gl2
      | program_step_syscall
          lc1 gl1
          e lc2 gl2
          (LOCAL: Local.fence_step lc1 gl1 Ordering.seqcst Ordering.seqcst lc2 gl2):
        program_step (ThreadEvent.syscall e) lc1 gl1 lc2 gl2
      | program_step_failure
          lc1 gl1
          (LOCAL: Local.failure_step lc1):
        program_step ThreadEvent.failure lc1 gl1 lc1 gl1
      | program_step_racy_read
          lc1 gl1
          loc to val ord
          (LOCAL: Local.racy_read_step lc1 gl1 loc to val ord):
        program_step (ThreadEvent.racy_read loc to val ord) lc1 gl1 lc1 gl1
      | program_step_racy_write
          lc1 gl1
          loc to val ord
          (LOCAL: Local.racy_write_step lc1 gl1 loc to ord):
        program_step (ThreadEvent.racy_write loc to val ord) lc1 gl1 lc1 gl1
      | program_step_racy_update
          lc1 gl1
          loc to valr valw ordr ordw
          (LOCAL: Local.racy_update_step lc1 gl1 loc to ordr ordw):
        program_step (ThreadEvent.racy_update loc to valr valw ordr ordw) lc1 gl1 lc1 gl1
    .


    (* step_future *)

    Lemma program_step_future
          e lc1 gl1 lc2 gl2
          (STEP: program_step e lc1 gl1 lc2 gl2)
          (WF1: Local.wf lc1 gl1)
          (GL1: Global.wf gl1):
      <<WF2: Local.wf lc2 gl2>> /\
      <<GL2: Global.wf gl2>> /\
      <<TVIEW_FUTURE: TView.le lc1.(Local.tview) lc2.(Local.tview)>> /\
      <<GL_FUTURE: Global.future gl1 gl2>>.
    Proof.
      inv STEP.
      - esplits; eauto; try refl.
      - inv LOCAL.
        exploit Local.read_step_future; eauto. i. des.
        esplits; eauto; try refl.
      - inv LOCAL.
        exploit Local.write_step_future; eauto; try by econs.
        { ss. eapply Time.bot_spec. }
        i. des.
        esplits; eauto; try refl.
      - inv LOCAL1. inv LOCAL2.
        exploit Local.read_step_future; eauto. i. des.
        exploit Local.write_step_future; eauto; try by econs.
        { etrans; eauto. inv STEP0. inv WRITE. inv ADD. left. auto. }
        i. des.
        esplits; eauto. etrans; eauto.
      - exploit Local.fence_step_future; eauto.
      - exploit Local.fence_step_future; eauto.
      - esplits; eauto; try refl.
      - esplits; eauto; try refl.
      - esplits; eauto; try refl.
      - esplits; eauto; try refl.
    Qed.


    (* step_disjoint *)

    Lemma program_step_disjoint
          e lc1 gl1 lc2 gl2 lc
          (STEP: program_step e lc1 gl1 lc2 gl2)
          (WF1: Local.wf lc1 gl1)
          (GL1: Global.wf gl1)
          (DISJOINT1: Local.disjoint lc1 lc)
          (WF: Local.wf lc gl1):
      <<DISJOINT2: Local.disjoint lc2 lc>> /\
      <<WF: Local.wf lc gl2>>.
    Proof.
      inv STEP.
      - esplits; eauto.
      - inv LOCAL. exploit Local.read_step_disjoint; eauto.
      - inv LOCAL. exploit Local.write_step_disjoint; eauto.
      - inv LOCAL1. inv LOCAL2.
        exploit Local.read_step_future; eauto. i. des.
        exploit Local.read_step_disjoint; eauto. i. des.
        exploit Local.write_step_disjoint; eauto.
      - exploit Local.fence_step_disjoint; eauto.
      - exploit Local.fence_step_disjoint; eauto.
      - esplits; eauto.
      - esplits; eauto.
      - esplits; eauto.
      - esplits; eauto.
    Qed.

    Lemma program_step_promises
          e lc1 gl1 lc2 gl2
          (STEP: program_step e lc1 gl1 lc2 gl2):
      BoolMap.le (Local.promises lc2) (Local.promises lc1) /\
      BoolMap.le (Global.promises gl2) (Global.promises gl1).
    Proof.
      inv STEP; ss; try by (inv LOCAL; ss).
      - inv LOCAL. inv STEP. ss.
      - inv LOCAL. inv STEP. inv FULFILL; ss.
        split; eauto using BoolMap.remove_le.
      - inv LOCAL1. inv LOCAL2. inv STEP. inv STEP0. inv FULFILL; ss.
        split; eauto using BoolMap.remove_le.
    Qed.

    Lemma program_step_promises_minus
          e lc1 gl1 lc2 gl2
          (STEP: program_step e lc1 gl1 lc2 gl2):
      BoolMap.minus (Global.promises gl1) (Local.promises lc1) =
      BoolMap.minus (Global.promises gl2) (Local.promises lc2).
    Proof.
      inv STEP; ss; try by (inv LOCAL; ss).
      - inv LOCAL. inv STEP. ss.
      - inv LOCAL. inv STEP. ss.
        eapply Promises.fulfill_minus; eauto.
      - inv LOCAL1. inv LOCAL2. inv STEP. inv STEP0. ss.
        eapply Promises.fulfill_minus; eauto.
    Qed.

    Lemma program_step_promises_bot
          e lc1 gl1 lc2 gl2
          (STEP: program_step e lc1 gl1 lc2 gl2)
          (PROMISES: Local.promises lc1 = BoolMap.bot):
      Local.promises lc2 = BoolMap.bot.
    Proof.
      inv STEP; try inv LOCAL; ss; try inv STEP; ss.
      - inv FULFILL; ss.
        exploit BoolMap.remove_get0; try exact REMOVE. i. des.
        rewrite PROMISES in *. ss.
      - inv LOCAL1. inv LOCAL2. inv STEP. inv STEP0. ss.
        inv FULFILL; ss.
        exploit BoolMap.remove_get0; try exact REMOVE. i. des.
        rewrite PROMISES in *. ss.
    Qed.

    Lemma program_step_gpromises_bot
          e lc1 gl1 lc2 gl2
          (STEP: program_step e lc1 gl1 lc2 gl2)
          (PROMISES: Global.promises gl1 = BoolMap.bot):
      Global.promises gl2 = BoolMap.bot.
    Proof.
      inv STEP; try inv LOCAL; ss; try inv STEP; ss.
      - inv FULFILL; ss.
        exploit BoolMap.remove_get0; try exact GREMOVE. i. des.
        rewrite PROMISES in *. ss.
      - inv LOCAL1. inv LOCAL2. inv STEP. inv STEP0. ss.
        inv FULFILL; ss.
        exploit BoolMap.remove_get0; try exact GREMOVE. i. des.
        rewrite PROMISES in *. ss.
    Qed.

    Lemma program_step_reserves
          e lc1 gl1 lc2 gl2
          (STEP: program_step e lc1 gl1 lc2 gl2):
      Local.reserves lc2 = Local.reserves lc1.
    Proof.
      inv STEP; try inv LOCAL; ss; try inv STEP; ss.
      inv LOCAL1. inv LOCAL2. inv STEP. inv STEP0. ss.
    Qed.
  End SCLocal.
End SCLocal.


Module SCThread.
  Section SCThread.
    Variable lang: language.
    Variable L: Loc.t -> bool.

    Inductive step (e:ThreadEvent.t): forall (e1 e2:Thread.t lang), Prop :=
    | step_intro
        st1 lc1 gl1
        st2 lc2 gl2
        (STATE: (Language.step lang) (ThreadEvent.get_program_event e) st1 st2)
        (LOCAL: SCLocal.program_step L e lc1 gl1 lc2 gl2):
        step e (Thread.mk lang st1 lc1 gl1) (Thread.mk lang st2 lc2 gl2)
    .
    Hint Constructors step: core.

    Definition all_step := union step.
    Hint Unfold all_step: core.


    (* future *)

    Lemma step_future
          e e1 e2
          (STEP: step e e1 e2)
          (LC_WF1: Local.wf (Thread.local e1) (Thread.global e1))
          (GL_WF1: Global.wf (Thread.global e1)):
      <<LC_WF2: Local.wf (Thread.local e2) (Thread.global e2)>> /\
      <<GL_WF2: Global.wf (Thread.global e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>> /\
      <<GL_FUTURE: Global.future (Thread.global e1) (Thread.global e2)>>.
    Proof.
      inv STEP. ss. eapply SCLocal.program_step_future; eauto.
    Qed.

    Lemma rtc_all_step_future
          e1 e2
          (STEPS: rtc all_step e1 e2)
          (LC_WF1: Local.wf (Thread.local e1) (Thread.global e1))
          (GL_WF1: Global.wf (Thread.global e1)):
      <<LC_WF2: Local.wf (Thread.local e2) (Thread.global e2)>> /\
      <<GL_WF2: Global.wf (Thread.global e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>> /\
      <<GL_FUTURE: Global.future (Thread.global e1) (Thread.global e2)>>.
    Proof.
      revert LC_WF1 GL_WF1. induction STEPS; i.
      - esplits; eauto; refl.
      - inv H. inv USTEP. exploit step_future; eauto. i. des.
        exploit IHSTEPS; eauto. i. des.
        esplits; eauto; etrans; eauto.
    Qed.


    (* disjoint *)

    Lemma step_disjoint
          e e1 e2 lc
          (STEP: step e e1 e2)
          (LC_WF1: Local.wf (Thread.local e1) (Thread.global e1))
          (GL_WF1: Global.wf (Thread.global e1))
          (DISJOINT1: Local.disjoint (Thread.local e1) lc)
          (LC_WF: Local.wf lc (Thread.global e1)):
      <<DISJOINT2: Local.disjoint (Thread.local e2) lc>> /\
      <<LC_WF: Local.wf lc (Thread.global e2)>>.
    Proof.
      inv STEP.
      eapply SCLocal.program_step_disjoint; eauto.
    Qed.


    (* promises *)

    Lemma step_promises
          e th1 th2
          (STEP: step e th1 th2):
      BoolMap.le (Local.promises (Thread.local th2)) (Local.promises (Thread.local th1)) /\
      BoolMap.le (Global.promises (Thread.global th2)) (Global.promises (Thread.global th1)).
    Proof.
      inv STEP. s.
      eapply SCLocal.program_step_promises; eauto.
    Qed.

    Lemma step_promises_minus
          e th1 th2
          (STEP: step e th1 th2):
      BoolMap.minus (Global.promises (Thread.global th1)) (Local.promises (Thread.local th1)) =
      BoolMap.minus (Global.promises (Thread.global th2)) (Local.promises (Thread.local th2)).
    Proof.
      inv STEP; s.
      eapply SCLocal.program_step_promises_minus; eauto.
    Qed.
  End SCThread.
End SCThread.


Module SCConfiguration.
  Section SCConfiguration.
    Variable L: Loc.t -> bool.

    Variant estep: forall (e: ThreadEvent.t) (tid: Ident.t) (c1 c2: Configuration.t), Prop :=
    | estep_intro
        e tid c1 lang st1 lc1 st2 lc2 gl2
        (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
        (STEP: SCThread.step L e
                             (Thread.mk _ st1 lc1 (Configuration.global c1))
                             (Thread.mk _ st2 lc2 gl2)):
      estep e tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st2, lc2) (Configuration.threads c1)) gl2)
    .
    Hint Constructors estep: core.

    Variant step: forall (e: MachineEvent.t) (tid: Ident.t) (c1 c2: Configuration.t), Prop :=
    | step_instro
        e tid c1 c2
        (STEP: estep e tid c1 c2):
        step (ThreadEvent.get_machine_event_pf e) tid c1 c2
    .
    Hint Constructors step: core.

    Variant all_step (c1 c2: Configuration.t): Prop :=
    | all_step_intro
        e tid
        (STEP: estep e tid c1 c2)
    .
    Hint Constructors all_step: core.

    Lemma estep_future
          e tid c1 c2
          (STEP: estep e tid c1 c2)
          (WF1: Configuration.wf c1):
      <<WF2: Configuration.wf c2>> /\
      <<GL_FUTURE: Global.future (Configuration.global c1) (Configuration.global c2)>>.
    Proof.
      inv WF1. inv WF. inv STEP; s.
      exploit THREADS; ss; eauto. i.
      exploit SCThread.step_future; eauto. s. i. des.
      splits; eauto.
      econs; ss. econs.
      - i. Configuration.simplify.
        + exploit THREADS; try apply TH1; eauto. i. des.
          exploit SCThread.step_disjoint; eauto. s. i. des.
          symmetry. auto.
        + exploit THREADS; try apply TH2; eauto. i. des.
          exploit SCThread.step_disjoint; eauto. i. des.
          auto.
        + eapply DISJOINT; [|eauto|eauto]. auto.
      - i. Configuration.simplify.
        exploit THREADS; try apply TH; eauto. i.
        exploit SCThread.step_disjoint; eauto. s. i. des.
        auto.
      - i. destruct (Local.promises lc2 loc) eqn:LGET.
        + exists tid, lang, st2, lc2. splits; ss.
          rewrite IdentMap.Facts.add_o. condtac; ss.
        + exploit SCThread.step_promises_minus; try exact STEP0. s. i.
          eapply equal_f in x1.
          revert x1. unfold BoolMap.minus. rewrite GET, LGET. s. i.
          destruct (Global.promises (Configuration.global c1) loc) eqn:GET1; ss.
          destruct (Local.promises lc1 loc) eqn:LGET1; ss.
          exploit PROMISES; eauto. i. des.
          exists tid0, lang0, st, lc. splits; ss.
          rewrite IdentMap.Facts.add_o. condtac; ss. subst. congr.
    Qed.

    Lemma step_future
          e tid c1 c2
          (STEP: step e tid c1 c2)
          (WF1: Configuration.wf c1):
      <<WF2: Configuration.wf c2>> /\
      <<GL_FUTURE: Global.future (Configuration.global c1) (Configuration.global c2)>>.
    Proof.
      inv STEP. eauto using estep_future.
    Qed.

    Lemma all_step_future
          c1 c2
          (STEP: all_step c1 c2)
          (WF1: Configuration.wf c1):
      <<WF2: Configuration.wf c2>> /\
      <<GL_FUTURE: Global.future (Configuration.global c1) (Configuration.global c2)>>.
    Proof.
      inv STEP. eapply step_future; eauto.
    Qed.

    Lemma rtc_all_step_future
          c1 c2
          (STEPS: rtc all_step c1 c2)
          (WF1: Configuration.wf c1):
      <<WF2: Configuration.wf c2>> /\
      <<GL_FUTURE: Global.future (Configuration.global c1) (Configuration.global c2)>>.
    Proof.
      revert WF1. induction STEPS; i.
      { splits; auto. refl. }
      { hexploit all_step_future; eauto.
        i. des. hexploit IHSTEPS; eauto. i. des. splits; eauto. etrans; eauto.
      }
    Qed.
  End SCConfiguration.
End SCConfiguration.


Definition is_accessing (e:ProgramEvent.t): option Loc.t :=
  match e with
  | ProgramEvent.read loc _ _ => Some loc
  | ProgramEvent.write loc _ _ => Some loc
  | ProgramEvent.update loc _ _ _ _ => Some loc
  | _ => None
  end.


(** L-SC race **)
Module SCRace.
  Section SCRace.
    Variable L: Loc.t -> bool.

    Definition race lang (th: Thread.t lang): Prop :=
      exists e st' loc,
        (<<STEP: Language.step _ e (Thread.state th) st'>>) /\
        (<<ACCESS: is_accessing e = (Some loc)>>) /\
        (<<LOC: L loc>>) /\
        (<<MAXIMAL: SCLocal.non_maximal th.(Thread.local) th.(Thread.global).(Global.memory) loc>>).

    Definition race_steps (c: Configuration.t) (tid: Ident.t): Prop :=
      exists lang st1 lc1,
        (<<TID: IdentMap.find tid (Configuration.threads c) = Some (existT _ lang st1, lc1)>>) /\
        (<<SCRACE: race (Thread.mk _ st1 lc1 c.(Configuration.global))>>).

    Definition racefree (c: Configuration.t): Prop :=
      forall tid c2
             (STEPS: rtc (SCConfiguration.all_step L) c c2),
        ~ race_steps c2 tid.

    Definition racefree_syn (syn: Threads.syntax): Prop :=
      racefree (Configuration.init syn).

    Lemma step_racefree
          e tid c1 c2
          (RACEFREE: racefree c1)
          (STEP: SCConfiguration.step L e tid c1 c2):
      racefree c2.
    Proof.
      ii. eapply RACEFREE; cycle 1; eauto.
      econs 2; eauto. inv STEP. econs; eauto.
    Qed.
  End SCRace.
End SCRace.
