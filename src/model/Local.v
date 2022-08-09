Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
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

Set Implicit Arguments.


Module ThreadEvent.
  Variant t :=
  | promise (loc: Loc.t)
  | reserve (loc: Loc.t)
  | cancel (loc: Loc.t)
  | silent
  | read (loc: Loc.t) (ts: Time.t) (val: Const.t) (released: option View.t) (ord: Ordering.t)
  | write (loc: Loc.t) (from to: Time.t) (val: Const.t) (released: option View.t) (ord: Ordering.t)
  | update (loc: Loc.t) (tsr tsw: Time.t) (valr valw: Const.t)
           (releasedr releasedw: option View.t) (ordr ordw: Ordering.t)
  | fence (ordr ordw: Ordering.t)
  | syscall (e: Event.t)
  | failure
  | racy_read (loc: Loc.t) (to: option Time.t) (val: Const.t) (ord: Ordering.t)
  | racy_write (loc: Loc.t) (to: option Time.t) (val: Const.t) (ord: Ordering.t)
  | racy_update (loc: Loc.t) (to: option Time.t) (valr valw: Const.t) (ordr ordw: Ordering.t)
  .
  #[global] Hint Constructors t: core.

  Definition get_event (e: t): option Event.t :=
    match e with
    | syscall e => Some e
    | _ => None
    end.

  Definition get_program_event (e: t): ProgramEvent.t :=
    match e with
    | read loc _ val _ ord => ProgramEvent.read loc val ord
    | write loc _ _ val _ ord => ProgramEvent.write loc val ord
    | update loc _ _ valr valw _ _ ordr ordw => ProgramEvent.update loc valr valw ordr ordw
    | fence ordr ordw => ProgramEvent.fence ordr ordw
    | syscall ev => ProgramEvent.syscall ev
    | failure => ProgramEvent.failure
    | racy_read loc _ val ord => ProgramEvent.read loc val ord
    | racy_write loc _ val ord => ProgramEvent.write loc val ord
    | racy_update loc _ valr valw ordr ordw => ProgramEvent.update loc valr valw ordr ordw
    | _ => ProgramEvent.silent
    end.

  Definition get_machine_event (e: t): MachineEvent.t :=
    match e with
    | syscall e => MachineEvent.syscall e
    | failure
    | racy_write _ _ _ _
    | racy_update _ _ _ _ _ _ => MachineEvent.failure
    | _ => MachineEvent.silent
    end.

  Definition get_machine_event_pf (e: t): MachineEvent.t :=
    match e with
    | syscall e => MachineEvent.syscall e
    | failure
    | racy_read _ _ _ _
    | racy_write _ _ _ _
    | racy_update _ _ _ _ _ _ => MachineEvent.failure
    | _ => MachineEvent.silent
    end.

  Definition is_reading (e:t): option (Loc.t * Time.t * Const.t * option View.t * Ordering.t) :=
    match e with
    | read loc ts val released ord => Some (loc, ts, val, released, ord)
    | update loc tsr _ valr _ releasedr _ ordr _ => Some (loc, tsr, valr, releasedr, ordr)
    | _ => None
    end.

  Definition is_writing (e:t): option (Loc.t * Time.t * Time.t * Const.t * option View.t * Ordering.t) :=
    match e with
    | write loc from to val released ord => Some (loc, from, to, val, released, ord)
    | update loc tsr tsw _ valw _ releasedw _ ordw => Some (loc, tsr, tsw, valw, releasedw, ordw)
    | _ => None
    end.

  Definition is_accessing (e:t): option (Loc.t * Time.t) :=
    match e with
    | read loc ts _ _ _ => Some (loc, ts)
    | write loc _ ts _ _ _ => Some (loc, ts)
    | update loc _ ts _ _ _ _ _ _ => Some (loc, ts)
    | _ => None
    end.

  Definition is_accessing_loc (l: Loc.t) (e: t): Prop :=
    match e with
    | read loc _ _ _ _
    | write loc _ _ _ _ _
    | update loc _ _ _ _ _ _ _ _
    | racy_read loc _ _ _
    | racy_write loc _ _ _
    | racy_update loc _ _ _ _ _ => loc = l
    | _ => False
    end.

  Definition is_racy (e: t): Prop :=
    match e with
    | racy_read _ _ _ _
    | racy_write _ _ _ _
    | racy_update _ _ _ _ _ _ => True
    | _ => False
    end.

  Definition is_racy_promise (e: t): Prop :=
    match e with
    | racy_read _ None _ _
    | racy_write _ None _ _ => True
    | racy_update _ None _ _ ordr ordw =>
        Ordering.le Ordering.plain ordr /\
        Ordering.le Ordering.plain ordw
    | _ => False
    end.

  Definition is_sc (e: t): Prop :=
    match e with
    | fence _ ordw => Ordering.le Ordering.seqcst ordw
    | syscall _ => True
    | _ => False
    end.

  Definition is_program (e: t): Prop :=
    match e with
    | promise _
    | reserve _
    | cancel _ => False
    | _ => True
    end.

  Definition is_silent (e: t): Prop :=
    get_machine_event e = MachineEvent.silent.

  Lemma eq_program_event_eq_loc
        e1 e2 loc
        (EVENT: get_program_event e1 = get_program_event e2):
    is_accessing_loc loc e1 <-> is_accessing_loc loc e2.
  Proof.
    unfold is_accessing_loc.
    destruct e1, e2; ss; inv EVENT; ss.
  Qed.
End ThreadEvent.


Module Local.
  Structure t := mk {
    tview: TView.t;
    promises: BoolMap.t;
    reserves: BoolMap.t;
  }.

  Definition init := mk TView.bot BoolMap.bot BoolMap.bot.

  Variant is_terminal (lc:t): Prop :=
  | is_terminal_intro
      (PROMISES: promises lc = BoolMap.bot)
  .
  #[global] Hint Constructors is_terminal: core.

  Variant wf (lc: t) (gl: Global.t): Prop :=
  | wf_intro
      (TVIEW_WF: TView.wf (tview lc))
      (TVIEW_CLOSED: TView.closed (tview lc) (Global.memory gl))
      (PROMISES: BoolMap.le (promises lc) (Global.promises gl))
      (PROMISES_FINITE: BoolMap.finite (promises lc))
      (RESERVES: BoolMap.le (reserves lc) (Global.reserves gl))
      (RESERVES_FINITE: BoolMap.finite (reserves lc))
  .
  #[global] Hint Constructors wf: core.

  Lemma fully_reserved_wf
        lc gl
        (WF: wf lc gl):
    wf lc (Global.fully_reserved gl).
  Proof.
    inv WF. econs; ss.
  Qed.

  Variant disjoint (lc1 lc2:t): Prop :=
  | disjoint_intro
      (PROMISES_DISJOINT: BoolMap.disjoint (promises lc1) (promises lc2))
      (RESERVES_DISJOINT: BoolMap.disjoint (reserves lc1) (reserves lc2))
  .
  #[global] Hint Constructors disjoint: core.

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    econs; symmetry; apply H.
  Qed.


  Variant promise_step (lc1: t) (gl1: Global.t) (loc: Loc.t) (lc2: t) (gl2: Global.t): Prop :=
  | promise_step_intro
      prm2 gprm2
      (PROMISE: Promises.promise (promises lc1) (Global.promises gl1) loc prm2 gprm2)
      (LC2: lc2 = mk (tview lc1) prm2 (reserves lc1))
      (GL2: gl2 = Global.mk (Global.sc gl1) gprm2 (Global.reserves gl1) (Global.memory gl1))
  .
  #[global] Hint Constructors promise_step: core.

  Variant reserve_step (lc1: t) (gl1: Global.t) (loc: Loc.t) (lc2: t) (gl2: Global.t): Prop :=
  | reserve_step_intro
      rsv2 grsv2
      (RESERVE: Reserves.reserve (reserves lc1) (Global.reserves gl1) loc rsv2 grsv2)
      (LC2: lc2 = mk (tview lc1) (promises lc1) rsv2)
      (GL2: gl2 = Global.mk (Global.sc gl1) (Global.promises gl1) grsv2 (Global.memory gl1))
  .
  #[global] Hint Constructors reserve_step: core.

  Variant cancel_step (lc1: t) (gl1: Global.t) (loc: Loc.t) (lc2: t) (gl2: Global.t): Prop :=
  | cancel_step_intro
      rsv2 grsv2
      (CANCEL: Reserves.cancel (reserves lc1) (Global.reserves gl1) loc rsv2 grsv2)
      (LC2: lc2 = mk (tview lc1) (promises lc1) rsv2)
      (GL2: gl2 = Global.mk (Global.sc gl1) (Global.promises gl1) grsv2 (Global.memory gl1))
  .
  #[global] Hint Constructors cancel_step: core.

  Variant read_step
          (lc1: t) (gl1: Global.t)
          (loc: Loc.t) (to: Time.t) (val: Const.t) (released: option View.t) (ord: Ordering.t)
          (lc2: t): Prop :=
  | read_step_intro
      from val' na
      tview2
      (GET: Memory.get loc to (Global.memory gl1) = Some (from, Message.mk val' released na))
      (VAL: Const.le val val')
      (READABLE: TView.readable (TView.cur (tview lc1)) loc to ord)
      (TVIEW: TView.read_tview (tview lc1) loc to released ord = tview2)
      (LC2: lc2 = mk tview2 (promises lc1) (reserves lc1)):
      read_step lc1 gl1 loc to val released ord lc2
  .
  #[global] Hint Constructors read_step: core.

  Variant write_step
          (reserved: TimeMap.t)
          (lc1: t) (gl1: Global.t)
          (loc: Loc.t) (from to: Time.t)
          (val: Const.t) (releasedm released: option View.t) (ord: Ordering.t)
          (lc2: t) (gl2: Global.t): Prop :=
  | write_step_intro
      prm2 gprm2 mem2
      (RELEASED: released = TView.write_released (tview lc1) loc to releasedm ord)
      (WRITABLE: TView.writable (TView.cur (tview lc1)) loc to ord)
      (RESERVED: Global.reserves gl1 loc = true /\ reserves lc1 loc = false -> Time.lt (reserved loc) from)
      (FULFILL: Promises.fulfill (promises lc1) (Global.promises gl1) loc ord prm2 gprm2)
      (WRITE: Memory.add (Global.memory gl1) loc from to
                         (Message.mk val released (Ordering.le ord Ordering.na)) mem2)
      (LC2: lc2 = mk (TView.write_tview (tview lc1) loc to ord) prm2 (reserves lc1))
      (GL2: gl2 = Global.mk (Global.sc gl1) gprm2 (Global.reserves gl1) mem2):
      write_step reserved lc1 gl1 loc from to val releasedm released ord lc2 gl2
  .
  #[global] Hint Constructors write_step: core.

  Variant fence_step (lc1: t) (gl1: Global.t) (ordr ordw: Ordering.t) (lc2: t) (gl2: Global.t): Prop :=
  | fence_step_intro
      tview2
      (READ: TView.read_fence_tview (tview lc1) ordr = tview2)
      (LC2: lc2 = mk (TView.write_fence_tview tview2 (Global.sc gl1) ordw)
                     (promises lc1) (reserves lc1))
      (GL2: gl2 = Global.mk (TView.write_fence_sc tview2 (Global.sc gl1) ordw)
                            (Global.promises gl1) (Global.reserves gl1) (Global.memory gl1))
      (PROMISES: Ordering.le Ordering.seqcst ordw -> promises lc1 = BoolMap.bot):
      fence_step lc1 gl1 ordr ordw lc2 gl2
  .
  #[global] Hint Constructors fence_step: core.

  Variant failure_step (lc1:t): Prop :=
  | failure_step_intro
  .
  #[global] Hint Constructors failure_step: core.

  Variant is_racy (lc1: t) (gl1: Global.t) (loc: Loc.t): forall (to: option Time.t) (ord: Ordering.t), Prop :=
  | is_racy_promise
      ord
      (GET: (Global.promises gl1) loc = true)
      (GETP: (promises lc1) loc = false):
    is_racy lc1 gl1 loc None ord
  | is_racy_message
      to from val released na ord
      (GET: Memory.get loc to (Global.memory gl1) = Some (from, Message.mk val released na))
      (RACE: TView.racy_view (TView.cur (tview lc1)) loc to)
      (MSG: Ordering.le Ordering.plain ord -> na = true):
    is_racy lc1 gl1 loc (Some to) ord
  .
  #[global] Hint Constructors is_racy: core.

  Variant racy_read_step (lc1: t) (gl1: Global.t) (loc: Loc.t) (to: option Time.t) (val:Const.t) (ord:Ordering.t): Prop :=
  | racy_read_step_intro
      (RACE: is_racy lc1 gl1 loc to ord)
  .
  #[global] Hint Constructors racy_read_step: core.

  Variant racy_write_step (lc1: t) (gl1: Global.t) (loc: Loc.t) (to: option Time.t) (ord: Ordering.t): Prop :=
  | racy_write_step_intro
      (RACE: is_racy lc1 gl1 loc to ord)
  .
  #[global] Hint Constructors racy_write_step: core.

  Variant racy_update_step (lc1: t) (gl1: Global.t) (loc: Loc.t):
    forall (to: option Time.t) (ordr ordw: Ordering.t), Prop :=
  | racy_update_step_ordr
      ordr ordw
      (ORDR: Ordering.le ordr Ordering.na):
    racy_update_step lc1 gl1 loc None ordr ordw
  | racy_update_step_ordw
      ordr ordw
      (ORDW: Ordering.le ordw Ordering.na):
    racy_update_step lc1 gl1 loc None ordr ordw
  | racy_update_step_race
      to ordr ordw
      (RACE: is_racy lc1 gl1 loc to ordr):
    racy_update_step lc1 gl1 loc to ordr ordw
  .
  #[global] Hint Constructors racy_update_step: core.


  Variant internal_step:
    forall (e: ThreadEvent.t) (lc1: t) (gl1: Global.t) (lc2: t) (gl2: Global.t), Prop :=
  | step_promise
      lc1 gl1 
      loc lc2 gl2
      (LOCAL: promise_step lc1 gl1 loc lc2 gl2):
    internal_step (ThreadEvent.promise loc) lc1 gl1 lc2 gl2
  | step_reserve
      lc1 gl1 
      loc lc2 gl2
      (LOCAL: reserve_step lc1 gl1 loc lc2 gl2):
    internal_step (ThreadEvent.reserve loc) lc1 gl1 lc2 gl2
  | step_cancel
      lc1 gl1 
      loc lc2 gl2
      (LOCAL: cancel_step lc1 gl1 loc lc2 gl2):
    internal_step (ThreadEvent.cancel loc) lc1 gl1 lc2 gl2
  .

  Variant program_step (reserved: TimeMap.t):
    forall (e: ThreadEvent.t) (lc1: t) (gl1: Global.t) (lc2: t) (gl2: Global.t), Prop :=
  | step_silent
      lc1 gl1:
    program_step reserved ThreadEvent.silent lc1 gl1 lc1 gl1
  | step_read
      lc1 gl1
      loc to val released ord lc2
      (LOCAL: read_step lc1 gl1 loc to val released ord lc2):
    program_step reserved (ThreadEvent.read loc to val released ord) lc1 gl1 lc2 gl1
  | step_write
      lc1 gl1
      loc from to val released ord lc2 gl2
      (LOCAL: write_step reserved lc1 gl1 loc from to val None released ord lc2 gl2):
    program_step reserved (ThreadEvent.write loc from to val released ord) lc1 gl1 lc2 gl2
  | step_update
      lc1 gl1
      loc ordr ordw
      tsr valr releasedr releasedw lc2
      tsw valw lc3 gl3
      (LOCAL1: read_step lc1 gl1 loc tsr valr releasedr ordr lc2)
      (LOCAL2: write_step reserved lc2 gl1 loc tsr tsw valw releasedr releasedw ordw lc3 gl3):
    program_step reserved
                 (ThreadEvent.update loc tsr tsw valr valw releasedr releasedw ordr ordw)
                 lc1 gl1 lc3 gl3
  | step_fence
      lc1 gl1
      ordr ordw lc2 gl2
      (LOCAL: fence_step lc1 gl1 ordr ordw lc2 gl2):
    program_step reserved (ThreadEvent.fence ordr ordw) lc1 gl1 lc2 gl2
  | step_syscall
      lc1 gl1
      e lc2 gl2
      (LOCAL: fence_step lc1 gl1 Ordering.seqcst Ordering.seqcst lc2 gl2):
    program_step reserved (ThreadEvent.syscall e) lc1 gl1 lc2 gl2
  | step_failure
      lc1 gl1
      (LOCAL: failure_step lc1):
    program_step reserved ThreadEvent.failure lc1 gl1 lc1 gl1
  | step_racy_read
      lc1 gl1
      loc to val ord
      (LOCAL: racy_read_step lc1 gl1 loc to val ord):
    program_step reserved (ThreadEvent.racy_read loc to val ord) lc1 gl1 lc1 gl1
  | step_racy_write
      lc1 gl1
      loc to val ord
      (LOCAL: racy_write_step lc1 gl1 loc to ord):
    program_step reserved (ThreadEvent.racy_write loc to val ord) lc1 gl1 lc1 gl1
  | step_racy_update
      lc1 gl1
      loc to valr valw ordr ordw
      (LOCAL: racy_update_step lc1 gl1 loc to ordr ordw):
    program_step reserved (ThreadEvent.racy_update loc to valr valw ordr ordw) lc1 gl1 lc1 gl1
  .
  #[global] Hint Constructors program_step: core.


  (* step_future *)

  Lemma promise_step_future
        lc1 gl1 loc lc2 gl2
        (STEP: promise_step lc1 gl1 loc lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.future gl1 gl2>>.
  Proof.
    inv LC_WF1. inv GL_WF1. inv STEP. ss.
    hexploit Promises.promise_le; eauto. i.
    hexploit Promises.promise_finite; eauto. i.
    splits; ss; try refl. econs; refl.
  Qed.

  Lemma reserve_step_future
        lc1 gl1 loc lc2 gl2
        (STEP: reserve_step lc1 gl1 loc lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.future gl1 gl2>>.
  Proof.
    inv LC_WF1. inv GL_WF1. inv STEP. ss.
    hexploit Reserves.reserve_le; eauto. i.
    hexploit Reserves.reserve_finite; eauto. i.
    inv RESERVE.
    splits; ss; try refl. econs; refl.
  Qed.

  Lemma cancel_step_future
        lc1 gl1 loc lc2 gl2
        (STEP: cancel_step lc1 gl1 loc lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.future gl1 gl2>>.
  Proof.
    inv LC_WF1. inv GL_WF1. inv STEP. ss.
    hexploit Reserves.cancel_le; eauto. i.
    hexploit Reserves.cancel_finite; eauto. i.
    inv CANCEL.
    splits; try refl; econs; ss; try refl.
  Qed.

  Lemma read_step_future
        lc1 gl1 loc ts val released ord lc2
        (STEP: read_step lc1 gl1 loc ts val released ord lc2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl1>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<REL_WF: View.opt_wf released>> /\
    <<REL_CLOSED: Memory.closed_opt_view released (Global.memory gl1)>> /\
    <<REL_TS: Time.le (View.rlx (View.unwrap released) loc) ts>>.
  Proof.
    inv LC_WF1. inv GL_WF1. inv STEP. ss.
    dup MEM_CLOSED. inv MEM_CLOSED0. exploit CLOSED; eauto. i. des.
    inv MSG_WF. inv MSG_CLOSED. inv MSG_TS.
    exploit TViewFacts.read_future; try exact GET; eauto.
    i. des. splits; auto.
    - econs; eauto.
    - apply TViewFacts.read_tview_incr.
  Qed.

  Lemma write_step_future
        reserved lc1 gl1 loc from to val releasedm released ord lc2 gl2
        (STEP: write_step reserved lc1 gl1 loc from to val releasedm released ord lc2 gl2)
        (REL_WF: View.opt_wf releasedm)
        (REL_CLOSED: Memory.closed_opt_view releasedm (Global.memory gl1))
        (REL_TS: Time.le (View.rlx (View.unwrap releasedm) loc) to)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.future gl1 gl2>> /\
    <<REL_WF: View.opt_wf released>> /\
    <<REL_TS: Time.le ((View.rlx (View.unwrap released)) loc) to>> /\
    <<REL_CLOSED: Memory.closed_opt_view released (Global.memory gl2)>>.
  Proof.
    inv LC_WF1. inv GL_WF1. inv STEP. ss.
    hexploit Promises.fulfill_le; try exact FULFILL; eauto. i.
    hexploit Promises.fulfill_finite; try exact FULFILL; eauto. i.
    exploit TViewFacts.write_future; eauto. s. i. des.
    exploit Memory.add_future; try apply WRITE; eauto.
    { econs. eapply TViewFacts.write_released_ts; eauto. }
    i. des.
    exploit Memory.add_get0; try apply WRITE; eauto. i. des.
    splits; eauto.
    - econs; eauto. ss.
      eapply Memory.future_closed_timemap; eauto.
    - apply TViewFacts.write_tview_incr. auto.
    - econs; ss. refl.
    - eapply TViewFacts.write_released_ts; eauto.
  Qed.

  Lemma fence_step_future
        lc1 gl1 ordr ordw lc2 gl2
        (STEP: fence_step lc1 gl1 ordr ordw lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.future gl1 gl2>>.
  Proof.
    inv LC_WF1. inv GL_WF1. inv STEP. ss.
    exploit TViewFacts.read_fence_future; eauto. i. des.
    exploit TViewFacts.write_fence_future; eauto. i. des.
    splits; eauto.
    - econs; ss.
    - etrans.
      + apply TViewFacts.write_fence_tview_incr. auto.
      + apply TViewFacts.write_fence_tview_mon; eauto; try refl.
        apply TViewFacts.read_fence_tview_incr. auto.
    - econs; try refl.
      apply TViewFacts.write_fence_sc_incr.
  Qed.

  Lemma internal_step_future
        e lc1 gl1 lc2 gl2
        (STEP: internal_step e lc1 gl1 lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.future gl1 gl2>>.
  Proof.
    inv STEP.
    - eapply promise_step_future; eauto.
    - eapply reserve_step_future; eauto.
    - eapply cancel_step_future; eauto.
  Qed.

  Lemma program_step_future
        reserved e lc1 gl1 lc2 gl2
        (STEP: program_step reserved e lc1 gl1 lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.future gl1 gl2>>.
  Proof.
    inv STEP; try by (esplits; eauto; try refl).
    - exploit read_step_future; eauto. i. des.
      esplits; eauto; try refl.
    - exploit write_step_future; eauto;
        (try by econs); try apply Time.bot_spec. i. des.
      esplits; eauto; try refl.
    - exploit read_step_future; eauto. i. des.
      exploit write_step_future; eauto; try by econs.
      { etrans; eauto. inv LOCAL2.
        econs. eauto using Memory.add_ts.
      }
      i. des.
      esplits; eauto. etrans; eauto.
    - exploit fence_step_future; eauto.
    - exploit fence_step_future; eauto.
  Qed.


  (* step_inhabited *)

  Lemma internal_step_inhabited
        e lc1 gl1 lc2 gl2
        (STEP: internal_step e lc1 gl1 lc2 gl2)
        (INHABITED1: Memory.inhabited (Global.memory gl1)):
    <<INHABITED2: Memory.inhabited (Global.memory gl2)>>.
  Proof.
    inv STEP; inv LOCAL; ss.
  Qed.

  Lemma program_step_inhabited
        reserved e lc1 gl1 lc2 gl2
        (STEP: program_step reserved e lc1 gl1 lc2 gl2)
        (INHABITED1: Memory.inhabited (Global.memory gl1)):
    <<INHABITED2: Memory.inhabited (Global.memory gl2)>>.
  Proof.
    inv STEP; eauto.
    - inv LOCAL. eauto using Memory.add_inhabited.
    - inv LOCAL2. eauto using Memory.add_inhabited.
    - inv LOCAL. ss.
    - inv LOCAL. ss.
  Qed.


  (* step_disjoint *)

  Lemma promise_step_disjoint
        lc1 gl1 loc lc2 gl2 lc
        (STEP: promise_step lc1 gl1 loc lc2 gl2)
        (DISJOINT1: disjoint lc1 lc)
        (LC_WF: wf lc gl1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<LC_WF: wf lc gl2>>.
  Proof.
    inv DISJOINT1. inv LC_WF. inv STEP.
    exploit Promises.promise_disjoint; eauto. i. des.
    esplits; eauto.
  Qed.

  Lemma reserve_step_disjoint
        lc1 gl1 loc lc2 gl2 lc
        (STEP: reserve_step lc1 gl1 loc lc2 gl2)
        (DISJOINT1: disjoint lc1 lc)
        (LC_WF: wf lc gl1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<LC_WF: wf lc gl2>>.
  Proof.
    inv DISJOINT1. inv LC_WF. inv STEP.
    exploit Reserves.reserve_disjoint; eauto. i. des.
    esplits; eauto.
  Qed.

  Lemma cancel_step_disjoint
        lc1 gl1 loc lc2 gl2 lc
        (STEP: cancel_step lc1 gl1 loc lc2 gl2)
        (DISJOINT1: disjoint lc1 lc)
        (LC_WF: wf lc gl1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<LC_WF: wf lc gl2>>.
  Proof.
    inv DISJOINT1. inv LC_WF. inv STEP.
    exploit Reserves.cancel_disjoint; eauto. i. des.
    esplits; eauto.
  Qed.

  Lemma read_step_disjoint
        lc1 gl1 loc ts val released ord lc2 lc
        (STEP: read_step lc1 gl1 loc ts val released ord lc2)
        (DISJOINT1: disjoint lc1 lc):
    disjoint lc2 lc.
  Proof.
    inv DISJOINT1. inv STEP. ss.
  Qed.

  Lemma write_step_disjoint
        reserved lc1 gl1 loc from to val releasedm released ord lc2 gl2 lc
        (STEP: write_step reserved lc1 gl1 loc from to val releasedm released ord lc2 gl2)
        (DISJOINT1: disjoint lc1 lc)
        (LC_WF: wf lc gl1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<LC_WF: wf lc gl2>>.
  Proof.
    inv DISJOINT1. inv LC_WF. inv STEP.
    exploit Promises.fulfill_disjoint; try exact FULFILL; eauto. i. des.
    esplits; eauto. econs; ss.
    eapply TView.add_closed; eauto.
  Qed.

  Lemma fence_step_disjoint
        lc1 gl1 ordr ordw lc2 gl2 lc
        (STEP: fence_step lc1 gl1 ordr ordw lc2 gl2)
        (DISJOINT1: disjoint lc1 lc)
        (LC_WF: wf lc gl1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<LC_WF: wf lc gl2>>.
  Proof.
    inv DISJOINT1. inv LC_WF. inv STEP. splits; ss.
  Qed.

  Lemma read_step_promises
        lc1 gl1 loc to val released ord lc2
        (READ: read_step lc1 gl1 loc to val released ord lc2):
    (promises lc1) = (promises lc2).
  Proof.
    inv READ. auto.
  Qed.

  Lemma internal_step_disjoint
        e lc1 gl1 lc2 gl2 lc
        (STEP: internal_step e lc1 gl1 lc2 gl2)
        (DISJOINT1: disjoint lc1 lc)
        (LC_WF: wf lc gl1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<LC_WF: wf lc gl2>>.
  Proof.
    inv STEP.
    - eapply promise_step_disjoint; eauto.
    - eapply reserve_step_disjoint; eauto.
    - eapply cancel_step_disjoint; eauto.
  Qed.

  Lemma program_step_disjoint
        reserved e lc1 gl1 lc2 gl2 lc
        (STEP: program_step reserved e lc1 gl1 lc2 gl2)
        (DISJOINT1: disjoint lc1 lc)
        (LC_WF: wf lc gl1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<LC_WF: wf lc gl2>>.
  Proof.
    inv STEP; try by (esplits; eauto).
    - exploit read_step_disjoint; eauto.
    - exploit write_step_disjoint; eauto.
    - exploit read_step_disjoint; eauto. i.
      exploit write_step_disjoint; eauto.
    - exploit fence_step_disjoint; eauto.
    - exploit fence_step_disjoint; eauto.
  Qed.

  Lemma program_step_promises
        reserved e lc1 gl1 lc2 gl2
        (STEP: program_step reserved e lc1 gl1 lc2 gl2):
    BoolMap.le (promises lc2) (promises lc1) /\
    BoolMap.le (Global.reserves gl2) (Global.reserves gl1).
  Proof.
    inv STEP; ss; try by (inv LOCAL; ss).
    - inv LOCAL. inv FULFILL; ss.
      split; eauto using BoolMap.remove_le.
    - inv LOCAL1. inv LOCAL2. inv FULFILL; ss.
      split; eauto using BoolMap.remove_le.
  Qed.

  Lemma program_step_reserves
        reserved e lc1 gl1 lc2 gl2
        (STEP: program_step reserved e lc1 gl1 lc2 gl2):
    reserves lc1 = reserves lc2 /\
    Global.reserves gl1 = Global.reserves gl2.
  Proof.
    inv STEP; ss; try by (inv LOCAL; ss).
    inv LOCAL1. inv LOCAL2. ss.
  Qed.

  Lemma internal_step_promises_minus
        e lc1 gl1 lc2 gl2
        (STEP: internal_step e lc1 gl1 lc2 gl2):
    BoolMap.minus (Global.promises gl1) (promises lc1) =
    BoolMap.minus (Global.promises gl2) (promises lc2).
  Proof.
    inv STEP; inv LOCAL; ss.
    eapply Promises.promise_minus; eauto.
  Qed.

  Lemma program_step_promises_minus
        reserved e lc1 gl1 lc2 gl2
        (STEP: program_step reserved e lc1 gl1 lc2 gl2):
    BoolMap.minus (Global.promises gl1) (promises lc1) =
    BoolMap.minus (Global.promises gl2) (promises lc2).
  Proof.
    inv STEP; ss; try by (inv LOCAL; ss).
    - inv LOCAL. ss.
      eapply Promises.fulfill_minus; eauto.
    - inv LOCAL1. inv LOCAL2. ss.
      eapply Promises.fulfill_minus; eauto.
  Qed.

  Lemma internal_step_reserves_minus
        e lc1 gl1 lc2 gl2
        (STEP: internal_step e lc1 gl1 lc2 gl2):
    BoolMap.minus (Global.reserves gl1) (reserves lc1) =
    BoolMap.minus (Global.reserves gl2) (reserves lc2).
  Proof.
    inv STEP; inv LOCAL; ss.
    - eapply Reserves.reserve_minus; eauto.
    - eapply Reserves.cancel_minus; eauto.
  Qed.

  Lemma program_step_reserves_minus
        reserved e lc1 gl1 lc2 gl2
        (STEP: program_step reserved e lc1 gl1 lc2 gl2):
    BoolMap.minus (Global.reserves gl1) (reserves lc1) =
    BoolMap.minus (Global.reserves gl2) (reserves lc2).
  Proof.
    inv STEP; ss; try by (inv LOCAL; ss).
    inv LOCAL1. inv LOCAL2. ss.
  Qed.
End Local.
