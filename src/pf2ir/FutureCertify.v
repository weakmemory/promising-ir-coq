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

Require Import Mapping.
Require Import PFConsistent.

Set Implicit Arguments.


Section FutureCertify.
  Variable lang: language.
  
  Variant certify (reserved: TimeMap.t) (loc: Loc.t) (ts: Time.t) (th: Thread.t lang): Prop :=
    | certify_failure
        pf e th1 th2
        (STEPS: rtc (pstep (Thread.step reserved true) (strict_pf /1\ non_sc)) th th1)
        (STEP_FAILURE: Thread.step reserved pf e th1 th2)
        (EVENT_FAILURE: ThreadEvent.get_machine_event e = MachineEvent.failure)
        (EVENT_PF: strict_pf e)
    | certify_fulfill
        pf e th1 th2
        from to val released ord
        (STEPS: rtc (pstep (Thread.step reserved true) (strict_pf /1\ non_sc)) th th1)
        (STEP_FULFILL: Thread.step reserved pf e th1 th2)
        (EVENT_FULFILL: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord))
        (TO: Time.lt ts to)
        (ORD: Ordering.le ord Ordering.na)
  .

  Lemma spf_consistent_certify
        th loc
        (LC_WF: Local.wf (Thread.local th) (Thread.global th))
        (GL_WF: Global.wf (Thread.global th))
        (CONS: PFConsistent.spf_consistent th)
        (PROMISED: Local.promises (Thread.local th) loc = true):
    certify (Memory.max_timemap (Global.memory (Thread.global th)))
            loc (Memory.max_ts loc (Global.memory (Thread.global th)))
            (Thread.fully_reserved th).
  Proof.
    inv CONS.
    { econs 1; eauto. }
    exploit (Memory.max_ts_spec loc); try apply GL_WF. i. des.
    remember (Memory.max_ts loc (Global.memory (Thread.global th))) as ts in *.
    exploit Thread.fully_reserved_wf; eauto.
    clear LC_WF GL_WF. i. des.
    remember (Memory.max_timemap (Global.memory (Thread.global th))) as reserved.
    remember (Thread.fully_reserved th) as th0.
    replace (Local.promises (Thread.local th) loc) with
      (Local.promises (Thread.local th0) loc) in * by (subst; ss).
    replace (Global.memory (Thread.global th)) with
      (Global.memory (Thread.global th0)) in * by (subst; ss).
    clear th Heqts Heqreserved Heqth0 MAX. revert PROMISED.
    induction STEPS; i.
    { rewrite PROMISES in *. ss. }
    destruct (Local.promises (Thread.local y) loc) eqn:PROMISEDY.
    { dup H. inv H0.
      exploit Thread.step_future; try exact STEP; eauto. i. des.
      exploit Memory.future_get1; try apply GL_FUTURE; eauto. i. des.
      exploit IHSTEPS; eauto. i. inv x2.
      - econs 1; try exact STEP_FAILURE; eauto.
      - econs 2; try exact STEP_FULFILL; eauto.
    }

    move PROMISEDY at bottom.
    inv H. inv STEP.
    inv STEP0; ss; (try congr); (try by inv LOCAL; ss; congr).
    { (* write *)
      assert (loc0 = loc /\ Ordering.le ord Ordering.na).
      { inv LOCAL. inv FULFILL; ss; try congr. split; ss.
        revert PROMISEDY. erewrite BoolMap.remove_o; eauto.
        condtac; ss. congr.
      }
      des. subst.
      destruct (TimeFacts.le_lt_dec to (Memory.max_ts loc (Global.memory gl1))); cycle 1.
      { econs 2; [refl|..].
        - econs 2; [|econs 3]; eauto.
        - ss.
        - exploit Memory.max_ts_spec; try exact GET. i. des.
          eapply TimeFacts.le_lt_lt; eauto.
        - ss.
      }
      exploit (Memory.max_ts_spec loc); try apply GL_WF. i. des.
      destruct msg0. clear MAX.
      econs 1; [refl|..].
      - econs 2; [|econs 9]; eauto.
        econs. econs 2; try exact GET0.
        + unfold TView.racy_view.
          eapply TimeFacts.lt_le_lt; eauto.
          inv LOCAL. inv WRITABLE. ss.
          eapply TimeFacts.le_lt_lt; eauto.
          apply LC_WF.
        + destruct ord; ss.
      - ss.
      - ss.
    }

    { (* update *)
      assert (Ordering.le ordw Ordering.na).
      { inv LOCAL1. inv LOCAL2.  inv FULFILL; ss; try congr. }
      econs 1; [refl|..].
      - econs 2; [|econs 10]; eauto.
      - ss.
      - ii. ss. des. destruct ordw; ss.
    }
  Qed.

  Variant thread_map (f: map_t) (reserved: TimeMap.t) (th fth: Thread.t lang): Prop :=
    | thread_map_intro
        (STATE: Thread.state th = Thread.state fth)
        (LOCAL: local_map f (Thread.local th) (Thread.local fth))
        (GLOBAL: global_map f reserved (Local.reserves (Thread.local th))
                            (Thread.global th) (Thread.global fth))
        (FPROMISES: Local.promises (Thread.local fth) = BoolMap.bot)
        (GRESERVES: Global.reserves (Thread.global th) = BoolMap.top)
        (FGRESERVES: Global.reserves (Thread.global fth) = BoolMap.bot)
  .

  Lemma event_map_program_event
        f e fe
        (MAP: event_map f e fe):
    ThreadEvent.get_program_event e = ThreadEvent.get_program_event fe.
  Proof.
    inv MAP; ss.
  Qed.

  Lemma event_map_machine_event
        f e fe
        (MAP: event_map f e fe):
    ThreadEvent.get_machine_event e = ThreadEvent.get_machine_event fe.
  Proof.
    inv MAP; ss.
  Qed.

  Lemma event_map_strict_pf
        f e fe
        (MAP: event_map f e fe):
    strict_pf e <-> strict_pf fe.
  Proof.
    inv MAP; ss.
    - destruct to, fto; ss.
    - destruct to, fto; ss.
    - destruct to, fto; ss.
  Qed.

  Lemma event_map_non_sc
        f e fe
        (MAP: event_map f e fe):
    non_sc e <-> non_sc fe.
  Proof.
    inv MAP; ss.
  Qed.

  Lemma map_step
        reserved freserved
        f1 th1 fth1
        e th2
        (MAP_WF1: map_wf f1)
        (MAP_COMPLETE1: map_complete
                          f1
                          (Global.memory (Thread.global th1))
                          (Global.memory (Thread.global fth1)))
        (MAP1: thread_map f1 reserved th1 fth1)
        (LC_WF1: Local.wf (Thread.local th1) (Thread.global th1))
        (GL_WF1: Global.wf (Thread.global th1))
        (FLC_WF1: Local.wf (Thread.local fth1) (Thread.global fth1))
        (FGL_WF1: Global.wf (Thread.global fth1))
        (RESERVED: Memory.closed_timemap reserved (Global.memory (Thread.global th1)))
        (STEP: Thread.step reserved true e th1 th2)
        (EVENT1: ~ ThreadEvent.is_racy_promise e)
        (EVENT2: ~ ThreadEvent.is_sc e):
    exists f2 fe fth2,
      (<<FSTEP: Thread.step freserved true fe fth1 fth2>>) /\
      (<<EVENT: event_map f2 e fe>>) /\
      (<<MAP_INCR: f1 <3= f2>>) /\
      (<<MAP_WF2: map_wf f2>>) /\
      (<<MAP_COMPLETE2: map_complete
                          f2
                          (Global.memory (Thread.global th2))
                          (Global.memory (Thread.global fth2))>>) /\
      (<<MAP2: thread_map f2 reserved th2 fth2>>).
  Proof.
    destruct th1, fth1. inv MAP1. ss. subst. inv STEP.
    exploit map_program_step; try exact LOCAL; try exact GLOBAL; eauto. i. des.
    esplits; eauto.
    - econs; try exact FSTEP.
      erewrite <- event_map_program_event; eauto.
    - eauto.
    - exploit Local.program_step_reserves; try exact STEP0. i. des.
      exploit Local.program_step_promises; try exact FSTEP. i. des.
      exploit Local.program_step_reserves; try exact FSTEP. i. des.
      econs; eauto; s; try congr.
      apply BoolMap.antisym; try apply BoolMap.bot_spec.
      etrans; eauto. rewrite FPROMISES. refl.
  Qed.

  Lemma map_rtc_step
        reserved freserved
        f1 th1 fth1
        th2
        (MAP_WF1: map_wf f1)
        (MAP_COMPLETE1: map_complete
                          f1
                          (Global.memory (Thread.global th1))
                          (Global.memory (Thread.global fth1)))
        (MAP1: thread_map f1 reserved th1 fth1)
        (LC_WF1: Local.wf (Thread.local th1) (Thread.global th1))
        (GL_WF1: Global.wf (Thread.global th1))
        (FLC_WF1: Local.wf (Thread.local fth1) (Thread.global fth1))
        (FGL_WF1: Global.wf (Thread.global fth1))
        (RESERVED: Memory.closed_timemap reserved (Global.memory (Thread.global th1)))
        (STEPS: rtc (pstep (Thread.step reserved true) (strict_pf /1\ non_sc)) th1 th2):
    exists f2 fth2,
      (<<FSTEPS: rtc (pstep (Thread.step freserved true) (strict_pf /1\ non_sc)) fth1 fth2>>) /\
      (<<MAP_INCR: f1 <3= f2>>) /\
      (<<MAP_WF2: map_wf f2>>) /\
      (<<MAP_COMPLETE2: map_complete
                          f2
                          (Global.memory (Thread.global th2))
                          (Global.memory (Thread.global fth2))>>) /\
      (<<MAP2: thread_map f2 reserved th2 fth2>>).
  Proof.
    revert f1 fth1 MAP_WF1 MAP_COMPLETE1 MAP1 FLC_WF1 FGL_WF1.
    induction STEPS; i.
    { esplits; eauto. }
    inv H. des.
    exploit map_step; eauto; try apply EVENT0. i. des.
    exploit Thread.step_future; try exact STEP; eauto. i. des.
    exploit Thread.step_future; try exact FSTEP; eauto. i. des.
    hexploit Memory.future_closed_timemap; try apply GL_FUTURE; eauto. i.
    exploit IHSTEPS; eauto. i. des.
    esplits; try exact MAP0; eauto.
    econs 2; try exact FSTEPS.
    econs; eauto.
    erewrite <- event_map_strict_pf; eauto.
    erewrite <- event_map_non_sc; eauto.
  Qed.

  Lemma event_map_is_writing
        f e fe
        loc from to val released ord
        (MAP: event_map f e fe)
        (WRITING: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord)):
    exists ffrom fto freleased,
      (<<FWRITING: ThreadEvent.is_writing fe = Some (loc, ffrom, fto, val, freleased, ord)>>) /\
      (<<FROM: f loc from ffrom>>) /\
      (<<TO: f loc to fto>>) /\
      (<<RELEASED: opt_view_map f released freleased>>).
  Proof.
    inv MAP; ss; inv WRITING; esplits; eauto.
  Qed.

  Lemma map_certify
        reserved freserved
        f th fth
        loc ts fts
        (MAP_WF: map_wf f)
        (MAP_COMPLETE: map_complete
                         f
                         (Global.memory (Thread.global th))
                         (Global.memory (Thread.global fth)))
        (MAP: thread_map f reserved th fth)
        (LC_WF: Local.wf (Thread.local th) (Thread.global th))
        (GL_WF: Global.wf (Thread.global th))
        (FLC_WF: Local.wf (Thread.local fth) (Thread.global fth))
        (FGL_WF: Global.wf (Thread.global fth))
        (RESERVED: Memory.closed_timemap reserved (Global.memory (Thread.global th)))
        (TS: f loc ts fts)
        (CERTIFY: certify reserved loc ts th):
    certify freserved loc fts fth.
  Proof.
    inv CERTIFY.
    { exploit map_rtc_step; try exact STEPS; eauto. i. des.
      exploit Thread.rtc_all_step_future; try eapply rtc_implies; try exact STEPS; eauto.
      { i. inv H. econs. econs. eauto. }
      i. des.
      exploit Thread.rtc_all_step_future; try eapply rtc_implies; try exact FSTEPS; eauto.
      { i. inv H. econs. econs. eauto. }
      i. des.
      hexploit Memory.future_closed_timemap; try apply GL_FUTURE; eauto. i.
      destruct pf; try by (inv STEP_FAILURE; inv STEP; ss).
      exploit map_step; try exact STEP_FAILURE; try exact MAP2; eauto.
      { destruct e; ss. }
      i. des.
      econs 1; try exact FSTEP; eauto.
      - erewrite <- event_map_machine_event; eauto.
      - erewrite <- event_map_strict_pf; eauto.
    }
    { exploit map_rtc_step; try exact STEPS; eauto.
      instantiate (1:=freserved). i. des.
      exploit Thread.rtc_all_step_future; try eapply rtc_implies; try exact STEPS; eauto.
      { i. inv H. econs. econs. eauto. }
      i. des.
      exploit Thread.rtc_all_step_future; try eapply rtc_implies; try exact FSTEPS; eauto.
      { i. inv H. econs. econs. eauto. }
      i. des.
      hexploit Memory.future_closed_timemap; try apply GL_FUTURE; eauto. i.
      destruct pf; try by (inv STEP_FULFILL; inv STEP; ss).
      exploit map_step; try exact STEP_FULFILL; try exact MAP2; eauto.
      { destruct e; ss. }
      { destruct e; ss. }
      instantiate (1:=freserved). i. des.
      exploit event_map_is_writing; try exact EVENT; eauto. i. des.
      econs 2; try exact FSTEP; eauto.
      inv MAP_WF0. eapply MAP_LT; try exact TO; eauto.
    }
  Qed.

  Lemma future_reserved_spaced
        loc mem fmem
        (INHABITED: Memory.inhabited mem)
        (FUTURE: Memory.future mem fmem)
        (RESERVED: forall ffrom fto fmsg
                     (GET: Memory.get loc fto mem = None)
                     (FGET: Memory.get loc fto fmem = Some (ffrom, fmsg)),
            Time.lt (Memory.max_ts loc mem) ffrom):
    exists max,
      Time.lt (Memory.max_ts loc mem) max /\
        forall ffrom fto fmsg
          (GET: Memory.get loc fto mem = None)
          (FGET: Memory.get loc fto fmem = Some (ffrom, fmsg)),
          Time.lt max ffrom.
  Proof.
    destruct (TimeFacts.le_lt_dec (Memory.max_ts loc fmem) (Memory.max_ts loc mem)).
    { exists (Time.incr (Memory.max_ts loc mem)).
      split; try apply Time.incr_spec. i.
      exploit RESERVED; eauto. i.
      exploit Memory.get_ts; try exact FGET. i. des; timetac.
      exploit Memory.max_ts_spec; try exact FGET. i. des.
      rewrite x1 in x0. rewrite l in MAX. timetac.
    }
    exploit (Memory.max_ts_spec loc); try apply INHABITED. i. des. clear MAX.
    exploit Memory.future_get1; try exact FUTURE; eauto. i. des.
    exploit Memory.next_exists; try exact x0; try exact l. i. des.
    exploit RESERVED; try exact x1.
    { destruct (Memory.get loc to mem) as [[]|] eqn:X; ss.
      exploit Memory.max_ts_spec; try exact X. i. des. timetac.
    }
    i.
    exists (Time.middle (Memory.max_ts loc mem) from0).
    split; try apply Time.middle_spec; ss. i.
    exploit RESERVED; try exact FGET; eauto. i.
    destruct (TimeFacts.le_lt_dec to fto).
    { inv l0.
      - exploit Memory.lt_get; try exact H; eauto. i.
        eapply TimeFacts.lt_le_lt; try exact x6.
        eapply TimeFacts.lt_le_lt; [apply Time.middle_spec; ss|].
        exploit Memory.get_ts; try exact x1. i. des; timetac.
      - inv H. rewrite x1 in *. inv FGET.
        apply Time.middle_spec; ss.
    }
    exploit (x3 fto); try congr.
    eapply TimeFacts.lt_le_lt; try exact x5.
    exploit Memory.get_ts; try exact FGET. i. des; timetac.
  Qed.

  Lemma future_closed_timemap_map
        (f: map_t) mem fmem tm
        (FUTURE: Memory.future mem fmem)
        (MAP: forall loc from to msg
                (GET: Memory.get loc to mem = Some (from, msg)),
            f loc to to)
        (CLOSED: Memory.closed_timemap tm mem):
    timemap_map f tm tm.
  Proof.
    ii. specialize (CLOSED loc). des. eauto.
  Qed.

  Lemma future_closed_view_map
        (f: map_t) mem fmem view
        (FUTURE: Memory.future mem fmem)
        (MAP: forall loc from to msg
                (GET: Memory.get loc to mem = Some (from, msg)),
            f loc to to)
        (CLOSED: Memory.closed_view view mem):
    view_map f view view.
  Proof.
    inv CLOSED.
    econs; eauto using future_closed_timemap_map.
  Qed.

  Lemma future_closed_opt_view_map
        (f: map_t) mem fmem view
        (FUTURE: Memory.future mem fmem)
        (MAP: forall loc from to msg
                (GET: Memory.get loc to mem = Some (from, msg)),
            f loc to to)
        (CLOSED: Memory.closed_opt_view view mem):
    opt_view_map f view view.
  Proof.
    inv CLOSED; econs.
    eauto using future_closed_view_map.
  Qed.

  Lemma future_closed_message_map
        (f: map_t) mem fmem msg
        (FUTURE: Memory.future mem fmem)
        (MAP: forall loc from to msg
                (GET: Memory.get loc to mem = Some (from, msg)),
            f loc to to)
        (CLOSED: Memory.closed_message msg mem):
    message_map f msg msg.
  Proof.
    inv CLOSED. econs.
    eauto using future_closed_opt_view_map.
  Qed.

  Lemma future_closed_tview_map
        (f: map_t) mem fmem tview
        (FUTURE: Memory.future mem fmem)
        (MAP: forall loc from to msg
                (GET: Memory.get loc to mem = Some (from, msg)),
            f loc to to)
        (CLOSED: TView.closed tview mem):
    tview_map f tview tview.
  Proof.
    inv CLOSED.
    econs; eauto using future_closed_view_map.
  Qed.

  Lemma future_map
        rsv mem fmem
        (CLOSED: Memory.closed mem)
        (FUTURE: Memory.future mem fmem)
        (RESERVED: forall loc ffrom fto fmsg
                     (RESERVED: rsv loc = true)
                     (GET: Memory.get loc fto mem = None)
                     (FGET: Memory.get loc fto fmem = Some (ffrom, fmsg)),
            Time.lt (Memory.max_ts loc mem) ffrom):
    exists f,
      (<<F: f = fun loc ts fts =>
                  ts = fts /\
                  exists from to msg,
                    Memory.get loc to mem = Some (from, msg) /\ (ts = from \/ ts = to)>>) /\
      (<<MAP_WF: map_wf f>>) /\
      (<<MAP_COMPLETE: map_complete f mem fmem>>) /\
      (<<MAP: memory_map f (Memory.max_timemap mem) rsv mem fmem>>).
  Proof.
    exists (fun loc ts fts =>
         ts = fts /\
           exists from to msg,
             Memory.get loc to mem = Some (from, msg) /\ (ts = from \/ ts = to)).
    splits; ss.
    { econs; ii; try by (des; subst; ss).
      splits; ss. esplits; eauto. apply CLOSED.
    }
    { ii. des; subst.
      - exploit Memory.future_get1; try exact FUTURE; eauto. i. des.
        esplits; eauto. left. ss.
      - exploit Memory.future_get1; try exact FUTURE; eauto. i. des.
        esplits; eauto. right. ss.
    }

    ii. destruct (rsv loc) eqn:RSV.
    { (* reserved *)
      exploit (future_reserved_spaced loc); try apply CLOSED; eauto. i. des.
      econs; i.
      - instantiate (1:=max).
        exploit Memory.future_get1; try exact FUTURE; eauto. i. des.
        esplits; try exact x2; eauto.
        + inv CLOSED. exploit CLOSED0; eauto. i. des.
          eapply future_closed_message_map; eauto. i.
          split; ss. esplits; eauto.
        + exploit Memory.max_ts_spec; try exact GET. i. des. timetac.
      - destruct (Memory.get loc fto mem) as [[]|] eqn:GET; eauto.
        right.
        exploit Memory.future_get1; try exact GET; eauto. i. des.
        rewrite x2 in *. inv FGET.
        esplits; try exact GET; eauto.
        + exploit Memory.max_ts_spec; try exact GET. i. des. timetac.
        + inv CLOSED. exploit CLOSED0; eauto. i. des.
          eapply future_closed_message_map; eauto. i.
          split; ss. esplits; eauto.
    }
    { (* non-reserved *)
      clear RESERVED. econs; i.
      - instantiate (1:=Memory.max_ts loc fmem).
        exploit Memory.future_get1; try exact GET; eauto. i. des.
        esplits; try exact x0; eauto.
        + inv CLOSED. exploit CLOSED0; eauto. i. des.
          eapply future_closed_message_map; eauto. i.
          split; ss. esplits; eauto.
        + i. exploit Memory.max_ts_spec; try exact GET. i. des. timetac.
      - exploit Memory.max_ts_spec; try exact FGET. i. des. timetac.
    }
  Qed.

  Lemma future_certify
        freserved
        th fth
        loc
        (STATE: Thread.state th = Thread.state fth)
        (TVIEW: Local.tview (Thread.local th) = Local.tview (Thread.local fth))
        (FPROMISES: Local.promises (Thread.local fth) = BoolMap.bot)
        (GRESERVES: Global.reserves (Thread.global th) = BoolMap.top)
        (FGRESERVES: Global.reserves (Thread.global fth) = BoolMap.bot)
        (MEMORY: Memory.future (Global.memory (Thread.global th)) (Global.memory (Thread.global fth)))
        (MEM_RESERVED: forall loc ffrom fto fmsg
                         (RESERVED: Local.reserves (Thread.local th) loc = true)
                         (GET: Memory.get loc fto (Global.memory (Thread.global th)) = None)
                         (FGET: Memory.get loc fto (Global.memory (Thread.global fth)) = Some (ffrom, fmsg)),
            Time.lt (Memory.max_ts loc (Global.memory (Thread.global th))) ffrom)
        (LC_WF: Local.wf (Thread.local th) (Thread.global th))
        (GL_WF: Global.wf (Thread.global th))
        (FLC_WF: Local.wf (Thread.local fth) (Thread.global fth))
        (FGL_WF: Global.wf (Thread.global fth))
        (CERTIFY: certify (Memory.max_timemap (Global.memory (Thread.global th))) loc
                          (Memory.max_ts loc (Global.memory (Thread.global th))) th):
    certify freserved loc (Memory.max_ts loc (Global.memory (Thread.global th))) fth.
  Proof.
    exploit future_map; try exact MEMORY; try apply GL_WF; eauto. i. des.
    eapply map_certify; eauto.
    - econs; ss.
      econs. rewrite <- TVIEW.
      eapply future_closed_tview_map; try apply LC_WF; eauto.
      i. subst. esplits; eauto.
    - apply Memory.max_timemap_closed. apply GL_WF.
    - exploit (Memory.max_ts_spec loc); try apply GL_WF. i. des.
      subst. esplits; eauto.
  Qed.
End FutureCertify.
