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
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Global.
Require Import Local.
Require Import Thread.

Require Import Mapping.
Require Import PFConsistent.
Require Import PFtoIRThread.

Set Implicit Arguments.


Module FutureCertify.
Section FutureCertify.
  Variable lang: language.
  
  Variant certify (loc: Loc.t) (th: Thread.t lang): Prop :=
    | certify_failure
        e th1 th2
        (STEPS: rtc (pstep (@Thread.step _) (strict_pf /1\ non_sc)) th th1)
        (STEP_FAILURE: Thread.step e th1 th2)
        (EVENT_FAILURE: ThreadEvent.get_machine_event e = MachineEvent.failure)
        (EVENT_PF: strict_pf e)
    | certify_fulfill
        e th1 th2
        from to val released ord
        (STEPS: rtc (pstep (@Thread.step _) (strict_pf /1\ non_sc)) th th1)
        (STEP_FULFILL: Thread.step e th1 th2)
        (EVENT_FULFILL: e = ThreadEvent.write loc from to val released ord)
        (TO: Time.lt (Memory.max_ts loc (Global.memory (Thread.global th1))) to)
        (ORD: Ordering.le ord Ordering.na)
  .

  Variant pf_certify (loc: Loc.t) (th: Thread.t lang): Prop :=
    | pf_certify_failure
        e th1 th2
        (STEPS: rtc (pstep (@Thread.step _) (fully_pf /1\ non_sc)) th th1)
        (STEP_FAILURE: Thread.step e th1 th2)
        (EVENT_FAILURE: ThreadEvent.get_machine_event e = MachineEvent.failure)
        (EVENT_PF: ~ ThreadEvent.is_racy_promise e)
    | pf_certify_fulfill
        e th1 th2
        from to val released ord
        (STEPS: rtc (pstep (@Thread.step _) (fully_pf /1\ non_sc)) th th1)
        (STEP_FULFILL: Thread.step e th1 th2)
        (EVENT_FULFILL: e = ThreadEvent.write loc from to val released ord)
        (TO: Time.lt (Memory.max_ts loc (Global.memory (Thread.global th1))) to)
        (ORD: Ordering.le ord Ordering.na)
  .

  Lemma spf_consistent_certify
        th loc
        (LC_WF: Local.wf (Thread.local th) (Thread.global th))
        (GL_WF: Global.wf (Thread.global th))
        (CONS: PFConsistent.spf_consistent th)
        (PROMISED: Local.promises (Thread.local th) loc = true):
    certify loc (Thread.cap_of th).
  Proof.
    inv CONS.
    { econs 1; eauto. }
    exploit Thread.cap_wf; eauto. clear LC_WF GL_WF. i. des.
    remember (Thread.cap_of th) as th0.
    replace (Local.promises (Thread.local th) loc) with
      (Local.promises (Thread.local th0) loc) in * by (subst; ss).
    clear th Heqth0. revert PROMISED.
    induction STEPS; i.
    { rewrite PROMISES in *. ss. }
    destruct (Local.promises (Thread.local y) loc) eqn:PROMISEDY.
    { dup H. inv H0.
      exploit Thread.step_future; try exact STEP; eauto. i. des.
      exploit IHSTEPS; eauto. i. inv x1.
      - econs 1; try exact STEP_FAILURE; eauto.
      - econs 2; try exact STEP_FULFILL; eauto.
    }

    move PROMISEDY at bottom.
    inv H. inv STEP; inv LOCAL; ss; (try congr); (try by inv LOCAL0; ss; congr).
    { (* promise *)
      inv LOCAL0. inv PROMISE. ss.
      revert PROMISEDY. erewrite BoolMap.add_o; eauto.
      condtac; ss. congr.
    }
    { (* write *)
      assert (loc0 = loc /\ Ordering.le ord Ordering.na).
      { inv LOCAL0. inv FULFILL; ss; try congr. split; ss.
        revert PROMISEDY. erewrite BoolMap.remove_o; eauto.
        condtac; ss. congr.
      }
      des. subst.
      exploit Local.write_max_exists; eauto. i. des.
      econs 2; [refl|..].
      - econs 2; [|econs 3]; try exact WRITE. eauto.
      - ss.
      - inv WRITE. ss.
        exploit Memory.add_ts; try exact WRITE0. i.
        etrans; eauto.
      - ss.
    }
    { (* update *)
      assert (Ordering.le ordw Ordering.na).
      { inv LOCAL1. inv LOCAL2.  inv FULFILL; ss; try congr. }
      econs 1; [refl|..].
      - econs 2; [|econs 10]; eauto.
      - ss.
      - split; ss. ii. des. destruct ordw; ss.
    }
  Qed.

  Variant thread_map (f: map_t) (th fth: Thread.t lang): Prop :=
    | thread_map_intro
        (STATE: Thread.state th = Thread.state fth)
        (LOCAL: local_map f (Thread.local th) (Thread.local fth))
        (GLOBAL: global_map f (Local.reserves (Thread.local th))
                            (Thread.global th) (Thread.global fth))
        (FPROMISES: Local.promises (Thread.local fth) = BoolMap.bot)
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

  Lemma event_map_is_program
        f e fe
        (MAP: event_map f e fe):
    ThreadEvent.is_program e <-> ThreadEvent.is_program fe.
  Proof.
    inv MAP; ss.
  Qed.

  Lemma event_map_is_racy_promise
        f e fe
        (MAP: event_map f e fe):
    ThreadEvent.is_racy_promise e <-> ThreadEvent.is_racy_promise fe.
  Proof.
    inv MAP; ss; destruct to, fto; ss.
  Qed.

  Lemma event_map_strict_pf
        f e fe
        (MAP: event_map f e fe):
    strict_pf e <-> strict_pf fe.
  Proof.
    inv MAP; ss; destruct to, fto; ss.
  Qed.

  Lemma event_map_non_sc
        f e fe
        (MAP: event_map f e fe):
    non_sc e <-> non_sc fe.
  Proof.
    inv MAP; ss.
  Qed.

  Lemma map_step
        f1 th1 fth1
        e th2
        (MAP_WF1: map_wf f1)
        (MAP_COMPLETE1: map_complete
                          f1
                          (Global.memory (Thread.global th1))
                          (Global.memory (Thread.global fth1)))
        (MAP1: thread_map f1 th1 fth1)
        (LC_WF1: Local.wf (Thread.local th1) (Thread.global th1))
        (GL_WF1: Global.wf (Thread.global th1))
        (FLC_WF1: Local.wf (Thread.local fth1) (Thread.global fth1))
        (FGL_WF1: Global.wf (Thread.global fth1))
        (STEP: Thread.step e th1 th2)
        (EVENT1: ~ ThreadEvent.is_racy_promise e)
        (EVENT2: ~ ThreadEvent.is_sc e):
    exists f2 fe fth2,
      (<<FSTEP: Thread.opt_step fe fth1 fth2>>) /\
      (<<EVENT: __guard__ (ThreadEvent.is_internal e /\ fe = ThreadEvent.silent \/
                           ThreadEvent.is_program e /\ event_map f2 e fe)>>) /\
      (<<MAP_INCR: f1 <3= f2>>) /\
      (<<MAP_WF2: map_wf f2>>) /\
      (<<MAP_COMPLETE2: map_complete
                          f2
                          (Global.memory (Thread.global th2))
                          (Global.memory (Thread.global fth2))>>) /\
      (<<MAP2: thread_map f2 th2 fth2>>).
  Proof.
    destruct th1, fth1. inv MAP1. ss. subst.
    inv STEP.
    - exploit map_internal_step; try exact LOCAL; try exact GLOBAL; eauto. i. des.
      esplits; eauto.
      + left. split; ss. inv LOCAL0; ss.
      + ss.
    - exploit map_program_step; try exact LOCAL; try exact GLOBAL; eauto. i. des.
      esplits.
      + econs 2. econs 2; [|eauto].
        erewrite <- event_map_program_event; eauto.
      + right. split; eauto. inv LOCAL0; ss.
      + ss.
      + ss.
      + ss.
      + econs; ss.
        exploit Local.program_step_promises; try exact FSTEP. i. des.
        apply BoolMap.antisym; try apply BoolMap.bot_spec.
        etrans; eauto. rewrite FPROMISES. refl.
  Qed.

  Lemma map_rtc_step
        f1 th1 fth1
        th2
        (MAP_WF1: map_wf f1)
        (MAP_COMPLETE1: map_complete
                          f1
                          (Global.memory (Thread.global th1))
                          (Global.memory (Thread.global fth1)))
        (MAP1: thread_map f1 th1 fth1)
        (LC_WF1: Local.wf (Thread.local th1) (Thread.global th1))
        (GL_WF1: Global.wf (Thread.global th1))
        (FLC_WF1: Local.wf (Thread.local fth1) (Thread.global fth1))
        (FGL_WF1: Global.wf (Thread.global fth1))
        (STEPS: rtc (pstep (@Thread.step _) (strict_pf /1\ non_sc)) th1 th2):
    exists f2 fth2,
      (<<FSTEPS: rtc (pstep (@Thread.step _) (fully_pf /1\ non_sc)) fth1 fth2>>) /\
      (<<MAP_INCR: f1 <3= f2>>) /\
      (<<MAP_WF2: map_wf f2>>) /\
      (<<MAP_COMPLETE2: map_complete
                          f2
                          (Global.memory (Thread.global th2))
                          (Global.memory (Thread.global fth2))>>) /\
      (<<MAP2: thread_map f2 th2 fth2>>).
  Proof.
    revert f1 fth1 MAP_WF1 MAP_COMPLETE1 MAP1 FLC_WF1 FGL_WF1.
    induction STEPS; i.
    { esplits; eauto. }
    inv H. des.
    exploit map_step; eauto; try apply EVENT; try apply EVENT0. i. des.
    exploit Thread.step_future; try exact STEP; eauto. i. des.
    exploit Thread.opt_step_future; try exact FSTEP; eauto. i. des.
    exploit IHSTEPS; eauto. i. des.
    esplits; try exact MAP0; eauto.
    inv FSTEP; eauto.
    econs 2; try exact FSTEPS. econs; eauto.
    inv EVENT1; des.
    - subst. repeat (split; ss).
    - split.
      + split.
        * erewrite <- event_map_is_program; eauto.
        * erewrite <- event_map_is_racy_promise; eauto. apply EVENT.
      + erewrite <- event_map_non_sc; eauto.
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
        f th fth loc
        (MAP_WF: map_wf f)
        (MAP_COMPLETE: map_complete
                         f
                         (Global.memory (Thread.global th))
                         (Global.memory (Thread.global fth)))
        (MAP: thread_map f th fth)
        (LC_WF: Local.wf (Thread.local th) (Thread.global th))
        (GL_WF: Global.wf (Thread.global th))
        (FLC_WF: Local.wf (Thread.local fth) (Thread.global fth))
        (FGL_WF: Global.wf (Thread.global fth))
        (CERTIFY: certify loc th):
    pf_certify loc fth.
  Proof.
    inv CERTIFY.
    { exploit map_rtc_step; try exact STEPS; eauto. i. des.
      exploit Thread.rtc_all_step_future; try eapply rtc_implies; try exact STEPS; eauto.
      { i. inv H. econs. eauto. }
      i. des.
      exploit Thread.rtc_all_step_future; try eapply rtc_implies; try exact FSTEPS; eauto.
      { i. inv H. econs. eauto. }
      i. des.
      exploit map_step; try exact STEP_FAILURE; try exact MAP2; eauto.
      { apply EVENT_PF. }
      { destruct e; ss. }
      i. des.
      unguardH EVENT. des.
      { subst. destruct e; ss. }
      inv FSTEP; try by (inv EVENT0; ss).
      econs 1; try exact STEP; eauto.
      - erewrite <- event_map_machine_event; eauto.
      - erewrite <- event_map_is_racy_promise; eauto. apply EVENT_PF.
    }
    { exploit map_rtc_step; try exact STEPS; eauto. i. des.
      destruct th1, fth2. inv MAP2. ss. subst.
      inv STEP_FULFILL; try by (inv LOCAL0; ss).
      exploit Thread.rtc_all_step_future; try eapply rtc_implies; try exact FSTEPS; eauto.
      { i. inv H. econs. eauto. }
      s. i. des.
      exploit Local.write_max_exists; try exact LC_WF2; try by econs 2. s. i. des.
      econs 2; try exact FSTEPS.
      - econs 2; [|econs 3; eauto]. eauto.
      - ss.
      - inv WRITE. ss.
        exploit Memory.add_ts; try exact WRITE0. i.
        etrans; eauto.
      - ss.
    }
  Qed.

  Lemma closed_timemap_map
        (f: map_t) mem tm
        (MAP: forall loc from to val released na
                (GET: Memory.get loc to mem = Some (from, Message.message val released na)),
            f loc to to)
        (CLOSED: Memory.closed_timemap tm mem):
    timemap_map f tm tm.
  Proof.
    ii. specialize (CLOSED loc). des. eauto.
  Qed.

  Lemma closed_view_map
        (f: map_t) mem view
        (MAP: forall loc from to val released na
                (GET: Memory.get loc to mem = Some (from, Message.message val released na)),
            f loc to to)
        (CLOSED: Memory.closed_view view mem):
    view_map f view view.
  Proof.
    inv CLOSED.
    econs; eauto using closed_timemap_map.
  Qed.

  Lemma closed_opt_view_map
        (f: map_t) mem view
        (MAP: forall loc from to val released na
                (GET: Memory.get loc to mem = Some (from, Message.message val released na)),
            f loc to to)
        (CLOSED: Memory.closed_opt_view view mem):
    opt_view_map f view view.
  Proof.
    inv CLOSED; econs.
    eauto using closed_view_map.
  Qed.

  Lemma closed_message_map
        (f: map_t) mem msg
        (MAP: forall loc from to val released na
                (GET: Memory.get loc to mem = Some (from, Message.message val released na)),
            f loc to to)
        (CLOSED: Memory.closed_message msg mem):
    message_map f msg msg.
  Proof.
    inv CLOSED; econs.
    eauto using closed_opt_view_map.
  Qed.

  Lemma closed_tview_map
        (f: map_t) mem tview
        (MAP: forall loc from to val released na
                (GET: Memory.get loc to mem = Some (from, Message.message val released na)),
            f loc to to)
        (CLOSED: TView.closed tview mem):
    tview_map f tview tview.
  Proof.
    inv CLOSED.
    econs; eauto using closed_view_map.
  Qed.

  Lemma future_map
        rsv mem mem_future fmem
        mem_cap
        (LE: Memory.le rsv mem)
        (CLOSED: Memory.closed mem)
        (FUTURE: Memory.future mem mem_future)
        (FUTURE_LE: Memory.le rsv mem_future)
        (SIM: PFtoIRThread.sim_memory fmem mem_future)
        (CAP: Memory.cap mem mem_cap):
    exists f,
      (<<F: f = fun loc ts fts =>
                  (ts = fts /\
                   exists from to val released na,
                     Memory.get loc to mem = Some (from, Message.message val released na) /\
                     __guard__ (ts = from \/ ts = to)) \/
                  ts = Time.incr (Memory.max_ts loc mem) /\
                  fts = Memory.max_ts loc fmem /\
                  Memory.get loc fts mem = None /\
                  exists from msg,
                    Memory.get loc fts fmem = Some (from, msg)>>) /\
      (<<MAP_WF: map_wf f>>) /\
      (<<MAP_COMPLETE: map_complete f mem_cap fmem>>) /\
      (<<MAP: memory_map f rsv mem_cap fmem>>).
  Proof.
    (* exists (fun loc ts fts => *)
    (*      (ts = fts /\ *)
    (*       exists from to msg, *)
    (*         Memory.get loc to mem = Some (from, msg) /\ (ts = from \/ ts = to)) \/ *)
    (*      ts = Time.incr (Memory.max_ts loc mem) /\ *)
    (*      fts = Memory.max_ts loc fmem /\ *)
    (*      Memory.get loc fts mem = None /\ *)
    (*      exists from msg, *)
    (*        Memory.get loc fts fmem = Some (from, msg) *)
    (*   ). *)
    esplits; [refl|..].
    { (* map_wf *)
      econs; ii; subst.
      { left. splits; ss.
        esplits; try eapply CLOSED; ss. unguard. auto.
      }
      { des; subst; ss.
        - exfalso.
          exploit Memory.max_ts_spec; try exact MAP0. i. des.
          unguardH MAP3. des; subst.
          + exploit Memory.get_ts; try exact MAP0. i. des.
            { exploit Time.incr_spec. rewrite x0. i. timetac. }
            exploit TimeFacts.lt_le_lt; try exact x0; try exact MAX. i.
            eapply Time.lt_strorder. etrans; try exact x1.
            apply Time.incr_spec.
          + eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; try exact MAX.
            apply Time.incr_spec.
        - exfalso.
          exploit Memory.max_ts_spec; try exact MAP5. i. des.
          unguardH MAP6. des; subst.
          + exploit Memory.get_ts; try exact MAP5. i. des.
            { exploit Time.incr_spec. rewrite x0. i. timetac. }
            exploit TimeFacts.lt_le_lt; try exact x0; try exact MAX. i.
            eapply Time.lt_strorder. etrans; try exact x1.
            apply Time.incr_spec.
          + eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; try exact MAX.
            apply Time.incr_spec.
      }
      { des; subst; ss.
        - unguardH MAP3. des; subst; try congr.
          exploit Memory.future_get1; try exact MAP0; eauto. i. des.
          inv SIM. exploit COMPLETE; eauto. i.
          exploit Memory.max_ts_spec; try exact x1. i. des.
          exploit Memory.get_ts; try exact x1. i. des; timetac.
          rewrite x2 in *.
          inv CLOSED. rewrite INHABITED in *. ss.
        - unguardH MAP6. des; subst; try congr.
          exploit Memory.future_get1; try exact MAP5; eauto. i. des.
          inv SIM. exploit COMPLETE; eauto. i.
          exploit Memory.max_ts_spec; try exact x1. i. des.
          exploit Memory.get_ts; try exact x1. i. des; timetac.
          rewrite x2 in *.
          inv CLOSED. rewrite INHABITED in *. ss.
      }
      { des; subst; ss; timetac.
        - unguardH MAP3. des; subst.
          + exploit Memory.max_ts_spec; try exact MAP0. i. des.
            exploit TimeFacts.le_lt_lt; try exact MAX; try apply Time.incr_spec. i.
            rewrite LT in x0.
            exploit Memory.get_ts; try exact MAP0. i. des; timetac.
          + exploit Memory.max_ts_spec; try exact MAP0. i. des.
            exploit TimeFacts.le_lt_lt; try exact MAX; try apply Time.incr_spec. i.
            timetac.
        - unguardH MAP6. des; subst.
          + exploit Memory.future_get1; try exact MAP5; eauto. i. des.
            inv SIM. exploit COMPLETE; eauto. i.
            exploit Memory.max_ts_spec; try exact x1. i. des.
            inv MAX; try congr.
            eapply TimeFacts.le_lt_lt; try exact H.
            exploit Memory.get_ts; try exact MAP5. i. des; timetac.
          + exploit Memory.future_get1; try exact MAP5; eauto. i. des.
            inv SIM. exploit COMPLETE; eauto. i.
            exploit Memory.max_ts_spec; try exact x1. i. des.
            inv MAX; try congr.
      }
      { des; subst; ss; timetac.
        - unguardH MAP3. des; subst.
          + exploit Memory.future_get1; try exact MAP0; eauto. i. des.
            inv SIM. exploit COMPLETE; eauto. i.
            exploit Memory.max_ts_spec; try exact x1. i. des.
            exploit TimeFacts.le_lt_lt; try exact LT; try exact MAX. i.
            exploit Memory.get_ts; try exact MAP0. i. des; timetac.
          + exploit Memory.future_get1; try exact MAP0; eauto. i. des.
            inv SIM. exploit COMPLETE; eauto. i.
            exploit Memory.max_ts_spec; try exact x1. i. des.
            timetac.
        - unguardH MAP6. des; subst.
          + exploit Memory.max_ts_spec; try exact MAP5. i. des.
            eapply TimeFacts.le_lt_lt; try apply Time.incr_spec.
            etrans; eauto.
            exploit Memory.get_ts; try exact MAP5. i. des; timetac.
          + exploit Memory.max_ts_spec; try exact MAP5. i. des.
            eapply TimeFacts.le_lt_lt; try apply Time.incr_spec. ss.
      }
    }

    { (* map_complete *)
      ii. unguard. des; subst.
      - inv CAP. exploit SOUND; eauto. i.
        exploit Memory.future_get1; try exact MAP0; eauto. i. des.
        inv SIM. exploit COMPLETE0; eauto. i.
        esplits; eauto.
      - inv CAP. exploit SOUND; eauto. i.
        exploit Memory.future_get1; try exact MAP0; eauto. i. des.
        inv SIM. exploit COMPLETE0; eauto. i.
        esplits; eauto.
      - exploit Memory.max_ts_spec; try eapply CLOSED. i. des.
        inv CAP. exploit (BACK loc); try exact GET. i.
        esplits; try exact x0; try exact MAP2. auto.
    }

    { (* memory_map *)
      econs; i.
      - destruct msg; auto. right.
        exploit Memory.cap_inv; try exact GET; eauto. i. des; ss.
        exploit Memory.future_get1; try exact x0; eauto. i. des.
        inv SIM. exploit COMPLETE; eauto. i.
        esplits; try exact x2.
        + left. esplits; eauto. left. ss.
        + left. esplits; eauto. right. ss.
        + inv CLOSED. exploit CLOSED0; eauto. i. des.
          eapply closed_message_map; eauto. i.
          left. esplits; eauto. right. ss.
      - destruct fmsg; cycle 1.
        { inv SIM. exploit GRESERVES; eauto. ss. }
        inv SIM. exploit SOUND; eauto. i.
        (* TODO: fix memory mapping *)
        admit.
    }
  Admitted.

  Lemma future_certify
        fth
        th loc mem_future
        (STATE: Thread.state th = Thread.state fth)
        (TVIEW: Local.tview (Thread.local th) = Local.tview (Thread.local fth))
        (FPROMISES: Local.promises (Thread.local fth) = BoolMap.bot)
        (FUTURE: Memory.future (Global.memory (Thread.global th)) mem_future)
        (SIM: PFtoIRThread.sim_memory (Global.memory (Thread.global fth)) mem_future)
        (LC_WF: Local.wf (Thread.local th) (Thread.global th))
        (GL_WF: Global.wf (Thread.global th))
        (LE_FUTURE: Memory.le (Local.reserves (Thread.local th)) mem_future)
        (FLC_WF: Local.wf (Thread.local fth) (Thread.global fth))
        (FGL_WF: Global.wf (Thread.global fth))
        (CERTIFY: certify loc (Thread.cap_of th)):
    pf_certify loc fth.
  Proof.
    exploit Thread.cap_wf; try exact LC_WF; eauto. i. des.
    exploit future_map; try exact FUTURE; try exact SIM;
      try apply LC_WF; try apply GL_WF; ss.
    { apply Memory.cap_of_cap. }
    i. des.
    eapply map_certify; try exact CERTIFY; eauto.
    econs; ss.
    econs. rewrite <- TVIEW.
    eapply closed_tview_map; try apply LC_WF; eauto.
    i. subst. left. esplits; eauto. right. ss.
  Qed.
End FutureCertify.
End FutureCertify.
