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

Require Import Cover.

Require Import PFConsistent.
Require Import Certify.
Require Import Mapping.

Set Implicit Arguments.


Definition is_cancel (e: ThreadEvent.t): Prop :=
  match e with
  | ThreadEvent.cancel _ _ _ => True
  | _ => False
  end.


Module CurrentCertify.
Section CurrentCertify.
  Variable (lang: language).

  Variant canceled_reserves (dom: list (Loc.t * Time.t)) (rsv rsvc: Memory.t): Prop :=
    | canceled_reserves_intro
        (SOUND: Memory.le rsvc rsv)
        (COMPLETE: forall loc from to msg
                          (GET: Memory.get loc to rsvc = Some (from, msg)),
            List.In (loc, to) dom)
  .

  Variant canceled_local (dom: list (Loc.t * Time.t)) (lc lcc: Local.t): Prop :=
    | canceled_local_intro
        (TVIEW: lcc.(Local.tview) = lc.(Local.tview))
        (PROMISES: lcc.(Local.promises) = lc.(Local.promises))
        (RESERVES: canceled_reserves dom lc.(Local.reserves) lcc.(Local.reserves))
  .

  Variant canceled_memory (rsv rsvc mem memc: Memory.t): Prop :=
    | canceled_memory_intro
        (SOUND: Memory.le memc mem)
        (COMPLETE: Memory.messages_le mem memc)
        (RESERVES: forall loc from to msg
                          (GET: Memory.get loc to rsv = Some (from, msg))
                          (GETC: Memory.get loc to rsvc = None),
            Memory.get loc to memc = None)
  .

  Variant canceled_thread (dom: list (Loc.t * Time.t)) (th thc: Thread.t lang): Prop :=
    | canceled_thread_intro
        (STATE: thc.(Thread.state) = th.(Thread.state))
        (LOCAL: canceled_local dom th.(Thread.local) thc.(Thread.local))
        (SC: th.(Thread.global).(Global.sc) = thc.(Thread.global).(Global.sc))
        (GPROMISES: th.(Thread.global).(Global.promises) = thc.(Thread.global).(Global.promises))
        (MEMORY: canceled_memory th.(Thread.local).(Local.reserves)
                                 thc.(Thread.local).(Local.reserves)
                                 th.(Thread.global).(Global.memory)
                                 thc.(Thread.global).(Global.memory))
  .

  Lemma canceled_thread_refl
        (th: Thread.t lang)
        (LC_WF: Local.wf th.(Thread.local) th.(Thread.global)):
    exists dom,
      canceled_thread dom th th.
  Proof.
    inv LC_WF. inv RESERVES_FINITE.
    exists x. econs; ss.
    { econs; ss. econs; ss. }
    { econs; ss. i. congr. }
  Qed.

  Lemma canceled_thread_step
        loc to dom
        th thc1
        (CANCELED1: canceled_thread ((loc, to)::dom) th thc1)
        (LC_WF: Local.wf thc1.(Thread.local) thc1.(Thread.global)):
    (<<CANCELED2: canceled_thread dom th thc1>>) \/
    exists from thc2,
      (<<CANCEL: Thread.step (ThreadEvent.cancel loc from to) thc1 thc2>>) /\
      (<<CANCELED2: canceled_thread dom th thc2>>).
  Proof.
    destruct th as [st [tview prm rsv] [sc gprm mem]].
    destruct thc1 as [stc1 [tviewc1 prmc1 rsvc1] [scc1 gprmc1 memc1]].
    inv CANCELED1. inv LOCAL. ss. subst.
    destruct (Memory.get loc to rsvc1) as [[from msg]|] eqn:X; cycle 1.
    { left. econs; ss. econs; ss.
      inv RESERVES. econs; ss. i.
      exploit COMPLETE; eauto. i. des; ss.
      inv x0. congr.
    }
    right. inv LC_WF. ss.
    exploit RESERVES_ONLY; eauto. i. subst.
    exploit Memory.remove_exists; try exact X. i. des.
    exploit Memory.remove_exists_le; try exact x0; eauto. i. des.
    hexploit Memory.remove_le; try exact x0. i.
    hexploit Memory.remove_le; try exact x1. i.
    esplits.
    { econs. econs. econs; eauto. }
    { econs; ss.
      { econs; ss.
        inv RESERVES. econs; [etrans; eauto|]. i.
        revert GET. erewrite Memory.remove_o; eauto. condtac; ss. i.
        exploit COMPLETE; eauto. i. des; ss; congr.
      }
      { inv MEMORY. econs; ss.
        { etrans; eauto. }
        { ii. erewrite Memory.remove_o; eauto.
          condtac; ss; eauto. des. subst.
          exploit Memory.remove_get0; try exact x1. i. des.
          exploit SOUND; eauto. i. congr.
        }
        { i. revert GETC.
          erewrite Memory.remove_o; eauto. condtac; ss; i.
          { des. subst.
            exploit Memory.remove_get0; try exact x1. i. des. ss.
          }
          { guardH o.
            exploit RESERVES1; eauto. i.
            erewrite Memory.remove_o; eauto. condtac; ss.
          }
        }
      }
    }
  Qed.

  Lemma canceled_thread_steps
        dom
        th thc1
        (CANCELED1: canceled_thread dom th thc1)
        (LC_WF: Local.wf thc1.(Thread.local) thc1.(Thread.global))
        (GL_WF: Global.wf thc1.(Thread.global)):
    exists thc2,
      (<<CANCEL: rtc (pstep (@Thread.step _) is_cancel) thc1 thc2>>) /\
      (<<CANCELED2: canceled_thread [] th thc2>>).
  Proof.
    revert th thc1 CANCELED1 LC_WF GL_WF.
    induction dom; i; eauto.
    destruct a as [loc to].
    exploit canceled_thread_step; eauto. i. des; eauto.
    exploit Thread.step_future; eauto. i. des.
    exploit IHdom; eauto. i. des.
    esplits; try exact CANCELED0.
    econs 2; eauto. econs; eauto. ss.
  Qed.

  Lemma cancel_reserves
        th
        (LC_WF: Local.wf th.(Thread.local) th.(Thread.global))
        (GL_WF: Global.wf th.(Thread.global)):
    exists thc,
      (<<CANCEL: rtc (pstep (@Thread.step _) is_cancel) th thc>>) /\
      (<<CANCELED: canceled_thread [] th thc>>).
  Proof.
    exploit canceled_thread_refl; eauto. i. des.
    exploit canceled_thread_steps; eauto.
  Qed.

  Lemma canceled_map
        (th thc: Thread.t lang)
        (CANCELED: canceled_thread [] th thc)
        (LC_WF: Local.wf th.(Thread.local) th.(Thread.global))
        (GL_WF: Global.wf th.(Thread.global)):
    exists f,
      (<<F: f = fun loc ts fts =>
                  ts = fts /\
                  exists from to msg,
                    Memory.get loc to th.(Thread.global).(Global.memory) = Some (from, msg) /\
                    __guard__ (ts = from \/ ts = to)>>) /\
      (<<MAP_WF: map_wf f>>) /\
      (<<MAP: thread_map_racy_promise f (Thread.cap_of th) thc>>).
  Proof.
    destruct th as [st [tview prm rsv] [sc gprm mem]].
    destruct thc as [stc [tviewc prmc rsvc] [scc gprmc memc]].
    inv CANCELED. inv LOCAL. ss. subst.
    esplits; try refl.
    { (* map_wf *)
      econs; ii; subst.
      { esplits; ss; try apply GL_WF. left. ss. }
      { exists (List.concat
                  (List.map (fun e => [fst e; fst (snd e)]) (DOMap.elements (Cell.raw (mem loc))))).
        i. des. subst.
        exploit DOMap.elements_correct; eauto. i.
        remember (DOMap.elements (Cell.raw (mem loc))) as l.
        clear - l x0 MAP1.
        revert fts from to msg MAP1 x0.
        induction l; ss; i. des; eauto.
        subst. ss. unguard. des; auto.
      }
      { des. subst. ss. }
      { des. subst. ss. }
      { des. subst. ss. }
      { des. subst. ss. }
    }

    (* thread_map *)
    econs; ss.
    { (* local_map *)
      econs. eapply closed_tview_map; try apply LC_WF. s. i.
      esplits; eauto. right. ss.
    }
    { (* global_map *)
      specialize (@Memory.cap_of_cap mem). intro CAP.
      hexploit Memory.cap_le; eauto. intro LE.
      inv RESERVES. inv MEMORY.
      econs. econs; ss; i.
      { destruct msg; auto. right.
        exploit Memory.cap_inv; eauto. i. des; ss.
        exploit COMPLETE0; eauto. i.
        esplits; unguard; eauto.
        inv GL_WF. inv MEM_CLOSED.
        exploit CLOSED; eauto. s. i. des. inv MSG_CLOSED.
        econs. eapply closed_opt_view_map; eauto. i.
        esplits; eauto.
      }
      { exploit SOUND0; eauto. i.
        esplits; eauto; (try refl); unguard; auto; i.
        { inv CAP. exploit SOUND1; eauto. i.
          econs; eauto.
        }
        { inv LC_WF. ss.
          exploit RESERVES0; eauto. i.
          exploit Memory.get_disjoint; [exact x1|exact x0|]. i. des; ss. subst.
          exploit RESERVES; eauto; try congr.
          destruct (Memory.get loc fto rsvc) as [[]|] eqn:X; ss.
          exploit COMPLETE; eauto. ss.
        }
      }
    }
  Qed.

  Lemma canceled_certify_racy_promise
        th thc loc
        (CANCELED: canceled_thread [] th thc)
        (LC_WF: Local.wf th.(Thread.local) th.(Thread.global))
        (GL_WF: Global.wf th.(Thread.global))
        (LC_WF_C: Local.wf thc.(Thread.local) thc.(Thread.global))
        (GL_WF_C: Global.wf thc.(Thread.global))
        (CERTIFY: certify_racy_promise loc (Thread.cap_of th)):
    @pf_certify_racy_promise lang loc thc.
  Proof.
    exploit Local.cap_wf; try exact CAP; try exact LC_WF. intro LC_WF_CAP.
    exploit Global.cap_wf; try exact GL_WF. intro GL_WF_CAP.
    exploit canceled_map; eauto. i. des.
    eapply map_certify_racy_promise; try exact CERTIFY; eauto.
  Qed.

  Lemma current_certify_racy_promise
        th loc
        (LC_WF: Local.wf th.(Thread.local) th.(Thread.global))
        (GL_WF: Global.wf th.(Thread.global))
        (CERTIFY: certify_racy_promise loc (Thread.cap_of th)):
    @certify_racy_promise lang loc th.
  Proof.
    exploit cancel_reserves; eauto. i. des.
    exploit Thread.rtc_all_step_future;
      try eapply rtc_implies; try exact CANCEL; eauto.
    { i. inv H. econs. eauto. }
    i. des.
    exploit canceled_certify_racy_promise; eauto. i.
    inv x0.
    - econs 1; try exact STEP_FAILURE; eauto.
      etrans.
      + eapply rtc_implies; try exact CANCEL.
        i. inv H. econs; eauto. destruct e0; ss. auto.
      + eapply rtc_implies; try exact STEPS.
        i. inv H. des. econs; eauto. split; ss.
        destruct e0; ss.
    - econs 2; try exact STEP_FULFILL; eauto.
      etrans.
      + eapply rtc_implies; try exact CANCEL.
        i. inv H. econs; eauto. destruct e; ss. auto.
      + eapply rtc_implies; try exact STEPS.
        i. inv H. des. econs; eauto. split; ss.
        destruct e; ss.
  Qed.

  Lemma promise_step_sim_thread
        th1 th2 loc
        (STEP: @Thread.step lang (ThreadEvent.promise loc) th1 th2):
    PFConsistent.sim_thread th1 th2.
  Proof.
    exploit Thread.step_promises_minus; eauto. i.
    inv STEP; inv LOCAL. inv LOCAL0. inv PROMISE; ss.
    econs; ss; try apply PFConsistent.sim_memory_PreOrder.
    eapply BoolMap.add_le; eauto.
  Qed.

  Lemma rtc_step_consistent_ceritfy_racy_promise
        th0 th1 th2 loc
        (LC_WF: Local.wf th0.(Thread.local) th0.(Thread.global))
        (GL_WF: Global.wf th0.(Thread.global))
        (STEP: Thread.step (ThreadEvent.promise loc) th0 th1)
        (STEPS: rtc (@Thread.all_step lang) th1 th2)
        (CONSISTENT: Thread.consistent th2):
    certify_racy_promise loc th0.
  Proof.
    cut (certify_racy_promise loc th1).
    { exploit promise_step_sim_thread; eauto. i. inv H.
      { exploit PFConsistent.sim_thread_rtc_non_sc_step;
          try eapply rtc_implies; try exact STEPS0; eauto.
        { i. inv H. des. econs; eauto. }
        i. des.
        exploit Thread.rtc_all_step_future;
          try eapply rtc_implies; try exact STEPS_SRC; eauto.
        { i. inv H. econs; eauto. }
        i. des.
        exploit PFConsistent.sim_thread_step; try exact STEP_FAILURE; eauto. i. des.
        unguard. des; subst; try by (destruct e; ss).
        inv STEP_SRC; ss.
        econs 1; eauto.
      }
      { exploit PFConsistent.sim_thread_rtc_non_sc_step;
          try eapply rtc_implies; try exact STEPS0; eauto.
        { i. inv H. des. econs; eauto. }
        i. des.
        exploit Thread.rtc_all_step_future;
          try eapply rtc_implies; try exact STEPS_SRC; eauto.
        { i. inv H. econs; eauto. }
        i. des.
        exploit PFConsistent.sim_thread_step; try exact STEP_FAILURE; eauto. i. des.
        unguard. des; subst; ss.
        inv STEP_SRC; ss.
        econs 2; eauto.
        eapply TimeFacts.le_lt_lt; eauto.
        eapply Memory.le_max_ts; try apply GL_WF2. apply SIM2.
      }
    }

    assert (PROMISED: th1.(Thread.local).(Local.promises) loc = true).
    { inv STEP; inv LOCAL. inv LOCAL0. inv PROMISE.
      exploit BoolMap.add_get0; try exact ADD. i. des. ss.
    }
    exploit Thread.step_future; eauto. i. des.
    clear th0 LC_WF GL_WF STEP TVIEW_FUTURE GL_FUTURE.
    exploit PFConsistent.rtc_all_step_rtc_non_sc_step; eauto. i. des; cycle 1.
    { (* failure during rtc step *)
      exploit PFConsistent.sim_thread_rtc_non_sc_step; try exact STEPS1; eauto.
      { apply PFConsistent.sim_thread_PreOrder. }
      i. des.
      exploit Thread.rtc_all_step_future;
        try eapply rtc_implies; try exact STEPS_SRC; eauto.
      { i. inv H. econs. eauto. }
      i. des.
      exploit PFConsistent.sim_thread_step; try exact STEP_FAILURE; eauto. i. des.
      unguard. des; subst; cycle 1.
      { destruct e; ss. }
      inv STEP_SRC; ss.
      econs 1; try exact STEP; eauto.
    }
    { (* sc during rtc step *)
      exploit PFConsistent.sim_thread_rtc_non_sc_step; try exact STEPS1; eauto.
      { apply PFConsistent.sim_thread_PreOrder. }
      i. des.
      exploit rtc_pf_step_certify_racy_promise; try exact STEPS_SRC; eauto.
      destruct (th2_src.(Thread.local).(Local.promises) loc) eqn:GETP; ss.
      inv SIM2. exploit PROMISES0; eauto.
      rewrite PROMISES. ss.
    }
    subst.
    destruct (th2.(Thread.local).(Local.promises) loc) eqn:PROMISED2; cycle 1.
    { (* fulfilled during rtc step *)
      exploit PFConsistent.sim_thread_rtc_non_sc_step; try exact STEPS1; eauto.
      { apply PFConsistent.sim_thread_PreOrder. }
      i. des.
      exploit rtc_pf_step_certify_racy_promise; try exact STEPS_SRC; eauto.
      destruct (th2_src.(Thread.local).(Local.promises) loc) eqn:GETP; ss.
      inv SIM2. exploit PROMISES; eauto.
    }
    (* fulfilled during certification *)
    exploit Thread.rtc_all_step_future; try exact STEPS; eauto. i. des.
    exploit PFConsistent.consistent_pf_consistent; eauto. i.
    exploit pf_consistent_certify_racy_promise; eauto. i.
    exploit current_certify_racy_promise; try exact x1; eauto. i.
    move STEPS1 at bottom. inv x2.
    { exploit PFConsistent.sim_thread_rtc_non_sc_step;
        try exact LC_WF2; try exact GL_WF2; try apply PFConsistent.sim_thread_PreOrder.
      { etrans; [exact STEPS1|].
        eapply rtc_implies; try exact STEPS0.
        i. inv H. des. econs; eauto.
      }
      i. des.
      exploit Thread.rtc_all_step_future;
        try eapply rtc_implies; try exact STEPS_SRC; ss.
      { i. inv H. econs. eauto. }
      i. des.
      exploit PFConsistent.sim_thread_step; try exact SIM2; eauto. i. des.
      unguard. des; subst; try by (destruct e; ss).
      inv STEP_SRC; ss.
      econs 1; eauto.
    }
    { exploit PFConsistent.sim_thread_rtc_non_sc_step;
        try exact LC_WF2; try exact GL_WF2; try apply PFConsistent.sim_thread_PreOrder.
      { etrans; [exact STEPS1|].
        eapply rtc_implies; try exact STEPS0.
        i. inv H. des. econs; eauto.
      }
      i. des.
      exploit Thread.rtc_all_step_future;
        try eapply rtc_implies; try exact STEPS_SRC; ss.
      { i. inv H. econs. eauto. }
      i. des.
      exploit PFConsistent.sim_thread_step; try exact SIM2; eauto. i. des.
      unguard. des; subst; ss.
      inv STEP_SRC; ss.
      econs 2; eauto.
      eapply TimeFacts.le_lt_lt; eauto.
      inv SIM2. inv MEMORY.
      eapply Memory.le_max_ts; try apply GL_WF1. apply SOUND.
    }
  Qed.
End CurrentCertify.
End CurrentCertify.
