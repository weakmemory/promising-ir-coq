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
Require Import Thread.

Set Implicit Arguments.


Module PFCertify.
  Section PFCertify.
    Variable lang: language.

    Variant pf_certify (loc: Loc.t) (th: Thread.t lang): Prop :=
      | pf_certify_failure
          pf e th1 th2
          (STEPS: rtc (tau (Thread.step (Memory.max_timemap (Global.memory (Thread.global th))) true))
                      (Thread.fully_reserved th) th1)
          (STEP_FAILURE: Thread.step (Memory.max_timemap (Global.memory (Thread.global th))) pf e th1 th2)
          (EVENT_FAILURE: ThreadEvent.get_machine_event e = MachineEvent.failure)
      | pf_certify_fulfill
          pf e th1 th2
          from to val released ord
          (STEPS: rtc (tau (Thread.step (Memory.max_timemap (Global.memory (Thread.global th))) true))
                      (Thread.fully_reserved th) th1)
          (STEP_FULFILL: Thread.step (Memory.max_timemap (Global.memory (Thread.global th))) pf e th1 th2)
          (EVENT_FULFILL: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord))
          (TO: Time.lt (Memory.max_ts loc (Global.memory (Thread.global th1))) to)
          (ORD: Ordering.le ord Ordering.na)
    .

    Variant pf_certify_aux (reserved: TimeMap.t) (loc: Loc.t) (th: Thread.t lang): Prop :=
      | pf_certify_aux_failure
          pf e th1 th2
          (STEPS: rtc (tau (Thread.step reserved true)) th th1)
          (STEP_FAILURE: Thread.step reserved pf e th1 th2)
          (EVENT_FAILURE: ThreadEvent.get_machine_event e = MachineEvent.failure)
      | pf_certify_aux_fulfill
          pf e th1 th2
          from to val released ord
          (STEPS: rtc (tau (Thread.step reserved true)) th th1)
          (STEP_FULFILL: Thread.step reserved pf e th1 th2)
          (EVENT_FULFILL: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord))
          (TO: Time.lt (Memory.max_ts loc (Global.memory (Thread.global th1))) to)
          (ORD: Ordering.le ord Ordering.na)
    .

    Definition non_sc (e: ThreadEvent.t): Prop :=
      ~ ThreadEvent.is_sc e /\ ThreadEvent.get_machine_event e = MachineEvent.silent.

    Variant certify (reserved: TimeMap.t) (loc: Loc.t) (th: Thread.t lang): Prop :=
      | certify_failure
          pf e th1 th2
          (STEPS: rtc (pstep (Thread.step_allpf reserved) non_sc) th th1)
          (STEP_FAILURE: Thread.step reserved pf e th1 th2)
          (EVENT_FAILURE: ThreadEvent.get_machine_event e = MachineEvent.failure)
      | certify_fulfill
          pf e th1 th2
          from to val released ord
          (STEPS: rtc (pstep (Thread.step_allpf reserved) non_sc) th th1)
          (STEP_FULFILL: Thread.step reserved pf e th1 th2)
          (EVENT_FULFILL: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord))
          (TO: Time.lt (Memory.max_ts loc (Global.memory (Thread.global th1))) to)
          (ORD: Ordering.le ord Ordering.na)
    .

    Variant non_sc_consistent (th: Thread.t lang): Prop :=
      | non_sc_consistent_failure
          pf e th1 th2
          (STEPS: rtc (pstep (Thread.step_allpf
                                (Memory.max_timemap (Global.memory (Thread.global th))))
                             non_sc)
                      th th1)
          (STEP_FAILURE: Thread.step (Memory.max_timemap (Global.memory (Thread.global th)))
                                     pf e th1 th2)
          (EVENT_FAILURE: ThreadEvent.get_machine_event e = MachineEvent.failure)
      | non_sc_consistent_promises
          th2
          (STEPS: rtc (pstep (Thread.step_allpf
                                (Memory.max_timemap (Global.memory (Thread.global th))))
                             non_sc)
                      th th2)
          (PROMISES: Local.promises (Thread.local th2) = BoolMap.bot)
    .

    Lemma rtc_tau_step_rtc_non_sc_step
          reserved (th1 th2: Thread.t lang)
          (STEPS: rtc (Thread.tau_step reserved) th1 th2):
      exists th2',
        (<<STEPS1: rtc (pstep (Thread.step_allpf reserved) non_sc) th1 th2'>>) /\
        ((<<TH2: th2' = th2>>) \/
         (<<STEPS2: rtc (Thread.tau_step reserved) th2' th2>>) /\
         (<<PROMISES: Local.promises (Thread.local th2') = BoolMap.bot>>)).
    Proof.
      induction STEPS.
      { esplits; eauto. }
      inv H. inv TSTEP.
      destruct (classic (ThreadEvent.is_sc e)).
      - esplits; [refl|]. right. split.
        + econs 2; eauto. econs; eauto.
        + inv STEP; inv STEP0; ss. inv LOCAL. auto.
      - des.
        + esplits; [|eauto]. econs 2; eauto.
          econs; eauto. destruct e; ss.
        + esplits; [|eauto]. econs 2; eauto.
          econs; eauto. destruct e; ss.
    Qed.

    Lemma consistent_non_sc_consistent
          th
          (CONS: Thread.consistent th):
      non_sc_consistent (Thread.fully_reserved th).
    Proof.
      inv CONS.
      - inv FAILURE.
        exploit rtc_tau_step_rtc_non_sc_step; eauto. i. des.
        + subst. econs 1; eauto.
        + econs 2; eauto.
      - exploit rtc_tau_step_rtc_non_sc_step; eauto. i. des.
        + subst. econs 2; eauto.
        + econs 2; eauto.
    Qed.

    Lemma non_sc_consistent_certify
          th loc
          (LC_WF: Local.wf (Thread.local th) (Thread.global th))
          (GL_WF: Global.wf (Thread.global th))
          (CONS: non_sc_consistent th)
          (PROMISED: Local.promises (Thread.local th) loc = true):
      certify (Memory.max_timemap (Global.memory (Thread.global th))) loc th.
    Proof.
      inv CONS.
      { econs 1; eauto. }
      remember (Memory.max_timemap (Global.memory (Thread.global th))) as reserved.
      clear Heqreserved. revert PROMISED.
      induction STEPS; i.
      { rewrite PROMISES in *. ss. }
      destruct (Local.promises (Thread.local y) loc) eqn:PROMISEDY.
      { dup H. inv H0. inv STEP.
        exploit Thread.step_future; try exact STEP; eauto. i. des.
        exploit IHSTEPS; eauto. i. inv x1.
        - econs 1; try exact STEP_FAILURE; eauto.
        - econs 2; try exact STEP_FULFILL; eauto.
      }

      move PROMISEDY at bottom.
      inv H. inv STEP.
      inv STEP0; inv STEP; ss; (try congr); (try by inv LOCAL; ss; congr).
      { (* promise *)
        inv LOCAL. inv PROMISE. ss.
        exploit BoolMap.add_le; try exact ADD; eauto. i. congr.
      }

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
          - ss.
          - ss.
        }

        exploit (Memory.max_ts_spec loc); try apply GL_WF. i. des.
        destruct msg. clear MAX.
        econs 1; [refl|..].
        - econs 2; [|econs 9]; eauto.
          econs. econs 2; eauto.
          + unfold TView.racy_view.
            eapply TimeFacts.lt_le_lt; eauto.
            inv LOCAL. inv WRITABLE. ss.
            eapply TimeFacts.le_lt_lt; eauto.
            apply LC_WF.
          + destruct ord; ss.
        - ss.
      }

      { (* update *)
        assert (Ordering.le ordw Ordering.na).
        { inv LOCAL1. inv LOCAL2.  inv FULFILL; ss; try congr. }
        econs 1; [refl|..].
        - econs 2; [|econs 10]; eauto.
        - ss.
      }
    Qed.

    Variant sim_thread (th_src th_tgt: Thread.t lang): Prop :=
      | sim_thread_intro
          (STATE: Thread.state th_src = Thread.state th_tgt)
          (TVIEW: Local.tview (Thread.local th_src) = Local.tview (Thread.local th_tgt))
          (RESERVES: BoolMap.le (Local.reserves (Thread.local th_tgt))
                                (Local.reserves (Thread.local th_src)))
          (SC: Global.sc (Thread.global th_src) = Global.sc (Thread.global th_tgt))
          (PROMISES: BoolMap.minus (Global.promises (Thread.global th_src))
                                   (Local.promises (Thread.local th_src)) =
                     BoolMap.minus (Global.promises (Thread.global th_tgt))
                                   (Local.promises (Thread.local th_tgt)))
          (GRESERVES: forall loc (GET: Local.reserves (Thread.local th_src) loc = false),
              Global.reserves (Thread.global th_tgt) loc = true)
          (MEMORY: Global.memory (Thread.global th_src) = Global.memory (Thread.global th_tgt))
    .

    Lemma fully_reserved_sim_thread th:
      sim_thread (Thread.fully_reserved th) (Thread.fully_reserved th).
    Proof.
      econs; ss.
    Qed.

    Lemma sim_thread_internal_step
          th1_src
          reserved e th1_tgt th2_tgt
          (SIM1: sim_thread th1_src th1_tgt)
          (STEP_TGT: Thread.step reserved false e th1_tgt th2_tgt):
      sim_thread th1_src th2_tgt.
    Proof.
      inv SIM1. inv STEP_TGT. ss. inv STEP.
      - inv LOCAL. econs; ss.
        rewrite PROMISES.
        eauto using Promises.promise_minus.
      - inv LOCAL. econs; ss.
        + inv RESERVE. ii. revert LHS.
          erewrite BoolMap.add_o; eauto. condtac; auto. i. subst.
          destruct (Local.reserves (Thread.local th1_src) loc) eqn:GET; ss.
          exploit GRESERVES; try exact GET. i.
          exploit BoolMap.add_get0; try exact GADD. i. des. congr.
        + i. inv RESERVE.
          erewrite BoolMap.add_o; eauto. condtac; auto.
      - inv LOCAL. econs; ss.
        + inv CANCEL. ii. revert LHS.
          erewrite BoolMap.remove_o; eauto. condtac; ss. auto.
        + i. inv CANCEL.
          erewrite BoolMap.remove_o; eauto. condtac; ss; auto. subst.
          exploit BoolMap.remove_get0; try exact REMOVE. i. des.
          exploit RESERVES; try exact GET1. i. congr.
    Qed.

    Lemma sim_is_racy
          lc_src gl_src lc_tgt gl_tgt
          loc to ord
          (TVIEW: Local.tview lc_src = Local.tview lc_tgt)
          (PROMISES: BoolMap.minus (Global.promises gl_src) (Local.promises lc_src) =
                     BoolMap.minus (Global.promises gl_tgt) (Local.promises lc_tgt))
          (MEMORY: Global.memory gl_src = Global.memory gl_tgt)
          (RACE_TGT: Local.is_racy lc_tgt gl_tgt loc to ord):
      Local.is_racy lc_src gl_src loc to ord.
    Proof.
      inv RACE_TGT.
      - eapply equal_f in PROMISES.
        unfold BoolMap.minus in *.
        rewrite GET, GETP in *. ss.
        destruct (Global.promises gl_src loc) eqn:GRSV; ss.
        destruct (Local.promises lc_src loc) eqn:RSV; ss.
        econs 1; eauto.
      - rewrite <- TVIEW, <- MEMORY in *. eauto.
    Qed.

    Lemma sim_thread_program_step
          reserved
          th1_src
          e th1_tgt th2_tgt
          (SIM1: sim_thread th1_src th1_tgt)
          (STEP_TGT: Thread.step reserved true e th1_tgt th2_tgt)
          (NONSC: ~ ThreadEvent.is_sc e):
      exists th2_src,
        (<<STEP_SRC: Thread.step reserved true e th1_src th2_src>>) /\
        (<<SIM2: sim_thread th2_src th2_tgt>>).
    Proof.
      destruct th1_src as [st1_src [tview1_src prm1_src rsv1_src] [sc1_src gprm1_src grsv1_src mem1_src]],
          th1_tgt as [st1_tgt [tview1_tgt prm1_tgt rsv1_tgt] [sc1_tgt gprm1_tgt grsv1_tgt mem1_tgt]].
      inv SIM1. ss. subst.
      inv STEP_TGT. inv STEP; ss.
      { (* silent *)
        esplits.
        - econs; [|econs 1]; eauto.
        - ss.
      }
      { (* read *)
        inv LOCAL. ss.
        esplits.
        - econs; [|econs 2]; eauto.
        - ss.
      }
      { (* write *)
        inv LOCAL. ss.
        esplits.
        - econs; [|econs 3]; eauto.
          econs; s; eauto.
          i. des. apply RESERVED.
          destruct (rsv1_tgt loc) eqn:RSV.
          + apply RESERVES in RSV. congr.
          + exploit GRESERVES; eauto.
        - econs; ss.
          rewrite PROMISES.
          eauto using Promises.fulfill_minus.
      }
      { (* update *)
        inv LOCAL1. inv LOCAL2. ss.
        esplits.
        - econs; [|econs 4]; eauto.
          econs; s; eauto.
          i. des. apply RESERVED.
          destruct (rsv1_tgt loc) eqn:RSV.
          + apply RESERVES in RSV. congr.
          + exploit GRESERVES; eauto.
        - econs; ss.
          rewrite PROMISES.
          eauto using Promises.fulfill_minus.
      }
      { (* fence *)
        inv LOCAL. ss.
        esplits.
        - econs; [|econs 5]; eauto. econs; ss.
        - ss.
      }
      { (* failure *)
        inv LOCAL. ss.
        esplits.
        - econs; [|econs 7]; eauto.
        - ss.
      }
      { (* racy read *)
        inv LOCAL. ss.
        esplits.
        - econs; [|econs 8]; eauto.
          econs. eapply sim_is_racy; try eapply RACE; ss.
        - ss.
      }
      { (* racy write *)
        inv LOCAL. ss.
        esplits.
        - econs; [|econs 9]; eauto.
          econs. eapply sim_is_racy; try eapply RACE; ss.
        - ss.
      }
      { (* racy update *)
        esplits.
        - econs; [|econs 10]; eauto.
          inv LOCAL.
          + econs 1. ss.
          + econs 2. ss.
          + econs 3. eapply sim_is_racy; try eapply RACE; ss.
        - ss.
      }
    Qed.

    Lemma program_step_reserves
          reserved e (th1 th2: Thread.t lang)
          (STEP: Thread.step reserved true e th1 th2):
      Local.reserves (Thread.local th1) = Local.reserves (Thread.local th2) /\
      Global.reserves (Thread.global th1) = Global.reserves (Thread.global th2).
    Proof.
      inv STEP. inv STEP0; ss; try by (inv LOCAL; ss).
      inv LOCAL1. inv LOCAL2. ss.
    Qed.

    Lemma certify_pf_certify_aux
          reserved
          th_src th_tgt loc
          (SIM: sim_thread th_src th_tgt)
          (CERTIFY: certify reserved loc th_tgt):
      pf_certify_aux reserved loc th_src.
    Proof.
      inv CERTIFY.
      { revert th_src SIM.
        induction STEPS; i.
        { destruct pf; [|inv STEP_FAILURE; inv STEP; ss].
          exploit sim_thread_program_step; try exact STEP_FAILURE; eauto.
          { destruct e; ss. }
          i. des.
          econs 1; [refl|..]; eauto.
        }
        inv H. inv STEP. destruct pf0.
        { exploit sim_thread_program_step; try exact STEP0; eauto; try apply EVENT. i. des.
          exploit IHSTEPS; eauto. i. inv x1.
          - econs 1; try exact STEP_FAILURE0; eauto.
            econs 2; eauto. econs; eauto. apply EVENT.
          - econs 2; try exact STEP_FULFILL; eauto.
            econs 2; eauto. econs; eauto. apply EVENT.
        }
        { eauto using sim_thread_internal_step. }
      }
      { revert th_src SIM.
        induction STEPS; i.
        { destruct pf; [|inv STEP_FULFILL; inv STEP; ss].
          exploit sim_thread_program_step; try exact STEP_FAILURE; eauto.
          { destruct e; ss. }
          i. des.
          econs 2; [refl|..]; eauto.
          inv SIM. congr.
        }
        inv H. inv STEP. destruct pf0.
        { exploit sim_thread_program_step; try exact STEP0; eauto; try apply EVENT. i. des.
          exploit IHSTEPS; eauto. i. inv x1.
          - econs 1; try exact STEP_FAILURE; eauto.
            econs 2; eauto. econs; eauto. apply EVENT.
          - econs 2; try exact STEP_FULFILL0; eauto.
            econs 2; eauto. econs; eauto. apply EVENT.
        }
        { eauto using sim_thread_internal_step. }
      }
    Qed.

    Lemma certify_pf_certify
          th loc
          (CERTIFY: certify (Memory.max_timemap (Global.memory (Thread.global th)))
                            loc (Thread.fully_reserved th)):
      pf_certify loc th.
    Proof.
      exploit certify_pf_certify_aux; try exact CERTIFY;
        try apply fully_reserved_sim_thread.
      i. inv x0.
      - econs 1; eauto.
      - econs 2; eauto.
    Qed.

    Lemma consistent_pf_certify
          th loc
          (LC_WF: Local.wf (Thread.local th) (Thread.global th))
          (GL_WF: Global.wf (Thread.global th))
          (CONS: Thread.consistent th)
          (PROMISED: th.(Thread.local).(Local.promises) loc = true):
      pf_certify loc th.
    Proof.
      apply certify_pf_certify; auto.
      apply Local.fully_reserved_wf in LC_WF.
      apply Global.fully_reserved_wf in GL_WF.
      replace (Global.memory (Thread.global th)) with
        (Global.memory (Thread.global (Thread.fully_reserved th))) by ss.
      apply non_sc_consistent_certify; auto.
      apply consistent_non_sc_consistent; auto.
    Qed.
  End PFCertify.
End PFCertify.
