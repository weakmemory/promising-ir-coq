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


Section PFCertify.
  Variable lang: language.

  Variant certify (reserved: OptTimeMap.t) (loc: Loc.t) (th: Thread.t lang): Prop :=
    | certify_failure
        pf e th1 th2
        (STEPS: rtc (Thread.tau_step reserved) th th1)
        (STEP_FAILURE: Thread.step reserved pf e th1 th2)
        (EVENT_FAILURE: ThreadEvent.get_machine_event e = MachineEvent.failure)
    | certify_fulfill
        pf e th1 th2
        from to val released ord
        (STEPS: rtc (Thread.tau_step reserved) th th1)
        (STEP_FULFILL: Thread.step reserved pf e th1 th2)
        (EVENT_FULFILL: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord))
        (TO: Time.lt (Memory.max_ts loc (Global.memory (Thread.global th1))) to)
        (ORD: Ordering.le ord Ordering.na)
  .

  Variant pf_certify (loc: Loc.t) (th: Thread.t lang): Prop :=
    | pf_certify_failure
        pf e th1 th2
        (STEPS: rtc (Thread.pf_tau_step (Global.max_reserved (Thread.global th))) th th1)
        (STEP_FAILURE: Thread.step (Global.max_reserved (Thread.global th)) pf e th1 th2)
        (EVENT_FAILURE: ThreadEvent.get_machine_event e = MachineEvent.failure)
    | pf_certify_fulfill
        pf e th1 th2
        from to val released ord
        (STEPS: rtc (Thread.pf_tau_step (Global.max_reserved (Thread.global th))) th th1)
        (STEP_FULFILL: Thread.step (Global.max_reserved (Thread.global th)) pf e th1 th2)
        (EVENT_FULFILL: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord))
        (TO: Time.lt (Memory.max_ts loc (Global.memory (Thread.global th1))) to)
        (ORD: Ordering.le ord Ordering.na)
  .

  Lemma consistent_certify
        th loc
        (LC_WF: Local.wf (Thread.local th) (Thread.global th))
        (GL_WF: Global.wf (Thread.global th))
        (CONS: Thread.consistent th)
        (PROMISED: Local.promises (Thread.local th) loc = true):
    certify (Global.max_reserved (Thread.global th)) loc th.
  Proof.
    inv CONS.
    { inv FAILURE. econs 1; eauto. }
    remember (Global.max_reserved (Thread.global th)) as reserved.
    clear Heqreserved. revert PROMISED.
    induction STEPS; i.
    { rewrite PROMISES in *. ss. }
    destruct (Local.promises (Thread.local y) loc) eqn:PROMISEDY.
    { dup H. inv H0. inv TSTEP.
      exploit Thread.step_future; try exact STEP; eauto. i. des.
      exploit IHSTEPS; eauto. i. inv x1.
      - econs 1; try exact STEP_FAILURE; eauto.
      - econs 2; try exact STEP_FULFILL; eauto.
    }

    move PROMISEDY at bottom.
    inv H. inv TSTEP.
    inv STEP; inv STEP0; ss; (try congr); (try by inv LOCAL; ss; congr).
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
        (SC: Global.sc (Thread.global th_src) = Global.sc (Thread.global th_tgt))
        (PROMISES: BoolMap.minus (Global.promises (Thread.global th_src)) (Local.promises (Thread.local th_src)) =
                   BoolMap.minus (Global.promises (Thread.global th_tgt)) (Local.promises (Thread.local th_tgt)))
        (RESERVES: BoolMap.minus (Global.reserves (Thread.global th_src)) (Local.reserves (Thread.local th_src)) =
                   BoolMap.minus (Global.reserves (Thread.global th_tgt)) (Local.reserves (Thread.local th_tgt)))
        (MEMORY: Global.memory (Thread.global th_src) = Global.memory (Thread.global th_tgt))
  .

  Lemma certify_pf_certify
        th loc
        (LC_WF: Local.wf (Thread.local th) (Thread.global th))
        (GL_WF: Global.wf (Thread.global th))
        (CERTIFY: certify (Global.max_reserved (Thread.global th)) loc th):
    pf_certify loc th.
  Proof.
  Admitted.

  Lemma consistent_pf_certify
        th loc
        (LC_WF: Local.wf (Thread.local th) (Thread.global th))
        (GL_WF: Global.wf (Thread.global th))
        (CONS: Thread.consistent th)
        (PROMISED: th.(Thread.local).(Local.promises) loc = true):
    pf_certify loc th.
  Proof.
    eauto using consistent_certify, certify_pf_certify.
  Qed.
End PFCertify.
