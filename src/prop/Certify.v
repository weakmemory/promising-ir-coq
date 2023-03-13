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

Set Implicit Arguments.


Section Certify.
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

  Lemma rtc_spf_step_certify
        th1 th2 loc
        (LC_WF: Local.wf (Thread.local th1) (Thread.global th1))
        (GL_WF: Global.wf (Thread.global th1))
        (STEPS: rtc (pstep (@Thread.step lang) (strict_pf /1\ non_sc)) th1 th2)
        (PROMISED: Local.promises (Thread.local th1) loc = true)
        (FULFILLED: Local.promises (Thread.local th2) loc = false):
    certify loc th1.
  Proof.
    revert PROMISED.
    induction STEPS; i; try congr.
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
    eapply rtc_spf_step_certify; eauto.
    rewrite PROMISES. ss.
  Qed.


  (* certify with transitions race with promises *)

  Variant certify_racy_promise (loc: Loc.t) (th: Thread.t lang): Prop :=
    | certify_racy_promise_failure
        e th1 th2
        (STEPS: rtc (pstep (@Thread.step _) (ThreadEvent.is_pf /1\ non_sc)) th th1)
        (STEP_FAILURE: Thread.step e th1 th2)
        (EVENT_FAILURE: ThreadEvent.get_machine_event e = MachineEvent.failure)
    | certify_racy_promise_fulfill
        e th1 th2
        from to val released ord
        (STEPS: rtc (pstep (@Thread.step _) (ThreadEvent.is_pf /1\ non_sc)) th th1)
        (STEP_FULFILL: Thread.step e th1 th2)
        (EVENT_FULFILL: e = ThreadEvent.write loc from to val released ord)
        (TO: Time.lt (Memory.max_ts loc (Global.memory (Thread.global th1))) to)
        (ORD: Ordering.le ord Ordering.na)
  .

  Variant pf_certify_racy_promise (loc: Loc.t) (th: Thread.t lang): Prop :=
    | pf_certify_racy_promise_failure
        e th1 th2
        (STEPS: rtc (pstep (@Thread.step _) (ThreadEvent.is_program /1\ non_sc)) th th1)
        (STEP_FAILURE: Thread.step e th1 th2)
        (EVENT_FAILURE: ThreadEvent.get_machine_event e = MachineEvent.failure)
    | pf_certify_racy_promise_fulfill
        e th1 th2
        from to val released ord
        (STEPS: rtc (pstep (@Thread.step _) (ThreadEvent.is_program /1\ non_sc)) th th1)
        (STEP_FULFILL: Thread.step e th1 th2)
        (EVENT_FULFILL: e = ThreadEvent.write loc from to val released ord)
        (TO: Time.lt (Memory.max_ts loc (Global.memory (Thread.global th1))) to)
        (ORD: Ordering.le ord Ordering.na)
  .

  Lemma rtc_pf_step_certify_racy_promise
        th1 th2 loc
        (LC_WF: Local.wf (Thread.local th1) (Thread.global th1))
        (GL_WF: Global.wf (Thread.global th1))
        (STEPS: rtc (pstep (@Thread.step lang) (ThreadEvent.is_pf /1\ non_sc)) th1 th2)
        (PROMISED: Local.promises (Thread.local th1) loc = true)
        (FULFILLED: Local.promises (Thread.local th2) loc = false):
    certify_racy_promise loc th1.
  Proof.
    revert PROMISED.
    induction STEPS; i; try congr.
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
    }
  Qed.

  Lemma pf_consistent_certify_racy_promise
        th loc
        (LC_WF: Local.wf (Thread.local th) (Thread.global th))
        (GL_WF: Global.wf (Thread.global th))
        (CONS: PFConsistent.pf_consistent th)
        (PROMISED: Local.promises (Thread.local th) loc = true):
    certify_racy_promise loc (Thread.cap_of th).
  Proof.
    inv CONS.
    { econs 1; eauto. }
    exploit Thread.cap_wf; eauto. clear LC_WF GL_WF. i. des.
    remember (Thread.cap_of th) as th0.
    replace (Local.promises (Thread.local th) loc) with
      (Local.promises (Thread.local th0) loc) in * by (subst; ss).
    eapply rtc_pf_step_certify_racy_promise; eauto.
    rewrite PROMISES. ss.
  Qed.
End Certify.
