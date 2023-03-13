Require Import RelationClasses.
Require Import Program.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.

From PromisingLib Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Promises.
Require Import Global.
Require Import Thread.
Require Import Configuration.
Require Import BoolMap.

Require Import ReorderInternal.

Require Import MemoryProps.
Require Import LowerMemory.

Set Implicit Arguments.



Definition release_event (e: ThreadEvent.t): Prop :=
  match e with
  | ThreadEvent.update _ _ _ _ _ _ _ _ ordw => True
  | ThreadEvent.write _ _ _ _ _ ord => Ordering.le Ordering.plain ord
  | ThreadEvent.fence _ ordw => Ordering.le Ordering.plain ordw
  | ThreadEvent.syscall _ => True
  | ThreadEvent.failure => True
  | ThreadEvent.racy_write _ _ _ _ => True
  | ThreadEvent.racy_update _ _ _ _ _ _ => True
  | _ => False
  end.

Definition is_na_write (e: ThreadEvent.t): Prop :=
  match e with
  | ThreadEvent.write _ _ _ _ _ ord => Ordering.le ord Ordering.na
  | ThreadEvent.update _ _ _ _ _ _ _ _ ordw => Ordering.le ordw Ordering.na
  | _ => False
  end.

Variant lower_step {lang} e (th0 th2: Thread.t lang): Prop :=
| lower_step_intro
    th1
    (CANCEL:
      ((<<NWRITE: ~ is_na_write e>>) /\ (<<EQ: th1 = th0>>))
      \/
        (exists loc from to val,
            (<<EVENT: e = ThreadEvent.write loc from to val None Ordering.na>>) /\
              (<<STEP: Thread.step (ThreadEvent.cancel loc from to) th0 th1>>) /\
              (<<PROMISED: th0.(Thread.local).(Local.promises) loc = true>>)))
    (STEP: Thread.program_step e th1 th2)
    (NRELEASE: ~ release_event e)
.

Lemma lower_step_step lang e th0 th1
      (STEP: @lower_step lang e th0 th1)
  :
  rtc (@Thread.all_step _) th0 th1.
Proof.
  i. inv STEP. des.
  { econs 2; [|refl]. econs; eauto. inv STEP0. econs; eauto. }
  { econs 2; [|].
    { econs. eauto. }
    { econs; [|refl]. inv STEP0. econs; eauto. }
  }
Qed.

Lemma tau_lower_step_tau_step lang:
  tau (@lower_step lang) <2= rtc (@Thread.tau_step lang).
Proof.
  i. inv PR. inv TSTEP. des.
  { econs 2; [|refl]. econs; eauto. inv STEP. econs; eauto. }
  { econs 2; [|].
    { econs; eauto. }
    { econs; [|refl]. inv STEP. econs; eauto. }
  }
Qed.

Lemma tau_lower_steps_tau_steps
      lang (th0 th1: Thread.t lang)
      (STEPS: rtc (tau lower_step) th0 th1)
  :
  rtc (@Thread.tau_step _) th0 th1.
Proof.
  eapply rtc_join. eapply rtc_implies; [|eauto].
  eapply tau_lower_step_tau_step.
Qed.

Lemma lower_step_tau_lower_step
      lang e (th0 th1: Thread.t lang)
      (STEP: lower_step e th0 th1)
  :
    tau lower_step th0 th1.
Proof.
  inv STEP. econs; eauto.
  { econs; eauto. }
  { destruct e; ss. }
Qed.

Lemma lower_step_future
      e lang (th1 th2: Thread.t lang)
      (STEP: lower_step e th1 th2)
      (LC_WF1: Local.wf (Thread.local th1) (Thread.global th1))
      (GL_WF1: Global.wf (Thread.global th1)):
  (<<LC_WF2: Local.wf (Thread.local th2) (Thread.global th2)>>) /\
    (<<GL_WF2: Global.wf (Thread.global th2)>>) /\
    (<<TVIEW_FUTURE: TView.le (Local.tview (Thread.local th1)) (Local.tview (Thread.local th2))>>) /\
    (<<GL_FUTURE: Global.future (Thread.global th1) (Thread.global th2)>>).
Proof.
  eapply Thread.rtc_all_step_future; eauto.
  eapply lower_step_step; eauto.
Qed.

Lemma lower_steps_future
      lang (th1 th2: Thread.t lang)
      (STEPS: rtc (tau lower_step) th1 th2)
      (LC_WF1: Local.wf (Thread.local th1) (Thread.global th1))
      (GL_WF1: Global.wf (Thread.global th1)):
  (<<LC_WF2: Local.wf (Thread.local th2) (Thread.global th2)>>) /\
    (<<GL_WF2: Global.wf (Thread.global th2)>>) /\
    (<<TVIEW_FUTURE: TView.le (Local.tview (Thread.local th1)) (Local.tview (Thread.local th2))>>) /\
    (<<GL_FUTURE: Global.future (Thread.global th1) (Thread.global th2)>>).
Proof.
  eapply Thread.rtc_tau_step_future; eauto.
  eapply tau_lower_steps_tau_steps; eauto.
Qed.


Section REORDER.

  Lemma split_program_step
        lang e (th0 th2: Thread.t lang)
        (STEP: Thread.program_step e th0 th2)
        (NRELEASE: ~ release_event e)
        (LOCAL: Local.wf (Thread.local th0) (Thread.global th0))
        (CLOSED: Global.wf (Thread.global th0)):
    (exists th1,
        (<<INTERNALS: rtc (@Thread.internal_step _) th0 th1>>) /\
          (<<LOWER: rtc (tau lower_step) th1 th2>>) /\
          (<<STATE: th0.(Thread.state) = th1.(Thread.state)>>)) \/
      (exists th1 e_race,
          (<<STEP: Thread.step e_race th0 th1>>) /\
            (<<RACE: ThreadEvent.get_machine_event e_race = MachineEvent.failure>>))
  .
  Proof.
    destruct (classic (exists th1 e_race,
                          (<<STEP: Thread.step e_race th0 th1>>) /\
                            (<<RACE: ThreadEvent.get_machine_event e_race = MachineEvent.failure>>))).
    { auto. }
    left.
    cut (exists th1,
            (<<INTERNALS: rtc (@Thread.internal_step _) th0 th1>>) /\
              (<<LOWER: lower_step e th1 th2>>) /\
              (<<STATE: th0.(Thread.state) = th1.(Thread.state)>>)).
    { i. des. esplits; eauto. econs 2; [|refl]. eapply lower_step_tau_lower_step; eauto. }
    inv STEP. inv LOCAL0; ss.
    { esplits; [refl|..]; eauto. econs; ss.
      { left. eauto. }
      { econs; eauto. }
    }
    { esplits; [refl|..]; eauto. econs; ss.
      { left. eauto. }
      { econs; eauto. }
    }
    { destruct ord; ss.
      inv LOCAL1. hexploit add_succeed_wf; eauto. i. des.
      hexploit Memory.add_exists.
      { eauto. }
      { eauto. }
      { eapply Message.wf_reserve. }
      i. des.
      hexploit Memory.add_exists_le.
      { eapply LOCAL. }
      { eauto. }
      i. des. destruct (lc1.(Local.promises) loc) eqn:PROMISED.
      { esplits.
        { econs 2; [|refl]. econs. econs 2. econs; eauto. }
        { econs; ss.
          { right.
            { esplits; eauto. econs. econs. econs; eauto. econs; eauto.
              { eapply memory_add_remove; eauto. }
              { eapply memory_add_remove; eauto. }
            }
          }
          { econs; ss. econs; eauto. }
        }
        { ss. }
      }
      { destruct (gl1.(Global.promises) loc) eqn:RACE.
        { exfalso. eapply H. esplits.
          { econs 2.
            2:{ eapply Local.program_step_racy_write. econs; eauto. }
            { eauto. }
          }
          { ss. }
        }
        esplits.
        { econs 2.
          { econs. econs 2. econs; eauto. }
          econs 2; [|refl].
          { econs. econs 1. econs; eauto. }
        }
        { econs; ss.
          { right.
            { esplits; eauto.
              2:{ rewrite loc_fun_add_spec. des_ifs. }
              econs. econs. econs; eauto. econs; eauto.
              { eapply memory_add_remove; eauto. }
              { eapply memory_add_remove; eauto. }
            }
          }
          { econs; ss. econs. econs; ss.
            { inv FULFILL; cycle 1.
              { inv REMOVE. rewrite PROMISED in *. ss. }
              econs 2; eauto.
              { econs.
                { rewrite loc_fun_add_spec. des_ifs. }
                { extensionality loc0. rewrite ! loc_fun_add_spec. des_ifs. }
              }
              { econs.
                { rewrite loc_fun_add_spec. des_ifs. }
                { extensionality loc0. rewrite ! loc_fun_add_spec. des_ifs. }
              }
            }
            { eauto. }
          }
        }
        { ss. }
      }
    }
    { esplits; [refl|..]; eauto. econs; ss.
      { left. eauto. }
      { econs; eauto. }
    }
    { esplits; [refl|..]; eauto. econs; ss.
      { left. eauto. }
      { econs; eauto. }
    }
  Qed.

  Lemma split_step
        lang e (th0 th2: Thread.t lang)
        (STEP: Thread.step e th0 th2)
        (NRELEASE: ~ release_event e)
        (LOCAL: Local.wf (Thread.local th0) (Thread.global th0))
        (CLOSED: Global.wf (Thread.global th0)):
    (exists th1,
        (<<INTERNALS: rtc (@Thread.internal_step _) th0 th1>>) /\
          (<<LOWER: rtc (tau lower_step) th1 th2>>) /\
          (<<STATE: th0.(Thread.state) = th1.(Thread.state)>>)) \/
      (exists th1 e_race,
          (<<STEP: Thread.step e_race th0 th1>>) /\
            (<<RACE: ThreadEvent.get_machine_event e_race = MachineEvent.failure>>))
  .
  Proof.
    inv STEP.
    { left. esplits.
      { econs 2; [|refl]. econs; eauto. }
      { refl. }
      ss.
    }
    { hexploit split_program_step; eauto. econs; eauto. }
  Qed.

  Lemma reorder_lower_step_internal_step
        lang e1 (th0 th1 th2: @Thread.t lang)
        (WF: Local.wf th0.(Thread.local) th0.(Thread.global))
        (CLOSED: Global.wf th0.(Thread.global))
        (STEP1: lower_step e1 th0 th1)
        (STEP2: Thread.internal_step th1 th2):
    exists th1',
      (<<STEP1: rtc (@Thread.internal_step _) th0 th1'>>) /\
        (<<STEP2: lower_step e1 th1' th2>>) /\
        (<<STATE: th0.(Thread.state) = th1'.(Thread.state)>>).
  Proof.
    inv STEP1. des; subst.
    { (* program; internal *)
      inv STEP. inv STEP2. ss.
      exploit reorder_program_internal; eauto.
      { destruct e1; ss. destruct ordw; ss. }
      i. unguard. des; subst.
      { esplits; try refl. econs; eauto. econs; eauto. }
      { esplits.
        { econs 2; try refl. econs. eauto. }
        { econs; eauto. econs; eauto. }
        { ss. }
      }
    }

    inv STEP0; inv LOCAL. inv STEP. inv LOCAL. ss.
    inv STEP2. inv LOCAL.
    { (* cancel; write; promise *)
      destruct (Loc.eq_dec loc loc0); subst.
      { exploit reorder_write_promise_same; eauto. i. unguard. des; subst.
        { esplits; eauto. econs.
          { right. esplits; eauto. }
          { econs; eauto. }
          { ss. }
        }
        { exploit reorder_cancel_promise; eauto. i. des.
          esplits.
          { econs 2; try refl. econs. econs 1. eauto. }
          { econs.
            { right. esplits; eauto. ss.
              inv STEP0. inv PROMISE.
              exploit BoolMap.add_get0; try exact ADD. i. des. ss.
            }
            { econs; eauto. }
            { ss. }
          }
          { ss. }
        }
      }
      { exploit reorder_write_promise; eauto. i. des.
        exploit reorder_cancel_promise; eauto. i. des.
        esplits.
        { econs 2; try refl. econs. econs 1. eauto. }
        { econs.
          { right. esplits; eauto. ss.
            inv STEP0. inv PROMISE. ss.
            erewrite BoolMap.add_o; eauto. condtac; ss.
          }
          { econs; eauto. }
          { ss. }
        }
        { ss. }
      }
    }

    { (* cancel; write; reserve *)
      exploit reorder_write_reserve; eauto. i. des.
      exploit reorder_cancel_reserve; eauto.
      { inv LOCAL0. inv CANCEL.
        exploit Memory.remove_get0; try exact MEM. i. des.
        exploit Memory.get_ts; try exact GET. i. des; ss. subst.
        inv CLOSED. inv MEM_CLOSED.
        rewrite INHABITED in *. ss.
      }
      { destruct (Loc.eq_dec loc loc0); auto. subst. right.
        inv LOCAL1. inv LOCAL2. inv RESERVE. ss.
        exploit Memory.add_get0; try exact WRITE. i. des.
        exploit Memory.add_get0; try exact MEM. i. des.
        exploit Memory.add_get1; try exact GET0; eauto. i.
        exploit Memory.get_disjoint; [exact x0|exact GET2|]. i. des; ss.
      }
      i. des. esplits.
      { econs 2; try refl. econs. econs 2. eauto. }
      { econs.
        { right. esplits; eauto. ss. inv STEP0. ss. }
        { econs; eauto. }
        { ss. }
      }
      { ss. }
    }

    { (* cancel; write; cancel *)
      exploit reorder_write_cancel; eauto. i. des.
      exploit reorder_cancel_cancel; [exact LOCAL0|..]; eauto. i. des.
      esplits.
      { econs 2; try refl. econs. econs 3. exact STEP0. }
      { econs.
        { right. esplits; eauto. ss. inv STEP0. ss. }
        { econs; eauto. }
        { ss. }
      }
      { ss. }
    }
  Qed.

  Lemma reorder_lower_steps_internal_steps
        lang (th0 th1 th2: @Thread.t lang)
        (WF: Local.wf th0.(Thread.local) th0.(Thread.global))
        (CLOSED: Global.wf th0.(Thread.global))
        (STEPS1: rtc (tau lower_step) th0 th1)
        (STEPS2: rtc (@Thread.internal_step _) th1 th2):
    exists th1',
      (<<STEPS1: rtc (@Thread.internal_step _) th0 th1'>>) /\
        (<<STEPS2: rtc (tau lower_step) th1' th2>>) /\
        (<<STATE: th0.(Thread.state) = th1'.(Thread.state)>>).
  Proof.
    revert th2 STEPS2.
    induction STEPS1; i.
    { esplits; eauto using Forall2_refl.
      clear - STEPS2.
      induction STEPS2; eauto.
      rewrite <- IHSTEPS2; eauto. inv H. ss.
    }
    inv H.
    exploit lower_step_future; eauto. i. des.
    exploit IHSTEPS1; eauto. i. des.
    cut (exists th1'',
            rtc (@Thread.internal_step _) x th1'' /\
              lower_step e th1'' th1' /\
              x.(Thread.state) = th1''.(Thread.state)).
    { i. des. esplits; eauto. }
    exploit Thread.rtc_internal_step_future; eauto. i. des.
    clear z STEPS1 IHSTEPS1 STEPS2 STEPS3.
    clear - WF CLOSED TSTEP STEPS0.
    rename th1' into z, STEPS0 into STEPS.
    revert x e WF CLOSED TSTEP.
    induction STEPS; i.
    { esplits; eauto. }
    exploit lower_step_future; eauto. i. des.
    exploit Thread.internal_step_future; eauto. i. des.
    exploit reorder_lower_step_internal_step; try exact TSTEP; eauto. i. des.
    exploit Thread.rtc_internal_step_future; eauto. i. des.
    exploit IHSTEPS; try exact STEP2; eauto. i. des.
    esplits; try exact x1; eauto.
    { etrans; eauto. }
    { congr. }
  Qed.

End REORDER.


Section CHERRY.

  (* unused *)
  Variant cherrypicked A: (A * A) -> (A * A) -> Prop :=
    | cherrypicked_unchanged
        a0 a1
      :
      cherrypicked (a0, a1) (a0, a1)
    | cherrypicked_changed
        a0 a1 a
      :
      cherrypicked (a0, a1) (a, a)
  .

  Global Program Instance cherrypicked_PreOrder A: PreOrder (@cherrypicked A).
  Next Obligation.
  Proof.
    ii. destruct x. econs 1.
  Qed.
  Next Obligation.
  Proof.
    ii. inv H; inv H0.
    { econs 1. }
    { econs 2. }
    { econs 2. }
    { econs 2. }
  Qed.

  Variant cherrypicked_promise:
    ((bool * bool) * (bool * bool)) -> ((bool * bool) * (bool * bool)) -> Prop :=
    | cherrypicked_promise_unchanged
        gp_src lp_src gp_tgt lp_tgt
      :
      cherrypicked_promise ((gp_src, lp_src), (gp_tgt, lp_tgt)) ((gp_src, lp_src), (gp_tgt, lp_tgt))
    | cherrypicked_promise_fulfilled
      :
      cherrypicked_promise ((true, true), (true, true)) ((false, false), (false, false))
  .

  Global Program Instance cherrypicked_promise_PreOrder: PreOrder (cherrypicked_promise).
  Next Obligation.
  Proof.
    ii. destruct x as [[] []]. econs 1.
  Qed.
  Next Obligation.
  Proof.
    ii. inv H; inv H0.
    { econs 1. }
    { econs 2. }
    { econs 2. }
  Qed.

  Definition cherrypicked_promises:
    ((BoolMap.t * BoolMap.t) * (BoolMap.t * BoolMap.t))
    ->
      ((BoolMap.t * BoolMap.t) * (BoolMap.t * BoolMap.t))
    -> Prop :=
    fun '((gprm_src0, lprm_src0), (gprm_tgt0, lprm_tgt0))
        '((gprm_src1, lprm_src1), (gprm_tgt1, lprm_tgt1)) =>
      forall loc, cherrypicked_promise
                    ((gprm_src0 loc, lprm_src0 loc), (gprm_tgt0 loc, lprm_tgt0 loc))
                    ((gprm_src1 loc, lprm_src1 loc), (gprm_tgt1 loc, lprm_tgt1 loc)).

  Global Program Instance cherrypicked_promises_PreOrder: PreOrder cherrypicked_promises.
  Next Obligation.
  Proof.
    unfold cherrypicked_promises. ii. des_ifs. i. refl.
  Qed.
  Next Obligation.
  Proof.
    unfold cherrypicked_promises. ii. des_ifs. i. etrans; eauto.
  Qed.

  Variant cherrypicked_content:
    ((option (Time.t * Message.t) * option (Time.t * Message.t)) * (option (Time.t * Message.t) * option (Time.t * Message.t))) -> ((option (Time.t * Message.t) * option (Time.t * Message.t)) * (option (Time.t * Message.t) * option (Time.t * Message.t))) -> Prop :=
    | cherrypicked_content_unchanged
        gm_src lm_src gm_tgt lm_tgt
      :
      cherrypicked_content ((gm_src, lm_src), (gm_tgt, lm_tgt)) ((gm_src, lm_src), (gm_tgt, lm_tgt))
    | cherrypicked_content_fulfilled
        from val released na
      :
      cherrypicked_content
        ((Some (from, Message.reserve), Some (from, Message.reserve)), (Some (from, Message.reserve), Some (from, Message.reserve)))
        ((Some (from, Message.message val released na), None), (Some (from, Message.message val released na), None))
  .

  Global Program Instance cherrypicked_content_PreOrder: PreOrder (cherrypicked_content).
  Next Obligation.
  Proof.
    ii. destruct x as [[] []]. econs 1.
  Qed.
  Next Obligation.
  Proof.
    ii. inv H; inv H0.
    { econs 1. }
    { econs 2. }
    { econs 2. }
  Qed.

  Definition cherrypicked_memory:
    ((Memory.t * Memory.t) * (Memory.t * Memory.t))
    ->
      ((Memory.t * Memory.t) * (Memory.t * Memory.t))
    -> Prop :=
    fun '((mem_src0, rsv_src0), (mem_tgt0, rsv_tgt0))
        '((mem_src1, rsv_src1), (mem_tgt1, rsv_tgt1)) =>
      forall loc to, cherrypicked_content
                       ((Memory.get loc to mem_src0, Memory.get loc to rsv_src0), (Memory.get loc to mem_tgt0, Memory.get loc to rsv_tgt0))
                       ((Memory.get loc to mem_src1, Memory.get loc to rsv_src1), (Memory.get loc to mem_tgt1, Memory.get loc to rsv_tgt1)).

  Global Program Instance cherrypicked_memory_PreOrder: PreOrder cherrypicked_memory.
  Next Obligation.
  Proof.
    unfold cherrypicked_memory. ii. des_ifs. i. refl.
  Qed.
  Next Obligation.
  Proof.
    unfold cherrypicked_memory. ii. des_ifs. i. etrans; eauto.
  Qed.

  Definition cherrypicked_global:
    ((Global.t * Local.t) * (Global.t * Local.t))
    ->
      ((Global.t * Local.t) * (Global.t * Local.t))
    -> Prop :=
    fun '((Global.mk sc_src0 gprm_src0 mem_src0, Local.mk tvw_src0 lprm_src0 rsv_src0), (Global.mk sc_tgt0 gprm_tgt0 mem_tgt0, Local.mk tvw_tgt0 lprm_tgt0 rsv_tgt0))
        '((Global.mk sc_src1 gprm_src1 mem_src1, Local.mk tvw_src1 lprm_src1 rsv_src1), (Global.mk sc_tgt1 gprm_tgt1 mem_tgt1, Local.mk tvw_tgt1 lprm_tgt1 rsv_tgt1)) =>
      (<<SC_SRC: sc_src1 = sc_src0>>) /\
        (<<SC_TGT: sc_tgt1 = sc_tgt0>>) /\
        (<<MEM: cherrypicked_memory ((mem_src0, rsv_src0), (mem_tgt0, rsv_tgt0)) ((mem_src1, rsv_src1), (mem_tgt1, rsv_tgt1))>>) /\
        (<<PRM: cherrypicked_promises ((gprm_src0, lprm_src0), (gprm_tgt0, lprm_tgt0)) ((gprm_src1, lprm_src1), (gprm_tgt1, lprm_tgt1))>>).

  Global Program Instance cherrypicked_global_PreOrder: PreOrder cherrypicked_global.
  Next Obligation.
  Proof.
    unfold cherrypicked_global. ii. des_ifs. splits; auto.
    { refl. }
    { refl. }
  Qed.
  Next Obligation.
  Proof.
    unfold cherrypicked_global. ii. des_ifs. des. subst. splits; auto.
    { etrans; eauto. }
    { etrans; eauto. }
  Qed.

End CHERRY.


Section LOWERMEM.
  Variable lang: language.

  Lemma strong_le_racy
        lc gl_src gl_tgt loc to_tgt ord
        (SIMGLOBAL: Global.strong_le gl_tgt gl_src)
        (RACE: Local.is_racy lc gl_tgt loc to_tgt ord)
        (LOCAL: Local.wf lc gl_tgt)
    :
    exists to_src,
      (<<RACE: Local.is_racy lc gl_src loc to_src ord>>).
  Proof.
    inv RACE.
    { inv SIMGLOBAL. inv ADDNA. specialize (ADDNA0 loc). des.
      { esplits. econs 1; eauto.
        { eapply Bool.le_implb in PROMISES.
          rewrite GET in PROMISES. ss.
        }
      }
      { rr in LATEST. des. esplits. econs 2; eauto.
        inv LOCAL. inv TVIEW_CLOSED. inv CUR.
        specialize (PLN loc). des. eapply LATEST0 in PLN. auto.
      }
    }
    { esplits. econs 2; eauto.
      { eapply SIMGLOBAL. eauto. }
    }
  Qed.

  Lemma lower_step_strong_future e_tgt st0 st1
        lc0 lc1 gl_tgt0 gl_tgt1
        gl_src0
        (STEP: lower_step e_tgt (Thread.mk lang st0 lc0 gl_tgt0) (Thread.mk lang st1 lc1 gl_tgt1))

        (SIMGLOBAL: Global.strong_le gl_tgt0 gl_src0)

        (LOCALSRC: Local.wf lc0 gl_src0)
        (LOCALTGT: Local.wf lc0 gl_tgt0)
        (GLOBALSRC: Global.wf gl_src0)
        (GLOBALTGT: Global.wf gl_tgt0)
    :
    (exists e_src gl_src1,
        (<<STEP: lower_step e_src (Thread.mk lang st0 lc0 gl_src0) (Thread.mk lang st1 lc1 gl_src1)>>) /\
          (<<SIMGLOBAL: Global.strong_le gl_tgt1 gl_src1>>) /\
          (<<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>>) /\
          (<<CHERRY: cherrypicked_global (gl_src0, lc0, (gl_tgt0, lc0)) (gl_src1, lc1, (gl_tgt1, lc1))>>)) \/
      (exists e_failure,
          (<<STEP: Thread.step e_failure (Thread.mk lang st0 lc0 gl_src0) (Thread.mk lang st1 lc0 gl_src0)>>) /\
            (<<EVENT: ThreadEvent.get_machine_event e_failure = MachineEvent.failure>>)).
  Proof.
    inv STEP. des; subst.
    { inv STEP0. inv LOCAL; ss.
      { left. exists (ThreadEvent.silent). esplits.
        { econs.
          { left. eauto. }
          { econs; eauto. }
          { ss. }
        }
        { ss. }
        { ss. }
        { des_ifs. splits; ss; i; try refl. }
      }
      { left. exists (ThreadEvent.read loc to val released ord).
        inv LOCAL0. esplits.
        { econs.
          { left. eauto. }
          { econs; eauto. econs; eauto.
            eapply SIMGLOBAL in GET. econs; eauto.
          }
          { ss. }
        }
        { ss. }
        { ss. }
        { des_ifs. splits; ss; i; try refl. }
      }
      { destruct ord; ss. }
      { left. exists (ThreadEvent.fence ordr ordw).
        inv LOCAL0. esplits.
        { econs.
          { left. eauto. }
          { econs; eauto. econs; eauto. econs; eauto.
            f_equal. eapply TViewFacts.write_fence_tview_acqrel.
            destruct ordw; ss.
          }
          { ss. }
        }
        { inv SIMGLOBAL. econs.
          { inv LE. econs; ss.
            rewrite ! TViewFacts.write_fence_sc_acqrel; auto.
            { destruct ordw; ss. }
            { destruct ordw; ss. }
          }
          inv ADDNA. econs; eauto.
        }
        { ss. }
        { des_ifs. splits; ss; i; try refl.
          { destruct ordw; ss. }
          { destruct ordw; ss. }
        }
      }
      { left. inv LOCAL0. hexploit strong_le_racy; eauto.
        i. des. exists (ThreadEvent.racy_read loc to_src val ord).
        esplits.
        { econs.
          { left. eauto. }
          { econs; eauto. }
          { ss. }
        }
        { auto. }
        { ss. }
        { des_ifs. splits; ss; i; try refl. }
      }
    }
    { inv STEP.
      2:{ inv LOCAL; ss. }
      inv STEP0; ss.
      destruct (classic (exists to, Local.is_racy lc0 gl_src0 loc to Ordering.na)).
      { des. right. esplits.
        { econs 2.
          2:{ eapply Local.program_step_racy_write. econs; eauto. }
          { eauto. }
        }
        { ss. }
      }
      left. ss. exists (ThreadEvent.write loc from to val None Ordering.na).
      inv LOCAL. inv LOCAL0. inv LOCAL. inv LOCAL1. ss.
      inv CANCEL. hexploit Memory.remove_exists_le.
      { eapply LOCALSRC. }
      { eauto. }
      i. des. hexploit add_succeed_wf; eauto. i. des.
      hexploit (@Memory.add_exists mem2' loc from to); eauto.
      { i. erewrite Memory.remove_o in GET2; eauto. des_ifs.
        hexploit Memory.get_disjoint.
        { eapply Memory.remove_get0. eapply H0. }
        { eapply GET2. }
        i. ss. des; clarify.
      }
      i. des.
      assert (exists gprm_src1,
                 (<<FULFILL: Promises.fulfill (Local.promises lc0) (Global.promises gl_src0) loc Ordering.na prm2 gprm_src1>>) /\
                   (<<SAME:__guard__((<<TGTG: gprm2 = gl_tgt0.(Global.promises)>>) /\ (<<SRCG: gprm_src1 = gl_src0.(Global.promises)>>) /\ (<<PRML: prm2 = lc0.(Local.promises)>>) \/
                                       ((<<TGTG: BoolMap.remove gl_tgt0.(Global.promises) loc gprm2>>) /\ (<<SRCG: BoolMap.remove gl_src0.(Global.promises) loc gprm_src1>>) /\ (<<PRML: BoolMap.remove lc0.(Local.promises) loc prm2>>)))>>)).
      { inv FULFILL.
        { esplits.
          { econs 1; eauto. }
          { left. splits; auto. }
        }
        { assert (SRC: Global.promises gl_src0 loc = true).
          { inv REMOVE. eapply LOCALSRC in GET. auto. }
          esplits.
          { econs 2; eauto. }
          { right. splits; auto. }
        }
      }
      des. esplits.
      { econs.
        { right. esplits; eauto. }
        { econs; eauto. }
        { ss. }
      }
      { inv SIMGLOBAL. econs; ss.
        { inv LE. econs; eauto; ss.
          ii. erewrite (@Memory.add_o _ mem0) in LHS; eauto.
          erewrite (@Memory.add_o _ mem2'); eauto.
          erewrite (@Memory.remove_o _ (Global.memory gl_tgt0)) in LHS; eauto.
          erewrite (@Memory.remove_o _ (Global.memory gl_src0)); eauto.
          des_ifs. eapply MEMORY; eauto.
        }
        { inv ADDNA. econs; ss. i. specialize (ADDNA0 loc0). des.
          { left. r in SAME. des; subst.
            { auto. }
            { inv TGTG. inv SRCG. rewrite ! loc_fun_add_spec.
              r. clear - PROMISES. des_ifs.
            }
          }
          { destruct (Loc.eq_dec loc0 loc); subst.
            { right. inv LATEST. des. exfalso.
              eapply H. esplits. econs 2; eauto.
              inv LOCALTGT. inv TVIEW_CLOSED. inv CUR.
              specialize (PLN loc). des.
              eapply LATEST in PLN. auto.
            }
            { right. inv LATEST. des.
              econs. esplits.
              { erewrite Memory.add_get1; eauto.
                eapply Memory.remove_get1 in GET; eauto.
                des; eauto. subst; ss.
              }
              { i. erewrite Memory.add_o in GET0; eauto.
                erewrite Memory.remove_o in GET0; eauto.
                des_ifs; eauto. ss. des; subst; ss.
              }
            }
          }
        }
      }
      { ss. }
      { des_ifs. splits; ss; i; try refl.
        { erewrite (@Memory.add_o mem2); eauto.
          erewrite (@Memory.remove_o mem0); eauto.
          erewrite (@Memory.add_o mem1); eauto.
          erewrite (@Memory.remove_o mem2'); eauto.
          erewrite (@Memory.remove_o rsv2); eauto. des_ifs.
          { ss. des; clarify.
            eapply Memory.remove_get0 in MEM.
            eapply Memory.remove_get0 in RSV.
            eapply Memory.remove_get0 in H0. des.
            rewrite GET3. rewrite GET. rewrite GET1. econs 2.
          }
          { econs. }
        }
        { r in SAME. des; subst.
          { refl. }
          { inv TGTG. inv SRCG. inv PRML.
            rewrite ! loc_fun_add_spec. des_ifs.
            { econs 2. }
            { refl. }
          }
        }
      }
    }
  Qed.

  Lemma lower_steps_strong_future st0 st1
        lc0 lc1 gl_tgt0 gl_tgt1
        gl_src0
        (STEPS: rtc (tau lower_step) (Thread.mk lang st0 lc0 gl_tgt0) (Thread.mk lang st1 lc1 gl_tgt1))

        (SIMGLOBAL: Global.strong_le gl_tgt0 gl_src0)

        (LOCALSRC: Local.wf lc0 gl_src0)
        (LOCALTGT: Local.wf lc0 gl_tgt0)
        (GLOBALSRC: Global.wf gl_src0)
        (GLOBALTGT: Global.wf gl_tgt0)
    :
    (exists gl_src1,
        (<<STEPS: rtc (tau lower_step) (Thread.mk lang st0 lc0 gl_src0) (Thread.mk lang st1 lc1 gl_src1)>>) /\
          (<<SIMGLOBAL: Global.strong_le gl_tgt1 gl_src1>>) /\
          (<<CHERRY: cherrypicked_global (gl_src0, lc0, (gl_tgt0, lc0)) (gl_src1, lc1, (gl_tgt1, lc1))>>)) \/
      (exists st0' st1' lc' gl' e_failure,
          (<<STEPS: rtc (tau lower_step) (Thread.mk lang st0 lc0 gl_src0) (Thread.mk lang st0' lc' gl')>>) /\
            (<<STEP: Thread.step e_failure (Thread.mk lang st0' lc' gl') (Thread.mk lang st1' lc' gl')>>) /\
            (<<EVENT: ThreadEvent.get_machine_event e_failure = MachineEvent.failure>>)).
  Proof.
    remember (Thread.mk _ st0 lc0 gl_tgt0).
    remember (Thread.mk _ st1 lc1 gl_tgt1).
    revert st0 st1 lc0 lc1 gl_tgt0 gl_src0 gl_tgt1 Heqt Heqt0 SIMGLOBAL LOCALSRC LOCALTGT GLOBALSRC GLOBALTGT.
    induction STEPS; i; clarify.
    { left. esplits; eauto. refl. }
    inv H. destruct y.
    hexploit lower_step_future; eauto. i. des.
    hexploit lower_step_strong_future; eauto. i. des.
    2:{ right. esplits; eauto. }
    hexploit lower_step_future; eauto. i. des. ss.
    hexploit IHSTEPS; eauto. i. des.
    { left. esplits.
      { econs 2; [|eauto]. econs; eauto. rewrite EVENT0. auto. }
      { auto. }
      { des_ifs. des. subst. splits; auto; i; try by (etrans; eauto). }
    }
    { right. esplits.
      { econs 2; [|eauto]. econs; eauto. rewrite EVENT0. auto. }
      { eauto. }
      { eauto. }
    }
  Qed.
End LOWERMEM.
