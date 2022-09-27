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


Definition non_sc (e: ThreadEvent.t): Prop :=
  ~ ThreadEvent.is_sc e /\ ThreadEvent.get_machine_event e = MachineEvent.silent.
#[export] Hint Unfold non_sc: core.

Definition strict_pf (e: ThreadEvent.t): Prop :=
  ThreadEvent.is_pf e  /\ ~ ThreadEvent.is_racy_promise e.
#[export] Hint Unfold strict_pf: core.


Module PFConsistent.
  Section PFConsistent.
    Variable lang: language.

    Variant pf_consistent (th: Thread.t lang): Prop :=
      | pf_consistent_failure
          e th1 th2
          (STEPS: rtc (pstep (@Thread.step _) (ThreadEvent.is_pf /1\ non_sc)) (Thread.cap_of th) th1)
          (STEP_FAILURE: Thread.step e th1 th2)
          (EVENT_FAILURE: ThreadEvent.get_machine_event e = MachineEvent.failure)
      | pf_consistent_fulfill
          th2
          (STEPS: rtc (pstep (@Thread.step _) (ThreadEvent.is_pf /1\ non_sc)) (Thread.cap_of th) th2)
          (PROMISES: Local.promises (Thread.local th2) = BoolMap.bot)
    .

    Variant spf_consistent (th: Thread.t lang): Prop :=
      | spf_consistent_failure
          e th1 th2
          (STEPS: rtc (pstep (@Thread.step _) (strict_pf /1\ non_sc)) (Thread.cap_of th) th1)
          (STEP_FAILURE: Thread.step e th1 th2)
          (EVENT_FAILURE: ThreadEvent.get_machine_event e = MachineEvent.failure)
          (EVENT_PF: strict_pf e)
      | spf_consistent_fulfill
          th2
          (STEPS: rtc (pstep (@Thread.step _) (strict_pf /1\ non_sc)) (Thread.cap_of th) th2)
          (PROMISES: Local.promises (Thread.local th2) = BoolMap.bot)
    .

    Variant spf_race (th: Thread.t lang): Prop :=
      | spf_race_intro
          e th1 th2
          (STEPS: rtc (pstep (@Thread.step _) (strict_pf /1\ non_sc)) th th1)
          (STEP_RACE: Thread.step e th1 th2)
          (EVENT_RACE: ThreadEvent.is_racy_promise e)
    .

    Variant non_sc_consistent (th: Thread.t lang): Prop :=
      | non_sc_consistent_failure
          e th1 th2
          (STEPS: rtc (pstep (@Thread.step _) non_sc) (Thread.cap_of th) th1)
          (STEP_FAILURE: Thread.step e th1 th2)
          (EVENT_FAILURE: ThreadEvent.get_machine_event e = MachineEvent.failure)
      | non_sc_consistent_promises
          th2
          (STEPS: rtc (pstep (@Thread.step _) non_sc) (Thread.cap_of th) th2)
          (PROMISES: Local.promises (Thread.local th2) = BoolMap.bot)
    .

    Lemma rtc_tau_step_rtc_non_sc_step
          (th1 th2: Thread.t lang)
          (STEPS: rtc (@Thread.tau_step _) th1 th2):
      exists th2',
        (<<STEPS1: rtc (pstep (@Thread.step _) non_sc) th1 th2'>>) /\
        ((<<TH2: th2' = th2>>) \/
         (<<STEPS2: rtc (@Thread.tau_step _) th2' th2>>) /\
         (<<PROMISES: Local.promises (Thread.local th2') = BoolMap.bot>>)).
    Proof.
      induction STEPS.
      { esplits; eauto. }
      inv H.
      destruct (classic (ThreadEvent.is_sc e)).
      - esplits; [refl|]. right. split.
        + econs 2; eauto. econs; eauto.
        + inv TSTEP; inv LOCAL; ss. inv LOCAL0. auto.
      - des.
        + esplits; [|eauto]. econs 2; eauto.
        + esplits; [|eauto]. econs 2; eauto.
    Qed.

    Lemma consistent_non_sc_consistent
          th
          (CONS: Thread.consistent th):
      non_sc_consistent th.
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

    Variant sim_memory (mem_src mem_tgt: Memory.t): Prop :=
      | sim_memory_intro
          (SOUND: Memory.le mem_src mem_tgt)
          (COMPLETE: Memory.messages_le mem_tgt mem_src)
    .

    #[local] Program Instance sim_memory_PreOrder: PreOrder sim_memory.
    Next Obligation.
      ii. econs; refl.
    Qed.
    Next Obligation.
      ii. inv H. inv H0. econs; etrans; eauto.
    Qed.

    Definition sim_greserves (rsv_src mem_src rsv_tgt mem_tgt: Memory.t): Prop :=
      forall loc from to
             (RSV_SRC: Memory.get loc to rsv_src = None)
             (GRSV_SRC: Memory.get loc to mem_src = Some (from, Message.reserve)),
        (<<RSV_TGT: Memory.get loc to rsv_tgt = None>>) /\
        (<<GRSV_TGT: Memory.get loc to mem_tgt = Some (from, Message.reserve)>>).

    Variant sim_thread (th_src th_tgt: Thread.t lang): Prop :=
      | sim_thread_intro
          (STATE: Thread.state th_src = Thread.state th_tgt)
          (TVIEW: Local.tview (Thread.local th_src) = Local.tview (Thread.local th_tgt))
          (PROMISES: BoolMap.le (Local.promises (Thread.local th_src))
                                (Local.promises (Thread.local th_tgt)))
          (RESERVES: Memory.le (Local.reserves (Thread.local th_src))
                               (Local.reserves (Thread.local th_tgt)))
          (SC: Global.sc (Thread.global th_src) = Global.sc (Thread.global th_tgt))
          (GPROMISES: BoolMap.minus (Global.promises (Thread.global th_src))
                                    (Local.promises (Thread.local th_src)) =
                      BoolMap.minus (Global.promises (Thread.global th_tgt))
                                    (Local.promises (Thread.local th_tgt)))
          (GRESERVES: sim_greserves
                        (Local.reserves (Thread.local th_src))
                        (Global.memory (Thread.global th_src))
                        (Local.reserves (Thread.local th_tgt))
                        (Global.memory (Thread.global th_tgt)))
          (MEMORY: sim_memory
                     (Global.memory (Thread.global th_src))
                     (Global.memory (Thread.global th_tgt)))
    .

    #[local] Program Instance sim_thread_PreOrder: PreOrder sim_thread.
    Next Obligation.
      ii. econs; ii; eauto; try refl.
    Qed.
    Next Obligation.
      ii. inv H. inv H0. econs; try by (etrans; eauto).
      ii. exploit GRESERVES; eauto. i. des. eauto.
    Qed.

    Lemma sim_memory_add
      rsv_src rsv_tgt
      mem1_src mem1_tgt
      loc from to msg mem2_tgt
      (MEM1: sim_memory mem1_src mem1_tgt)
      (GRESERVES1: sim_greserves rsv_src mem1_src rsv_tgt mem1_tgt)
      (ADD_TGT: Memory.add mem1_tgt loc from to msg mem2_tgt)
      (MSG: msg <> Message.reserve):
      exists mem2_src,
        (<<ADD_SRC: Memory.add mem1_src loc from to msg mem2_src>>) /\
        (<<MEM2: sim_memory mem2_src mem2_tgt>>) /\
        (<<GRESERVES2: sim_greserves rsv_src mem2_src rsv_tgt mem2_tgt>>).
    Proof.
      inv MEM1.
      exploit (@Memory.add_exists mem1_src loc from to msg); i.
      { exploit SOUND; eauto. i.
        exploit Memory.add_get1; eauto. i.
        exploit Memory.add_get0; eauto. i. des.
        exploit Memory.get_disjoint; [exact x1|exact GET0|].
        i. des; subst; try congr.
        symmetry. ss.
      }
      { inv ADD_TGT. inv ADD. ss. }
      { inv ADD_TGT. inv ADD. ss. }
      des. esplits; eauto.
      - econs; ii.
        + erewrite Memory.add_o; eauto.
          revert LHS. erewrite Memory.add_o; try exact x0.
          condtac; ss; eauto.
        + erewrite Memory.add_o; eauto.
          revert LHS. erewrite Memory.add_o; try exact ADD_TGT.
          condtac; ss; eauto.
      - ii. erewrite (@Memory.add_o mem2_tgt); eauto.
        revert GRSV_SRC. erewrite (@Memory.add_o mem2); eauto.
        condtac; ss; eauto. i. des. inv GRSV_SRC.
        exploit Memory.add_get0; try exact x0. i. des. congr.
    Qed.

    Lemma sim_memory_reserve
      rsv1_src mem1_src
      rsv1_tgt mem1_tgt
      loc from to rsv2_tgt mem2_tgt
      (MEM1: sim_memory mem1_src mem1_tgt)
      (RESERVES1: Memory.le rsv1_src rsv1_tgt)
      (GRESERVES1: sim_greserves rsv1_src mem1_src rsv1_tgt mem1_tgt)
      (RESERVE_TGT: Memory.reserve rsv1_tgt mem1_tgt loc from to rsv2_tgt mem2_tgt):
      (<<MEM2: sim_memory mem1_src mem2_tgt>>) /\
      (<<RESERVES2: Memory.le rsv1_src rsv2_tgt>>) /\
      (<<GRESERVES2: sim_greserves rsv1_src mem1_src rsv1_tgt mem2_tgt>>).
    Proof.
      inv MEM1. inv RESERVE_TGT.
      hexploit Memory.add_le; try exact MEM. i.
      hexploit Memory.le_messages_le; eauto. i.
      splits.
      - econs; try by (etrans; eauto).
        ii. revert LHS. erewrite Memory.add_o; eauto.
        condtac; ss; eauto.
      - etrans; eauto using Memory.add_le.
      - ii. exploit GRESERVES1; eauto. i. des. splits; ss.
        erewrite Memory.add_o; eauto.
        condtac; ss; eauto. des. subst.
        exploit Memory.add_get0; try exact MEM. i. des. congr.
    Qed.

    Lemma sim_memory_cancel
      rsv1_src mem1_src
      rsv1_tgt mem1_tgt
      loc from to rsv2_tgt mem2_tgt
      (MEM1: sim_memory mem1_src mem1_tgt)
      (RESERVES1: Memory.le rsv1_src rsv1_tgt)
      (GRESERVES1: sim_greserves rsv1_src mem1_src rsv1_tgt mem1_tgt)
      (LE1_SRC: Memory.le rsv1_src mem1_src)
      (CANCEL_TGT: Memory.cancel rsv1_tgt mem1_tgt loc from to rsv2_tgt mem2_tgt):
      (<<MEM2: sim_memory mem1_src mem2_tgt>>) /\
      (<<RESERVES2: Memory.le rsv1_src rsv2_tgt>>) /\
      (<<GRESERVES2: sim_greserves rsv1_src mem1_src rsv1_tgt mem2_tgt>>) \/
      exists rsv2_src mem2_src,
        (<<CANCEL_SRC: Memory.cancel rsv1_src mem1_src loc from to rsv2_src mem2_src>>) /\
        (<<MEM2: sim_memory mem2_src mem2_tgt>>) /\
        (<<RESERVES2: Memory.le rsv2_src rsv2_tgt>>) /\
        (<<GRESERVES2: sim_greserves rsv2_src mem2_src rsv2_tgt mem2_tgt>>).
    Proof.
      inv MEM1. inv CANCEL_TGT.
      destruct (Memory.get loc to rsv1_src) as [[]|] eqn:RSV_SRC.
      { right.
        exploit Memory.remove_get0; try exact RSV. i. des.
        exploit RESERVES1; eauto. i.
        rewrite x0 in *. inv GET.
        exploit LE1_SRC; eauto. i.
        exploit Memory.remove_exists; try exact RSV_SRC. i. des.
        exploit Memory.remove_exists; try exact x1. i. des.
        esplits; eauto; ii.
        - econs; ii.
          + erewrite Memory.remove_o; eauto.
            revert LHS. erewrite Memory.remove_o; try exact x3.
            condtac; ss; eauto.
          + erewrite Memory.remove_o; eauto.
            revert LHS. erewrite Memory.remove_o; try exact MEM.
            condtac; ss; eauto.
        - erewrite Memory.remove_o; eauto.
          revert LHS. erewrite Memory.remove_o; try exact x2.
          condtac; ss; eauto.
        - erewrite Memory.remove_o in RSV_SRC0; eauto.
          erewrite Memory.remove_o in GRSV_SRC; eauto.
          des_ifs. ss. guardH o.
          exploit GRESERVES1; eauto. i. des.
          exploit Memory.remove_get1; try exact GRSV_TGT; eauto. i. des; try congr.
          splits; ss.
          erewrite Memory.remove_o; eauto. condtac; ss.
      }
      { left.
        destruct (Memory.get loc to mem1_src) as [[]|] eqn:GRSV_SRC.
        { exploit Memory.remove_get0; try exact RSV. i. des.
          exploit Memory.remove_get0; try exact MEM. i. des.
          exploit SOUND; eauto. i.
          rewrite x0 in *. inv GET1.
          exploit GRESERVES1; eauto. i. des. congr.
        }
        splits; ii.
        - hexploit Memory.remove_le; try exact MEM. i.
          hexploit Memory.le_messages_le; try exact H. i.
          econs; try by (etrans; eauto). ii.
          erewrite Memory.remove_o; eauto. condtac; ss; eauto.
          des. subst. congr.
        - erewrite Memory.remove_o; eauto. condtac; ss; eauto.
          des. subst. congr.
        - exploit GRESERVES1; eauto. i. des.
          erewrite (@Memory.remove_o mem2_tgt); eauto. condtac; ss.
          des. subst. congr.
      }
    Qed.

    (* TODO *)

    Lemma sim_thread_non_pf_step
          th1_src
          e th1_tgt th2_tgt
          (SIM1: sim_thread th1_src th1_tgt)
          (STEP_TGT: Thread.step e th1_tgt th2_tgt)
          (EVENT: ~ ThreadEvent.is_pf e):
      sim_thread th1_src th2_tgt.
    Proof.
      inv SIM1. inv STEP_TGT; inv LOCAL; ss.
      - inv LOCAL0. econs; ss.
        + etrans; eauto.
          inv PROMISE. eauto using BoolMap.add_le.
        + rewrite GPROMISES.
          eauto using Promises.promise_minus.
        + rewrite GPROMISES_INV.
          eauto using Promises.promise_minus_inv.
      - inv LOCAL0. inv RESERVE. econs; ss.
        + hexploit Memory.add_le; try exact RSV. i. etrans; eauto.
        + inv MEMORY.
          hexploit Memory.add_le; try exact MEM. i.
          hexploit Memory.le_messages_le; try exact H. i.
          econs; try by (etrans; eauto).
          ii. revert LHS. erewrite Memory.add_o; eauto.
          condtac; ss; eauto.
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

    Lemma sim_fulfill
          prm1_src gprm1_src
          prm1_tgt gprm1_tgt loc ord prm2_tgt gprm2_tgt
          (PROMISES: BoolMap.le prm1_src prm1_tgt)
          (GPROMISES: BoolMap.minus gprm1_src prm1_src = BoolMap.minus gprm1_tgt prm1_tgt)
          (GPROMISES_INV: BoolMap.minus prm1_src gprm1_src = BoolMap.minus prm1_tgt gprm1_tgt)
          (FULFILL_TGT: Promises.fulfill prm1_tgt gprm1_tgt loc ord prm2_tgt gprm2_tgt):
      exists prm2_src gprm2_src,
        (<<FULFILL_SRC: Promises.fulfill prm1_src gprm1_src loc ord prm2_src gprm2_src>>) /\
        (<<PROMISES: BoolMap.le prm2_src prm2_tgt>>) /\
        (<<GPROMISES: BoolMap.minus gprm2_src prm2_src = BoolMap.minus gprm2_tgt prm2_tgt>>) /\
        (<<GPROMISES_INV: BoolMap.minus prm2_src gprm2_src = BoolMap.minus prm2_tgt gprm2_tgt>>).
    Proof.
      inv FULFILL_TGT.
      { esplits; [econs 1|..]; eauto. }
      exploit BoolMap.remove_get0; try exact REMOVE. i. des.
      exploit BoolMap.remove_get0; try exact GREMOVE. i. des.
      destruct (prm1_src loc) eqn:GET_SRC.
      - destruct (gprm1_src loc) eqn:GGET_SRC; cycle 1.
        { unfold BoolMap.minus in *.
          eapply equal_f in GPROMISES_INV.
          rewrite GET1, GET0, GET_SRC, GGET_SRC in GPROMISES_INV. ss.
        }
        exploit BoolMap.remove_exists; try exact GET_SRC. i. des.
        exploit BoolMap.remove_exists; try exact GGET_SRC. i. des.
        esplits; [econs 2|..]; eauto using BoolMap.le_remove.
        + erewrite <- BoolMap.remove_minus; try exact x0; try exact x1.
          rewrite GPROMISES. eauto using BoolMap.remove_minus.
        + erewrite <- BoolMap.remove_minus; try exact x0; try exact x1.
          rewrite GPROMISES_INV. eauto using BoolMap.remove_minus.
      - destruct (gprm1_src loc) eqn:GGET_SRC.
        { unfold BoolMap.minus in *.
          eapply equal_f in GPROMISES.
          rewrite GET1, GET0, GET_SRC, GGET_SRC in GPROMISES. ss.
        }
        esplits; [econs 1|..]; eauto.
        + ii. exploit PROMISES; eauto. i.
          inv REMOVE. unfold LocFun.add. condtac; ss. congr.
        + extensionality x. unfold BoolMap.minus in *.
          inv REMOVE. inv GREMOVE. unfold LocFun.add. condtac; ss.
          * subst. rewrite GET_SRC, GGET_SRC. ss.
          * eapply equal_f in GPROMISES. rewrite GPROMISES. ss.
        + extensionality x. unfold BoolMap.minus in *.
          inv REMOVE. inv GREMOVE. unfold LocFun.add. condtac; ss.
          * subst. rewrite GET_SRC, GGET_SRC. ss.
          * eapply equal_f in GPROMISES_INV. rewrite GPROMISES_INV. ss.
    Qed.

    Lemma sim_thread_pf_step
          th1_src
          e th1_tgt th2_tgt
          (SIM1: sim_thread th1_src th1_tgt)
          (STEP_TGT: Thread.step e th1_tgt th2_tgt)
          (NONSC: ~ ThreadEvent.is_sc e):
      exists th2_src,
        (<<STEP_SRC: Thread.step e th1_src th2_src>>) /\
        (<<SIM2: sim_thread th2_src th2_tgt>>).
    Proof.
      destruct th1_src as [st1_src [tview1_src prm1_src rsv1_src] [sc1_src gprm1_src mem1_src]],
          th1_tgt as [st1_tgt [tview1_tgt prm1_tgt rsv1_tgt] [sc1_tgt gprm1_tgt mem1_tgt]].
      inv SIM1. ss. subst.
      inv STEP_TGT. inv LOCAL; ss.
      { (* silent *)
        esplits.
        - econs; [|econs 1]; eauto.
        - ss.
      }
      { (* read *)
        inv LOCAL0. ss.
        esplits.
        - econs; [|econs 2]; eauto.
        - ss.
      }
      { (* write *)
        inv LOCAL0. ss.
        exploit sim_fulfill; try exact FULFILL; eauto. i. des.
        esplits.
        - econs; [|econs 3]; eauto.
          econs; s; eauto.
          i. des. apply RESERVED.
          destruct (rsv1_tgt loc) eqn:RSV.
          + apply RESERVES in RSV. congr.
          + exploit GRESERVES; eauto.
        - econs; ss.
      }
      { (* update *)
        inv LOCAL1. inv LOCAL2. ss.
        exploit sim_fulfill; try exact FULFILL; eauto. i. des.
        esplits.
        - econs; [|econs 4]; eauto.
          econs; s; eauto.
          i. des. apply RESERVED.
          destruct (rsv1_tgt loc) eqn:RSV.
          + apply RESERVES in RSV. congr.
          + exploit GRESERVES; eauto.
        - econs; ss.
      }
      { (* fence *)
        inv LOCAL0. ss.
        esplits.
        - econs; [|econs 5]; eauto. econs; ss.
        - ss.
      }
      { (* failure *)
        inv LOCAL0. ss.
        esplits.
        - econs; [|econs 7]; eauto.
        - ss.
      }
      { (* racy read *)
        inv LOCAL0. ss.
        esplits.
        - econs; [|econs 8]; eauto.
          econs. eapply sim_is_racy; try eapply RACE; ss.
        - ss.
      }
      { (* racy write *)
        inv LOCAL0. ss.
        esplits.
        - econs; [|econs 9]; eauto.
          econs. eapply sim_is_racy; try eapply RACE; ss.
        - ss.
      }
      { (* racy update *)
        esplits.
        - econs; [|econs 10]; eauto.
          inv LOCAL0.
          + econs 1. ss.
          + econs 2. ss.
          + econs 3. eapply sim_is_racy; try eapply RACE; ss.
        - ss.
      }
    Qed.

    Lemma sim_thread_rtc_non_sc_step
          reserved
          th1_src
          th1_tgt th2_tgt
          (SIM1: sim_thread th1_src th1_tgt)
          (STEPS_TGT: rtc (pstep (Thread.step_allpf reserved) non_sc) th1_tgt th2_tgt):
      exists th2_src,
        (<<STEPS_SRC: rtc (pstep (Thread.step reserved true) non_sc) th1_src th2_src>>) /\
        (<<SIM2: sim_thread th2_src th2_tgt>>).
    Proof.
      revert th1_src SIM1.
      induction STEPS_TGT; eauto; i.
      inv H. inv STEP.
      destruct pf; eauto using sim_thread_internal_step.
      exploit sim_thread_program_step; try exact SIM1; eauto.
      { ii. apply EVENT in H. ss. }
      i. des.
      exploit IHSTEPS_TGT; eauto. i. des.
      esplits; [econs 2|]; eauto.
    Qed.

    Lemma non_sc_consistent_pf_consistent_aux
          reserved th_src th_tgt
          (SIM: sim_thread th_src th_tgt)
          (CONS: non_sc_consistent reserved th_tgt):
      pf_consistent_aux reserved th_src.
    Proof.
      inv CONS.
      - exploit sim_thread_rtc_non_sc_step; eauto. i. des.
        destruct pf; cycle 1.
        { inv STEP_FAILURE. inv LOCAL; ss. }
        exploit sim_thread_program_step; try exact SIM2; eauto.
        { destruct e; ss. }
        i. des.
        econs 1; eauto.
      - exploit sim_thread_rtc_non_sc_step; eauto. i. des.
        econs 2; eauto.
        inv SIM2. rewrite PROMISES in *.
        extensionality x. specialize (PROMISES0 x).
        destruct (Local.promises (Thread.local th2_src) x); ss; auto.
        exploit PROMISES0; eauto.
    Qed.

    Lemma pf_consistent_aux_pf_consistent
          th
          (CONS: pf_consistent_aux
                   (Memory.max_timemap (Global.memory (Thread.global th)))
                   (Thread.cap_of th)):
      pf_consistent th.
    Proof.
      inv CONS.
      - econs 1; eauto.
      - econs 2; eauto.
    Qed.

    Lemma consistent_pf_consistent
          th
          (CONS: Thread.consistent th):
      pf_consistent th.
    Proof.
      apply pf_consistent_aux_pf_consistent.
      eapply non_sc_consistent_pf_consistent_aux;
        try apply fully_reserved_sim_thread.
      apply consistent_non_sc_consistent. auto.
    Qed.

    Lemma rtc_pf_steps_rtc_spf_steps
          reserved th1 th2
          (STEPS: rtc (pstep (Thread.step reserved true) non_sc) th1 th2):
      (<<SPF_STEPS: rtc (pstep (Thread.step reserved true) (strict_pf /1\ non_sc)) th1 th2>>) \/
      (<<SPF_RACE: spf_race reserved th1>>).
    Proof.
      induction STEPS; eauto.
      inv H. destruct (classic (ThreadEvent.is_racy_promise e)).
      { right. econs; eauto. }
      des.
      - left. econs 2; eauto.
      - right. inv SPF_RACE.
        econs; [econs 2|..]; eauto.
    Qed.

    Lemma pf_consistent_spf_consistent
          th
          (CONS: pf_consistent th):
      (<<SPF_CONS: spf_consistent th>>) \/
      (<<SPF_RACE: spf_race
                     (Memory.max_timemap (Global.memory (Thread.global th)))
                     (Thread.cap_of th)>>).
    Proof.
      inv CONS.
      - exploit rtc_pf_steps_rtc_spf_steps; eauto. i. des; eauto.
        destruct (classic (ThreadEvent.is_racy_promise e)).
        + right. econs; eauto.
        + left. econs 1; eauto.
      - exploit rtc_pf_steps_rtc_spf_steps; eauto. i. des; eauto.
        left. econs 2; eauto.
    Qed.
  End PFConsistent.
End PFConsistent.
