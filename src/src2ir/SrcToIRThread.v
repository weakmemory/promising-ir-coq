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
Require Import Configuration.
Require Import PFConfiguration.
Require Import Behavior.

Require Import PFConsistent.

Set Implicit Arguments.


Module SrcToIRThread.
  Section SrcToIRThread.
    Variable lang: language.

    Variant sim_memory (mem_pf mem_ir: Memory.t): Prop :=
      | sim_memory_intro
          (SOUND: Memory.le mem_pf mem_ir)
          (COMPLETE: Memory.messages_le mem_ir mem_pf)
          (GRESERVES: forall loc from to msg
                        (GET: Memory.get loc to mem_pf = Some (from, msg)),
              msg <> Message.reserve)
    .
    #[local] Hint Constructors sim_memory: core.

    Lemma init_sim_memory: sim_memory Memory.init Memory.init.
    Proof.
      econs; ss. i.
      exploit Memory.init_get; eauto. i. des. subst. ss.
    Qed.

    Variant sim_thread (th_pf th_ir: Thread.t lang): Prop :=
      | sim_thread_intro
          (STATE: Thread.state th_pf = Thread.state th_ir)
          (TVIEW: Local.tview (Thread.local th_pf) = Local.tview (Thread.local th_ir))
          (PROMISES: Local.promises (Thread.local th_pf) = BoolMap.bot)
          (RESERVES: Local.reserves (Thread.local th_pf) = Memory.bot)
          (SC: Global.sc (Thread.global th_pf) = Global.sc (Thread.global th_ir))
          (GPROMISES: Global.promises (Thread.global th_pf) = BoolMap.bot)
          (MEMORY: sim_memory (Global.memory (Thread.global th_pf)) (Global.memory (Thread.global th_ir)))
    .
    #[local] Hint Constructors sim_thread: core.

    Lemma sim_memory_cap
          mem_pf mem_ir
          (SIM: sim_memory mem_pf mem_ir):
      sim_memory mem_pf (Memory.cap_of mem_ir).
    Proof.
      specialize (Memory.cap_of_cap mem_ir). i.
      inv SIM. econs; ii; eauto.
      - inv H. eauto.
      - exploit Memory.cap_inv; eauto. i. des; ss. eauto.
      - eapply GRESERVES; eauto.
    Qed.

    Lemma sim_thread_cap
          th_pf th_ir
          (SIM: SrcToIRThread.sim_thread th_pf th_ir):
      SrcToIRThread.sim_thread th_pf (Thread.cap_of th_ir).
    Proof.
      inv SIM. econs; ss.
      eapply sim_memory_cap; eauto.
    Qed.

    Lemma sim_memory_add
          mem1_pf mem1_ir
          loc from to msg mem2_ir
          (MEM1: sim_memory mem1_pf mem1_ir)
          (ADD_IR: Memory.add mem1_ir loc from to msg mem2_ir)
          (MSG: msg <> Message.reserve):
      exists mem2_pf,
        (<<ADD_PF: Memory.add mem1_pf loc from to msg mem2_pf>>) /\
        (<<MEM2: sim_memory mem2_pf mem2_ir>>).
    Proof.
      inv MEM1.
      exploit (@Memory.add_exists mem1_pf loc from to msg); i.
      { exploit SOUND; eauto. i.
        exploit Memory.add_get1; eauto. i.
        exploit Memory.add_get0; eauto. i. des.
        exploit Memory.get_disjoint; [exact x1|exact GET0|].
        i. des; subst; try congr.
        symmetry. ss.
      }
      { inv ADD_IR. inv ADD. ss. }
      { inv ADD_IR. inv ADD. ss. }
      des. esplits; eauto. econs; ii.
      - erewrite Memory.add_o; eauto.
        revert LHS. erewrite Memory.add_o; try exact x0.
        condtac; ss; eauto.
      - erewrite Memory.add_o; eauto.
        revert LHS. erewrite Memory.add_o; try exact ADD_IR.
        condtac; ss; eauto.
      - subst. revert GET.
        erewrite Memory.add_o; eauto. condtac; ss; i.
        + des. inv GET. ss.
        + eapply GRESERVES; eauto.
    Qed.

    Lemma sim_memory_reserve
          mem1_pf
          rsv1_ir mem1_ir
          loc from to rsv2_ir mem2_ir
          (MEM1: sim_memory mem1_pf mem1_ir)
          (RESERVE_IR: Memory.reserve rsv1_ir mem1_ir loc from to rsv2_ir mem2_ir):
      (<<MEM2: sim_memory mem1_pf mem2_ir>>).
    Proof.
      inv MEM1. inv RESERVE_IR. econs; ii.
      - erewrite Memory.add_o; eauto.
        condtac; ss; eauto. des. subst.
        exploit SOUND; eauto. i.
        exploit Memory.add_get0; try exact MEM. i. des. congr.
      - revert LHS. erewrite Memory.add_o; eauto.
        condtac; ss; eauto.
      - eapply GRESERVES; eauto.
    Qed.

    Lemma sim_memory_cancel
          mem1_pf
          rsv1_ir mem1_ir
          loc from to rsv2_ir mem2_ir
          (MEM1: sim_memory mem1_pf mem1_ir)
          (CANCEL_IR: Memory.cancel rsv1_ir mem1_ir loc from to rsv2_ir mem2_ir):
      (<<MEM2: sim_memory mem1_pf mem2_ir>>).
    Proof.
      inv MEM1. inv CANCEL_IR. econs; ii.
      - erewrite Memory.remove_o; eauto.
        condtac; ss; eauto. des. subst.
        exploit SOUND; eauto. i.
        exploit Memory.remove_get0; try exact MEM. i. des.
        rewrite GET in *. inv x0.
        exploit GRESERVES; eauto. ss.
      - revert LHS. erewrite Memory.remove_o; eauto.
        condtac; ss; eauto.
      - eapply GRESERVES; eauto.
    Qed.

    Lemma sim_is_racy
          lc_src gl_src lc_tgt gl_tgt
          loc to ord
          (TVIEW: Local.tview lc_src = Local.tview lc_tgt)
          (MEMORY: sim_memory (Global.memory gl_src) (Global.memory gl_tgt))
          (RACE_TGT: Local.is_racy lc_tgt gl_tgt loc (Some to) ord):
      Local.is_racy lc_src gl_src loc (Some to) ord.
    Proof.
      inv RACE_TGT.
      inv MEMORY. exploit COMPLETE; eauto. i.
      econs 2; eauto. congr.
    Qed.

    Lemma sim_thread_internal_step
          th1_pf th1_ir
          e th2_ir
          (SIM1: sim_thread th1_pf th1_ir)
          (STEP: Thread.step e th1_ir th2_ir)
          (EVENT: ThreadEvent.is_internal e):
      <<SIM2: sim_thread th1_pf th2_ir>>.
    Proof.
      inv SIM1. inv STEP; inv LOCAL; ss; inv LOCAL0; ss.
      - exploit sim_memory_reserve; eauto.
      - exploit sim_memory_cancel; eauto.
    Qed.

    Lemma sim_thread_step
          th1_pf th1_ir
          e_ir th2_ir
          (SIM1: sim_thread th1_pf th1_ir)
          (STEP: Thread.step e_ir th1_ir th2_ir)
          (PF: ~ ThreadEvent.is_racy_promise e_ir):
      exists e_pf th2_pf,
        (<<STEP_PF: Thread.opt_step e_pf th1_pf th2_pf>>) /\
        (<<EVENT_PF: ThreadEvent.is_program e_pf>>) /\
        (<<EVENT: __guard__ (
                      e_pf = ThreadEvent.silent /\ ThreadEvent.is_internal e_ir \/
                      e_pf = e_ir)>>) /\
        (<<SIM2: sim_thread th2_pf th2_ir>>).
    Proof.
      unguard.
      destruct th1_ir as [st1_ir [tview1_ir prm1_ir rsv1_ir] [sc1_ir gprm1_ir mem1_ir]],
          th1_pf as [st1_pf [tview1_pf prm1_pf rsv1_pf] [sc1_pf gprm1_pf mem1_pf]].
      inv SIM1. ss. subst.
      inv STEP; inv LOCAL; ss.
      { (* promise *)
        inv LOCAL0. ss.
        esplits; [econs 1|..]; eauto; ss.
      }
      { (* reserve *)
        inv LOCAL0. ss.
        exploit sim_memory_reserve; try exact RESERVE; eauto. i. des.
        esplits; [econs 1|..]; eauto; ss.
      }
      { (* cancel *)
        inv LOCAL0. ss.
        exploit sim_memory_cancel; try exact RESERVE; eauto. i. des.
        esplits; [econs 1|..]; eauto; ss.
      }
      { (* silent *)
        esplits.
        - econs 2. econs 2; [|econs 1]; eauto.
        - ss.
        - right. ss.
        - ss.
      }
      { (* read *)
        inv LOCAL0. ss.
        dup MEMORY. inv MEMORY0. exploit COMPLETE; eauto. i.
        esplits.
        - econs 2. econs 2; [|econs 2]; eauto.
        - ss.
        - right. ss.
        - ss.
      }
      { (* write *)
        inv LOCAL0. ss.
        exploit sim_memory_add; try exact WRITE; eauto; ss. i. des.
        esplits.
        - econs 2. econs 2; [|econs 3]; eauto.
        - ss.
        - right. ss.
        - ss.
      }
      { (* update *)
        inv LOCAL1. inv LOCAL2. ss.
        dup MEMORY. inv MEMORY0. exploit COMPLETE; eauto. i.
        exploit sim_memory_add; try exact WRITE; eauto; ss. i. des.
        esplits.
        - econs 2. econs 2; [|econs 4]; eauto.
        - ss.
        - right. ss.
        - ss.
      }
      { (* fence *)
        inv LOCAL0. ss.
        esplits.
        - econs 2. econs 2; [|econs 5]; eauto.
        - ss.
        - right. ss.
        - ss.
      }
      { (* syscall *)
        inv LOCAL0. ss.
        esplits.
        - econs 2. econs 2; [|econs 6]; eauto.
        - ss.
        - right. ss.
        - ss.
      }
      { (* failure *)
        inv LOCAL0. ss.
        esplits.
        - econs 2. econs 2; [|econs 7]; eauto.
        - ss.
        - right. ss.
        - ss.
      }
      { (* racy read *)
        inv LOCAL0. destruct to; ss.
        esplits.
        - econs 2. econs 2; [|econs 8]; eauto.
          econs. eapply sim_is_racy; try eapply RACE; ss.
        - ss.
        - right. ss.
        - ss.
      }
      { (* racy write *)
        inv LOCAL0. destruct to; ss.
        esplits.
        - econs 2. econs 2; [|econs 9]; eauto.
          econs. eapply sim_is_racy; try eapply RACE; ss.
        - ss.
        - right. ss.
        - ss.
      }
      { (* racy update *)
        destruct to; ss.
        - esplits.
          + econs 2. econs 2; [|econs 10]; eauto.
            inv LOCAL0. econs 3.
            eapply sim_is_racy; try eapply RACE; ss.
          + ss.
          + right. ss.
          + ss.
        - esplits.
          + econs 2. econs 2; [|econs 10]; eauto.
            apply not_and_or in PF. des.
            * econs 1; ss. destruct ordr; ss.
            * econs 2; ss. destruct ordw; ss.
          + ss.
          + right. ss.
          + ss.
      }
    Qed.

    Lemma rtc_tau_step_cases
          th1 th2
          (STEPS: rtc (@Thread.tau_step lang) th1 th2):
      (<<STEPS: rtc (pstep (@Thread.step _)
                           (fun e => ~ ThreadEvent.is_racy_promise e /\ ThreadEvent.is_silent e))
                    th1 th2>>) \/
      exists th e th2,
        (<<STEPS: rtc (pstep (@Thread.step _)
                             (fun e => ~ ThreadEvent.is_racy_promise e /\ ThreadEvent.is_silent e))
                      th1 th>>) /\
        (<<STEP_RACE: Thread.step e th th2>>) /\
        (<<EVENT_RACE: ThreadEvent.is_racy_promise e>>).
    Proof.
      induction STEPS; eauto. inv H.
      destruct (classic (ThreadEvent.is_racy_promise e)).
      - right. esplits; try exact STEP; eauto.
      - des.
        + left. econs 2; eauto.
        + right. esplits; try exact STEP_RACE; eauto.
    Qed.

    Lemma plus_step_cases
          th1 th2 e th3
          (STEPS: rtc (@Thread.tau_step lang) th1 th2)
          (STEP: Thread.step e th2 th3):
      (<<STEPS: rtc (pstep (@Thread.step _)
                           (fun e => ~ ThreadEvent.is_racy_promise e /\ ThreadEvent.is_silent e))
                    th1 th2>>) /\
      (<<EVENT: ~ ThreadEvent.is_racy_promise e>>) \/
      exists th e th2,
        (<<STEPS: rtc (pstep (@Thread.step _)
                             (fun e => ~ ThreadEvent.is_racy_promise e /\ ThreadEvent.is_silent e))
                      th1 th>>) /\
        (<<STEP_RACE: Thread.step e th th2>>) /\
        (<<EVENT_RACE: ThreadEvent.is_racy_promise e>>).
    Proof.
      exploit rtc_tau_step_cases; try exact STEPS. i. des.
      - destruct (classic (ThreadEvent.is_racy_promise e)).
        + right. esplits; eauto.
        + left. eauto.
      - right. esplits; eauto.
    Qed.

    Lemma sim_thread_rtc_step
          th1_pf th1_ir
          th2_ir
          (SIM1: sim_thread th1_pf th1_ir)
          (STEPS: rtc (pstep (@Thread.step _)
                             (fun e => ~ ThreadEvent.is_racy_promise e /\ ThreadEvent.is_silent e))
                      th1_ir th2_ir):
      exists th2_pf,
        (<<STEPS_PF: rtc (pstep (@Thread.step _)
                                (fun e => ThreadEvent.is_program e /\ ThreadEvent.is_silent e))
                         th1_pf th2_pf>>) /\
        (<<SIM2: sim_thread th2_pf th2_ir>>).
    Proof.
      revert th1_pf SIM1.
      induction STEPS; i; eauto.
      inv H. des.
      exploit sim_thread_step; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      inv STEP_PF; eauto.
      esplits; try exact SIM0.
      econs 2; eauto. econs; eauto. split; ss.
      unguard. des; subst; ss.
    Qed.
  End SrcToIRThread.
End SrcToIRThread.
