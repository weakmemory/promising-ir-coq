Require Import RelationClasses.

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
(* Require Import MemoryFacts. *)
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Behavior.
Require Import Global.
Require Import BoolMap.
Require Import Promises.

Require Import Cover.
(* Require Import MemorySplit. *)
(* Require Import MemoryMerge. *)
(* Require Import FulfillStep. *)
(* Require Import PromiseConsistent. *)
Require Import MemoryProps.

Require Import Program.

(* Require Import Pred. *)
Require Import Delayed.
Require Import LowerMemory.
Require Import DelayedStep.
Require Import DelayedSimulation.
Require Import LowerStep.
(* Require Import NALoc. *)

Set Implicit Arguments.



Section WORLD.

Variable world: Type.
Context `{M: PCM.t}.

Variable world_messages_le: Messages.t -> Messages.t -> BoolMap.t -> BoolMap.t -> PCM.car -> (world * PCM.car) -> (world * PCM.car) -> Prop.
Context `{world_messages_le_PreOrder: forall msgs_src msgs_tgt gown_src gown_tgt ctx, PreOrder (world_messages_le msgs_src msgs_tgt gown_src gown_tgt ctx)}.

Hypothesis world_messages_le_mon:
  forall msgs_src0 msgs_tgt0 msgs_src1 msgs_tgt1
         gown_src0 gown_tgt0 gown_src1 gown_tgt1
         ctx0 ctx1 w0 w1
         (LE: world_messages_le msgs_src1 msgs_tgt1 gown_src1 gown_tgt1 ctx1 w0 w1)
         (MSGSRC: msgs_src0 <4= msgs_src1)
         (MSGTGT: msgs_tgt0 <4= msgs_tgt1)
         (GOWNSRC: BoolMap.le gown_src0 gown_src1)
         (GOWNTGT: BoolMap.le gown_tgt0 gown_tgt1)
         (CTX: PCM.extends ctx0 ctx1),
    world_messages_le msgs_src0 msgs_tgt0 gown_src0 gown_tgt0 ctx0 w0 w1.

Hypothesis world_messages_le_frame:
  forall msgs_src msgs_tgt gown_src gown_tgt c0 c1 w0 w1 l0 l1
         (LE: world_messages_le msgs_src msgs_tgt gown_src gown_tgt (PCM.add c0 c1) (w0, l0) (w1, l1)),
    world_messages_le msgs_src msgs_tgt gown_src gown_tgt c0 (w0, PCM.add l0 c1) (w1, PCM.add l1 c1).

Variable sim_global: forall (w: world) (m: PCM.car) (gl_src gl_tgt:Global.t), Prop.


Section LANG.
  Variable lang_src lang_tgt: language.

  Definition sim_thread_wf
             b c w l st_src lc_src gl_src st_tgt lc_tgt gl_tgt :=
    (<<SIM: @DelayedSimulation.sim_thread world M world_messages_le sim_global lang_src lang_tgt b c w l st_src lc_src gl_src st_tgt lc_tgt gl_tgt>>) /\
    (<<LOCALSRC: Local.wf lc_src gl_src>>) /\
    (<<LOCALTGT: Local.wf lc_tgt gl_tgt>>) /\
    (<<MEMSRC: Global.wf gl_src>>) /\
    (<<MEMTGT: Global.wf gl_tgt>>) /\
    (<<MEMORY: b = false -> sim_global w (PCM.add l c) gl_src gl_tgt>>)
  .

  Definition sim_thread_base_flag_mon:
    forall
      b0 b1 c w l st_src lc_src gl_src st_tgt lc_tgt gl_tgt
      (LE: b0 = true -> b1 = true)
      (SIM: @DelayedSimulation.sim_thread world M world_messages_le sim_global lang_src lang_tgt b0 c w l st_src lc_src gl_src st_tgt lc_tgt gl_tgt),
      @DelayedSimulation.sim_thread world M world_messages_le sim_global lang_src lang_tgt b1 c w l st_src lc_src gl_src st_tgt lc_tgt gl_tgt.
  Proof.
    pcofix CIH. i. punfold SIM. pfold. ii. exploit SIM; eauto.
    i. des; eauto. left. splits; auto.
    { ii. exploit RELEASE; eauto. i. des; eauto.
      { esplits; eauto. }
      { esplits; eauto. right. esplits; eauto. inv SIM0; ss. right.
        eapply CIH; eauto.
      }
    }
    { ii. exploit LOWER; eauto. i. des; eauto.
      { esplits; eauto. }
      { esplits; eauto. right. esplits; eauto. inv SIM0; ss. right.
        eapply CIH; eauto.
      }
    }
    { ii. exploit PROMISE; eauto. i. des; eauto.
      { esplits; eauto. }
      { esplits; eauto. right. esplits; eauto.
        { i. eapply gL3. destruct b0, b1; ss. hexploit LE; ss. }
        { inv SIM0; ss. right. eapply CIH; eauto. }
      }
    }
    { ii. exploit CAP; eauto.
      { destruct b0, b1; ss. hexploit LE; ss. }
      { i. rr in x0. subst. rr. des. inv SIM0; ss. esplits; eauto. }
    }
    { ii. exploit FUTURE; eauto.
      { destruct b0, b1; ss. hexploit LE; ss. }
      i. des; eauto.
      { esplits; eauto. }
      { esplits; eauto. right. inv SIM0; ss. esplits; eauto. }
    }
  Qed.

  Lemma sim_thread_flag_mon
        b c w l st_src lc_src gl_src st_tgt lc_tgt gl_tgt
        (SIM: sim_thread_wf b c w l st_src lc_src gl_src st_tgt lc_tgt gl_tgt)
    :
      sim_thread_wf true c w l st_src lc_src gl_src st_tgt lc_tgt gl_tgt.
  Proof.
    red in SIM. des. red. esplits; eauto; ss.
    punfold SIM0. pfold. ii. exploit SIM0; eauto. i. des.
    { left. esplits; eauto; ss.
      ii. exploit PROMISE; eauto. i. des.
      { esplits; eauto. }
      { esplits; eauto. right. esplits; eauto; ss.
        inv SIM; ss. left. eauto. eapply sim_thread_base_flag_mon; [|eauto]. ss. }
    }
    { right. eauto. }
  Qed.

  Lemma steps_steps_failure lang th0 th1
        (STEPS: rtc (@Thread.tau_step lang) th0 th1)
        (FAILURE: Thread.steps_failure th1)
    :
      Thread.steps_failure th0.
  Proof.
    inv FAILURE. econs.
    { etrans; eauto. }
    { eauto. }
    { eauto. }
  Qed.

  Lemma sim_thread_failure_failure
        (w: world) st_src lc_src gl_src
        st_tgt lc_tgt gl_tgt
        (SIM: _sim_thread_failure
                lang_src lang_tgt w st_src lc_src gl_src
                st_tgt lc_tgt gl_tgt)
    :
      Thread.steps_failure (Thread.mk _ st_src lc_src gl_src).
  Proof.
    red in SIM. des. eapply steps_steps_failure; eauto.
  Qed.

  Lemma sim_thread_wf_promise_step
        c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0
        st_tgt1 lc_tgt1 gl_tgt1 b
        (STEP_TGT: Thread.internal_step
                     (Thread.mk _ st_tgt0 lc_tgt0 gl_tgt0)
                     (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1))
        (SIM: sim_thread_wf b c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0)
        (CONS: rtc_consistent (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1))
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 gl_src0)>>) \/
      exists w1 l1 st_src1 lc_src1 gl_src1,
        (<<STEPS: rtc (@Thread.tau_step _)
                      (Thread.mk _ st_src0 lc_src0 gl_src0)
                      (Thread.mk _ st_src1 lc_src1 gl_src1)>>) /\
        (<<SIM: sim_thread_wf b c w1 l1 st_src1 lc_src1 gl_src1 st_tgt1 lc_tgt1 gl_tgt1>>) /\
        (<<WORLD: world_messages_le (unchangable gl_src0.(Global.memory) lc_src0.(Local.reserves)) (unchangable gl_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) (BoolMap.minus gl_src0.(Global.promises) lc_src0.(Local.promises)) (BoolMap.minus gl_tgt0.(Global.promises) lc_tgt0.(Local.promises)) c (w0, l0) (w1, l1)>>).
  Proof.
    red in SIM. des. punfold SIM0.
    exploit Thread.internal_step_future; eauto. i. des. ss.
    exploit SIM0; eauto. i. des; ss.
    2:{ left. eapply sim_thread_failure_failure; eauto. }
    exploit PROMISE; eauto. i. des.
    { left. eapply steps_steps_failure; eauto. }
    hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
    right. inv SIM; ss. esplits.
    { eauto. }
    { red. esplits; eauto. }
    { eauto. }
  Qed.

  Lemma sim_thread_wf_promise_steps
        c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0
        st_tgt1 lc_tgt1 gl_tgt1 b
        (STEP_TGT: rtc (@Thread.internal_step _)
                       (Thread.mk _ st_tgt0 lc_tgt0 gl_tgt0)
                       (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1))
        (SIM: sim_thread_wf b c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0)
        (CONS: rtc_consistent (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1))
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 gl_src0)>>) \/
      exists w1 l1 st_src1 lc_src1 gl_src1,
        (<<STEPS: rtc (@Thread.tau_step _)
                      (Thread.mk _ st_src0 lc_src0 gl_src0)
                      (Thread.mk _ st_src1 lc_src1 gl_src1)>>) /\
        (<<SIM: sim_thread_wf b c w1 l1 st_src1 lc_src1 gl_src1 st_tgt1 lc_tgt1 gl_tgt1>>) /\
        (<<WORLD: world_messages_le (unchangable gl_src0.(Global.memory) lc_src0.(Local.reserves)) (unchangable gl_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) (BoolMap.minus gl_src0.(Global.promises) lc_src0.(Local.promises)) (BoolMap.minus gl_tgt0.(Global.promises) lc_tgt0.(Local.promises)) c (w0, l0) (w1, l1)>>).
  Proof.
    remember (Thread.mk _ st_tgt0 lc_tgt0 gl_tgt0).
    remember (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1).
    revert b w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0
           st_tgt1 lc_tgt1 gl_tgt1 Heqt Heqt0 SIM CONS.
    induction STEP_TGT; i; clarify.
    { right. esplits; eauto.
      { refl. }
    }
    { destruct y.
      hexploit sim_thread_wf_promise_step; eauto.
      { eapply internal_steps_rtc_consistent; eauto. }
      i. des.
      { left. eauto. }
      hexploit IHSTEP_TGT; eauto. i. des.
      { left. eapply steps_steps_failure; eauto. }
      right. esplits.
      { etrans; eauto. }
      { destruct b; eauto. }
      { etrans.
        { eauto. }
        { eapply world_messages_le_mon; eauto.
          { i. eapply unchangable_rtc_tau_step_increase in STEPS; eauto. }
          { i. inv H. eapply unchangable_internal_step in LOCAL; eauto. }
          { apply Thread.rtc_tau_step_promises_minus in STEPS. ss. rewrite STEPS. refl. }
          { inv H. apply Local.internal_step_promises_minus in LOCAL. rewrite LOCAL. refl. }
          { refl. }
        }
      }
    }
  Qed.

  Lemma sim_thread_wf_program_step
        b c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0
        st_tgt1 lc_tgt1 gl_tgt1 e_tgt
        (STEP_TGT: Thread.program_step e_tgt
                                       (Thread.mk _ st_tgt0 lc_tgt0 gl_tgt0)
                                       (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1))
        (SIM: sim_thread_wf b c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0)
        (NRELEASE: ~ release_event e_tgt)
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 gl_src0)>>) \/
      exists w1 l1 st_src1 lc_src1 gl_src1,
        (<<STEPS: rtc (@Thread.tau_step _)
                      (Thread.mk _ st_src0 lc_src0 gl_src0)
                      (Thread.mk _ st_src1 lc_src1 gl_src1)>>) /\
        (<<SIM: sim_thread_wf true c w1 l1 st_src1 lc_src1 gl_src1 st_tgt1 lc_tgt1 gl_tgt1>>) /\
        (<<WORLD: world_messages_le (unchangable gl_src0.(Global.memory) lc_src0.(Local.reserves)) (unchangable gl_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) (BoolMap.minus gl_src0.(Global.promises) lc_src0.(Local.promises)) (BoolMap.minus gl_tgt0.(Global.promises) lc_tgt0.(Local.promises)) c (w0, l0) (w1, l1)>>).
  Proof.
    red in SIM. des.
    hexploit Thread.program_step_future; eauto. i. des. ss.
    punfold SIM0. exploit SIM0; eauto. i. des; ss.
    2:{ left. eapply sim_thread_failure_failure; eauto. }
    exploit LOWER; eauto. i. des.
    { left. eapply steps_steps_failure; eauto. }
    hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
    right. inv SIM; ss. esplits.
    { eauto. }
    { red. esplits; eauto; ss. }
    { eauto. }
  Qed.

  Lemma sim_thread_wf_lower_step
        b c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0
        st_tgt1 lc_tgt1 gl_tgt1 e_tgt
        (STEP_TGT: lower_step e_tgt
                              (Thread.mk _ st_tgt0 lc_tgt0 gl_tgt0)
                              (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1))
        (SIM: sim_thread_wf b c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0)
        (CONS: ThreadEvent.get_machine_event e_tgt = MachineEvent.silent -> rtc_consistent (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1))
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 gl_src0)>>) \/
      exists w1 l1 st_src1 lc_src1 gl_src1,
        (<<STEPS: rtc (@Thread.tau_step _)
                      (Thread.mk _ st_src0 lc_src0 gl_src0)
                      (Thread.mk _ st_src1 lc_src1 gl_src1)>>) /\
        (<<SIM: sim_thread_wf true c w1 l1 st_src1 lc_src1 gl_src1 st_tgt1 lc_tgt1 gl_tgt1>>) /\
        (<<WORLD: world_messages_le (unchangable gl_src0.(Global.memory) lc_src0.(Local.reserves)) (unchangable gl_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) (BoolMap.minus gl_src0.(Global.promises) lc_src0.(Local.promises)) (BoolMap.minus gl_tgt0.(Global.promises) lc_tgt0.(Local.promises)) c (w0, l0) (w1, l1)>>).
  Proof.
    inv STEP_TGT. des; clarify.
    { hexploit sim_thread_wf_program_step; eauto. }
    { inv STEP0; [|inv LOCAL; ss]. hexploit sim_thread_wf_promise_step.
      { econs; eauto. }
      { eauto. }
      { eapply program_step_rtc_consistent; eauto. }
      i. des; eauto.
      hexploit sim_thread_wf_program_step; eauto. i. des.
      { left. eapply steps_steps_failure; eauto. }
      right. esplits.
      { etrans; eauto. }
      { eauto. }
      { etrans.
        { eauto. }
        { eapply world_messages_le_mon; eauto.
          { i. eapply unchangable_rtc_tau_step_increase in STEPS; eauto. }
          { i. eapply unchangable_internal_step in LOCAL; eauto. }
          { apply Thread.rtc_tau_step_promises_minus in STEPS. ss. rewrite STEPS. refl. }
          { apply Local.internal_step_promises_minus in LOCAL. rewrite LOCAL. refl. }
          { refl. }
        }
      }
    }
  Qed.

  Lemma sim_thread_wf_lower_steps
        b c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0
        st_tgt1 lc_tgt1 gl_tgt1
        (STEP_TGT: rtc (tau (@lower_step _))
                       (Thread.mk _ st_tgt0 lc_tgt0 gl_tgt0)
                       (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1))
        (SIM: sim_thread_wf b c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0)
        (CONS: rtc_consistent (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1))
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 gl_src0)>>) \/
      exists w1 l1 st_src1 lc_src1 gl_src1,
        (<<STEPS: rtc (@Thread.tau_step _)
                      (Thread.mk _ st_src0 lc_src0 gl_src0)
                      (Thread.mk _ st_src1 lc_src1 gl_src1)>>) /\
        (<<SIM: sim_thread_wf true c w1 l1 st_src1 lc_src1 gl_src1 st_tgt1 lc_tgt1 gl_tgt1>>) /\
        (<<WORLD: world_messages_le (unchangable gl_src0.(Global.memory) lc_src0.(Local.reserves)) (unchangable gl_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) (BoolMap.minus gl_src0.(Global.promises) lc_src0.(Local.promises)) (BoolMap.minus gl_tgt0.(Global.promises) lc_tgt0.(Local.promises)) c (w0, l0) (w1, l1)>>).
  Proof.
    remember (Thread.mk _ st_tgt0 lc_tgt0 gl_tgt0).
    remember (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1).
    revert b w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0
           st_tgt1 lc_tgt1 gl_tgt1 Heqt Heqt0 SIM.
    induction STEP_TGT; i; clarify.
    { right. esplits; eauto.
      { eapply sim_thread_flag_mon; eauto. }
      { refl. }
    }
    { inv H. destruct y.
      hexploit sim_thread_wf_lower_step; eauto.
      { eapply rtc_implies in STEP_TGT.
        2:{ eapply tau_lower_step_tau_step. }
        eapply rtc_join in STEP_TGT.
        i. eapply tau_steps_rtc_consistent; eauto.
      }
      i. des.
      { left. eauto. }
      hexploit IHSTEP_TGT; eauto. i. des.
      { left. eapply steps_steps_failure; eauto. }
      right. esplits.
      { etrans; eauto. }
      { eauto. }
      { etrans.
        { eauto. }
        { eapply world_messages_le_mon; eauto.
          { i. eapply unchangable_rtc_tau_step_increase in STEPS; eauto. }
          { i. eapply lower_step_step in TSTEP.
            eapply unchangable_rtc_all_step_increase in TSTEP; eauto. }
          { apply Thread.rtc_tau_step_promises_minus in STEPS. ss. rewrite STEPS. refl. }
          { eapply lower_step_step in TSTEP.
            apply Thread.rtc_all_step_promises_minus in TSTEP. ss. rewrite TSTEP. refl. }
          { refl. }
        }
      }
    }
  Qed.

  Lemma sim_thread_wf_release_step
        b c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0
        st_tgt1 lc_tgt1 gl_tgt1 e_tgt
        (STEP_TGT: Thread.step e_tgt
                               (Thread.mk _ st_tgt0 lc_tgt0 gl_tgt0)
                               (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1))
        (RELEASE: release_event e_tgt)
        (SIM: sim_thread_wf b c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0)
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 gl_src0)>>) \/
      exists w1 l1 e_src
             st_src1 lc_src1 gl_src1
             st_src2 lc_src2 gl_src2
             st_src3 lc_src3 gl_src3,
        (<<STEPS0: rtc (@Thread.tau_step _)
                       (Thread.mk _ st_src0 lc_src0 gl_src0)
                       (Thread.mk _ st_src1 lc_src1 gl_src1)>>) /\
        (<<STEPS1: Thread.opt_step
                     e_src
                     (Thread.mk _ st_src1 lc_src1 gl_src1)
                     (Thread.mk _ st_src2 lc_src2 gl_src2)>>) /\
        (<<STEPS2: rtc (@Thread.tau_step _)
                       (Thread.mk _ st_src2 lc_src2 gl_src2)
                       (Thread.mk _ st_src3 lc_src3 gl_src3)>>) /\
        (<<EVENT: machine_event_le (ThreadEvent.get_machine_event e_tgt) (ThreadEvent.get_machine_event e_src)>>) /\
        (<<SIM: sim_thread_wf false c w1 l1 st_src3 lc_src3 gl_src3 st_tgt1 lc_tgt1 gl_tgt1>>) /\
        (<<WORLD: world_messages_le (unchangable gl_src0.(Global.memory) lc_src0.(Local.reserves)) (unchangable gl_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) (BoolMap.minus gl_src0.(Global.promises) lc_src0.(Local.promises)) (BoolMap.minus gl_tgt0.(Global.promises) lc_tgt0.(Local.promises)) c (w0, l0) (w1, l1)>>).
  Proof.
    red in SIM. des. punfold SIM0.
    exploit Thread.step_future; eauto. i. des. ss.
    exploit SIM0; eauto. i. des; ss.
    2:{ left. eapply sim_thread_failure_failure; eauto. }
    exploit RELEASE0; eauto. i. des.
    { left. eapply steps_steps_failure; eauto. }
    hexploit Thread.rtc_tau_step_future; [eapply STEPS|..]; eauto. i. des; ss.
    hexploit Thread.opt_step_future; [eapply STEP_SRC|..]; eauto. i. des; ss.
    hexploit Thread.rtc_tau_step_future; [eapply STEPS_AFTER|..]; eauto. i. des; ss.
    right. inv SIM; ss. esplits.
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { red. esplits; eauto. }
    { eauto. }
  Qed.

  Lemma sim_thread_wf_dstep
        c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0
        st_tgt1 lc_tgt1 gl_tgt1 e_tgt
        (STEP_TGT: dstep e_tgt
                         (Thread.mk _ st_tgt0 lc_tgt0 gl_tgt0)
                         (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1))
        (SIM: sim_thread_wf false c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0)
        (CONS: ThreadEvent.get_machine_event e_tgt = MachineEvent.silent -> rtc_consistent (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1))
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 gl_src0)>>) \/
      exists w1 l1 e_src
             st_src1 lc_src1 gl_src1
             st_src2 lc_src2 gl_src2
             st_src3 lc_src3 gl_src3,
        (<<STEPS0: rtc (@Thread.tau_step _)
                       (Thread.mk _ st_src0 lc_src0 gl_src0)
                       (Thread.mk _ st_src1 lc_src1 gl_src1)>>) /\
        (<<STEPS1: Thread.opt_step
                     e_src
                     (Thread.mk _ st_src1 lc_src1 gl_src1)
                     (Thread.mk _ st_src2 lc_src2 gl_src2)>>) /\
        (<<STEPS2: rtc (@Thread.tau_step _)
                       (Thread.mk _ st_src2 lc_src2 gl_src2)
                       (Thread.mk _ st_src3 lc_src3 gl_src3)>>) /\
        (<<EVENT: machine_event_le (ThreadEvent.get_machine_event e_tgt) (ThreadEvent.get_machine_event e_src)>>) /\
        (<<SIM: sim_thread_wf false c w1 l1 st_src3 lc_src3 gl_src3 st_tgt1 lc_tgt1 gl_tgt1>>) /\
        (<<WORLD: world_messages_le (unchangable gl_src0.(Global.memory) lc_src0.(Local.reserves)) (unchangable gl_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) (BoolMap.minus gl_src0.(Global.promises) lc_src0.(Local.promises)) (BoolMap.minus gl_tgt0.(Global.promises) lc_tgt0.(Local.promises)) c (w0, l0) (w1, l1)>>).
  Proof.
    inv STEP_TGT. dup SIM. red in SIM. des.
    hexploit rtc_join.
    { eapply rtc_implies; [|eapply LOWERS]. eapply tau_lower_step_tau_step. }
    intros LOWERS'.
    hexploit Thread.rtc_internal_step_future; [eapply PROMISES|..]; eauto. i. des; ss.
    hexploit Thread.rtc_tau_step_future; [eapply LOWERS'|..]; eauto. i. des; ss.
    hexploit Thread.step_future; [eapply STEP_RELEASE|..]; eauto. i. des; ss.
    destruct e2, e3. ss.
    hexploit sim_thread_wf_promise_steps; eauto.
    { eapply tau_steps_rtc_consistent; eauto.
      eapply step_rtc_consistent; eauto.
    }
    i. des; ss.
    { eauto. }
    hexploit sim_thread_wf_lower_steps; eauto.
    { eapply step_rtc_consistent; eauto. }
    i. des; ss.
    { left. eapply steps_steps_failure; eauto. }
    hexploit sim_thread_wf_release_step; eauto. i. des; ss.
    { left. eapply steps_steps_failure; eauto. eapply steps_steps_failure; eauto. }
    right. esplits.
    { etrans; [eauto|]. etrans; [eauto|]. eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { etrans.
      { eauto. }
      eapply world_messages_le_mon.
      2:{ i. eapply (unchangable_rtc_tau_step_increase STEPS); eauto. }
      2:{ i. eapply rtc_implies in PROMISES; [eapply (unchangable_rtc_all_step_increase PROMISES); eauto|]. i. inv H. econs; eauto. }
      2:{ apply Thread.rtc_tau_step_promises_minus in STEPS. simpl in *. rewrite STEPS. refl. }
      2:{ i. eapply rtc_implies in PROMISES.
          { apply (Thread.rtc_tau_step_promises_minus) in PROMISES. simpl in *. rewrite PROMISES. refl. }
          { i. inv H. econs; [econs 1; eauto|inv LOCAL; ss]. }
      }
      2:{ refl. }
      ss. etrans.
      { eauto. }
      eapply world_messages_le_mon.
      2:{ i. eapply (unchangable_rtc_tau_step_increase STEPS0); eauto. }
      2:{ i. eapply rtc_implies in LOWERS; [eapply rtc_join in LOWERS; eapply (unchangable_rtc_tau_step_increase LOWERS); eauto|]. eapply tau_lower_step_tau_step. }
      2:{ apply Thread.rtc_tau_step_promises_minus in STEPS0. simpl in *. rewrite STEPS0. refl. }
      2:{ i. eapply rtc_implies in LOWERS; [|eapply tau_lower_step_tau_step].
          eapply rtc_join in LOWERS.
          eapply Thread.rtc_tau_step_promises_minus in LOWERS. simpl in *. rewrite LOWERS. refl.
      }
      2:{ refl. }
      ss.
    }
  Qed.

  Lemma sim_thread_wf_rtc_tau_dstep
        c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0
        st_tgt1 lc_tgt1 gl_tgt1
        (STEP_TGT: rtc (tau (@dstep lang_tgt))
                       (Thread.mk _ st_tgt0 lc_tgt0 gl_tgt0)
                       (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1))
        (SIM: sim_thread_wf false c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0)
        (CONS: rtc_consistent (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1))
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 gl_src0)>>) \/
      exists w1 l1
             st_src1 lc_src1 gl_src1,
        (<<STEPS: rtc (@Thread.tau_step _)
                      (Thread.mk _ st_src0 lc_src0 gl_src0)
                      (Thread.mk _ st_src1 lc_src1 gl_src1)>>) /\
        (<<SIM: sim_thread_wf false c w1 l1 st_src1 lc_src1 gl_src1 st_tgt1 lc_tgt1 gl_tgt1>>) /\
        (<<WORLD: world_messages_le (unchangable gl_src0.(Global.memory) lc_src0.(Local.reserves)) (unchangable gl_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) (BoolMap.minus gl_src0.(Global.promises) lc_src0.(Local.promises)) (BoolMap.minus gl_tgt0.(Global.promises) lc_tgt0.(Local.promises)) c (w0, l0) (w1, l1)>>).
  Proof.
    remember (Thread.mk _ st_tgt0 lc_tgt0 gl_tgt0).
    remember (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1).
    revert w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0
           st_tgt1 lc_tgt1 gl_tgt1 Heqt Heqt0 SIM.
    induction STEP_TGT; i; clarify.
    { right. esplits; eauto. refl. }
    { inv H. destruct y.
      hexploit sim_thread_wf_dstep; eauto.
      { eapply rtc_dstep_rtc_tau_step in STEP_TGT.
        i. eapply tau_steps_rtc_consistent; eauto.
      }
      i. des.
      { left. eauto. }
      assert (STEPS_SRC: rtc (@Thread.tau_step lang_src)
                             (Thread.mk _ st_src0 lc_src0 gl_src0)
                             (Thread.mk _ st_src3 lc_src3 gl_src3)).
      { etrans; [eauto|]. etrans; [|eapply STEPS2]. inv STEPS1.
        { refl. }
        { econs 2; [|refl]. econs.
          { eauto. }
          { rewrite EVENT in EVENT0. inv EVENT0; ss. }
        }
      }
      hexploit IHSTEP_TGT; eauto. i. des.
      { left. eapply steps_steps_failure; eauto. }
      right. esplits.
      { etrans; eauto. }
      { eauto. }
      { etrans.
        { eauto. }
        { eapply world_messages_le_mon; eauto.
          { i. eapply unchangable_rtc_tau_step_increase in STEPS_SRC; eauto. }
          { i. hexploit unchangable_rtc_all_step_increase.
            { eapply dstep_rtc_all_step; eauto. }
            { eauto. }
            { eauto. }
          }
          { apply Thread.rtc_tau_step_promises_minus in STEPS_SRC. simpl in *. rewrite STEPS_SRC. refl. }
          { i. hexploit Thread.rtc_all_step_promises_minus.
            { eapply dstep_rtc_all_step; eauto. }
            i. ss. rewrite H. refl.
          }
          { refl. }
        }
      }
    }
  Qed.

  Lemma lower_step_rtc_consistent lang th0 th1 e
        (STEP: @lower_step lang e th0 th1)
        (CONS: ThreadEvent.get_machine_event e = MachineEvent.silent -> rtc_consistent th1)
    :
    rtc_consistent th0.
  Proof.
    inv STEP. des; clarify.
    { eapply program_step_rtc_consistent; eauto.
      apply CONS. destruct e; ss.
    }
    { eapply step_rtc_consistent; eauto. i.
      eapply program_step_rtc_consistent; eauto.
    }
  Qed.

  Lemma lower_steps_rtc_consistent lang th0 th1
        (STEPS: rtc (tau (@lower_step lang)) th0 th1)
        (CONS: rtc_consistent th1)
    :
    rtc_consistent th0.
  Proof.
    revert CONS. induction STEPS; eauto.
    i. inv H. eapply lower_step_rtc_consistent; eauto.
  Qed.

  Lemma dstep_rtc_consistent lang th0 th1 e
        (STEP: @dstep lang e th0 th1)
        (CONS: ThreadEvent.get_machine_event e = MachineEvent.silent -> rtc_consistent th1)
    :
    rtc_consistent th0.
  Proof.
    inv STEP.
    eapply internal_steps_rtc_consistent; eauto.
    eapply lower_steps_rtc_consistent; eauto.
    eapply step_rtc_consistent; eauto.
  Qed.

  Lemma tau_dsteps_rtc_consistent lang th0 th1
        (STEPS: rtc (tau (@dstep lang)) th0 th1)
        (CONS: rtc_consistent th1)
    :
    rtc_consistent th0.
  Proof.
    revert CONS. induction STEPS; eauto.
    i. inv H. eapply dstep_rtc_consistent; eauto.
  Qed.

  Lemma dsteps_rtc_consistent lang th0 th1 e
        (STEPS: @dsteps lang e th0 th1)
        (CONS: e = MachineEvent.silent -> rtc_consistent th1)
    :
    rtc_consistent th0.
  Proof.
    inv STEPS.
    { eapply tau_dsteps_rtc_consistent; eauto.
      eapply internal_steps_rtc_consistent; eauto.
    }
    { eapply tau_dsteps_rtc_consistent; eauto.
      eapply dstep_rtc_consistent; eauto.
    }
  Qed.

  Lemma sim_thread_wf_dsteps
        c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0
        st_tgt1 lc_tgt1 gl_tgt1 e_tgt
        (STEP_TGT: dsteps e_tgt
                          (Thread.mk _ st_tgt0 lc_tgt0 gl_tgt0)
                          (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1))
        (SIM: sim_thread_wf false c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0)
        (CONS: e_tgt = MachineEvent.silent -> rtc_consistent (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1))
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 gl_src0)>>) \/
      exists w1 l1 e_src
             st_src1 lc_src1 gl_src1
             st_src2 lc_src2 gl_src2
             st_src3 lc_src3 gl_src3,
        (<<STEPS0: rtc (@Thread.tau_step _)
                       (Thread.mk _ st_src0 lc_src0 gl_src0)
                       (Thread.mk _ st_src1 lc_src1 gl_src1)>>) /\
        (<<STEPS1: Thread.opt_step
                     e_src
                     (Thread.mk _ st_src1 lc_src1 gl_src1)
                     (Thread.mk _ st_src2 lc_src2 gl_src2)>>) /\
        (<<STEPS2: rtc (@Thread.tau_step _)
                       (Thread.mk _ st_src2 lc_src2 gl_src2)
                       (Thread.mk _ st_src3 lc_src3 gl_src3)>>) /\
        (<<EVENT: machine_event_le e_tgt (ThreadEvent.get_machine_event e_src)>>) /\
        (<<SIM: sim_thread_wf false c w1 l1 st_src3 lc_src3 gl_src3 st_tgt1 lc_tgt1 gl_tgt1>>) /\
        (<<WORLD: world_messages_le (unchangable gl_src0.(Global.memory) lc_src0.(Local.reserves)) (unchangable gl_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) (BoolMap.minus gl_src0.(Global.promises) lc_src0.(Local.promises)) (BoolMap.minus gl_tgt0.(Global.promises) lc_tgt0.(Local.promises)) c (w0, l0) (w1, l1)>>).
  Proof.
    inv STEP_TGT.
    { dup SIM. red in SIM. des.
      pose proof (rtc_dstep_rtc_tau_step DSTEPS) as DSTEPS'.
      hexploit Thread.rtc_tau_step_future; [eapply DSTEPS'|..]; eauto. i. des; ss.
      destruct e2. ss.
      hexploit sim_thread_wf_rtc_tau_dstep; eauto.
      { eapply internal_steps_rtc_consistent; eauto. }
      i. des; ss.
      { left. eauto. }
      hexploit sim_thread_wf_promise_steps; eauto. i. des; ss.
      { left. eapply steps_steps_failure; eauto. }
      right. esplits.
      { eauto. }
      { econs 1. }
      { eauto. }
      { econs. }
      { eauto. }
      { etrans.
        { eauto. }
        { eapply world_messages_le_mon; eauto.
          { i. eapply unchangable_rtc_tau_step_increase in STEPS; eauto. }
          { i. hexploit unchangable_rtc_tau_step_increase; [eapply DSTEPS'|..]; eauto. }
          { apply Thread.rtc_tau_step_promises_minus in STEPS. simpl in *. rewrite STEPS. refl. }
          { apply Thread.rtc_tau_step_promises_minus in DSTEPS'. simpl in *. rewrite DSTEPS'. refl. }
          { refl. }
        }
      }
    }
    { dup SIM. red in SIM. des.
      pose proof (rtc_dstep_rtc_tau_step DSTEPS) as DSTEPS'.
      pose proof (dstep_rtc_all_step DSTEP) as DSTEP'.
      hexploit Thread.rtc_tau_step_future; [eapply DSTEPS'|..]; eauto. i. des; ss.
      destruct e2. ss.
      hexploit sim_thread_wf_rtc_tau_dstep; eauto.
      { eapply dstep_rtc_consistent; eauto. }
      i. des; ss.
      { left. eauto. }
      hexploit sim_thread_wf_dstep; eauto.
      i. des; ss.
      { left. eapply steps_steps_failure; eauto. }
      right. esplits.
      { etrans; eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { etrans.
        { eauto. }
        { eapply world_messages_le_mon; eauto.
          { i. eapply unchangable_rtc_tau_step_increase in STEPS; eauto. }
          { i. hexploit unchangable_rtc_tau_step_increase; [eapply DSTEPS'|..]; eauto. }
          { apply Thread.rtc_tau_step_promises_minus in STEPS. simpl in *. rewrite STEPS. refl. }
          { apply Thread.rtc_tau_step_promises_minus in DSTEPS'. simpl in *. rewrite DSTEPS'. refl. }
          { refl. }
        }
      }
    }
  Qed.

  Lemma sim_thread_wf_cap
        c w0 l0 st_src0 lc_src0 gl_src0 st_tgt lc_tgt gl_tgt
        (SIM: sim_thread_wf false c w0 l0 st_src0 lc_src0 gl_src0 st_tgt lc_tgt gl_tgt)
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 gl_src0)>>) \/
      exists w1 l1 st_src1 lc_src1 gl_src1,
        (<<STEPS: rtc (@Thread.tau_step _)
                      (Thread.mk _ st_src0 lc_src0 (Global.cap_of gl_src0))
                      (Thread.mk _ st_src1 lc_src1 gl_src1)>>) /\
        (<<SIM: sim_thread_wf false c w1 l1 st_src1 lc_src1 gl_src1 st_tgt lc_tgt (Global.cap_of gl_tgt)>>).
  Proof.
    red in SIM. des. punfold SIM0. exploit SIM0; eauto. i. des; ss.
    2:{ left. eapply sim_thread_failure_failure; eauto. }
    exploit CAP; eauto. i. rr in x0. des. inv SIM; ss. right. esplits.
    { refl. }
    { red. esplits; eauto.
      { eapply Local.cap_wf; eauto. }
      { eapply Local.cap_wf; eauto. }
      { eapply Global.cap_wf; eauto. }
      { eapply Global.cap_wf; eauto. }
    }
  Qed.

  Lemma sim_thread_wf_terminal
        c w0 l0 st_src0 lc_src0 gl_src0 st_tgt lc_tgt gl_tgt
        (SIM: sim_thread_wf true c w0 l0 st_src0 lc_src0 gl_src0 st_tgt lc_tgt gl_tgt)
        (LANG_TGT: Language.is_terminal _ st_tgt)
        (LOCAL_TGT: Local.is_terminal lc_tgt)
    :
    (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 gl_src0)>>) \/
    exists w1 l1
           st_src1 lc_src1 gl_src1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src0 lc_src0 gl_src0)
                    (Thread.mk _ st_src1 lc_src1 gl_src1)>>) /\
      (<<LANG_SRC: Language.is_terminal _ st_src1>>) /\
      (<<LOCAL_SRC: Local.is_terminal lc_src1>>) /\
      (<<WORLD: world_messages_le (unchangable gl_src0.(Global.memory) lc_src0.(Local.reserves)) (unchangable gl_tgt.(Global.memory) lc_tgt.(Local.reserves)) (BoolMap.minus gl_src0.(Global.promises) lc_src0.(Local.promises)) (BoolMap.minus gl_tgt.(Global.promises) lc_tgt.(Local.promises)) c (w0, l0) (w1, l1)>>) /\
      (<<MEM: sim_global w1 (PCM.add l1 c) gl_src1 gl_tgt>>)
  .
  Proof.
    red in SIM. des. punfold SIM0. exploit SIM0; eauto.
    i. des.
    2:{ left. eapply sim_thread_failure_failure; eauto. }
    exploit TERMINAL; eauto.
    i. des; ss.
    { left. eapply steps_steps_failure; eauto. }
    right. esplits; eauto.
  Qed.

  Definition sim_thread_wf_past c w l st_src lc_src gl_src st_tgt lc_tgt gl_tgt :=
    exists c' w' gl_src' gl_tgt',
      (<<SIM: sim_thread_wf false c' w' l st_src lc_src gl_src' st_tgt lc_tgt gl_tgt'>>) /\
      (<<MEM_FUTURE_SRC: Global.strong_le gl_src' gl_src>>) /\
      (<<MEM_FUTURE_TGT: Global.le gl_tgt' gl_tgt>>) /\
      (<<WORLD: world_messages_le (Messages.of_memory lc_src.(Local.reserves)) (Messages.of_memory lc_tgt.(Local.reserves)) lc_src.(Local.promises) lc_tgt.(Local.promises) l (w', c') (w, c)>>) /\
      (<<CONSISTENTSRC: Thread.consistent (Thread.mk _ st_src lc_src gl_src')>>) /\
      (<<NFAILURE: ~ Thread.steps_failure (Thread.mk _ st_src lc_src gl_src')>>) /\
      (<<LOCALSRC: Local.wf lc_src gl_src>>) /\
      (<<LOCALTGT: Local.wf lc_tgt gl_tgt>>) /\
      (<<MEMSRC: Global.wf gl_src>>) /\
      (<<MEMTGT: Global.wf gl_tgt>>) /\
      (<<MEMORY: sim_global w (PCM.add l c) gl_src gl_tgt>>)
  .

  Lemma sim_thread_wf_past_future
        c w0 l0 st_src0 lc_src0 gl_src0 st_tgt lc_tgt gl_tgt
        (SIM: sim_thread_wf_past c w0 l0 st_src0 lc_src0 gl_src0 st_tgt lc_tgt gl_tgt)
    :
    (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 gl_src0)>>) \/
    exists w1 l1
           st_src1 lc_src1 gl_src1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src0 lc_src0 gl_src0)
                    (Thread.mk _ st_src1 lc_src1 gl_src1)>>) /\
      (<<SIM: sim_thread_wf false c w1 l1 st_src1 lc_src1 gl_src1 st_tgt lc_tgt gl_tgt>>) /\
      (<<WORLD: world_messages_le (unchangable gl_src0.(Global.memory) lc_src0.(Local.reserves)) (unchangable gl_tgt.(Global.memory) lc_tgt.(Local.reserves)) (BoolMap.minus gl_src0.(Global.promises) lc_src0.(Local.promises)) (BoolMap.minus gl_tgt.(Global.promises) lc_tgt.(Local.promises)) c (w0, l0) (w1, l1)>>).
  Proof.
    red in SIM. des. red in SIM0. des.
    punfold SIM. exploit SIM; eauto. i. des.
    2:{ exfalso. eapply NFAILURE. eapply sim_thread_failure_failure; eauto. }
    exploit FUTURE; eauto. i. des.
    { left. eapply steps_steps_failure; eauto. }
    inv SIM0; ss. right. esplits; eauto.
    hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
    red. esplits; eauto.
  Qed.

  Lemma sim_thread_wf_consistent_aux
        c w l st_src lc_src gl_src st_tgt lc_tgt gl_tgt
        (CONSISTENT: delayed_consistent (Thread.mk _ st_tgt lc_tgt gl_tgt))
        (SIM: sim_thread_wf false c l w st_src lc_src gl_src st_tgt lc_tgt gl_tgt)
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src lc_src gl_src)>>) \/
      (<<CONSISTENT: Thread.consistent (Thread.mk _ st_src lc_src gl_src)>>).
  Proof.
    destruct (classic (Thread.steps_failure (Thread.mk _ st_src lc_src gl_src))) as [FAILURE|NFAILURE].
    { auto. }
    right. rr.
    rr in CONSISTENT. hexploit sim_thread_wf_cap; eauto. i. des; ss.
    { left. destruct e2. subst.
      hexploit sim_thread_wf_dsteps; eauto.
      { ss. }
      i. des.
      { eapply steps_steps_failure; eauto. }
      { inv EVENT. inv STEPS1; ss. econs.
        { etrans; eauto. }
        { eauto. }
        { auto. }
      }
    }
    { destruct e2, e3. subst. ss.
      pose proof (dsteps_rtc_all_step DSTEPS) as STEPS_TGT0.
      hexploit rtc_join.
      { eapply rtc_implies; [|eapply STEPS0|..]. eapply tau_lower_step_tau_step. }
      intros STEPS_TGT1.
      dup SIM0. red in SIM0. des.
      hexploit Thread.rtc_all_step_future; [eapply STEPS_TGT0|..]; eauto; ss. i. des.
      hexploit sim_thread_wf_dsteps; eauto.
      { i. eapply tau_steps_rtc_consistent; eauto.
        eapply consistent_rtc_consistent. econs 2; [refl|]; ss.
      }
      i. des.
      { left. eapply steps_steps_failure; eauto. }
      { hexploit sim_thread_wf_lower_steps; eauto.
        { eapply consistent_rtc_consistent. econs 2; [refl|]; ss. }
        i. des.
        { left. eapply steps_steps_failure; [|eauto].
          etrans; eauto. etrans; eauto. etrans; [|eauto]. inv STEPS2.
          { refl. }
          { econs 2; [|refl]. econs.
            { eauto. }
            { inv EVENT; ss. }
          }
        }
        inv EVENT. red in SIM1. des.
        assert (STEPS_SRC: rtc (@Thread.tau_step _) (Thread.mk _ st_src lc_src (Global.cap_of gl_src)) (Thread.mk _ st_src4 lc_src4 gl_src4)).
        { etrans; eauto. etrans; eauto. etrans; [|eauto]. etrans; [|eauto]. inv STEPS2.
          { refl. }
          { econs 2; [|refl]. econs; eauto. }
        }
        red in SIM3. des.
        punfold SIM1. exploit SIM1; eauto.
        i. des; ss.
        2:{ left. eapply steps_steps_failure; eauto. eapply sim_thread_failure_failure; eauto. }
        exploit CERTIFICATION; eauto. i. des.
        { left. eapply steps_steps_failure; eauto. eapply steps_steps_failure; eauto. }
        econs 2.
        { etrans; eauto. }
        { eauto. }
      }
    }
  Qed.

  Lemma sim_thread_wf_consistent
        c w l st_src lc_src gl_src st_tgt lc_tgt gl_tgt
        (CONSISTENT: delayed_consistent (Thread.mk _ st_tgt lc_tgt gl_tgt))
        (SIM: sim_thread_wf false c w l st_src lc_src gl_src st_tgt lc_tgt gl_tgt)
    :
    (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src lc_src gl_src)>>) \/
    ((<<CONSISTENT: Thread.consistent (Thread.mk _ st_src lc_src gl_src)>>) /\
     (<<SIM: sim_thread_wf_past c w l st_src lc_src gl_src st_tgt lc_tgt gl_tgt>>))
  .
  Proof.
    hexploit sim_thread_wf_consistent_aux; eauto. i. des; eauto.
    destruct (classic (Thread.steps_failure (Thread.mk _ st_src lc_src gl_src))) as [FAILURE|NFAILURE].
    { auto. }
    right. splits; auto. dup SIM. red in SIM. des.
    red. esplits; eauto; try by refl.
  Qed.

  Lemma sim_thread_wf_past_dsteps
        c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0
        st_tgt1 lc_tgt1 gl_tgt1 e_tgt
        (STEP_TGT: dsteps e_tgt
                          (Thread.mk _ st_tgt0 lc_tgt0 gl_tgt0)
                          (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1))
        (SIM: sim_thread_wf_past c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0)
        (CONS_TGT: e_tgt <> MachineEvent.failure ->
                   delayed_consistent (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1))
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 gl_src0)>>) \/
      exists w1 l1 e_src
             st_src1 lc_src1 gl_src1
             st_src2 lc_src2 gl_src2
             st_src3 lc_src3 gl_src3,
        (<<STEPS0: rtc (@Thread.tau_step _)
                       (Thread.mk _ st_src0 lc_src0 gl_src0)
                       (Thread.mk _ st_src1 lc_src1 gl_src1)>>) /\
        (<<STEPS1: Thread.opt_step
                     e_src
                     (Thread.mk _ st_src1 lc_src1 gl_src1)
                     (Thread.mk _ st_src2 lc_src2 gl_src2)>>) /\
        (<<STEPS2: rtc (@Thread.tau_step _)
                       (Thread.mk _ st_src2 lc_src2 gl_src2)
                       (Thread.mk _ st_src3 lc_src3 gl_src3)>>) /\
        (<<EVENT: machine_event_le e_tgt (ThreadEvent.get_machine_event e_src)>>) /\
        (<<CONT: forall (EVENT: ThreadEvent.get_machine_event e_src <> MachineEvent.failure),
            (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src3 lc_src3 gl_src3)>>) \/
            ((<<CONSISTENT: Thread.consistent (Thread.mk _ st_src3 lc_src3 gl_src3)>>) /\
             (<<SIM: sim_thread_wf_past c w1 l1 st_src3 lc_src3 gl_src3 st_tgt1 lc_tgt1 gl_tgt1>>) /\
             (<<WORLD: world_messages_le (unchangable gl_src0.(Global.memory) lc_src0.(Local.reserves)) (unchangable gl_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) (BoolMap.minus gl_src0.(Global.promises) lc_src0.(Local.promises)) (BoolMap.minus gl_tgt0.(Global.promises) lc_tgt0.(Local.promises)) c (w0, l0) (w1, l1)>>))>>).
  Proof.
    hexploit sim_thread_wf_past_future; eauto. i. des.
    { left. eauto. }
    hexploit sim_thread_wf_dsteps; eauto.
    { i. subst. eapply consistent_rtc_consistent.
      eapply delayed_consistent_consistent; eauto.
      eapply CONS_TGT; ss.
    }
    i. des.
    { left. eapply steps_steps_failure; eauto. }
    right. esplits.
    { etrans; eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { i. hexploit CONS_TGT; eauto.
      { inv EVENT; ss. rewrite H1 in *. ss. }
      i. hexploit sim_thread_wf_consistent; eauto. i. des.
      { eauto. }
      { right. esplits; eauto.
        etrans.
        { eauto. }
        eapply world_messages_le_mon; eauto.
        { i. eapply unchangable_rtc_tau_step_increase in STEPS; eauto. }
        { apply Thread.rtc_tau_step_promises_minus in STEPS. ss. rewrite STEPS. refl. }
        { refl. }
      }
    }
  Qed.

  Lemma sim_thread_wf_past_dsteps_full
        c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0
        st_tgt1 lc_tgt1 gl_tgt1 e_tgt
        (STEP_TGT: dsteps e_tgt
                          (Thread.mk _ st_tgt0 lc_tgt0 gl_tgt0)
                          (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1))
        (SIM: sim_thread_wf_past c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0)
        (CONS_TGT: e_tgt <> MachineEvent.failure ->
                   delayed_consistent (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1))
    :
    (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 gl_src0)>>) \/
      ((exists w1 l1 st_src1 lc_src1 gl_src1,
           (<<STEPS0: rtc (@Thread.tau_step _)
                          (Thread.mk _ st_src0 lc_src0 gl_src0)
                          (Thread.mk _ st_src1 lc_src1 gl_src1)>>) /\
           (<<SILENT: e_tgt = MachineEvent.silent>>) /\
           (<<CONSISTENT: Thread.consistent (Thread.mk _ st_src1 lc_src1 gl_src1)>>) /\
           (<<SIM: sim_thread_wf_past c w1 l1 st_src1 lc_src1 gl_src1 st_tgt1 lc_tgt1 gl_tgt1>>) /\
           (<<WORLD: world_messages_le (unchangable gl_src0.(Global.memory) lc_src0.(Local.reserves)) (unchangable gl_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) (BoolMap.minus gl_src0.(Global.promises) lc_src0.(Local.promises)) (BoolMap.minus gl_tgt0.(Global.promises) lc_tgt0.(Local.promises)) c (w0, l0) (w1, l1)>>)) \/
       (exists e_src
               st_src1 lc_src1 gl_src1
               st_src2 lc_src2 gl_src2,
           (<<STEPS0: rtc (@Thread.tau_step _)
                          (Thread.mk _ st_src0 lc_src0 gl_src0)
                          (Thread.mk _ st_src1 lc_src1 gl_src1)>>) /\
           (<<STEPS1: Thread.step
                        e_src
                        (Thread.mk _ st_src1 lc_src1 gl_src1)
                        (Thread.mk _ st_src2 lc_src2 gl_src2)>>) /\
           (<<CONSISTENT0: Thread.consistent (Thread.mk _ st_src2 lc_src2 gl_src2)>>) /\
           (<<EVENT: machine_event_le e_tgt (ThreadEvent.get_machine_event e_src)>>) /\
           (<<CONT: __guard__
                      ((<<FAILURE: Thread.steps_failure (Thread.mk _ st_src2 lc_src2 gl_src2)>>) \/
                       (exists w1 l1 st_src3 lc_src3 gl_src3,
                           (<<STEPS2: rtc (@Thread.tau_step _)
                                          (Thread.mk _ st_src2 lc_src2 gl_src2)
                                          (Thread.mk _ st_src3 lc_src3 gl_src3)>>) /\
                           (<<CONSISTENT1: Thread.consistent (Thread.mk _ st_src3 lc_src3 gl_src3)>>) /\
                           (<<SIM: sim_thread_wf_past c w1 l1 st_src3 lc_src3 gl_src3 st_tgt1 lc_tgt1 gl_tgt1>>) /\
                           (<<WORLD: world_messages_le (unchangable gl_src0.(Global.memory) lc_src0.(Local.reserves)) (unchangable gl_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) (BoolMap.minus gl_src0.(Global.promises) lc_src0.(Local.promises)) (BoolMap.minus gl_tgt0.(Global.promises) lc_tgt0.(Local.promises)) c (w0, l0) (w1, l1)>>)))>>))).
  Proof.
    hexploit sim_thread_wf_past_dsteps; eauto. i. des.
    { left. eauto. }
    destruct (ThreadEvent.get_machine_event e_src) eqn:EQ.
    { assert (STEPS_SRC: rtc (@Thread.tau_step _ )
                             (Thread.mk _ st_src0 lc_src0 gl_src0)
                             (Thread.mk _ st_src3 lc_src3 gl_src3)).
      { etrans; eauto. etrans; [|eauto]. inv STEPS1.
        { refl. }
        { econs 2; [|refl]. econs; eauto. }
      }
      hexploit CONT; eauto; ss. i. des.
      { left. eapply steps_steps_failure; eauto. }
      right. esplits.
      { left. esplits; eauto. inv EVENT; auto. }
    }
    { inv STEPS1; ss. right. right. esplits.
      { eauto. }
      { eauto. }
      { econs 2.
        { refl. }
        { ss. inv STEP; inv LOCAL; ss. inv LOCAL0; ss. eauto. }
      }
      { rewrite EQ. eauto. }
      hexploit CONT; eauto; ss. i. des.
      { left. eapply steps_steps_failure; [|eauto]; eauto. }
      right. esplits; eauto.
    }
    { inv STEPS1; ss. left. repeat red. econs.
      { eauto. }
      { eauto. }
      { eauto. }
    }
  Qed.

  Lemma sim_thread_wf_past_terminal
        c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0
        st_tgt1 lc_tgt1 gl_tgt1
        (SIM: sim_thread_wf_past c w0 l0 st_src0 lc_src0 gl_src0 st_tgt0 lc_tgt0 gl_tgt0)
        (STEPS_TGT: rtc (tau (@lower_step _))
                        (Thread.mk _ st_tgt0 lc_tgt0 gl_tgt0)
                        (Thread.mk _ st_tgt1 lc_tgt1 gl_tgt1))
        (LANG_TGT: Language.is_terminal _ st_tgt1)
        (LOCAL_TGT: Local.is_terminal lc_tgt1)
    :
    (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 gl_src0)>>) \/
    exists w1 l1
           st_src1 lc_src1 gl_src1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src0 lc_src0 gl_src0)
                    (Thread.mk _ st_src1 lc_src1 gl_src1)>>) /\
      (<<LANG_SRC: Language.is_terminal _ st_src1>>) /\
      (<<LOCAL_SRC: Local.is_terminal lc_src1>>) /\
      (<<WORLD: world_messages_le (unchangable gl_src0.(Global.memory) lc_src0.(Local.reserves)) (unchangable gl_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) (BoolMap.minus gl_src0.(Global.promises) lc_src0.(Local.promises)) (BoolMap.minus gl_tgt0.(Global.promises) lc_tgt0.(Local.promises)) c (w0, l0) (w1 ,l1)>>) /\
      (<<MEM: sim_global w1 (PCM.add l1 c) gl_src1 gl_tgt1>>)
  .
  Proof.
    hexploit sim_thread_wf_past_future; eauto. i. des.
    { left. eauto. }
    hexploit sim_thread_wf_lower_steps; eauto.
    { inv LOCAL_TGT. eapply bot_rtc_consistent; ss. }
    i. des.
    { left. eapply steps_steps_failure; eauto. }
    hexploit sim_thread_wf_terminal; eauto. i. des.
    { left. eapply steps_steps_failure; eauto. eapply steps_steps_failure; eauto. }
    right. esplits.
    { etrans; [|eauto]. etrans; eauto. }
    { eauto. }
    { eauto. }
    { etrans.
      { eauto. }
      eapply world_messages_le_mon.
      { etrans.
        { eauto. }
        eapply world_messages_le_mon.
        { eauto. }
        { i. eapply unchangable_rtc_tau_step_increase in STEPS0; eauto. }
        { i. eapply rtc_implies in STEPS_TGT.
          2:{ eapply tau_lower_step_tau_step. }
          eapply rtc_join in STEPS_TGT.
          eapply unchangable_rtc_tau_step_increase in STEPS_TGT; eauto. }
        { apply Thread.rtc_tau_step_promises_minus in STEPS0. ss. rewrite STEPS0. refl. }
        { i. eapply rtc_implies in STEPS_TGT.
          2:{ eapply tau_lower_step_tau_step. }
          eapply rtc_join in STEPS_TGT.
          apply Thread.rtc_tau_step_promises_minus in STEPS_TGT. ss. rewrite STEPS_TGT. refl. }
        { refl. }
      }
      { i. eapply unchangable_rtc_tau_step_increase in STEPS; eauto. }
      { auto. }
      {  apply Thread.rtc_tau_step_promises_minus in STEPS. ss. rewrite STEPS. refl. }
      { refl. }
      { refl. }
    }
    { eauto. }
  Qed.

  Lemma sim_thread_wf_past_update
        c0 w0 l st_src lc_src gl_src0 st_tgt lc_tgt gl_tgt0
        c1 w1 gl_src1 gl_tgt1
        (SIM: sim_thread_wf_past c0 w0 l st_src lc_src gl_src0 st_tgt lc_tgt gl_tgt0)
        (MEM_FUTURE_SRC: Global.strong_le gl_src0 gl_src1)
        (MEM_FUTURE_TGT: Global.le gl_tgt0 gl_tgt1)
        (WORLD_FUTURE: world_messages_le (Messages.of_memory lc_src.(Local.reserves)) (Messages.of_memory lc_tgt.(Local.reserves)) lc_src.(Local.promises) lc_tgt.(Local.promises) l (w0, c0) (w1, c1))
        (LOCALSRC: Local.wf lc_src gl_src1)
        (LOCALTGT: Local.wf lc_tgt gl_tgt1)
        (MEMSRC: Global.wf gl_src1)
        (MEMTGT: Global.wf gl_tgt1)
        (MEMORY: sim_global w1 (PCM.add l c1) gl_src1 gl_tgt1)
    :
    sim_thread_wf_past c1 w1 l st_src lc_src gl_src1 st_tgt lc_tgt gl_tgt1.
  Proof.
    red in SIM. des. red. esplits; eauto.
    { etrans; eauto. }
    { etrans; eauto. }
    { etrans; eauto. }
  Qed.
End LANG.

Section Simulation.
  Definition SIM :=
    forall (ths1_src:Threads.t) (gl0_src:Global.t)
           (ths1_tgt:Threads.t) (gl0_tgt:Global.t), Prop.

  Definition _sim
             (sim: SIM)
             (ths_src0:Threads.t) (gl_src0:Global.t)
             (ths_tgt0:Threads.t) (gl_tgt0:Global.t)
    : Prop :=
    forall (WF_SRC: Configuration.wf (Configuration.mk ths_src0 gl_src0))
           (WF_TGT: Configuration.wf (Configuration.mk ths_tgt0 gl_tgt0)),
      (<<TERMINAL:
        forall c_term (TERMINAL_TGT: DConfiguration.terminal_steps (IdentSet.elements (Threads.tids ths_tgt0)) (Configuration.mk ths_tgt0 gl_tgt0) c_term),
           (<<FAILURE: Configuration.steps_failure (Configuration.mk ths_src0 gl_src0)>>) \/
            exists ths_src1 gl_src1,
              (<<STEPS_SRC: rtc Configuration.tau_step (Configuration.mk ths_src0 gl_src0) (Configuration.mk ths_src1 gl_src1)>>) /\
              (<<TERMINAL_SRC: Threads.is_terminal ths_src1>>)>>) /\
        (<<STEP:
          forall e_tgt tid_tgt ths_tgt1 gl_tgt1
                 (STEP_TGT: DConfiguration.step e_tgt tid_tgt (Configuration.mk ths_tgt0 gl_tgt0) (Configuration.mk ths_tgt1 gl_tgt1)),
            (<<FAILURE: Configuration.steps_failure (Configuration.mk ths_src0 gl_src0)>>) \/
              exists e_src tid_src ths_src1 gl_src1 ths_src2 gl_src2,
                (<<STEPS_SRC: rtc Configuration.tau_step (Configuration.mk ths_src0 gl_src0) (Configuration.mk ths_src1 gl_src1)>>) /\
                (<<STEP_SRC: Configuration.opt_step e_src tid_src (Configuration.mk ths_src1 gl_src1) (Configuration.mk ths_src2 gl_src2)>>) /\
                (<<EVENT: machine_event_le e_tgt e_src>>) /\
                ((<<FAILURE: Configuration.steps_failure (Configuration.mk ths_src2 gl_src2)>>) \/
                   exists ths_src3 gl_src3,
                     (<<STEPS_AFTER: rtc Configuration.tau_step (Configuration.mk ths_src2 gl_src2) (Configuration.mk ths_src3 gl_src3)>>) /\
                     (<<SIM: forall (EVENT: e_src <> MachineEvent.failure), sim ths_src3 gl_src3 ths_tgt1 gl_tgt1>>))>>)
  .

  Lemma _sim_mon: monotone4 _sim.
  Proof.
    ii. exploit IN; try apply SC1; eauto. i. des.
    splits; eauto. i.
    exploit STEP; eauto. i. des; eauto.
    { right. esplits; eauto. }
    { right. esplits; eauto. right. esplits; eauto. }
  Qed.
  Hint Resolve _sim_mon: paco.

  Definition sim: SIM := paco4 _sim bot4.
End Simulation.
Hint Resolve _sim_mon: paco.


Lemma sim_adequacy
      ths_src gl_src
      ths_tgt gl_tgt
      (WF_SRC: Configuration.wf (Configuration.mk ths_src gl_src))
      (WF_TGT: Configuration.wf (Configuration.mk ths_tgt gl_tgt))
      (SIM: sim ths_src gl_src ths_tgt gl_tgt):
  DConfiguration.delayed_behaviors (Configuration.mk ths_tgt gl_tgt) <2=
  behaviors Configuration.step (Configuration.mk ths_src gl_src).
Proof.
  s. i.
  revert WF_SRC WF_TGT SIM.
  revert ths_src gl_src.
  remember (Configuration.mk ths_tgt gl_tgt).
  revert ths_tgt gl_tgt Heqt.
  induction PR; i; subst.
  - punfold SIM0. exploit SIM0; eauto; try refl. i. des.
    exploit TERMINAL; eauto. i. des.
    + inv FAILURE. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3. eauto.
    + eapply rtc_tau_step_behavior; eauto.
      econs 1. eauto.
  - destruct c2.
    punfold SIM0. exploit SIM0; eauto; try refl. i. des.
    hexploit STEP0; eauto. i. des.
    + inv FAILURE. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3. eauto.
    + inv FAILURE.
      eapply rtc_tau_step_behavior; eauto. inv STEP_SRC.
      { eapply rtc_tau_step_behavior; eauto. eapply behaviors_failure; eauto. }
      { inv EVENT0. econs 2; [eauto| | auto].
        { eapply rtc_tau_step_behavior; eauto. eapply behaviors_failure; eauto. }
        { etrans; eauto. }
      }
    + hexploit SIM1; eauto.
      { inv EVENT0; ss. }
      clear SIM1. intros SIM1.
      inv SIM1; [|done].
      eapply rtc_tau_step_behavior; eauto.
      exploit DConfiguration.step_future; try exact STEP; eauto. i. des.
      exploit Configuration.rtc_tau_step_future;[eapply STEPS_SRC|..]; eauto. i. des.
      exploit Configuration.opt_step_future;[eapply STEP_SRC|..]; eauto. i. des.
      exploit Configuration.rtc_tau_step_future;[eapply STEPS_AFTER|..]; eauto. i. des.
      exploit Configuration.rtc_tau_step_future; eauto. i. des.
      inv EVENT0. inv STEP_SRC.
      econs 2; [eauto| |auto].
      2:{ etrans; eauto. }
      eapply rtc_tau_step_behavior; eauto.
  - destruct c2.
    punfold SIM0. exploit SIM0; eauto; try refl. i. des.
    hexploit STEP0; eauto. i. des.
    + inv FAILURE. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3; eauto.
    + inv FAILURE.
      eapply rtc_tau_step_behavior; eauto. inv STEP_SRC.
      { eapply rtc_tau_step_behavior; eauto. eapply behaviors_failure; eauto. }
      { eapply rtc_tau_step_behavior; eauto. inv EVENT. econs 3; eauto. }
    + eapply rtc_tau_step_behavior; eauto.
      exploit DConfiguration.step_future; try exact STEP; eauto. i. des.
      exploit Configuration.rtc_tau_step_future; try exact STEPS_SRC; eauto. i. des.
      inv EVENT. inv STEP_SRC. econs 3; eauto.
  - destruct c2.
    punfold SIM0. exploit SIM0; eauto; try refl. i. des.
    hexploit STEP0; eauto. i. des.
    + inv FAILURE. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3; eauto.
    + inv FAILURE. des.
      eapply rtc_tau_step_behavior; eauto.
      inv EVENT. inv STEP_SRC.
      { eapply rtc_tau_step_behavior; eauto. econs 3; eauto. }
      { eapply rtc_tau_step_behavior; eauto.
        econs 4; eauto. eapply rtc_tau_step_behavior; eauto. econs 3; eauto. }
    + hexploit SIM1; eauto.
      { inv EVENT; ss. }
      clear SIM1. intros SIM1.
      inv SIM1; [|done].
      eapply rtc_tau_step_behavior; eauto.
      exploit DConfiguration.step_future; try exact STEP; eauto. i. des.
      exploit Configuration.rtc_tau_step_future; try exact STEPS_SRC; eauto. i. des.
      inv STEP_SRC.
      * eapply rtc_tau_step_behavior; eauto.
        eapply IHPR; [..|eauto|]; eauto.
        exploit Configuration.rtc_tau_step_future; try exact STEPS_AFTER; eauto. i. des. auto.
      * inv EVENT. econs 4; eauto. eapply rtc_tau_step_behavior; eauto.
        exploit Configuration.step_future; try apply STEP1; eauto. s. i. des.
        eapply IHPR; eauto.
        exploit Configuration.rtc_tau_step_future; try exact STEPS_AFTER; eauto. i. des. auto.
  - econs 5.
Qed.

Lemma tids_find
      tids ths_src ths_tgt
      tid
      (TIDS_SRC: tids = Threads.tids ths_src)
      (TIDS_TGT: tids = Threads.tids ths_tgt):
  (exists lang_src st_src lc_src, IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src)) <->
  (exists lang_tgt st_tgt lc_tgt, IdentMap.find tid ths_tgt = Some (existT _ lang_tgt st_tgt, lc_tgt)).
Proof.
  split; i; des.
  - destruct (IdentSet.mem tid tids) eqn:MEM.
    + rewrite TIDS_TGT in MEM.
      rewrite Threads.tids_o in MEM.
      destruct (IdentMap.find tid ths_tgt); ss.
      destruct p. destruct s. esplits; eauto.
    + rewrite TIDS_SRC in MEM.
      rewrite Threads.tids_o in MEM.
      destruct (IdentMap.find tid ths_src); ss.
  - destruct (IdentSet.mem tid tids) eqn:MEM.
    + rewrite TIDS_SRC in MEM.
      rewrite Threads.tids_o in MEM.
      destruct (IdentMap.find tid ths_src); ss.
      destruct p. destruct s. esplits; eauto.
    + rewrite TIDS_TGT in MEM.
      rewrite Threads.tids_o in MEM.
      destruct (IdentMap.find tid ths_tgt); ss.
Qed.

Lemma thread_rtc_step_rtc_step
      ths1_src gl1_src
      gl2_src
      tid lang_src st1_src lc1_src st2_src lc2_src
      (WF_SRC: Configuration.wf (Configuration.mk ths1_src gl1_src))
      (FIND: IdentMap.find tid ths1_src = Some (existT _ lang_src st1_src, lc1_src))
      (STEPS: rtc (@Thread.tau_step lang_src)
                  (Thread.mk lang_src st1_src lc1_src gl1_src)
                  (Thread.mk lang_src st2_src lc2_src gl2_src))
      (LOCAL: Thread.consistent (Thread.mk lang_src st2_src lc2_src gl2_src)):
  (<<STEPS: rtc Configuration.tau_step
                (Configuration.mk ths1_src gl1_src)
                (Configuration.mk (IdentMap.add tid (existT _ lang_src st2_src, lc2_src) ths1_src) gl2_src)>>).
Proof.
  inv WF_SRC. inv WF. ss. exploit THREADS; eauto. i.
  exploit Thread.rtc_tau_step_future; eauto. s. i. des.
  generalize (rtc_tail STEPS). i. des.
  - inv H0.
    assert (STEP0: Configuration.step
                     MachineEvent.silent tid
                     (Configuration.mk ths1_src gl1_src)
                     (Configuration.mk (IdentMap.add tid (existT _ lang_src st2_src, lc2_src) ths1_src) gl2_src)).
    { rewrite <- EVENT. econs; ss; eauto. }
    econs; eauto. econs; eauto.
  - inv H.
    replace (IdentMap.add tid (existT _ lang_src st2_src, lc2_src) ths1_src) with ths1_src; auto.
    apply IdentMap.eq_leibniz. ii.
    rewrite -> IdentMap.gsident; auto.
Qed.

Lemma thread_failure_configuration_failure
      ths1_src gl1_src
      tid lang_src st1_src lc1_src
      (WF_SRC: Configuration.wf (Configuration.mk ths1_src gl1_src))
      (FIND: IdentMap.find tid ths1_src = Some (existT _ lang_src st1_src, lc1_src))
      (STEPS: Thread.steps_failure (Thread.mk lang_src st1_src lc1_src gl1_src))
  :
  Configuration.steps_failure (Configuration.mk ths1_src gl1_src).
Proof.
  inv STEPS. destruct th2, th3.
  econs.
  { refl. }
  rewrite <- EVENT_FAILURE. econs; eauto; ss.
Qed.

Definition res_map: Type := IdentMap.t PCM.car.
Definition res_map_sum (rs: res_map): PCM.car :=
  IdentMap.fold (fun _ => PCM.add) rs PCM.unit.

Lemma res_map_sum_add rs tid r
      (FIND: IdentMap.find tid rs = None)
  :
  res_map_sum (IdentMap.add tid r rs) = PCM.add r (res_map_sum rs).
Proof.
  unfold res_map_sum.
  erewrite IdentMap.Properties.fold_add; ss; auto.
  { ii. subst. auto. }
  { ii. erewrite PCM.add_assoc. erewrite PCM.add_assoc.
    f_equal. eapply PCM.add_comm.
  }
  { apply IdentMap.Facts.not_find_in_iff. auto. }
Qed.

Lemma res_map_sum_remove rs tid r
      (FIND: IdentMap.find tid rs = Some r)
  :
  res_map_sum rs = PCM.add r (res_map_sum (IdentMap.remove tid rs)).
Proof.
  erewrite <- res_map_sum_add.
  { f_equal. eapply IdentMap.eq_leibniz.
    ii. erewrite IdentMap.gsspec. erewrite IdentMap.grspec. des_ifs. eauto.
  }
  { apply IdentMap.grs. }
Qed.

Lemma identmap_remove_remove_neq A (m: IdentMap.t A) tid0 tid1
  :
  IdentMap.remove tid0 (IdentMap.remove tid1 m)
  =
  IdentMap.remove tid1 (IdentMap.remove tid0 m).
Proof.
  eapply IdentMap.eq_leibniz.
  ii. erewrite IdentMap.grspec. erewrite IdentMap.grspec.
  erewrite IdentMap.grspec. erewrite IdentMap.grspec. des_ifs.
Qed.

Lemma identmap_remove_remove_eq A (m: IdentMap.t A) tid
  :
  IdentMap.remove tid (IdentMap.remove tid m)
  =
    IdentMap.remove tid m.
Proof.
  eapply IdentMap.eq_leibniz.
  ii. erewrite IdentMap.grspec. erewrite IdentMap.grspec.
  des_ifs.
Qed.

Lemma identmap_remove_add_neq A (m: IdentMap.t A) tid0 tid1 a
      (NEQ: tid0 <> tid1)
  :
  IdentMap.remove tid0 (IdentMap.add tid1 a m)
  =
  IdentMap.add tid1 a (IdentMap.remove tid0 m).
Proof.
  eapply IdentMap.eq_leibniz.
  ii. erewrite IdentMap.gsspec. erewrite IdentMap.grspec.
  erewrite IdentMap.gsspec. erewrite IdentMap.grspec. des_ifs.
Qed.

Lemma identmap_remove_add_eq A (m: IdentMap.t A) tid a
  :
  IdentMap.remove tid (IdentMap.add tid a m)
  =
    IdentMap.remove tid m.
Proof.
  eapply IdentMap.eq_leibniz.
  ii. erewrite IdentMap.grspec. erewrite IdentMap.gsspec.
  erewrite IdentMap.grspec. des_ifs.
Qed.

Lemma identmap_add_remove_eq A (m: IdentMap.t A) tid a
  :
  IdentMap.add tid a m
  =
  IdentMap.add tid a (IdentMap.remove tid m).
Proof.
  eapply IdentMap.eq_leibniz.
  ii. erewrite IdentMap.gsspec. erewrite IdentMap.gsspec.
  erewrite IdentMap.grspec. des_ifs.
Qed.

Lemma sim_threads_terminal_step
      (tids: Ident.t -> Prop)
      ths_src0 gl_src0
      ths_tgt0 gl_tgt0 w0 rs0
      ths_tgt1 gl_tgt1
      tid
      (TIDS: Threads.tids ths_src0 = Threads.tids ths_tgt0)
      (SIM: forall tid0 lang_src st_src lc_src lang_tgt st_tgt lc_tgt
                   (IN: tids tid0),
          IdentMap.find tid0 ths_src0 = Some (existT _ lang_src st_src, lc_src) ->
          IdentMap.find tid0 ths_tgt0 = Some (existT _ lang_tgt st_tgt, lc_tgt) ->
         exists l,
           (<<RESFIND: IdentMap.find tid0 rs0 = Some l>>) /\
             (<<SIM: @sim_thread_wf_past lang_src lang_tgt (res_map_sum (IdentMap.remove tid0 rs0)) w0 l st_src lc_src gl_src0 st_tgt lc_tgt gl_tgt0>>))
      (TERMINAL: forall tid0 lang_src st_src lc_src
                        (NIN: ~ tids tid0),
          IdentMap.find tid0 ths_src0 = Some (existT _ lang_src st_src, lc_src) ->
          (<<STATE: (Language.is_terminal lang_src) st_src>>) /\ (<<THREAD: Local.is_terminal lc_src>>))
      (WF_SRC: Configuration.wf (Configuration.mk ths_src0 gl_src0))
      (WF_TGT: Configuration.wf (Configuration.mk ths_tgt0 gl_tgt0))
      (STEP_TGT: DConfiguration.terminal_step tid (Configuration.mk ths_tgt0 gl_tgt0) (Configuration.mk ths_tgt1 gl_tgt1))
      (NTID: tids tid)
  :
    (<<FAILURE: Configuration.steps_failure (Configuration.mk ths_src0 gl_src0)>>) \/
    exists ths_src1 gl_src1 w1 rs1,
      (<<STEPS_SRC: rtc Configuration.tau_step (Configuration.mk ths_src0 gl_src0) (Configuration.mk ths_src1 gl_src1)>>) /\
      (<<SIM: forall tid0 lang_src st_src lc_src lang_tgt st_tgt lc_tgt
                     (IN: tids tid0)
                     (NEQ: tid0 <> tid),
          IdentMap.find tid0 ths_src1 = Some (existT _ lang_src st_src, lc_src) ->
          IdentMap.find tid0 ths_tgt1 = Some (existT _ lang_tgt st_tgt, lc_tgt) ->
         exists l,
           (<<RESFIND: IdentMap.find tid0 rs1 = Some l>>) /\
             (<<SIM: @sim_thread_wf_past lang_src lang_tgt (res_map_sum (IdentMap.remove tid0 rs1)) w1 l st_src lc_src gl_src1 st_tgt lc_tgt gl_tgt1>>)>>) /\
      (<<TERMINAL: forall tid0 lang_src st_src lc_src
                          (TID: tid0 = tid \/ ~ tids tid0),
          IdentMap.find tid0 ths_src1 = Some (existT _ lang_src st_src, lc_src) ->
          (<<STATE: (Language.is_terminal lang_src) st_src>>) /\ (<<THREAD: Local.is_terminal lc_src>>)>>) /\
      (<<TIDS: Threads.tids ths_src1 = Threads.tids ths_tgt1>>)
.
Proof.
  i. dup STEP_TGT. inv STEP_TGT. ss.
  destruct (IdentMap.find tid ths_src0) as [[[lang_src st_src] lc_src]|] eqn:FIND_SRC; cycle 1.
  { remember (Threads.tids ths_src0) as tids0 eqn:TIDS_SRC.
    exploit tids_find; [exact TIDS_SRC|exact TIDS|..]. i. des.
    exploit x1; eauto. intros x. des. rewrite FIND_SRC in x. inv x. }
  dup WF_SRC. dup WF_TGT.
  inv WF_SRC. inv WF_TGT. inv WF. inv WF0. ss.
  exploit SIM; eauto. i. des.
  hexploit sim_thread_wf_past_terminal; eauto. i. des.
  { left. eapply thread_failure_configuration_failure; eauto. }
  { hexploit thread_rtc_step_rtc_step; [eapply WF_SRC0|..]; eauto.
    { econs 2. esplits; eauto. inv LOCAL_SRC. ss. }
    i. hexploit Configuration.rtc_tau_step_strong_le; eauto. i. des.
    2:{ eauto. }
    right. esplits; eauto.
    { instantiate (1:=w1).
      i. hexploit DConfiguration.terminal_step_future; eauto. i. des.
      hexploit Configuration.rtc_tau_step_future; eauto. i. des. ss.
      inv WF0. inv WF2. ss. inv WF. inv WF0.
      exploit THREADS1; eauto. i. exploit THREADS2; eauto. i.
      erewrite IdentMap.gso in H0; auto. erewrite IdentMap.gso in H1; auto.
      hexploit SIM; eauto. i. des. esplits.
      { erewrite IdentMap.gso; [|eauto].
        erewrite IdentMap.gro; [|eauto]. eauto.
      }
      eapply sim_thread_wf_past_update; eauto.
      { eapply Global.future_le; eauto. }
      { erewrite res_map_sum_remove in WORLD.
        2:{ rewrite IdentMap.gro; [|eauto]. eauto. }
        apply world_messages_le_frame in WORLD.
        instantiate (1:=l1).
        replace (res_map_sum (IdentMap.remove tid0 rs0)) with (PCM.add l (res_map_sum (IdentMap.remove tid0 (IdentMap.remove tid rs0)))).
        2:{ symmetry. rewrite identmap_remove_remove_neq. eapply res_map_sum_remove. erewrite IdentMap.gro; eauto. }
        replace (res_map_sum (IdentMap.remove tid0 (IdentMap.add tid l1 (IdentMap.remove tid rs0)))) with (PCM.add l1 (res_map_sum (IdentMap.remove tid0 (IdentMap.remove tid rs0)))).
        2:{ symmetry. rewrite identmap_remove_add_neq; auto.
            rewrite res_map_sum_add; auto.
            rewrite identmap_remove_remove_neq. apply IdentMap.grs.
        }
        eapply world_messages_le_mon; eauto.
        { destruct lc_src0, lc_src. eapply other_promise_unchangable; eauto. }
        { destruct lc_tgt, lc1. eapply other_promise_unchangable; eauto. }
        { destruct lc_src0, lc_src. eapply other_promise_included; eauto. }
        { destruct lc_tgt, lc1. eapply other_promise_included; eauto. }
        { refl. }
      }
      { rewrite identmap_remove_add_neq; auto.
        rewrite res_map_sum_add.
        2:{ rewrite identmap_remove_remove_neq. apply IdentMap.grs. }
        rewrite PCM.add_assoc. rewrite (PCM.add_comm l0 l1).
        rewrite <- PCM.add_assoc.
        rewrite <- res_map_sum_remove; auto.
        rewrite IdentMap.gro; auto.
      }
    }
    { i. ss. des.
      { subst. erewrite IdentMap.gss in H0. dependent destruction H0; eauto. }
      { erewrite IdentMap.gso in H0; eauto.
        ii. subst. eapply TID0; eauto.
      }
    }
    { rewrite ! Threads.tids_add. f_equal; auto. }
  }
Qed.

Lemma sim_threads_terminal_steps
      ths_src0 gl_src0
      ths_tgt0 gl_tgt0 w0 rs0
      tids c_tgt
      (STEPS_TGT: DConfiguration.terminal_steps tids (Configuration.mk ths_tgt0 gl_tgt0) c_tgt)
      (WF_SRC: Configuration.wf (Configuration.mk ths_src0 gl_src0))
      (WF_TGT: Configuration.wf (Configuration.mk ths_tgt0 gl_tgt0))
      (SIM: forall tid0 lang_src st_src lc_src lang_tgt st_tgt lc_tgt
                   (IN: List.In tid0 tids),
          IdentMap.find tid0 ths_src0 = Some (existT _ lang_src st_src, lc_src) ->
          IdentMap.find tid0 ths_tgt0 = Some (existT _ lang_tgt st_tgt, lc_tgt) ->
         exists l,
           (<<RESFIND: IdentMap.find tid0 rs0 = Some l>>) /\
             (<<SIM: @sim_thread_wf_past lang_src lang_tgt (res_map_sum (IdentMap.remove tid0 rs0)) w0 l st_src lc_src gl_src0 st_tgt lc_tgt gl_tgt0>>))
      (TERMINAL: forall tid lang_src st_src lc_src
                        (NIN: ~ List.In tid tids),
          IdentMap.find tid ths_src0 = Some (existT _ lang_src st_src, lc_src) ->
          (<<STATE: (Language.is_terminal lang_src) st_src>>) /\ (<<THREAD: Local.is_terminal lc_src>>))
      (TIDS: Threads.tids ths_src0 = Threads.tids ths_tgt0)
  :
    (<<FAILURE: Configuration.steps_failure (Configuration.mk ths_src0 gl_src0)>>) \/
    exists ths_src1 gl_src1,
      (<<STEPS_SRC: rtc Configuration.tau_step (Configuration.mk ths_src0 gl_src0) (Configuration.mk ths_src1 gl_src1)>>) /\
      (<<TERMINAL: forall tid0 lang_src st_src lc_src,
          IdentMap.find tid0 ths_src1 = Some (existT _ lang_src st_src, lc_src) ->
          (<<STATE: (Language.is_terminal lang_src) st_src>>) /\ (<<THREAD: Local.is_terminal lc_src>>)>>)
.
Proof.
  remember (Configuration.mk ths_tgt0 gl_tgt0) as c_tgt0.
  revert ths_src0 gl_src0 ths_tgt0 gl_tgt0 w0 rs0 WF_SRC WF_TGT SIM TERMINAL TIDS Heqc_tgt0.
  induction STEPS_TGT; i; subst.
  { right. esplits; eauto. }
  { left. inv STEP.
    destruct (IdentMap.find tid ths_src0) as [[[lang_src st_src] lc_src]|] eqn:FIND_SRC; cycle 1.
    { remember (Threads.tids ths_src0) as tids0 eqn:TIDS_SRC.
      exploit tids_find; [exact TIDS_SRC|exact TIDS|..]. i. des.
      exploit x1; eauto. intros x. des. rewrite FIND_SRC in x. inv x. }
    dup WF_SRC. dup WF_TGT.
    inv WF_SRC. inv WF_TGT. inv WF. inv WF0. ss.
    exploit SIM0; eauto. i. des.
    hexploit sim_thread_wf_past_dsteps_full; eauto. i.
    assert (FAILURE: Thread.steps_failure (Thread.mk _ st_src lc_src gl_src0)).
    { i. des; ss; eauto. rr in CONT. des; eauto.
      { inv EVENT. econs; eauto. }
      { inv EVENT. econs; eauto. }
    }
    clear H.
    inv FAILURE. destruct th2, th3.
    econs; [refl|]. rewrite <- EVENT_FAILURE.
    econs; eauto; ss.
  }
  { destruct c2. ss.
    hexploit (@sim_threads_terminal_step (fun tid0 => List.In tid0 (tid::tids))).
    { eapply TIDS. }
    { i. eapply SIM0; eauto. }
    { i. eapply TERMINAL; eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { ss. eauto. }
    i. des.
    { left. eauto. }
    hexploit DConfiguration.terminal_step_future; eauto. i. des; ss.
    hexploit Configuration.rtc_tau_step_future; eauto. i. des; ss.
    hexploit IHSTEPS_TGT.
    { eapply WF0. }
    { eapply WF2. }
    { i. eapply SIM1; eauto. ii. subst. eauto. }
    { i. eapply TERMINAL0; [|eauto]. destruct (Ident.eq_dec tid0 tid); auto.
      right. ii. des; clarify.
    }
    { auto. }
    { auto. }
    i. des.
    { inv FAILURE. left. econs.
      { etrans; eauto. }
      { eauto. }
    }
    { right. esplits.
      { etrans; eauto. }
      i. eauto.
    }
  }
Qed.

Lemma sim_threads_terminal
      ths_src0 gl_src0
      ths_tgt0 gl_tgt0 w0 rs0 c_tgt
      (STEPS_TGT: DConfiguration.terminal_steps (IdentSet.elements (Threads.tids ths_tgt0)) (Configuration.mk ths_tgt0 gl_tgt0) c_tgt)
      (WF_SRC: Configuration.wf (Configuration.mk ths_src0 gl_src0))
      (WF_TGT: Configuration.wf (Configuration.mk ths_tgt0 gl_tgt0))
      (SIM: forall tid lang_src st_src lc_src lang_tgt st_tgt lc_tgt,
          IdentMap.find tid ths_src0 = Some (existT _ lang_src st_src, lc_src) ->
          IdentMap.find tid ths_tgt0 = Some (existT _ lang_tgt st_tgt, lc_tgt) ->
         exists l,
           (<<RESFIND: IdentMap.find tid rs0 = Some l>>) /\
             (<<SIM: @sim_thread_wf_past lang_src lang_tgt (res_map_sum (IdentMap.remove tid rs0)) w0 l st_src lc_src gl_src0 st_tgt lc_tgt gl_tgt0>>))
      (TIDS: Threads.tids ths_src0 = Threads.tids ths_tgt0)
  :
    (<<FAILURE: Configuration.steps_failure (Configuration.mk ths_src0 gl_src0)>>) \/
    exists ths_src1 gl_src1,
      (<<STEPS_SRC: rtc Configuration.tau_step (Configuration.mk ths_src0 gl_src0) (Configuration.mk ths_src1 gl_src1)>>) /\
      (<<TERMINAL: forall tid0 lang_src st_src lc_src,
          IdentMap.find tid0 ths_src1 = Some (existT _ lang_src st_src, lc_src) ->
          (<<STATE: (Language.is_terminal lang_src) st_src>>) /\ (<<THREAD: Local.is_terminal lc_src>>)>>)
.
Proof.
  eapply sim_threads_terminal_steps; eauto.
  i. exfalso. eapply NIN.
  cut (SetoidList.InA eq tid (IdentSet.elements (Threads.tids ths_src0))).
  { rewrite <- TIDS. clear. i. induction H; ss; eauto. }
  eapply IdentSet.elements_spec1. eapply LocSet.Facts.mem_2.
  rewrite Threads.tids_o. rewrite H. auto.
Qed.

Lemma sim_threads_sim
      ths_src gl0_src
      ths_tgt gl0_tgt w rs
      (TIDS: Threads.tids ths_src = Threads.tids ths_tgt)
      (SIM: forall tid lang_src st_src lc_src lang_tgt st_tgt lc_tgt,
          IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src) ->
          IdentMap.find tid ths_tgt = Some (existT _ lang_tgt st_tgt, lc_tgt) ->
          exists l,
            (<<RESFIND: IdentMap.find tid rs = Some l>>) /\
              (<<SIM: @sim_thread_wf_past lang_src lang_tgt (res_map_sum (IdentMap.remove tid rs)) w l st_src lc_src gl0_src st_tgt lc_tgt gl0_tgt>>))
  :
    sim ths_src gl0_src ths_tgt gl0_tgt.
Proof.
  remember (Threads.tids ths_src) as tids eqn:TIDS_SRC.
  rename TIDS into TIDS_TGT.
  revert w rs ths_src gl0_src ths_tgt gl0_tgt tids TIDS_SRC TIDS_TGT SIM.
  pcofix CIH. i. pfold. ii. splits.
  - (* TERMINAL CASE *)
    subst. i. eapply sim_threads_terminal; eauto.

  - (* STEP CASE *)
    i. dup STEP_TGT. inv STEP_TGT. ss.
    destruct (IdentMap.find tid_tgt ths_src) as [[[lang_src st_src] lc_src]|] eqn:FIND_SRC; cycle 1.
    { remember (Threads.tids ths_src) as tids eqn:TIDS_SRC.
      exploit tids_find; [exact TIDS_SRC|exact TIDS_TGT|..]. i. des.
      exploit x1; eauto. intros x. des. rewrite FIND_SRC in x. inv x. }
    dup WF_SRC. dup WF_TGT.
    inv WF_SRC. inv WF_TGT. inv WF. inv WF0. ss.
    exploit SIM0; eauto. i. des.
    hexploit sim_thread_wf_past_dsteps_full; eauto. i. des.
    { left. eapply thread_failure_configuration_failure; eauto. }
    { hexploit Thread.rtc_tau_step_strong_le; eauto. i. des; ss.
      2:{ left. eapply thread_failure_configuration_failure; eauto. }
      hexploit thread_rtc_step_rtc_step; [eapply WF_SRC0|..]; eauto.
      i. right. esplits.
      { eauto. }
      { econs 1. }
      { subst. econs. }
      { right. esplits.
        { refl. }
        { right. eapply CIH; ss.
          { rewrite ! Threads.tids_add. f_equal; eauto. }
          { i. instantiate (1:=w1). instantiate (1:=IdentMap.add tid_tgt l1 (IdentMap.remove tid_tgt rs)).
            rewrite IdentMap.gsspec in H0. rewrite IdentMap.gsspec in H1. des_ifs.
            { inv H0. eapply inj_pair2 in H2. eapply inj_pair2 in H4. subst. esplits.
              { erewrite IdentMap.gss. eauto. }
              { eauto. rewrite identmap_remove_add_eq; auto. rewrite identmap_remove_remove_eq; auto. }
            }
            { eapply DConfiguration.step_future in STEP_TGT0; eauto. des. ss.
              eapply Configuration.rtc_tau_step_future in H; eauto. des. ss.
              hexploit SIM0; eauto. i. des. inv WF0. inv WF2. ss. esplits.
              { erewrite IdentMap.gso; eauto. erewrite IdentMap.gro; eauto. }
              eapply sim_thread_wf_past_update; eauto.
              { eapply Global.future_le; eauto. }
              { erewrite res_map_sum_remove in WORLD.
                2:{ rewrite IdentMap.gro; [|eauto]. eauto. }
                apply world_messages_le_frame in WORLD.
                replace (res_map_sum (IdentMap.remove tid rs)) with (PCM.add l (res_map_sum (IdentMap.remove tid (IdentMap.remove tid_tgt rs)))).
                2:{ symmetry. rewrite identmap_remove_remove_neq. eapply res_map_sum_remove. erewrite IdentMap.gro; eauto. }
                replace (res_map_sum (IdentMap.remove tid (IdentMap.add tid_tgt l1 (IdentMap.remove tid_tgt rs)))) with (PCM.add l1 (res_map_sum (IdentMap.remove tid (IdentMap.remove tid_tgt rs)))).
                2:{ symmetry. rewrite identmap_remove_add_neq; auto.
                    rewrite res_map_sum_add; auto.
                    rewrite identmap_remove_remove_neq. apply IdentMap.grs.
                }
                eapply world_messages_le_mon; eauto.
                { destruct lc_src0, lc_src. eapply other_promise_unchangable; eauto. }
                { destruct lc_tgt, lc1. eapply other_promise_unchangable; eauto. }
                { destruct lc_src0, lc_src. eapply other_promise_included; eauto. }
                { destruct lc_tgt, lc1. eapply other_promise_included; eauto. }
                { refl. }
              }
              { inv WF. eapply THREADS1. erewrite IdentMap.gso; eauto. }
              { inv WF0. eapply THREADS1. erewrite IdentMap.gso; eauto. }
              { red in SIM2. des.
                rewrite identmap_remove_add_neq; auto.
                rewrite res_map_sum_add.
                2:{ rewrite identmap_remove_remove_neq. apply IdentMap.grs. }
                rewrite PCM.add_assoc. rewrite (PCM.add_comm l0 l1).
                rewrite <- PCM.add_assoc.
                rewrite <- res_map_sum_remove; auto.
                rewrite IdentMap.gro; auto.
              }
            }
          }
        }
      }
    }
    { assert (STEP_SRC: Configuration.step
                          (ThreadEvent.get_machine_event e_src) tid_tgt
                          (Configuration.mk ths_src gl0_src)
                          (Configuration.mk
                             (IdentMap.add tid_tgt (existT _ lang_src st_src2, lc_src2) ths_src)
                             gl_src2)).
      { econs; eauto. }
      hexploit Configuration.step_strong_le; eauto. i. des; auto. ss.
      hexploit DConfiguration.step_future; eauto. i. des. ss.
      right. esplits.
      { refl. }
      { econs 2. eauto. }
      { eauto. }
      red in CONT. des.
      { left. eapply thread_failure_configuration_failure; eauto.
        erewrite IdentMap.gss. eauto.
      }
      { hexploit thread_rtc_step_rtc_step; [eapply WF2|..]; eauto.
        { erewrite IdentMap.gss. eauto. }
        i. des.
        hexploit Configuration.rtc_tau_step_strong_le; eauto. i. des; auto. ss.
        right. esplits.
        { eauto. }
        right. eapply CIH; ss.
        { rewrite IdentMap.add_add_eq.
          rewrite ! Threads.tids_add. f_equal; eauto. }


        { i. instantiate (1:=w1). instantiate (1:=IdentMap.add tid_tgt l1 (IdentMap.remove tid_tgt rs)).
          rewrite ! IdentMap.gsspec in H0. rewrite ! IdentMap.gsspec in H1. des_ifs.
          { inv H0. eapply inj_pair2 in H2. eapply inj_pair2 in H4. subst. esplits.
            { erewrite IdentMap.gss. eauto. }
            { eauto. rewrite identmap_remove_add_eq; auto. rewrite identmap_remove_remove_eq; auto. }
          }
          { hexploit SIM0; eauto. i. des. inv WF0. inv WF1. ss. esplits.
            { erewrite IdentMap.gso; eauto. erewrite IdentMap.gro; eauto. }
            eapply sim_thread_wf_past_update; eauto.
            { etrans; eauto. }
            { eapply Global.future_le; eauto. }
            { erewrite res_map_sum_remove in WORLD.
              2:{ rewrite IdentMap.gro; [|eauto]. eauto. }
              apply world_messages_le_frame in WORLD.
              replace (res_map_sum (IdentMap.remove tid rs)) with (PCM.add l (res_map_sum (IdentMap.remove tid (IdentMap.remove tid_tgt rs)))).
              2:{ symmetry. rewrite identmap_remove_remove_neq. eapply res_map_sum_remove. erewrite IdentMap.gro; eauto. }
              replace (res_map_sum (IdentMap.remove tid (IdentMap.add tid_tgt l1 (IdentMap.remove tid_tgt rs)))) with (PCM.add l1 (res_map_sum (IdentMap.remove tid (IdentMap.remove tid_tgt rs)))).
              2:{ symmetry. rewrite identmap_remove_add_neq; auto.
                  rewrite res_map_sum_add; auto.
                  rewrite identmap_remove_remove_neq. apply IdentMap.grs.
              }
              eapply world_messages_le_mon; eauto.
              { destruct lc_src0, lc_src. eapply other_promise_unchangable; eauto. }
              { destruct lc_tgt, lc1. eapply other_promise_unchangable; eauto. }
              { destruct lc_src0, lc_src. eapply other_promise_included; eauto. }
              { destruct lc_tgt, lc1. eapply other_promise_included; eauto. }
              { refl. }
            }
            { inv WF0. eapply THREADS1. erewrite ! IdentMap.gso; eauto. }
            { inv WF. eapply THREADS1. erewrite IdentMap.gso; eauto. }
            { red in SIM2. des.
              rewrite identmap_remove_add_neq; auto.
              rewrite res_map_sum_add.
              2:{ rewrite identmap_remove_remove_neq. apply IdentMap.grs. }
              rewrite PCM.add_assoc. rewrite (PCM.add_comm l0 l1).
              rewrite <- PCM.add_assoc.
              rewrite <- res_map_sum_remove; auto.
              rewrite IdentMap.gro; auto.
            }
          }
        }
      }
    }
    Unshelve. all: ss; eauto.
Qed.

Lemma res_map_sum_unit A m
  :
  res_map_sum (IdentMap.map (fun _: A => PCM.unit) m) = PCM.unit.
Proof.
  unfold res_map_sum.
  cut (forall x e (EMPTY: forall tid r, IdentMap.find tid e = Some r -> r = PCM.unit),
          IdentMap.fold (fun _ => PCM.add) e x = x).
  { i. eapply H. i. rewrite IdentMap.Facts.map_o in H0.
    unfold option_map in *. des_ifs.
  }
  intros x e. clear m.
  change ((fun m fm => forall (EMPTY: forall tid r, IdentMap.find tid m = Some r -> r = PCM.unit), fm = x) e (IdentMap.fold (fun _ => PCM.add) e x)).
  eapply IdentMap.Properties.fold_rec; ss.
  i. unfold IdentMap.Properties.Add in *.
  hexploit H2.
  { i. specialize (H1 tid). setoid_rewrite IdentMap.gsspec in H1. des_ifs.
    { exfalso. eapply H0. eapply LocMap.Properties.F.in_find_iff.
      setoid_rewrite H3. ss.
    }
    { eapply EMPTY. rewrite <- H1 in H3. eauto. }
  }
  i. subst.
  hexploit EMPTY.
  { setoid_rewrite H1. erewrite IdentMap.gss. eauto. }
  i. subst. rewrite PCM.add_comm. eapply PCM.unit_id.
Qed.

Lemma sim_init (s_src s_tgt: Threads.syntax) (w_init: world)
      (SIM: forall tid,
          option_rel (fun '(existT _ lang_src st_src) '(existT _ lang_tgt st_tgt) =>
                        @sim_thread world M world_messages_le sim_global
                                    lang_src lang_tgt false PCM.unit w_init PCM.unit
                                    (lang_src.(Language.init) st_src) Local.init Global.init
                                    (lang_tgt.(Language.init) st_tgt) Local.init Global.init) (IdentMap.find tid s_src) (IdentMap.find tid s_tgt))
      (MEM: sim_global w_init PCM.unit Global.init Global.init)
  :
    DConfiguration.delayed_behaviors (Configuration.init s_tgt) <2=
    behaviors Configuration.step (Configuration.init s_src).
Proof.
  destruct (classic (exists tid lang syn,
                        (<<FIND: IdentMap.find tid s_src = Some (existT _ lang syn)>>) /\
                        (<<FAILURE: Thread.steps_failure (Thread.mk lang (lang.(Language.init) syn) Local.init Global.init)>>))) as [?|NFAILURE].
  { des. inv FAILURE. destruct th2, th3. i. econs 3.
    rewrite <- EVENT_FAILURE. econs; eauto; ss.
    unfold Threads.init. rewrite IdentMap.Facts.map_o.
    setoid_rewrite FIND. ss.
  }
  eapply sim_adequacy.
  { eapply Configuration.init_wf. }
  { eapply Configuration.init_wf. }
  { eapply sim_threads_sim.
    { eapply IdentSet.ext. i. specialize (SIM i). ss.
      rewrite Threads.tids_o. rewrite Threads.tids_o. unfold Threads.init.
      rewrite ! IdentMap.Facts.map_o in *. unfold option_map in *. des_ifs.
      { setoid_rewrite Heq in SIM. setoid_rewrite Heq0 in SIM. ss. }
      { setoid_rewrite Heq in SIM. setoid_rewrite Heq0 in SIM. ss. }
    }
    { i. instantiate (1:=w_init). instantiate (1:=IdentMap.map (fun _ => PCM.unit) s_src).
      exists PCM.unit. specialize (SIM tid). unfold Threads.init in *.
      rewrite IdentMap.Facts.map_o in *. unfold option_map in *. des_ifs.
      2:{ setoid_rewrite Heq in Heq1. ss. }
      setoid_rewrite Heq in Heq1. clarify.
      dependent destruction H. dependent destruction H1.
      setoid_rewrite Heq0 in SIM. ss.
      des_ifs. splits; auto. ss.
      replace (res_map_sum (IdentMap.remove tid (IdentMap.map (fun _ => PCM.unit) s_src))) with PCM.unit.
      2:{ rewrite <- IdentMap.map_remove. symmetry. eapply res_map_sum_unit. }
      rr. esplits.
      { red. esplits; eauto.
        { eapply Local.init_wf. }
        { eapply Local.init_wf. }
        { eapply Global.init_wf. }
        { eapply Global.init_wf. }
        { rewrite PCM.unit_id. auto. }
      }
      { refl. }
      { refl. }
      { refl. }
      { econs 2; [refl|]. ss. }
      { ii. eapply NFAILURE; eauto. }
      { eapply Local.init_wf. }
      { eapply Local.init_wf. }
      { eapply Global.init_wf. }
      { eapply Global.init_wf. }
      { rewrite PCM.unit_id. auto. }
    }
  }
Qed.

End WORLD.
#[export] Hint Resolve _sim_thread_mon: paco.
