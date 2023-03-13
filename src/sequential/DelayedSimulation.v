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

(* Require Import JoinedView. *)
(* Require Import Pred. *)
(* Require Import Delayed. *)
Require Import LowerMemory.
Require Import LowerStep.

Set Implicit Arguments.


Module PCM.
  Class t: Type := mk {
    car: Type;
    unit: car;
    add: car -> car -> car;
    wf: car -> Prop;
    add_comm: forall a b, add a b = add b a;
    add_assoc: forall a b c, add a (add b c) = add (add a b) c;
    unit_id: forall a, add a unit = a;
    wf_unit: wf unit;
    wf_mon: forall a b, wf (add a b) -> wf a;
  }
  .

  Definition extends `{M: t} (a b: car) := exists ctx, add a ctx = b.
  Definition updatable `{M: t} (a b: car) := forall ctx, wf (add a ctx) -> wf (add b ctx).
  Definition updatable_set (M: t) (a: car) (B: car -> Prop) := forall ctx (WF: wf (add a ctx)),
    exists b, <<IN: B b>> /\ <<WF: wf (add b ctx)>>.

  Global Program Instance extends_PreOrder `{M: t}: PreOrder extends.
  Next Obligation.
  Proof.
    ii. eexists. eapply unit_id.
  Qed.
  Next Obligation.
  Proof.
    ii. unfold extends in *. des. subst.
    exists (add ctx0 ctx). apply add_assoc.
  Qed.
End PCM.


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

Variable sim_global: forall (w: world) (m: PCM.car) (gl_src gl_tgt:Global.t), Prop.

Section SimulationThread.

  Definition SIM_THREAD :=
    forall (lang_src lang_tgt:language)
           (b: bool) (c: PCM.car) (w: world) (l: PCM.car)
           (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (gl0_src:Global.t)
           (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (gl0_tgt:Global.t), Prop.

  Definition _sim_thread_promise_step
             (lang_src lang_tgt:language)
             (sim_thread: forall (b1: bool) (c1: PCM.car) (w1: world) (l1: PCM.car) (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (gl0_src:Global.t)
                                 (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (gl0_tgt:Global.t), Prop)
             (b: bool)
             (c: PCM.car)
             (w0: world) (l0: PCM.car)
             st1_src lc1_src gl1_src
             st1_tgt lc1_tgt gl1_tgt :=
    forall st3_tgt lc3_tgt gl3_tgt
           (STEP_TGT: Thread.internal_step
                        (Thread.mk _ st1_tgt lc1_tgt gl1_tgt)
                        (Thread.mk _ st3_tgt lc3_tgt gl3_tgt))
           (CONSISTENT: rtc_consistent (Thread.mk _ st3_tgt lc3_tgt gl3_tgt)),
    exists st2_src lc2_src gl2_src,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st1_src lc1_src gl1_src)
                    (Thread.mk _ st2_src lc2_src gl2_src)>>) /\
        ((<<FAILURE: Thread.steps_failure (Thread.mk _ st2_src lc2_src gl2_src)>>) \/
           exists w3 l3,
             (<<gL3: b = false -> sim_global w3 (PCM.add l3 c) gl2_src gl3_tgt>>) /\
               (<<SIM: sim_thread b c w3 l3 st2_src lc2_src gl2_src st3_tgt lc3_tgt gl3_tgt>>) /\
               (<<WORLD: world_messages_le (unchangable gl1_src.(Global.memory) lc1_src.(Local.reserves)) (unchangable gl1_tgt.(Global.memory) lc1_tgt.(Local.reserves)) (BoolMap.minus gl1_src.(Global.promises) lc1_src.(Local.promises)) (BoolMap.minus gl1_tgt.(Global.promises) lc1_tgt.(Local.promises)) c (w0, l0) (w3, l3)>>))
  .

  Definition _sim_thread_cap
             (lang_src lang_tgt:language)
             (sim_thread: forall (b1: bool) (c1: PCM.car) (w1: world) (l1: PCM.car) (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (gl0_src:Global.t)
                                 (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (gl0_tgt:Global.t), Prop)
             (c: PCM.car)
             (w0: world) (l0: PCM.car)
             st1_src lc1_src gl1_src
             st1_tgt lc1_tgt gl1_tgt :=
    exists w3 l3,
      (<<GLOBAL3: sim_global w3 (PCM.add l3 c) (Global.cap_of gl1_src) (Global.cap_of gl1_tgt)>>) /\
      (<<SIM: sim_thread false c w3 l3 st1_src lc1_src (Global.cap_of gl1_src) st1_tgt lc1_tgt (Global.cap_of gl1_tgt)>>).

  Definition _sim_thread_future
             (lang_src lang_tgt:language)
             (sim_thread: forall (b1: bool) (c1: PCM.car) (w1: world) (l1: PCM.car) (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (gl0_src:Global.t)
                                 (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (gl0_tgt:Global.t), Prop)
             (c0: PCM.car)
             (w0: world) (l0: PCM.car)
             st1_src lc1_src gl1_src
             st1_tgt lc1_tgt gl1_tgt :=
    forall gl2_src gl2_tgt w1 c1
           (MEMSRC: Global.strong_le gl1_src gl2_src)
           (MEMTGT: Global.le gl1_tgt gl2_tgt)
           (WORLD: world_messages_le (Messages.of_memory lc1_src.(Local.reserves)) (Messages.of_memory lc1_tgt.(Local.reserves)) lc1_src.(Local.promises) lc1_tgt.(Local.promises) l0 (w0, c0) (w1, c1))
           (MEMORY: sim_global w1 (PCM.add l0 c1) gl2_src gl2_tgt)
           (WF_SRC: Local.wf lc1_src gl2_src)
           (WF_TGT: Local.wf lc1_tgt gl2_tgt)
           (MEM_SRC: Global.wf gl2_src)
           (MEM_TGT: Global.wf gl2_tgt)
           (CONSISTENT: Thread.consistent (Thread.mk _ st1_src lc1_src gl1_src)),
    exists st2_src lc2_src gl3_src,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st1_src lc1_src gl2_src)
                    (Thread.mk _ st2_src lc2_src gl3_src)>>) /\
      ((<<FAILURE: Thread.steps_failure (Thread.mk _ st2_src lc2_src gl3_src)>>) \/
       exists w3 l3,
         (<<MEMORY3: sim_global w3 (PCM.add l3 c1) gl3_src gl2_tgt>>) /\
         (<<SIM: sim_thread false c1 w3 l3 st2_src lc2_src gl3_src st1_tgt lc1_tgt gl2_tgt>>) /\
         (<<WORLD: world_messages_le (unchangable gl2_src.(Global.memory) lc1_src.(Local.reserves)) (unchangable gl2_tgt.(Global.memory) lc1_tgt.(Local.reserves)) (BoolMap.minus gl2_src.(Global.promises) lc1_src.(Local.promises)) (BoolMap.minus gl2_tgt.(Global.promises) lc1_tgt.(Local.promises)) c1 (w1, l0) (w3, l3)>>))
  .

  Definition _sim_thread_release_step
             (lang_src lang_tgt:language)
             (sim_thread: forall (b1: bool) (c1: PCM.car) (w1: world) (l1: PCM.car) (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (gl0_src:Global.t)
                                 (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (gl0_tgt:Global.t), Prop)
             (c: PCM.car)
             (w0: world) (l0: PCM.car)
             st1_src lc1_src gl1_src
             st1_tgt lc1_tgt gl1_tgt :=
    forall e_tgt st3_tgt lc3_tgt gl3_tgt
           (STEP_TGT: Thread.step e_tgt
                                  (Thread.mk _ st1_tgt lc1_tgt gl1_tgt)
                                  (Thread.mk _ st3_tgt lc3_tgt gl3_tgt))
           (RELEASE: release_event e_tgt),
    exists st2_src lc2_src gl2_src,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st1_src lc1_src gl1_src)
                    (Thread.mk _ st2_src lc2_src gl2_src)>>) /\
      ((<<FAILURE: Thread.steps_failure (Thread.mk _ st2_src lc2_src gl2_src)>>) \/
       exists e_src st3_src lc3_src gl3_src st4_src lc4_src gl4_src w3 l3,
         (<<STEP_SRC: Thread.opt_step e_src
                                      (Thread.mk _ st2_src lc2_src gl2_src)
                                      (Thread.mk _ st3_src lc3_src gl3_src)>>) /\
         (<<STEPS_AFTER: rtc (@Thread.tau_step _)
                             (Thread.mk _ st3_src lc3_src gl3_src)
                             (Thread.mk _ st4_src lc4_src gl4_src)>>) /\
         (<<EVENT: machine_event_le (ThreadEvent.get_machine_event e_tgt) (ThreadEvent.get_machine_event e_src)>>) /\
         (<<MEMORY3: sim_global w3 (PCM.add l3 c) gl4_src gl3_tgt>>) /\
         (<<SIM: sim_thread false c w3 l3 st4_src lc4_src gl4_src st3_tgt lc3_tgt gl3_tgt>>) /\
         (<<WORLD: world_messages_le (unchangable gl1_src.(Global.memory) lc1_src.(Local.reserves)) (unchangable gl1_tgt.(Global.memory) lc1_tgt.(Local.reserves)) (BoolMap.minus gl1_src.(Global.promises) lc1_src.(Local.promises)) (BoolMap.minus gl1_tgt.(Global.promises) lc1_tgt.(Local.promises)) c (w0, l0) (w3, l3)>>))
  .

  Definition _sim_thread_terminal
             (lang_src lang_tgt:language)
             (sim_thread: forall (b1: bool) (c1: PCM.car) (w1: world) (l1: PCM.car) (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (gl0_src:Global.t)
                                 (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (gl0_tgt: Global.t), Prop)
             (c: PCM.car)
             (w0: world) (l0: PCM.car)
             st1_src lc1_src gl1_src
             st1_tgt lc1_tgt gl1_tgt :=
    forall (TERMINAL_TGT: (Language.is_terminal lang_tgt) st1_tgt)
           (BOT: Local.is_terminal lc1_tgt),
    exists st2_src lc2_src gl2_src,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st1_src lc1_src gl1_src)
                    (Thread.mk _ st2_src lc2_src gl2_src)>>) /\
      ((<<FAILURE: Thread.steps_failure (Thread.mk _ st2_src lc2_src gl2_src)>>) \/
       exists w3 l3,
         (<<TERMINAL_SRC: (Language.is_terminal lang_src) st2_src>>) /\
         (<<BOT: Local.is_terminal lc2_src>>) /\
         (<<MEMORY3: sim_global w3 (PCM.add l3 c) gl2_src gl1_tgt>>) /\
         (<<WORLD: world_messages_le (unchangable gl1_src.(Global.memory) lc1_src.(Local.reserves)) (unchangable gl1_tgt.(Global.memory) lc1_tgt.(Local.reserves)) (BoolMap.minus gl1_src.(Global.promises) lc1_src.(Local.promises)) (BoolMap.minus gl1_tgt.(Global.promises) lc1_tgt.(Local.promises)) c (w0, l0) (w3, l3)>>)).

  Definition _sim_thread_certification
             (lang_src lang_tgt:language)
             (sim_thread: forall (b1: bool) (c1: PCM.car) (w1: world) (l1: PCM.car) (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (gl0_src:Global.t)
                                 (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (gl0_tgt:Global.t), Prop)
             (c0: PCM.car)
             (w0: world) (l0: PCM.car)
             st1_src lc1_src gl1_src
             lc1_tgt :=
    forall (BOT: lc1_tgt.(Local.promises) = BoolMap.bot),
    exists st2_src lc2_src gl2_src,
      (<<STEPS: rtc (@Thread.tau_step lang_src)
                    (Thread.mk _ st1_src lc1_src gl1_src)
                    (Thread.mk _ st2_src lc2_src gl2_src)>>) /\
        ((<<FAILURE: Thread.steps_failure (Thread.mk _ st2_src lc2_src gl2_src)>>) \/
           (<<BOT: lc2_src.(Local.promises) = BoolMap.bot>>)).

  Definition _sim_thread_lower_step
             (lang_src lang_tgt:language)
             (sim_thread: forall (b1: bool) (c1: PCM.car) (w1: world) (l1: PCM.car) (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (gl0_src:Global.t)
                                 (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (gl0_tgt:Global.t), Prop)
             (c: PCM.car)
             (w0: world) (l0: PCM.car)
             st1_src lc1_src gl1_src
             st1_tgt lc1_tgt gl1_tgt :=
    forall e_tgt st3_tgt lc3_tgt gl3_tgt
           (STEP_TGT: Thread.program_step e_tgt
                                          (Thread.mk _ st1_tgt lc1_tgt gl1_tgt)
                                          (Thread.mk _ st3_tgt lc3_tgt gl3_tgt))
           (NRELEASE: ~ release_event e_tgt),
    exists st2_src lc2_src gl2_src,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st1_src lc1_src gl1_src)
                    (Thread.mk _ st2_src lc2_src gl2_src)>>) /\
      ((<<FAILURE: Thread.steps_failure (Thread.mk _ st2_src lc2_src gl2_src)>>) \/
       exists w3 l3,
         ((<<SIM: sim_thread true c w3 l3 st2_src lc2_src gl2_src st3_tgt lc3_tgt gl3_tgt>>) /\
          (<<WORLD: world_messages_le (unchangable gl1_src.(Global.memory) lc1_src.(Local.reserves)) (unchangable gl1_tgt.(Global.memory) lc1_tgt.(Local.reserves)) (BoolMap.minus gl1_src.(Global.promises) lc1_src.(Local.promises)) (BoolMap.minus gl1_tgt.(Global.promises) lc1_tgt.(Local.promises)) c (w0, l0) (w3, l3)>>)))
  .

  Definition _sim_thread_failure
             (lang_src lang_tgt:language)
             (w0: world)
             (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (gl0_src:Global.t)
             (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (gl0_tgt:Global.t) :=
    exists st2_src lc2_src gl2_src,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st1_src lc1_src gl0_src)
                    (Thread.mk _ st2_src lc2_src gl2_src)>>) /\
        (<<FAILURE: Thread.steps_failure (Thread.mk _ st2_src lc2_src gl2_src)>>).

  Definition _sim_thread
             (sim_thread: SIM_THREAD)
             (lang_src lang_tgt:language)
             (b0: bool) (c0: PCM.car) (w0: world) (l0: PCM.car)
             (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (gl0_src:Global.t)
             (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (gl0_tgt:Global.t): Prop :=
    forall
      (WF_SRC: Local.wf lc1_src gl0_src)
      (WF_TGT: Local.wf lc1_tgt gl0_tgt)
      (MEM_SRC: Global.wf gl0_src)
      (MEM_TGT: Global.wf gl0_tgt),
      ((<<RELEASE: _sim_thread_release_step _ _ (@sim_thread _ _) c0 w0 l0 st1_src lc1_src gl0_src st1_tgt lc1_tgt gl0_tgt>>) /\
         (<<CERTIFICATION: _sim_thread_certification _ lang_tgt (@sim_thread _ _) c0 w0 l0 st1_src lc1_src gl0_src lc1_tgt>>) /\
         (<<LOWER: _sim_thread_lower_step _ _ (@sim_thread _ _) c0 w0 l0 st1_src lc1_src gl0_src st1_tgt lc1_tgt gl0_tgt>>) /\
         (<<TERMINAL: _sim_thread_terminal _ _ (@sim_thread _ _) c0 w0 l0 st1_src lc1_src gl0_src st1_tgt lc1_tgt gl0_tgt>>) /\
         (<<PROMISE: _sim_thread_promise_step _ _ (@sim_thread _ _) b0 c0 w0 l0 st1_src lc1_src gl0_src st1_tgt lc1_tgt gl0_tgt>>) /\
         (<<CAP: b0 = false -> _sim_thread_cap _ _ (@sim_thread _ _) c0 w0 l0 st1_src lc1_src gl0_src st1_tgt lc1_tgt gl0_tgt>>) /\
         (<<FUTURE: b0 = false -> _sim_thread_future _ _ (@sim_thread _ _) c0 w0 l0 st1_src lc1_src gl0_src st1_tgt lc1_tgt gl0_tgt>>)) \/
        (<<FAILURE: _sim_thread_failure _ _ w0 st1_src lc1_src gl0_src st1_tgt lc1_tgt gl0_tgt>>)
  .

  Lemma _sim_thread_mon: monotone12 _sim_thread.
  Proof.
    ii. red in IN. exploit IN; eauto. i. des; auto.
    left. splits; eauto.
    { ii. exploit RELEASE; eauto. i. des.
      { esplits; eauto. }
      { esplits; eauto. right. esplits; eauto. }
    }
    { ii. exploit LOWER; eauto. i. des.
      { esplits; eauto. }
      { esplits; eauto. right. esplits; eauto. }
    }
    { ii. exploit PROMISE; eauto. i. des.
      { esplits; eauto. }
      { esplits; eauto. right. esplits; eauto. }
    }
    { ii. exploit CAP; eauto. i. rr in x12. des. rr. esplits; eauto. }
    { ii. exploit FUTURE; eauto. i. des.
      { esplits; eauto. }
      { esplits; eauto. right. esplits; eauto. }
    }
  Qed.
  #[local] Hint Resolve _sim_thread_mon: paco.

  Definition sim_thread: SIM_THREAD := paco12 _sim_thread bot12.
End SimulationThread.
#[local] Hint Resolve _sim_thread_mon: paco.


End WORLD.
#[export] Hint Resolve _sim_thread_mon: paco.
