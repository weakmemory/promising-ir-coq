Require Import Lia.
Require Import RelationClasses.
Require Import Program.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.

Require Import Time.
From PromisingLib Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import BoolMap.
Require Import Promises.
Require Import Global.
Require Import Thread.
Require Import Configuration.
Require Import Behavior.

Require Import MemoryProps.
Require Import Certify.
Require Import CurrentCertify.
Require Import PFConsistent.

Set Implicit Arguments.

Definition owned_future_mem_loc loc: Memory.t -> Memory.t -> Prop :=
  fun mem0 mem1 =>
    forall from to val released na
           (GET: Memory.get loc to mem1 = Some (from, Message.message val released na)),
      Memory.get loc to mem0 = Some (from, Message.message val released na)
.

Global Program Instance owned_future_mem_loc_PreOrder loc:
  PreOrder (owned_future_mem_loc loc).
Next Obligation.
Proof.
  ii. auto.
Qed.
Next Obligation.
Proof.
  ii. eapply H; auto.
Qed.

Definition owned_future_global_loc loc: Global.t -> Global.t -> Prop :=
  fun gl0 gl1 =>
    (<<MEM: owned_future_mem_loc loc gl0.(Global.memory) gl1.(Global.memory)>>) /\
      (<<PROM: gl1.(Global.promises) loc = gl0.(Global.promises) loc>>)
.

Global Program Instance owned_future_global_loc_PreOrder loc:
  PreOrder (owned_future_global_loc loc).
Next Obligation.
Proof.
  unfold owned_future_global_loc. ii. splits.
  { refl. }
  { auto. }
Qed.
Next Obligation.
Proof.
  unfold owned_future_global_loc. ii. des. splits.
  { etrans; eauto. }
  { etrans; eauto. }
Qed.

Definition owned_future_global_promises
           (prom: BoolMap.t) (gl0 gl1: Global.t): Prop :=
  forall loc (OWNED: prom loc = true), owned_future_global_loc loc gl0 gl1.

Global Program Instance owned_future_global_promises_PreOrder prom:
  PreOrder (owned_future_global_promises prom).
Next Obligation.
Proof.
  ii. refl.
Qed.
Next Obligation.
Proof.
  ii. etrans; eauto.
Qed.

Lemma owned_future_global_promises_mon
      prom0 prom1 gl0 gl1
      (FUTURE: owned_future_global_promises prom1 gl0 gl1)
      (LE: BoolMap.le prom0 prom1)
  :
  owned_future_global_promises prom0 gl0 gl1.
Proof.
  ii. eapply FUTURE; eauto.
Qed.



Lemma local_reserve_step_owned_future
      own
      loc from to lc0 gl0 lc1 gl1
      (STEP: Local.reserve_step lc0 gl0 loc from to lc1 gl1):
  owned_future_global_promises
    own
    gl0 gl1.
Proof.
  inv STEP; ss. inv RESERVE. ii. rr. splits; ss.
  ii. erewrite Memory.add_o in GET; eauto. des_ifs.
Qed.

Lemma local_cancel_step_owned_future
      own
      loc from to lc0 gl0 lc1 gl1
      (STEP: Local.cancel_step lc0 gl0 loc from to lc1 gl1):
  owned_future_global_promises
    own
    gl0 gl1.
Proof.
  inv STEP; ss. inv CANCEL. ii. rr. splits; ss.
  ii. erewrite Memory.remove_o in GET; eauto. des_ifs.
Qed.

Lemma local_program_step_owned_future
      own
      e lc0 gl0 lc1 gl1
      (STEP: Local.program_step e lc0 gl0 lc1 gl1):
  (<<FUTURE: owned_future_global_promises
               own
               gl0 gl1>>) \/
    (exists loc from to val released ord,
        (<<ACCESS: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord)>>) /\
          (<<RACE: own loc = true>>)).
Proof.
  inv STEP; ss.
  { left. r. refl. }
  { left. r. refl. }
  { destruct (own loc) eqn:RACE.
    { right. esplits; eauto. }
    { left. ii. assert (NEQ: loc0 <> loc).
      { ii. subst. rewrite RACE in *. ss. }
      inv LOCAL. econs; ss.
      { ii. erewrite Memory.add_o in GET; eauto. des_ifs. ss. des; clarify. }
      { inv FULFILL; ss. inv REMOVE. inv GREMOVE.
        rr. erewrite ! loc_fun_add_spec. condtac; subst; ss.
      }
    }
  }
  { destruct (own loc) eqn:RACE.
    { right. esplits; eauto. }
    { left. ii. assert (NEQ: loc0 <> loc).
      { ii. subst. rewrite RACE in *. ss. }
      inv LOCAL1. inv LOCAL2. econs; ss.
      { ii. erewrite Memory.add_o in GET0; eauto.
        destruct (loc_ts_eq_dec (loc0, to) (loc, tsw)); ss. des; clarify.
      }
      { inv FULFILL; ss. inv REMOVE. inv GREMOVE.
        rr. erewrite ! loc_fun_add_spec. condtac; subst; ss.
      }
    }
  }
  { left. inv LOCAL; ss. ii. split; ss. }
  { left. inv LOCAL; ss. ii. split; ss. }
  { left. r. refl. }
  { left. r. refl. }
  { left. r. refl. }
  { left. r. refl. }
Qed.

Lemma program_step_owned_future
      own
      e lang (th1 th2: Thread.t lang)
      (STEP: Thread.program_step e th1 th2):
  (exists loc from to val released ord,
      (<<ACCESS: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord)>>) /\
        (<<RACE: own loc = true>>)) \/
    (<<FUTURE: owned_future_global_promises
                 own
                 (th1.(Thread.global)) (th2.(Thread.global))>>).
Proof.
  inv STEP. hexploit local_program_step_owned_future; eauto.
  i. des; cycle 1.
  { left. destruct e; ss; clarify.
    { esplits; eauto. }
    { esplits; eauto. }
  }
  right. esplits; eauto.
Qed.

Lemma pf_step_owned_future
      own
      lang (th1 th2: Thread.t lang)
      (STEP: pstep (@Thread.step lang) (ThreadEvent.is_pf /1\ non_sc) th1 th2):
  (exists loc from to val released ord th2' e',
      (<<STEP: Thread.step e' th1 th2'>>) /\
        (<<ACCESS: ThreadEvent.is_writing e' = Some (loc, from, to, val, released, ord)>>) /\
        (<<RACE: own loc = true>>)) \/
    ((<<FUTURE: owned_future_global_promises
                  own
                  (th1.(Thread.global)) (th2.(Thread.global))>>)).
Proof.
  inv STEP. des. inv STEP0; ss.
  { right. inv LOCAL; ss.
    eapply local_cancel_step_owned_future; eauto.
  }
  { hexploit program_step_owned_future.
    { econs; eauto. }
    i. des.
    { left. esplits; eauto. }
    right. esplits; eauto.
  }
Qed.

Lemma pf_steps_owned_future
      own
      lang (th1 th2: Thread.t lang)
      (STEPS: rtc (pstep (@Thread.step lang) (ThreadEvent.is_pf /1\ non_sc)) th1 th2):
  (exists th1' th2' e' loc from to val released ord,
      (<<STEPS: rtc (pstep (@Thread.step lang) (ThreadEvent.is_pf /1\ non_sc)) th1 th1'>>) /\
        (<<STEP: Thread.step e' th1' th2'>>) /\
        (<<ACCESS: ThreadEvent.is_writing e' = Some (loc, from, to, val, released, ord)>>) /\
        (<<RACE: own loc = true>>)) \/
    ((<<FUTURE: owned_future_global_promises
                  own
                  (th1.(Thread.global)) (th2.(Thread.global))>>)).
Proof.
  induction STEPS; i.
  { right. splits; auto. refl. }
  hexploit pf_step_owned_future; eauto. i. des.
  { left. esplits; eauto. }
  { left. esplits; eauto. }
  { left. esplits.
    { econs 2; eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
  }
  { right. r. etrans; eauto. }
Qed.

Lemma promise_step_owned_future
      own
      lang (th1 th2: Thread.t lang) loc
      (STEP: Thread.step (ThreadEvent.promise loc) th1 th2)
      (LC_WF1: Local.wf (Thread.local th1) (Thread.global th1))
      (GL_WF1: Global.wf (Thread.global th1))
      (CONS: rtc_consistent th2)
  :
  (exists th1' th2' e',
      (<<STEPS: rtc (pstep (@Thread.step lang) (ThreadEvent.is_pf /1\ non_sc)) th1 th1'>>) /\
        (<<STEP: Thread.step e' th1' th2'>>) /\
        ((<<FAILURE: ThreadEvent.get_machine_event e' = MachineEvent.failure>>) \/
           (exists loc from to val released ord,
               (<<ACCESS: ThreadEvent.is_writing e' = Some (loc, from, to, val, released, ord)>>) /\
                 (<<RACE: own loc = true>>)))) \/
    ((<<FUTURE: owned_future_global_promises
                  own
                  (th1.(Thread.global)) (th2.(Thread.global))>>) /\
       (<<NOWN: own loc = false>>)).
Proof.
  destruct (own loc) eqn:RACE.
  { left.
    rr in CONS. des.
    eapply CurrentCertify.rtc_step_consistent_ceritfy_racy_promise in STEP.
    2:{ eauto. }
    2:{ eauto. }
    2:{ eapply rtc_implies; [|eauto]. i. inv H. econs; eauto. }
    2:{ eauto. }
    inv STEP.
    { hexploit pf_steps_owned_future; eauto. i. des.
      { esplits; eauto. right. esplits; eauto. }
      { esplits; eauto. }
    }
    { esplits; eauto. right. esplits; eauto. ss. }
  }
  { right.
    inv STEP; inv LOCAL; ss. inv LOCAL0; ss. esplits; eauto.
    ii. rr. splits; ss. inv PROMISE. inv ADD. inv GADD.
    erewrite loc_fun_add_spec. des_ifs.
  }
Qed.

Lemma step_owned_future
      own
      lang (th1 th2: Thread.t lang) e
      (STEP: Thread.step e th1 th2)
      (LC_WF1: Local.wf (Thread.local th1) (Thread.global th1))
      (GL_WF1: Global.wf (Thread.global th1))
      (CONS: rtc_consistent th2)
  :
  (exists th1' th2' e',
      (<<STEPS: rtc (pstep (@Thread.step lang) (ThreadEvent.is_pf /1\ non_sc)) th1 th1'>>) /\
        (<<STEP: Thread.step e' th1' th2'>>) /\
        ((<<FAILURE: ThreadEvent.get_machine_event e' = MachineEvent.failure>>) \/
           (exists loc from to val released ord,
               (<<ACCESS: ThreadEvent.is_writing e' = Some (loc, from, to, val, released, ord)>>) /\
                 (<<RACE: own loc = true>>)))) \/
    ((<<FUTURE: owned_future_global_promises
                  own
                  (th1.(Thread.global)) (th2.(Thread.global))>>)).
Proof.
  inv STEP.
  { inv LOCAL.
    { hexploit promise_step_owned_future; eauto. i. des.
      { left. esplits; eauto. }
      { left. esplits; eauto. right. esplits; eauto. }
      { right. esplits; eauto. }
    }
    { right. esplits; eauto. eapply local_reserve_step_owned_future; eauto. }
    { right. esplits; eauto. eapply local_cancel_step_owned_future; eauto. }
  }
  { hexploit program_step_owned_future; eauto.
    { econs; eauto. }
    i. des; ss.
    { left. esplits; eauto. right. esplits; eauto. }
    { right. esplits; eauto. }
  }
Qed.

Lemma local_internal_step_owned_future
      e lc0 gl0 lc1 gl1
      (STEP: Local.internal_step e lc0 gl0 lc1 gl1)
  :
  owned_future_global_promises
    (BoolMap.minus gl0.(Global.promises) lc0.(Local.promises))
    gl0 gl1.
Proof.
  inv STEP.
  { inv LOCAL. inv PROMISE. ii; ss. split; ss.
    inv ADD. inv GADD. rewrite loc_fun_add_spec.
    unfold BoolMap.minus, andb, negb in OWNED. des_ifs.
  }
  { inv LOCAL. inv RESERVE. ii. split; ss.
    ii. erewrite Memory.add_o in GET; eauto. des_ifs.
  }
  { inv LOCAL. inv CANCEL. ii. split; ss.
    ii. erewrite Memory.remove_o in GET; eauto. des_ifs.
  }
Qed.

Lemma internal_step_owned_future
      lang (th1 th2: Thread.t lang)
      (STEP: Thread.internal_step th1 th2)
  :
  owned_future_global_promises
    (BoolMap.minus th1.(Thread.global).(Global.promises) th1.(Thread.local).(Local.promises))
    (th1.(Thread.global)) (th2.(Thread.global)).
Proof.
  inv STEP. eapply local_internal_step_owned_future in LOCAL; ss.
Qed.

Lemma rtc_internal_step_owned_future
      lang (th1 th2: Thread.t lang)
      (STEPS: rtc (@Thread.internal_step _) th1 th2)
  :
  owned_future_global_promises
    (BoolMap.minus th1.(Thread.global).(Global.promises) th1.(Thread.local).(Local.promises))
    (th1.(Thread.global)) (th2.(Thread.global)).
Proof.
  induction STEPS; i.
  { refl. }
  { hexploit internal_step_owned_future; eauto. i. etrans; eauto.
    inv H. ss. apply Local.internal_step_promises_minus in LOCAL.
    rewrite LOCAL. auto.
  }
Qed.
