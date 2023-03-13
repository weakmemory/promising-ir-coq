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
Require Import BoolMap.
Require Import Promises.
Require Import Global.
(* Require Import MemoryFacts. *)
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import Cover.
(* Require Import MemorySplit. *)
(* Require Import MemoryMerge. *)
(* Require Import FulfillStep. *)
Require Import MemoryProps.

Require Import LowerMemory.

Set Implicit Arguments.

Variant max_readable (gl: Global.t) (prom: BoolMap.t) (loc: Loc.t) (ts: Time.t) (val: Const.t) (released: option View.t): Prop :=
  | max_readable_intro
      from na
      (GET: Memory.get loc ts gl.(Global.memory) = Some (from, Message.message val released na))
      (NONE: implb (gl.(Global.promises) loc) (prom loc))
      (MAX: forall ts' from' msg
                   (TS: Time.lt ts ts')
                   (GET: Memory.get loc ts' gl.(Global.memory) = Some (from', msg))
                   (MSG: msg <> Message.reserve),
          False)
.

Lemma max_readable_inj gl prom loc ts0 ts1 val0 val1 released0 released1
      (MAX0: max_readable gl prom loc ts0 val0 released0)
      (MAX1: max_readable gl prom loc ts1 val1 released1)
  :
    (<<TS: ts0 = ts1>>) /\ (<<VAL: val0 = val1>>) /\ (<<RELEASED: released0 = released1>>).
Proof.
  inv MAX0. inv MAX1.
  assert (ts0 = ts1).
  { apply TimeFacts.antisym.
    { destruct (Time.le_lt_dec ts0 ts1); auto.
      hexploit MAX0; eauto; ss.
    }
    { destruct (Time.le_lt_dec ts1 ts0); auto.
      hexploit MAX; eauto; ss.
    }
  }
  subst. split; auto. clarify.
Qed.

Lemma read_tview_max tvw loc released
      (WF: TView.wf tvw)
  :
    TView.read_tview tvw loc (View.pln (TView.cur tvw) loc) released Ordering.na = tvw.
Proof.
  unfold TView.read_tview. des_ifs. ss.
  rewrite ! View.le_join_l.
  { destruct tvw; auto. }
  { apply View.singleton_rw_spec.
    { apply WF. }
    { transitivity (View.rlx (TView.cur tvw) loc).
      { apply WF. }
      { apply WF. }
    }
  }
  { apply View.bot_spec. }
  { apply View.singleton_rw_spec.
    { apply WF. }
    { apply WF. }
  }
  { apply View.bot_spec. }
Qed.


Lemma max_readable_view_mon gl prom rsv tvw0 tvw1 loc ts val released
      (MAX: max_readable gl prom loc ts val released)
      (TS: tvw0.(TView.cur).(View.pln) loc = ts)
      (TVIEW: TView.le tvw0 tvw1)
      (WF: Local.wf (Local.mk tvw1 prom rsv) gl)
  :
    max_readable gl prom loc (tvw1.(TView.cur).(View.pln) loc) val released.
Proof.
  subst. replace (tvw1.(TView.cur).(View.pln) loc) with (tvw0.(TView.cur).(View.pln) loc); auto.
  apply TimeFacts.antisym.
  { apply TVIEW. }
  destruct (Time.le_lt_dec (tvw1.(TView.cur).(View.pln) loc) (tvw0.(TView.cur).(View.pln) loc)); auto.
  inv MAX. inv WF.
  inv TVIEW_CLOSED. inv CUR. specialize (PLN loc). des.
  exploit MAX0; eauto; ss.
Qed.

Lemma non_max_readable_future gl0 gl1 prom rsv tvw loc ts
      (MAX: forall val released, ~ max_readable gl0 prom loc ts val released)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (FUTURE: Global.strong_le gl0 gl1)
      (WF: Local.wf (Local.mk tvw prom rsv) gl0)
  :
    forall val released, ~ max_readable gl1 prom loc ts val released.
Proof.
  subst. ii. inv H.
  inv WF. inv TVIEW_CLOSED. inv CUR. specialize (PLN loc). des. ss.
  inv FUTURE. inv LE. exploit MEMORY; eauto; ss. i.
  eapply MAX; eauto. econs; eauto.
  { inv ADDNA. specialize (ADDNA0 loc). des.
    { destruct (gl0.(Global.promises) loc), (gl1.(Global.promises) loc), (prom loc); ss. }
    { exfalso. inv LATEST. des. eapply MAX0; eauto. ss. }
  }
  { i. destruct msg; ss. exploit MEMORY; eauto. }
Qed.

Lemma max_readable_read_only_aux gl prom tvw rsv loc ts val released ord
      ts' val' released' lc
      (MAX: max_readable gl prom loc ts val released)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (READ: Local.read_step (Local.mk tvw prom rsv) gl loc ts' val' released' ord lc)
  :
    (<<TS: ts' = ts>>) /\ (<<VAL: Const.le val' val>>) /\ (<<RELEASED: released' = released>>).
Proof.
  assert (ts' = ts).
  { dup READ. inv READ.
    apply TimeFacts.antisym.
    { destruct (Time.le_lt_dec ts' (tvw.(TView.cur).(View.pln) loc)); auto.
      inv MAX. hexploit MAX0; eauto; ss.
    }
    { inv READABLE. auto. }
  }
  subst. inv MAX. inv READ. clarify.
Qed.

Lemma max_readable_read_only gl prom tvw rsv loc ts val released
      ts' val' released' lc
      (MAX: max_readable gl prom loc ts val released)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (READ: Local.read_step (Local.mk tvw prom rsv) gl loc ts' val' released' Ordering.na lc)
      (WF: Local.wf (Local.mk tvw prom rsv) gl)
  :
    (<<TS: ts' = ts>>) /\ (<<VAL: Const.le val' val>>) /\ (<<RELEASED: released' = released>>) /\ (<<LOCAL: lc = Local.mk tvw prom rsv>>).
Proof.
  hexploit max_readable_read_only_aux; eauto.
  i. des. splits; auto.
  inv READ. ss. f_equal.
  unfold TView.read_tview.
  change (Ordering.le Ordering.relaxed Ordering.na) with false. ss.
  change (Ordering.le Ordering.acqrel Ordering.na) with false. ss.
  rewrite ! View.join_bot_r.
  rewrite View.le_join_l; cycle 1.
  { eapply View.singleton_rw_spec; [eapply WF|eapply WF].  }
  rewrite View.le_join_l; cycle 1.
  { eapply View.singleton_rw_spec; [eapply WF|].
    transitivity (View.rlx (TView.cur tvw) loc); [eapply WF|eapply WF].
  }
  destruct tvw; auto.
Qed.

Lemma max_readable_not_racy gl prom rsv tvw loc to ts val released ord
      (MAX: max_readable gl prom loc ts val released)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (RACE: Local.is_racy (Local.mk tvw prom rsv) gl loc to ord)
      (WF: Local.wf (Local.mk tvw prom rsv) gl)
  :
    False.
Proof.
  inv RACE.
  { inv MAX. ss. rewrite GET in NONE. rewrite GETP in NONE. ss. }
  { inv MAX. ss. exploit MAX0; eauto. ss. }
Qed.

Lemma max_readable_not_read_race gl prom rsv tvw loc to ts val released
      val' ord
      (MAX: max_readable gl prom loc ts val released)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (READ: Local.racy_read_step (Local.mk tvw prom rsv) gl loc to val' ord)
      (WF: Local.wf (Local.mk tvw prom rsv) gl)
  :
    False.
Proof.
  inv READ. eapply max_readable_not_racy; eauto.
Qed.

Lemma max_readable_not_write_race gl prom rsv tvw loc to ts val released ord
      (MAX: max_readable gl prom loc ts val released)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (WRITE: Local.racy_write_step (Local.mk tvw prom rsv) gl loc to ord)
      (WF: Local.wf (Local.mk tvw prom rsv) gl)
  :
    False.
Proof.
  inv WRITE. eapply max_readable_not_racy; eauto.
Qed.

Lemma max_readable_read gl prom rsv tvw loc ts val0 val1 released
      (MAX: max_readable gl prom loc ts val1 released)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (WF: Local.wf (Local.mk tvw prom rsv) gl)
      (VAL: Const.le val0 val1)
  :
    exists released,
      (<<READ: Local.read_step (Local.mk tvw prom rsv) gl loc ts val0 released Ordering.na (Local.mk tvw prom rsv)>>).
Proof.
  inv MAX. esplits. econs; eauto.
  { econs; ss. refl. }
  ss. f_equal. rewrite read_tview_max; auto. apply WF.
Qed.


Variant fulfilled_memory (loc: Loc.t) (mem0 mem1: Memory.t): Prop :=
| fulfilled_memory_intro
    (OTHER: forall loc' (NEQ: loc' <> loc) to,
        Memory.get loc' to mem1 = Memory.get loc' to mem0)
    (GET: forall to from msg
                 (GET: Memory.get loc to mem1 = Some (from, msg)),
        Memory.get loc to mem0 = Some (from, msg))
.

Global Program Instance fulfilled_memory_PreOrder loc: PreOrder (fulfilled_memory loc).
Next Obligation.
Proof.
  ii. econs; eauto.
Qed.
Next Obligation.
Proof.
  ii. inv H. inv H0. econs.
  { i. transitivity (Memory.get loc' to y); eauto. }
  { i. exploit GET0; eauto. }
Qed.

Lemma fulfilled_memory_cancel loc from to msg mem0 mem1
      (CANCEL: Memory.remove mem0 loc from to msg mem1)
  :
    fulfilled_memory loc mem0 mem1.
Proof.
  econs.
  { i. erewrite (@Memory.remove_o mem1); eauto. des_ifs. des; clarify. }
  { i. erewrite (@Memory.remove_o mem1) in GET; eauto. des_ifs. }
Qed.

Lemma fulfilled_memory_max_ts loc mem0 mem1
      (INHABITED: Memory.inhabited mem1)
      (FULFILLED: fulfilled_memory loc mem0 mem1)
  :
    Time.le (Memory.max_ts loc mem1) (Memory.max_ts loc mem0).
Proof.
  specialize (INHABITED loc).
  apply Memory.max_ts_spec in INHABITED. des.
  apply FULFILLED in GET.
  apply Memory.max_ts_spec in GET. des. auto.
Qed.

Lemma fulfilled_memory_get0 loc mem0 mem1
      (FULFILLED: fulfilled_memory loc mem0 mem1)
      l to from msg
      (GET: Memory.get l to mem1 = Some (from, msg))
  :
    Memory.get l to mem0 = Some (from, msg).
Proof.
  destruct (Loc.eq_dec l loc).
  { subst. eapply FULFILLED in GET. des. eauto. }
  { inv FULFILLED. rewrite OTHER in GET; auto. }
Qed.

Variant unchanged_loc_memory (loc: Loc.t) (mem0 mem1: Memory.t): Prop :=
| unchanged_loc_memory_intro
    (UNCH: forall to, Memory.get loc to mem1 = Memory.get loc to mem0)
.

Definition unchanged_loc_promises (loc: Loc.t) (prom0 prom1: BoolMap.t): Prop :=
  prom1 loc = prom0 loc.

Global Program Instance unchanged_loc_memory_Equivalence loc:
  Equivalence (unchanged_loc_memory loc).
Next Obligation.
Proof.
  ii. econs. auto.
Qed.
Next Obligation.
Proof.
  ii. inv H. econs; eauto.
Qed.
Next Obligation.
Proof.
  ii. inv H. inv H0. econs. i. etrans; eauto.
Qed.

Global Program Instance unchanged_loc_promises_Equivalence loc:
  Equivalence (unchanged_loc_promises loc).
Next Obligation. ii. rr. refl. Qed.
Next Obligation. ii. rr. symmetry. auto. Qed.
Next Obligation. ii. rr. etrans; eauto. Qed.

Variant unchanged_loc_global (loc: Loc.t) (gl0 gl1: Global.t): Prop :=
| unchanged_loc_global_intro
    (MEMORY: unchanged_loc_memory loc gl0.(Global.memory) gl1.(Global.memory))
    (PROMISES: unchanged_loc_promises loc gl0.(Global.promises) gl1.(Global.promises))
.

Global Program Instance unchanged_loc_global_Equivalence loc:
  Equivalence (unchanged_loc_global loc).
Next Obligation.
Proof.
  ii. econs; refl.
Qed.
Next Obligation.
Proof.
  ii. inv H. econs; symmetry; auto.
Qed.
Next Obligation.
Proof.
  ii. inv H. inv H0. econs; etrans; eauto.
Qed.

Lemma unchanged_loc_max_readable prom0 gl0 prom1 gl1 loc
      (MEM: unchanged_loc_global loc gl0 gl1)
      (PROM: unchanged_loc_promises loc prom0 prom1)
  :
    forall ts val released,
      max_readable gl0 prom0 loc ts val released
      <->
      max_readable gl1 prom1 loc ts val released.
Proof.
  inv MEM. inv MEMORY.
  i. split; i.
  { inv H. econs.
    { rewrite UNCH. eauto. }
    { rewrite PROM. rewrite PROMISES. auto. }
    { i. eapply MAX; eauto. rewrite <- UNCH. eauto. }
  }
  { inv H. econs.
    { rewrite <- UNCH. eauto. }
    { rewrite <- PROM. rewrite <- PROMISES. auto. }
    { i. eapply MAX; eauto. rewrite UNCH. eauto. }
  }
Qed.

Lemma add_unchanged_loc mem0 mem1 loc from to msg loc0
      (ADD: Memory.add mem0 loc from to msg mem1)
      (NEQ: loc0 <> loc)
  :
    unchanged_loc_memory loc0 mem0 mem1.
Proof.
  econs. i. erewrite (@Memory.add_o mem1 mem0); eauto.
  des_ifs. ss. des; clarify.
Qed.

Lemma promises_add_unchanged_loc prm0 prm1 loc loc0
      (ADD: BoolMap.add prm0 loc prm1)
      (NEQ: loc0 <> loc)
  :
    unchanged_loc_promises loc0 prm0 prm1.
Proof.
  rr. inv ADD. setoid_rewrite LocFun.add_spec. des_ifs.
Qed.

Lemma promises_remove_unchanged_loc prm0 prm1 loc loc0
      (REMOVE: BoolMap.remove prm0 loc prm1)
      (NEQ: loc0 <> loc)
  :
    unchanged_loc_promises loc0 prm0 prm1.
Proof.
  rr. inv REMOVE. setoid_rewrite LocFun.add_spec. des_ifs.
Qed.

Lemma promises_fulfill_unchanged_loc prm0 gprm0 loc ord prm1 gprm1 loc0
      (FULFILL: Promises.fulfill prm0 gprm0 loc ord prm1 gprm1)
      (NEQ: loc0 <> loc)
  :
  (<<PROM: unchanged_loc_promises loc0 prm0 prm1>>) /\
    (<<GPROM: unchanged_loc_promises loc0 gprm0 gprm1>>).
Proof.
  inv FULFILL.
  { split; refl. }
  { split; eapply promises_remove_unchanged_loc; eauto. }
Qed.

Lemma promises_promise_unchanged_loc prm0 gprm0 loc prm1 gprm1 loc0
      (PROMISE: Promises.promise prm0 gprm0 loc prm1 gprm1)
      (NEQ: loc0 <> loc)
  :
  (<<PROM: unchanged_loc_promises loc0 prm0 prm1>>) /\
    (<<GPROM: unchanged_loc_promises loc0 gprm0 gprm1>>).
Proof.
  inv PROMISE.
  split; eapply promises_add_unchanged_loc; eauto.
Qed.

Lemma remove_unchanged_loc mem0 mem1 loc from to msg loc0
      (REMOVE: Memory.remove mem0 loc from to msg mem1)
      (NEQ: loc0 <> loc)
  :
    unchanged_loc_memory loc0 mem0 mem1.
Proof.
  econs. i. erewrite (@Memory.remove_o mem1 mem0); eauto.
  des_ifs; ss; des; clarify.
Qed.

Lemma reserve_unchanged_loc rsv0 mem0 loc from to rsv1 mem1 loc0
      (RESERVE: Memory.reserve rsv0 mem0 loc from to rsv1 mem1)
      (NEQ: loc0 <> loc)
  :
  (<<RSV: unchanged_loc_memory loc0 rsv0 rsv1>>) /\
    (<<MEM: unchanged_loc_memory loc0 mem0 mem1>>).
Proof.
  inv RESERVE. split; eapply add_unchanged_loc; eauto.
Qed.

Lemma cancel_unchanged_loc rsv0 mem0 loc from to rsv1 mem1 loc0
      (CANCEL: Memory.cancel rsv0 mem0 loc from to rsv1 mem1)
      (NEQ: loc0 <> loc)
  :
  (<<RSV: unchanged_loc_memory loc0 rsv0 rsv1>>) /\
    (<<MEM: unchanged_loc_memory loc0 mem0 mem1>>).
Proof.
  inv CANCEL. split; eapply remove_unchanged_loc; eauto.
Qed.



Lemma remove_reserves_loc prom0 mem0 loc
      (MLE: Memory.le prom0 mem0)
      (FIN: Memory.finite prom0)
      (INHABITED: Memory.inhabited mem0)
  :
    exists prom1 mem1,
      (<<RESERVE: cancel_future_memory loc prom0 mem0 prom1 mem1>>) /\
      (<<MEM: fulfilled_memory loc mem0 mem1>>) /\
      (<<RESERVE: forall to from msg
                         (GET: Memory.get loc to prom1 = Some (from, msg)),
          msg <> Message.reserve>>) /\
      (<<PROMISES: forall loc' to,
          Memory.get loc' to prom1 =
          if Loc.eq_dec loc' loc
          then match (Memory.get loc' to prom0) with
               | Some (from, Message.reserve) => None
               | x => x
               end
          else Memory.get loc' to prom0>>) /\
      (<<INHABITED: Memory.inhabited mem1>>).
Proof.
  hexploit (wf_cell_msgs_exists (prom0 loc)). i. des. clear WFMSGS.
  hexploit (@list_filter_exists _ (fun '(_, _, msg) => msg = Message.reserve) l).
  i. des.
  assert (exists rs,
             forall from to (GET: Memory.get loc to prom0 = Some (from, Message.reserve)),
               List.In to rs).
  { exists (List.map (snd <*> fst) l').  i.
    hexploit (proj1 (COMPLETE0 (from, to, Message.reserve))).
    { split; auto. apply COMPLETE. auto. }
    i. eapply List.in_map with (f:=(snd <*> fst)) in H. auto.
  }
  clear l l' COMPLETE COMPLETE0. des. ginduction rs.
  { i. exists prom0, mem0. splits.
    { econs. }
    { refl. }
    { ii. subst. eapply H in GET; eauto. }
    { i. des_ifs. hexploit H; eauto. ss. }
    { auto. }
  }
  { i. destruct (classic (exists from, Memory.get loc a prom0 = Some (from, Message.reserve))).
    { des.
      hexploit (@Memory.remove_exists prom0 loc from a Message.reserve); auto.
      i. des.
      hexploit Memory.remove_exists.
      { eapply MLE. eapply Memory.remove_get0; eauto. } i. des.
      assert (REMOVE: Memory.cancel prom0 mem0 loc from a mem2 mem1).
      { econs; eauto. }
      hexploit (IHrs mem2 mem1 loc); auto.
      { eapply cancel_memory_le; eauto. }
      { eapply Memory.remove_finite; eauto. }
      { apply Memory.cancel_inhabited in REMOVE; auto. }
      { i. erewrite Memory.remove_o in GET; eauto. des_ifs.
        ss. des; clarify. apply H in GET. des; clarify. }
      { i. des. exists prom1, mem3. splits.
        { econs; eauto. }
        { etrans; eauto. eapply fulfilled_memory_cancel; eauto. }
        { auto. }
        { i. rewrite PROMISES.
          erewrite (@Memory.remove_o mem2); eauto.
          des_ifs; ss; des; clarify.
        }
        { auto. }
      }
    }
    { eapply (IHrs prom0 mem0 loc); eauto. i.
      hexploit H; eauto. i. ss. des; clarify.
      exfalso. eapply H0. eauto.
    }
  }
Qed.

(* Lemma ts_le_memory_write_na *)
(*       ts0 prom0 mem0 loc from to val prom1 mem1 msgs kinds kind ts1 *)
(*       (WRITE: Memory.write_na ts1 prom0 mem0 loc from to val prom1 mem1 msgs kinds kind) *)
(*       (TS: Time.le ts0 ts1) *)
(*   : *)
(*     Memory.write_na ts0 prom0 mem0 loc from to val prom1 mem1 msgs kinds kind. *)
(* Proof. *)
(*   revert ts0 TS. induction WRITE; i. *)
(*   { econs 1; eauto. eapply TimeFacts.le_lt_lt; eauto. } *)
(*   { econs 2; eauto. eapply TimeFacts.le_lt_lt; eauto. } *)
(* Qed. *)

(* Lemma write_na_ts_lt ts prom0 mem0 loc from to val prom1 mem1 msgs kinds kind *)
(*       (WRITE: Memory.write_na ts prom0 mem0 loc from to val prom1 mem1 msgs kinds kind) *)
(*   : *)
(*     Time.lt ts to. *)
(* Proof. *)
(*   induction WRITE; auto. etrans; eauto. *)
(* Qed. *)

Lemma add_max_ts mem0 loc from to msg mem1
      (ADD: Memory.add mem0 loc from to msg mem1)
      (CLOSED: Memory.closed mem0)
  :
  Memory.max_ts loc mem1 = if (Time.le_lt_dec to (Memory.max_ts loc mem0)) then (Memory.max_ts loc mem0) else to.
Proof.
  inv CLOSED. specialize (INHABITED loc).
  eapply Memory.max_ts_spec in INHABITED. des.
  eapply Memory.add_get1 in GET; eauto.
  eapply Memory.max_ts_spec in GET. des; eauto.
  hexploit Memory.add_get0; eauto. i. des.
  hexploit Memory.max_ts_spec; eauto. i. des.
  erewrite Memory.add_o in GET2; eauto. des_ifs.
  { ss. des; clarify. eapply TimeFacts.antisym; auto. }
  { ss. des; clarify. eapply TimeFacts.antisym; auto.
    eapply Memory.max_ts_spec in GET2. des; eauto. }
  { ss. des; clarify. }
  { ss. des; clarify. eapply TimeFacts.antisym; auto.
    eapply Memory.max_ts_spec in GET2. des; eauto.
    left. eapply TimeFacts.le_lt_lt; eauto.
  }
Qed.

Lemma le_add_max_ts mem0 loc from to msg mem1
      (ADD: Memory.add mem0 loc from to msg mem1)
      (TO: Time.le (Memory.max_ts loc mem0) to)
  :
    Memory.max_ts loc mem1 = to.
Proof.
  hexploit Memory.add_get0; eauto. i. des.
  eapply Memory.max_ts_spec in GET0. des.
  erewrite Memory.add_o in GET1; eauto. des_ifs.
  { ss. des; clarify. }
  { ss. des; clarify.
    apply Memory.max_ts_spec in GET1. des.
    apply TimeFacts.antisym; auto. etrans; eauto.
  }
Qed.

Lemma timemap_singleton_neq loc ts loc0
      (NEQ: loc0 <> loc)
  :
    TimeMap.singleton loc ts loc0 = Time.bot.
Proof.
  unfold TimeMap.singleton. setoid_rewrite LocFun.add_spec_neq; auto.
Qed.

Lemma timemap_singleton_eq loc ts
  :
    TimeMap.singleton loc ts loc = ts.
Proof.
  unfold TimeMap.singleton. setoid_rewrite LocFun.add_spec_eq; auto.
Qed.

Lemma local_write_step_timestamp_pln
      lc0 gl0 loc from to val releasedm released ord lc1 gl1
      (WRITE: Local.write_step lc0 gl0 loc from to val releasedm released ord lc1 gl1)
      (WF: TView.wf lc0.(Local.tview))
  :
    lc1.(Local.tview).(TView.cur).(View.pln) loc = to.
Proof.
  inv WRITE. ss. unfold TimeMap.join.
  rewrite timemap_singleton_eq. apply TimeFacts.le_join_r.
  inv WRITABLE. left. eapply TimeFacts.le_lt_lt; eauto.
  eapply WF.
Qed.

Lemma local_write_step_timestamp_rlx
      lc0 gl0 loc from to val releasedm released ord lc1 gl1
      (WRITE: Local.write_step lc0 gl0 loc from to val releasedm released ord lc1 gl1)
      (WF: TView.wf lc0.(Local.tview))
  :
    lc1.(Local.tview).(TView.cur).(View.rlx) loc = to.
Proof.
  inv WRITE. ss. unfold TimeMap.join.
  rewrite timemap_singleton_eq. apply TimeFacts.le_join_r.
  inv WRITABLE. left. eauto.
Qed.

Lemma max_readable_na_write_step gl0 rsv0 prom0 tvw0 loc ts from to val0 val1 released
      (MAX: max_readable gl0 prom0 loc ts val0 released)
      (TS: tvw0.(TView.cur).(View.pln) loc = ts)
      (WF: Local.wf (Local.mk tvw0 prom0 rsv0) gl0)
      (CLOSED: Global.wf gl0)
      (FROM: Time.le (Memory.max_ts loc gl0.(Global.memory)) from)
      (TO: Time.lt from to)
  :
  exists mem1 mem2 rsv1 tvw1,
    (<<RESERVE: cancel_future_memory loc rsv0 gl0.(Global.memory) rsv1 mem1>>) /\
      (<<ADD0: Memory.add mem1 loc from to (Message.message val1 None true) mem2>>) /\
      (<<RESERVES: forall loc' ts',
          Memory.get loc' ts' rsv1 =
            if Loc.eq_dec loc' loc
            then None
            else Memory.get loc' ts' rsv0>>) /\
      (<<WRITE: Local.write_step (Local.mk tvw0 prom0 rsv1) (Global.mk gl0.(Global.sc) gl0.(Global.promises) mem1) loc from to val1 None None Ordering.na (Local.mk tvw1 (fun loc' => if Loc.eq_dec loc' loc then false else prom0 loc') rsv1) (Global.mk gl0.(Global.sc) (fun loc' => if Loc.eq_dec loc' loc then false else gl0.(Global.promises) loc') mem2)>>) /\
      (<<VIEW: tvw1.(TView.cur).(View.pln) loc = to>>) /\
      (<<MAXTS: Memory.max_ts loc mem2 = to>>) /\
      (<<MAX: max_readable (Global.mk gl0.(Global.sc) (fun loc' => if Loc.eq_dec loc' loc then false else gl0.(Global.promises) loc') mem2) (fun loc' => if Loc.eq_dec loc' loc then false else prom0 loc') loc to val1 None>>)
.
Proof.
  hexploit (@remove_reserves_loc rsv0 gl0.(Global.memory) loc).
  { apply WF. }
  { apply WF. }
  { eapply CLOSED. }
  i. des.
  hexploit (@Memory.add_exists mem1 loc from to (Message.message val1 None true)); auto.
  { ii. eapply Memory.max_ts_spec in GET2. des.
    inv LHS. inv RHS. ss.
    eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; [apply FROM0|].
    etrans; eauto. etrans; eauto. etrans; [|eapply FROM].
    eapply fulfilled_memory_max_ts; eauto.
  }
  i. des.
  assert (WRITE: Local.write_step (Local.mk tvw0 prom0 prom1) (Global.mk gl0.(Global.sc) gl0.(Global.promises) mem1) loc from to val1 None None Ordering.na (Local.mk (TView.write_tview tvw0 loc to Ordering.na) (fun loc' => if Loc.eq_dec loc' loc then false else prom0 loc') prom1) (Global.mk gl0.(Global.sc) (fun loc' => if Loc.eq_dec loc' loc then false else gl0.(Global.promises) loc') mem2)).
  { econs; ss.
    { econs. inv WF. inv TVIEW_CLOSED. inv CUR. specialize (RLX loc). des.
      ss. eapply Memory.max_ts_spec in RLX. des.
      eapply TimeFacts.le_lt_lt; [eapply MAX0|].
      eapply TimeFacts.le_lt_lt; eauto.
    }
    { destruct (prom0 loc) eqn:EQ.
      { econs 2; ss. econs; ss. eapply WF. ss. }
      { econs 1.
        { extensionality l. des_ifs. }
        { extensionality l. des_ifs. inv MAX.
          rewrite EQ in NONE. destruct (gl0.(Global.promises) loc); ss.
        }
      }
    }
    { ss. }
  }
  assert (MAXTS: Memory.max_ts loc mem2 = to).
  { eapply le_add_max_ts; eauto. etrans.
    { eapply fulfilled_memory_max_ts; eauto. }
    etrans; eauto. left. auto.
  }
  eexists mem1, mem2, prom1,  _. splits; eauto.
  { i. rewrite PROMISES. des_ifs.
    inv WF. eapply RESERVES_ONLY in Heq. ss.
  }
  { hexploit local_write_step_timestamp_pln; eauto. eapply WF. }
  { econs.
    { eapply Memory.add_get0; eauto. }
    { ss. des_ifs. }
    { i. ss. eapply Memory.max_ts_spec in GET. des.
      subst. eapply Time.lt_strorder.
      eapply TimeFacts.le_lt_lt; [apply MAX0|apply TS0].
    }
  }
Qed.

Lemma write_max_readable
      lc0 gl0 loc from to val releasedm released ord lc1 gl1
      val0 released0
      (WRITE: Local.write_step lc0 gl0 loc from to val releasedm released ord lc1 gl1)
      (WF: Local.wf lc0 gl0)
      (MAX: max_readable gl1 lc1.(Local.promises) loc (lc1.(Local.tview).(TView.cur).(View.pln) loc) val0 released0)
  :
    (<<VAL: val0 = val>>) /\ (<<RELEASED: released0 = released>>).
Proof.
  hexploit local_write_step_timestamp_pln; eauto.
  { apply WF. }
  i. rewrite H in MAX. inv MAX. inv WRITE.
  eapply Memory.add_get0 in WRITE0. des. ss. clarify.
Qed.

Lemma max_readable_write gl0 rsv0 prom0 tvw0 loc ts from to val1 lprm1 gprm1 ord releasedm
      (TS: tvw0.(TView.cur).(View.pln) loc = ts)
      (WF: Local.wf (Local.mk tvw0 prom0 rsv0) gl0)
      (CLOSED: Global.wf gl0)
      (FROM: Time.le (Memory.max_ts loc gl0.(Global.memory)) from)
      (TO: Time.lt from to)
      (FULFILL: Promises.fulfill prom0 gl0.(Global.promises) loc ord lprm1 gprm1)
      (RELEASEDM: View.opt_wf releasedm)
      (NORACE: gl0.(Global.promises) loc = true -> prom0 loc = true)
  :
  exists tvw1 mem1,
    (<<WRITE: Local.write_step (Local.mk tvw0 prom0 rsv0) gl0 loc from to val1 releasedm (TView.write_released tvw0 loc to releasedm ord) ord (Local.mk tvw1 lprm1 rsv0) (Global.mk gl0.(Global.sc) gprm1 mem1)>>) /\
      (<<ADD0: Memory.add gl0.(Global.memory) loc from to (Message.message val1 (TView.write_released tvw0 loc to releasedm ord) (Ordering.le ord Ordering.na)) mem1>>) /\
      (<<VIEWPLN: tvw1.(TView.cur).(View.pln) loc = to>>) /\
      (<<VIEWRLX: tvw1.(TView.cur).(View.rlx) loc = to>>) /\
      (<<MAXTS: Memory.max_ts loc mem1 = to>>) /\
      (<<MAX: max_readable (Global.mk gl0.(Global.sc) gprm1 mem1) lprm1 loc to val1 (TView.write_released tvw0 loc to releasedm ord)>>)
.
Proof.
  hexploit (@Memory.add_exists gl0.(Global.memory) loc from to (Message.message val1 (TView.write_released tvw0 loc to releasedm ord) (Ordering.le ord Ordering.na))); auto.
  { ii. eapply Memory.max_ts_spec in GET2. des.
    inv LHS. inv RHS. ss.
    eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; [apply FROM0|].
    etrans; eauto.
  }
  { econs; eauto. eapply TViewFacts.write_future0; eauto. eapply WF. }
  i. des.
  assert (MAXTS: Memory.max_ts loc mem2 = to).
  { eapply le_add_max_ts; eauto. etrans; eauto. left. auto. }
  assert (WRITE: Local.write_step
                   (Local.mk tvw0 prom0 rsv0)
                   gl0
                   loc from to val1 releasedm (TView.write_released tvw0 loc to releasedm ord) ord
                   (Local.mk (TView.write_tview tvw0 loc to ord) lprm1 rsv0)
                   (Global.mk gl0.(Global.sc) gprm1 mem2)).
  { econs; ss; eauto.
    { econs. inv WF. inv TVIEW_CLOSED. inv CUR. specialize (RLX loc). des.
      ss. eapply Memory.max_ts_spec in RLX. des.
      eapply TimeFacts.le_lt_lt; [eapply MAX|].
      eapply TimeFacts.le_lt_lt; eauto.
    }
  }
  esplits; eauto.
  { eapply local_write_step_timestamp_pln in WRITE; eauto. eapply WF. }
  { eapply local_write_step_timestamp_rlx in WRITE; eauto. eapply WF. }
  { econs.
    { eapply Memory.add_get0; eauto. }
    { ss. inv FULFILL.
      { unfold implb. des_ifs. eapply NORACE; auto. }
      { inv REMOVE. inv GREMOVE. setoid_rewrite LocFun.add_spec_eq. auto. }
    }
    { i. ss. eapply Memory.max_ts_spec in GET. des.
      subst. eapply Time.lt_strorder.
      eapply TimeFacts.le_lt_lt; [apply MAX|apply TS0].
    }
  }
Qed.

Lemma non_max_readable_race gl prom tvw rsv loc
      (MAX: forall val released, ~ max_readable gl prom loc (tvw.(TView.cur).(View.pln) loc) val released)
      (WF: Local.wf (Local.mk tvw prom rsv) gl)
  :
    exists to, Local.is_racy (Local.mk tvw prom rsv) gl loc to Ordering.na.
Proof.
  inv WF. inv TVIEW_CLOSED. inv CUR. ss.
  specialize (PLN loc). des.
  apply NNPP. ii. eapply MAX. econs; eauto.
  { destruct (prom loc) eqn:LCPROM, (Global.promises gl loc) eqn:GLPROM; ss.
    exfalso. eapply H. exists None. econs; ss.
  }
  { destruct msg; ss. i. eapply H.
    eexists (Some ts'). econs; eauto.
  }
Qed.

Lemma non_max_readable_read gl prom rsv tvw loc ts val'
      (MAX: forall val released, ~ max_readable gl prom loc ts val released)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (WF: Local.wf (Local.mk tvw prom rsv) gl)
  :
    exists to, Local.racy_read_step (Local.mk tvw prom rsv) gl loc to val' Ordering.na.
Proof.
  subst. hexploit non_max_readable_race; eauto. i. des. eauto.
Qed.

Lemma non_max_readable_write gl prom rsv tvw loc ts
      (MAX: forall val released, ~ max_readable gl prom loc ts val released)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (WF: Local.wf (Local.mk tvw prom rsv) gl)
  :
    exists to, Local.racy_write_step (Local.mk tvw prom rsv) gl loc to Ordering.na.
Proof.
  subst. hexploit non_max_readable_race; eauto. i. des. eauto.
Qed.

Variant added_memory loc msgs mem0 mem1: Prop :=
| added_memory_intro
    (MLE: Memory.le mem0 mem1)
    (OTHER: forall loc' (NEQ: loc' <> loc) to, Memory.get loc' to mem1 = Memory.get loc' to mem0)
    (COMPLETE: forall from to msg
                      (IN: List.In (from, to, msg) msgs),
        Memory.get loc to mem1 = Some (from, msg))
    (SOUND: forall from to msg
                   (GET: Memory.get loc to mem1 = Some (from, msg)),
        (<<GET: Memory.get loc to mem0 = Some (from, msg)>>) \/
        (<<IN: List.In (from, to, msg) msgs>>))
.

Lemma added_memory_nil loc mem
  :
    added_memory loc [] mem mem.
Proof.
  econs; eauto.
  { refl. }
  { i. ss. }
Qed.

Lemma added_memory_cons loc from to msg msgs mem0 mem1 mem2
      (ADD: Memory.add mem0 loc from to msg mem1)
      (ADDED: added_memory loc msgs mem1 mem2)
  :
    added_memory loc ((from, to, msg)::msgs) mem0 mem2.
Proof.
  inv ADDED. econs; eauto.
  { etrans; eauto. ii. eapply Memory.add_get1 in LHS; eauto. }
  { i. rewrite OTHER; auto.
    erewrite (@Memory.add_o mem1); eauto. des_ifs.
    ss. des; clarify.
  }
  { i. ss. des; clarify.
    { eapply MLE. eapply Memory.add_get0; eauto. }
    { apply COMPLETE; auto. }
  }
  { i. apply SOUND in GET. des; ss; auto.
    erewrite Memory.add_o in GET0; eauto. des_ifs; auto.
    ss. des; clarify. auto.
  }
Qed.

Lemma added_memory_unchanged_loc loc msgs mem0 mem1 loc0
      (ADDED: added_memory loc msgs mem0 mem1)
      (NEQ: loc0 <> loc)
  :
    unchanged_loc_memory loc0 mem0 mem1.
Proof.
  induction ADDED. econs. i.
  rewrite OTHER; eauto.
Qed.


Lemma add_promises_latest lang (st: lang.(Language.state)) prm gprm tvw sc loc msgs:
  forall mem0 rsv0
         (WFMSGS: wf_cell_msgs msgs)
         (MLE: Memory.le rsv0 mem0)
         (MEM: Memory.closed mem0)
         (FORALL: List.Forall
                    (fun '(from, to, msg) => (__guard__((<<RESERVE: msg = Message.reserve>>) /\ (<<DISJOINT: forall to2 from2 msg2 (GET: Memory.get loc to2 mem0 = Some (from2, msg2)), Interval.disjoint (from, to) (from2, to2)>>))) /\ (<<TS: Time.lt from to>>)) msgs),
  exists rsv1 mem1,
    (<<STEPS: rtc (@Thread.internal_step _) (Thread.mk _ st (Local.mk tvw prm rsv0) (Global.mk sc gprm mem0)) (Thread.mk _ st (Local.mk tvw prm rsv1) (Global.mk sc gprm mem1))>>) /\
    (<<MEM: added_memory loc msgs mem0 mem1>>) /\
    (<<PROMISES: added_memory loc msgs rsv0 rsv1>>).
Proof.
  induction msgs; i.
  { esplits; eauto.
    { eapply added_memory_nil. }
    { eapply added_memory_nil. }
  }
  { inv FORALL. destruct a as [[from to] msg]. des.
    red in WFMSGS. des. inv DISJOINT. inv MSGSWF. guardH H3.
    rr in H1. des; subst.
    hexploit (@Memory.add_exists mem0 loc from to Message.reserve); eauto.
    i. des. hexploit Memory.add_exists_le; eauto. i. des.
    assert (ADD: Memory.reserve rsv0 mem0 loc from to mem2' mem2).
    { econs; eauto. }
    hexploit (IHmsgs mem2 mem2').
    { red. splits; auto. }
    { ii. erewrite (@Memory.add_o _ rsv0) in LHS; eauto.
      erewrite (@Memory.add_o _ mem0); eauto. des_ifs. eapply MLE; auto.
    }
    { eapply Memory.add_closed; eauto. }
    { eapply List.Forall_forall.
      intros [[from0 to0] msgs0]. i.
      eapply List.Forall_forall in H2; eauto.
      eapply List.Forall_forall in H4; eauto.
      eapply List.Forall_forall in HD; eauto. ss. des; subst.
      { timetac. }
      splits; auto.
      { rr in H2. des. rr. splits; auto. i.
        erewrite Memory.add_o in GET; eauto. des_ifs.
        { ss. des; clarify.
          symmetry. eapply interval_le_disjoint. auto.
        }
        { eapply DISJOINT0; eauto. }
      }
    }
    i. des. esplits.
    { econs 2; [|eauto]. econs. econs 2; eauto. }
    { eapply added_memory_cons; eauto. }
    { eapply added_memory_cons; eauto. }
  }
Qed.
