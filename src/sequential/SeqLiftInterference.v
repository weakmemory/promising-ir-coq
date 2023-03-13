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
Require Import BoolMap.
Require Import Promises.
Require Import Global.
Require Import Thread.
Require Import Configuration.

Require Import Cover.
(* Require Import MemorySplit. *)
(* Require Import MemoryMerge. *)
(* Require Import FulfillStep. *)
Require Import MemoryProps.

Require Import LowerMemory.
(* Require Import JoinedView. *)

Require Import MaxView.
(* Require Import Delayed. *)

Require Import Lia.

(* Require Import JoinedView. *)
Require Import SeqLift.
Require Import Sequential.

(* Require Import Pred. *)

Require Import SeqLiftStep.

Lemma max_value_no_flag_le f srctm flag_src flag_tgt lc_src lc_tgt mem_src mem_tgt loc v_src v_tgt
      (MEM: sim_global flag_src flag_tgt (BoolMap.minus mem_src.(Global.promises) lc_src.(Local.promises)) f mem_src mem_tgt)
      (LOCAL: sim_local f flag_src flag_tgt srctm lc_src lc_tgt)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
      (MAXSRC: max_value_src loc (Some v_src) mem_src lc_src)
      (MAXTGT: max_value_tgt loc (Some v_tgt) mem_tgt lc_tgt)
      (LOCALWF: Local.wf lc_tgt mem_tgt)
      (WF: Mapping.wfs f)
  :
    Const.le v_tgt v_src.
Proof.
  hexploit no_flag_max_value_same; eauto.
  i. des. inv MAX. inv MAXTGT.
  hexploit MAX0; eauto. i. des. hexploit MAX; eauto. i. des.
  eapply max_readable_inj in MAX1; eauto. des. subst. auto.
Qed.

Lemma max_value_sim_timestamp_exact
      f srctm flag_src flag_tgt lc_src lc_tgt mem_src mem_tgt loc v_src v_tgt
      (MEM: sim_global flag_src flag_tgt (BoolMap.minus mem_src.(Global.promises) lc_src.(Local.promises)) f mem_src mem_tgt)
      (LOCAL: sim_local f flag_src flag_tgt srctm lc_src lc_tgt)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
      (MAXSRC: max_value_src loc (Some v_src) mem_src lc_src)
      (MAXTGT: max_value_tgt loc (Some v_tgt) mem_tgt lc_tgt)
      (LOCALWF: Local.wf lc_tgt mem_tgt)
      (WF: Mapping.wfs f)
  :
    sim_timestamp_exact
      (f loc) ((f loc).(Mapping.ver))
      (lc_src.(Local.tview).(TView.cur).(View.pln) loc)
      (Some (lc_tgt.(Local.tview).(TView.cur).(View.pln) loc)).
Proof.
  inv MEM.
  inv MAXTGT. hexploit MAX; eauto. i. des. inv MAX0.
  inv MAXSRC. hexploit MAX0; eauto. i. des. inv MAX2.
  hexploit sim_memory_get; eauto; ss.
  { unfold boolmap_plus. rewrite FLAGSRC. rewrite FLAGTGT. ss. }
  { unfold implb in NONE0. unfold BoolMap.minus, andb, negb. des_ifs. }
  i. des; cycle 1.
  { hexploit MAX3; eauto; ss. eapply TimeFacts.le_lt_lt; eauto.
    eapply sim_timestamp_le; eauto.
    { inv LOCAL. inv TVIEW. eapply sim_tview_cur; auto. }
    { refl. }
    { eapply mapping_latest_wf_loc. }
  }
  assert (to_src = (tvw0.(TView.cur).(View.pln) loc)); [|clarify].
  inv LOCAL. ss. eapply TimeFacts.antisym.
  { destruct (Time.le_lt_dec to_src (View.pln (TView.cur tvw0) loc)); ss.
    exfalso. hexploit MAX3; eauto. inv MSG; ss.
  }
  { eapply sim_timestamp_le.
    { eapply TVIEW; auto. }
    { eauto. }
    { refl. }
    { eauto. }
    { eapply mapping_latest_wf_loc. }
  }
Qed.

Variant sim_reserves_past
        (reserves: list (Loc.t * Time.t * Time.t))
        (f_past: Mapping.ts)

        (f: Mapping.ts)
        (prom_src prom_tgt: Memory.t): Prop :=
| sim_reserves_past_intro
    (MESSAGENORMAL: forall loc to from msg_tgt
                     (GET: Memory.get loc to prom_tgt = Some (from, msg_tgt))
                     (IN: ~ List.In (loc, to, from) reserves),
        exists fto ffrom,
          (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom (Some from)>>) /\
          (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto (Some to)>>) /\
          (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)>>) /\
          (<<RESERVE: msg_tgt = Message.reserve>>))
    (MESSAGERESERVE: forall loc to from msg_tgt
                     (GET: Memory.get loc to prom_tgt = Some (from, msg_tgt))
                     (IN: List.In (loc, to, from) reserves),
        exists fto ffrom,
          (<<FROM: sim_timestamp_exact (f_past loc) (f_past loc).(Mapping.ver) ffrom (Some from)>>) /\
          (<<TO: sim_timestamp_exact (f_past loc) (f_past loc).(Mapping.ver) fto (Some to)>>) /\
          (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)>>) /\
          (<<RESERVE: msg_tgt = Message.reserve>>))
    (SOUND: forall loc fto ffrom
                   (GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)),
        ((exists to from,
             (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto (Some to)>>) /\
               (<<GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)>>) /\
               (<<IN: ~ List.In (loc, to, from) reserves>>)) \/
           (exists to from,
               (<<TO: sim_timestamp_exact (f_past loc) (f_past loc).(Mapping.ver) fto (Some to)>>) /\
                 (<<GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)>>) /\
                 (<<IN: List.In (loc, to, from) reserves>>))))
    (RESERVES: forall loc from to (IN: List.In (loc, to, from) reserves),
        Memory.get loc to prom_tgt = Some (from, Message.reserve))
    (DISJOINT: forall loc to_src0 to_src1 to_tgt0 to_tgt1 msg0 from_tgt0 from_tgt1
                      (GET: Memory.get loc to_tgt0 prom_tgt = Some (from_tgt0, msg0))
                      (NIN: ~ List.In (loc, to_tgt0, from_tgt0) reserves)
                      (IN: List.In (loc, to_tgt1, from_tgt1) reserves)
                      (TS0: sim_timestamp_exact (f_past loc) (f_past loc).(Mapping.ver) to_src1 (Some to_tgt1))
                      (TS1: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src0 (Some to_tgt0)),
        to_src1 <> to_src0)
.

Lemma sim_reserves_past_nil_sim_promises
      f_past f prom_src prom_tgt
      (SIM: sim_reserves_past [] f_past f prom_src prom_tgt)
  :
  sim_reserves f prom_src prom_tgt.
Proof.
  inv SIM. econs; eauto; ss.
  { i. hexploit MESSAGENORMAL; eauto. i. des. esplits; eauto. }
  { i. hexploit SOUND; eauto. i. des.
    { esplits; eauto. }
    { ss. }
  }
Qed.

Lemma promise_step_max_values_src
      lang st0 st1 lc0 lc1 mem0 mem1 vs
      (PROMISE: Thread.internal_step (Thread.mk lang st0 lc0 mem0) (Thread.mk _ st1 lc1 mem1))
      (MAX: max_values_src vs mem0 lc0)
  :
  max_values_src vs mem1 lc1.
Proof.
  inv PROMISE. eapply promise_max_values_src; eauto.
Qed.

Lemma promise_steps_max_values_src
      lang st0 st1 lc0 lc1 mem0 mem1 vs
      (PROMISE: rtc (@Thread.internal_step _) (Thread.mk lang st0 lc0 mem0) (Thread.mk _ st1 lc1 mem1))
      (MAX: max_values_src vs mem0 lc0)
  :
  max_values_src vs mem1 lc1.
Proof.
  remember (Thread.mk lang st0 lc0 mem0).
  remember (Thread.mk lang st1 lc1 mem1).
  revert st0 st1 lc0 lc1 mem0 mem1 Heqt Heqt0 MAX. induction PROMISE; i; clarify.
  destruct y. eapply promise_step_max_values_src in H; eauto.
Qed.

Inductive wf_reserve_list: list (Loc.t * Time.t * Time.t) -> Prop :=
| wf_reserve_list_nil
  :
  wf_reserve_list []
| wf_reserve_list_cons
    loc from to tl
    (TL: wf_reserve_list tl)
    (HD: List.Forall (fun '(loc0, to0, from0) => forall (LOC: loc0 = loc), Interval.disjoint (from, to) (from0, to0)) tl)
  :
  wf_reserve_list ((loc, to, from)::tl)
.

Lemma past_update_sim_reserves
      prom_src0 loc to_tgt from_tgt reserves f_past f prom_tgt
      prom_src1 prom_src2 to_src0 from_src0 to_src1 from_src1
      (SIMPROM: sim_reserves_past ((loc, to_tgt, from_tgt)::reserves) f_past f prom_src0 prom_tgt)
      (RESERVES: wf_reserve_list ((loc, to_tgt, from_tgt)::reserves))
      (REMOVE: Memory.remove prom_src0 loc from_src0 to_src0 Message.reserve prom_src1)
      (ADD: Memory.add prom_src1 loc from_src1 to_src1 Message.reserve prom_src2)
      (TO0: sim_timestamp_exact (f_past loc) (f_past loc).(Mapping.ver) to_src0 (Some to_tgt))
      (FROM0: sim_timestamp_exact (f_past loc) (f_past loc).(Mapping.ver) from_src0 (Some from_tgt))
      (TO1: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src1 (Some to_tgt))
      (FROM1: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src1 (Some from_tgt))
      (BOTNONE: forall loc, Memory.get loc Time.bot prom_tgt = None)
      (MAPWF0: Mapping.wfs f_past)
      (MAPWF1: Mapping.wfs f)
  :
  sim_reserves_past reserves f_past f prom_src2 prom_tgt.
Proof.
  pose proof mapping_latest_wf_loc as VERWF.
  assert (NODUP: forall from0, ~ List.In (loc, to_tgt, from0) reserves).
  { ii. inv RESERVES. eapply List.Forall_forall in HD; eauto. ss.
    inv SIMPROM. hexploit RESERVES; eauto.
    { left. eauto. }
    i. hexploit memory_get_ts_strong; [eapply H0|]. i. des; clarify.
    { rewrite BOTNONE in H0. ss. }
    hexploit RESERVES; eauto.
    { right. eauto. }
    i. hexploit memory_get_ts_strong; [eapply H0|]. i. des; clarify.
    eapply HD; auto.
    { instantiate (1:=to_tgt). econs; ss. refl. }
    { econs; ss. refl. }
  }
  assert (GET: Memory.get loc to_tgt prom_tgt = Some (from_tgt, Message.reserve)).
  { inv SIMPROM. eapply RESERVES0; eauto. left. auto. }
  inv SIMPROM. econs.
  { i. destruct (classic ((loc, to, from) = (loc0, to_tgt, from_tgt))).
    { clarify. esplits; eauto.
      { eapply Memory.add_get0; eauto. }
    }
    { hexploit MESSAGENORMAL; eauto.
      { ii. ss. des; eauto. clarify. }
      i. des. esplits; eauto.
      eapply Memory.add_get1; eauto.
      erewrite Memory.remove_o; eauto. des_ifs.
      ss. des; clarify. exfalso. eapply DISJOINT; eauto. ii. des; auto.
    }
  }
  { i. hexploit MESSAGERESERVE; eauto.
    { right. auto. }
    i. des. esplits; eauto.
    eapply Memory.add_get1; eauto. erewrite Memory.remove_o; eauto. des_ifs.
    ss. des; clarify. exfalso.
    eapply sim_timestamp_exact_unique in TO0; eauto. clarify.
    eapply NODUP; eauto.
  }
  { i. erewrite Memory.add_o in GET0; eauto.
    erewrite Memory.remove_o in GET0; eauto. des_ifs.
    { ss. des; clarify. left. esplits; eauto. }
    { guardH o. guardH o0. hexploit SOUND; eauto. i. des.
      { left. esplits; eauto. ii. eapply IN. right. auto. }
      { right. esplits; eauto. ss. des; auto. clarify.
        eapply sim_timestamp_exact_inject in TO0; eauto.
        subst. red in o0. des; ss.
      }
    }
  }
  { i. eapply RESERVES0; eauto. right. auto. }
  { i. destruct (classic ((loc0, to_tgt0, from_tgt0) = (loc, to_tgt, from_tgt))).
    { clarify. ii. subst.
      hexploit RESERVES0.
      { right. eauto. }
      i. hexploit MESSAGERESERVE.
      { eauto. }
      { right. auto. }
      i. des.
      eapply sim_timestamp_exact_inject in TO1; eauto. subst.
      eapply sim_timestamp_exact_inject in TS0; eauto. subst.
      eapply Memory.add_get0 in ADD. des.
      erewrite Memory.remove_o in GET1; eauto. des_ifs.
      ss. des; clarify.
      eapply sim_timestamp_exact_unique in TO0; eauto. clarify.
    }
    { eapply DISJOINT; eauto.
      { ii. ss. des; ss; auto. }
      { ss. right. eauto. }
    }
  }
Qed.

Lemma sim_reserves_past_get_reserve
      reserves f_past f prom_src prom_tgt loc to_tgt from_tgt
      (SIM: sim_reserves_past reserves f_past f prom_src prom_tgt)
      (IN: List.In (loc, to_tgt, from_tgt) reserves)
  :
    exists to_src from_src,
      (<<FROM: sim_timestamp_exact (f_past loc) (f_past loc).(Mapping.ver) from_src (Some from_tgt)>>) /\
      (<<TO: sim_timestamp_exact (f_past loc) (f_past loc).(Mapping.ver) to_src (Some to_tgt)>>) /\
      (<<GETTGT: Memory.get loc to_tgt prom_tgt = Some (from_tgt, Message.reserve)>>) /\
      (<<GETSRC: Memory.get loc to_src prom_src = Some (from_src, Message.reserve)>>)
.
Proof.
  inv SIM.
  hexploit RESERVES; eauto. i.
  hexploit MESSAGERESERVE; eauto. i. des. esplits; eauto.
Qed.

Lemma sim_reserves_past_update
      reserves f_past f flag_tgt rsv_tgt mem_tgt
      (MAPLE: Mapping.les f_past f)
      (MAPWF1: Mapping.wfs f)
      (MAPWF0: Mapping.wfs f_past)
      (MLETGT: Memory.le rsv_tgt mem_tgt.(Global.memory))
      (INHABITED: Memory.inhabited mem_tgt.(Global.memory))
      (ONLY: Memory.reserve_only rsv_tgt)
  :
    forall
      rsv_src0 mem_src0 prm_src
      (RESERVES: wf_reserve_list reserves)
      (MLESRC: Memory.le rsv_src0 mem_src0.(Global.memory))
      (SIMMEM: sim_global (fun _ => false) flag_tgt (BoolMap.minus (Global.promises mem_src0) prm_src) f mem_src0 mem_tgt)
      (SIMPROM: sim_reserves_past reserves f_past f rsv_src0 rsv_tgt)
      (EMPTY: forall loc from_tgt to_tgt from_src to_src from to msg
                     (IN: List.In (loc, to_tgt, from_tgt) reserves)
                     (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src (Some from_tgt))
                     (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt))
                     (GET: Memory.get loc to mem_src0.(Global.memory) = Some (from, msg)),
          Interval.disjoint (from_src, to_src) (from, to))
      lang st tvw,
    exists rsv_src1 mem_src1,
      (<<STEPS: rtc (@Thread.internal_step _) (Thread.mk lang st (Local.mk tvw prm_src rsv_src0) mem_src0) (Thread.mk lang st (Local.mk tvw prm_src rsv_src1) mem_src1)>>) /\
      (<<SIMMEM: sim_global (fun _ => false) flag_tgt (BoolMap.minus (Global.promises mem_src1) prm_src) f mem_src1 mem_tgt>>) /\
      (<<SIMPROM: sim_reserves f rsv_src1 rsv_tgt>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt.(Global.memory) rsv_tgt) f mem_src0.(Global.memory) f mem_src1.(Global.memory)>>) /\
      (<<OWNED: forall loc, owned_future_global_loc loc mem_src0 mem_src1>>)
.
Proof.
  pose proof mapping_latest_wf_loc as VERWF.
  induction reserves.
  { i. esplits.
    { refl. }
    { eauto. }
    { eapply sim_reserves_past_nil_sim_promises; eauto. }
    { eapply space_future_memory_refl; eauto. refl. }
    { i. refl. }
  }
  i. destruct a as [[loc from_tgt] to_tgt].
  assert (BOTNONE: forall loc0, Memory.get loc0 Time.bot rsv_tgt = None).
  { i. destruct (Memory.get loc0 Time.bot rsv_tgt) eqn:GET; auto.
    destruct p. dup GET. eapply MLETGT in GET.
    rewrite (INHABITED loc0) in GET; ss. clarify.
    exploit ONLY; eauto. i. ss.
  }
  hexploit sim_reserves_past_get_reserve; eauto.
  { left. eauto. }
  i. des. hexploit Memory.remove_exists.
  { eapply GETSRC. }
  intros [rsv_src1 REMOVEPROM].
  hexploit Memory.remove_exists.
  { eapply MLESRC. eauto. }
  intros [mem_src1 REMOVEMEM].
  hexploit sim_timestamp_exact_mon_exists; [eapply FROM|..]; eauto.
  intros [from_src1 [FROM1 _]]. des.
  hexploit sim_timestamp_exact_mon_exists; [eapply TO|..]; eauto.
  intros [to_src1 [TO1 _]]. des.
  assert (PROMISE0: Memory.cancel rsv_src0 mem_src0.(Global.memory) loc from_src to_src rsv_src1 mem_src1).
  { econs; eauto. }
  hexploit cancel_memory_le; eauto. intros MLE1.
  hexploit (@Memory.add_exists mem_src1 loc from_src1 to_src1 Message.reserve).
  { i. eapply EMPTY; eauto.
    { left. eauto. }
    { erewrite Memory.remove_o in GET2; eauto. des_ifs. eauto. }
  }
  { eapply sim_timestamp_exact_lt; eauto.
    hexploit memory_get_ts_strong; [eapply GETTGT|..]. i. des; clarify.
    rewrite BOTNONE in GETTGT. ss.
  }
  { econs. }
  intros [mem_src2 ADDMEM].
  hexploit Memory.add_exists_le; eauto.
  intros [rsv_src2 ADDPROM].
  assert (PROMISE1: Memory.reserve rsv_src1 mem_src1 loc from_src1 to_src1 rsv_src2 mem_src2).
  { econs; eauto. }
  hexploit reserve_memory_le; eauto. intros MLE2.
  inv SIMMEM. hexploit IHreserves.
  { inv RESERVES. eauto. }
  { instantiate (1:=Global.mk _ _ _). eapply MLE2. }
  { econs; eauto.
    eapply src_cancel_sim_memory in REMOVEMEM; eauto.
    eapply add_src_covered_sim_memory; eauto. i. econs.
    { eapply MLETGT; eauto. }
    { eauto. }
  }
  { eapply past_update_sim_reserves; eauto. }
  { i. erewrite Memory.add_o in GET; eauto.
    erewrite Memory.remove_o in GET; eauto. des_ifs.
    { ss. des; clarify. inv RESERVES.
      eapply sim_disjoint; eauto.
      eapply List.Forall_forall in HD; eauto. ss. symmetry. auto.
    }
    { eapply EMPTY; eauto. right. auto. }
  }
  i. des. esplits.
  { econs 2.
    { econs 1. econs 3; eauto. }
    econs 2.
    { econs 1. econs 2; eauto. }
    { eapply STEPS. }
  }
  { eauto. }
  { eauto. }
  { eapply space_future_memory_trans_memory; eauto.
    eapply space_future_memory_trans_memory.
    { eapply space_future_covered_decr.
      i. eapply remove_covered in COVERED; eauto. des; eauto.
    }
    { eapply space_future_covered_add; eauto.
      i. eapply sim_disjoint; eauto. inv MSG.
      hexploit Memory.get_disjoint.
      { eapply MLETGT. eapply GETTGT. }
      { eapply GET. }
      i. des; clarify.
    }
    { eauto. }
  }
  { i. etrans; eauto. rr. splits; ss. etrans.
    { eapply remove_owned_future; eauto. }
    { eapply add_reserve_owned_future; eauto. }
  }
Qed.

Lemma to_NoDup A (l: list A)
  :
    exists l_nd,
      (<<NODUP: List.NoDup l_nd>>) /\
      (<<IFF: forall a, List.In a l <-> List.In a l_nd>>).
Proof.
  induction l.
  { exists []. splits; ss. econs. }
  { des. destruct (classic (List.In a l_nd)).
    { exists l_nd. splits; auto. i. ss. split; i.
      { des.
        { subst. auto. }
        { eapply IFF; auto. }
      }
      { right. eapply IFF; auto. }
    }
    { exists (a::l_nd). splits.
      { econs; ss. }
      { i. ss. split; i.
        { des; auto. right. eapply IFF; auto. }
        { des; auto. right. eapply IFF; auto. }
      }
    }
  }
Qed.

Lemma sim_reserves_past_exists
      f0 f1
      mem_src0 mem_src1 mem_tgt rsv_src rsv_tgt prm_src flag_tgt
      (MAPLE: Mapping.les f0 f1)
      (SIM: sim_reserves f0 rsv_src rsv_tgt)
      (MEMORY: sim_global (fun _ => false) flag_tgt (BoolMap.minus mem_src0.(Global.promises) prm_src) f0 mem_src0 mem_tgt)
      (SPACE: space_future_memory (Messages.of_memory rsv_tgt) f0 mem_src0.(Global.memory) f1 mem_src1.(Global.memory))
      (FINITE: Memory.finite rsv_tgt)
      (ONLY: Memory.reserve_only rsv_tgt)
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wfs f1)
      (MLESRC0: Memory.le rsv_src mem_src0.(Global.memory))
  :
    exists reserves,
      (<<PROM: sim_reserves_past reserves f0 f1 rsv_src rsv_tgt>>) /\
      (<<RESERVES: wf_reserve_list reserves>>) /\
      (<<EMPTY: forall loc from_tgt to_tgt from_src to_src from to msg
                       (IN: List.In (loc, to_tgt, from_tgt) reserves)
                       (FROM: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) from_src (Some from_tgt))
                       (TO: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) to_src (Some to_tgt))
                       (GET: Memory.get loc to mem_src1.(Global.memory) = Some (from, msg)),
          Interval.disjoint (from_src, to_src) (from, to)>>)
.
Proof.
  pose proof mapping_latest_wf_loc as VERWF.
  red in FINITE. des.
  assert (exists (reserves0: list (Loc.t * Time.t * Time.t)),
             forall loc to_tgt from_tgt to_src from_src
                    (DOM: List.In (loc, to_tgt) dom)
                    (GET: Memory.get loc to_tgt rsv_tgt = Some (from_tgt, Message.reserve))
                    (FROM: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) from_src (Some from_tgt))
                    (TO: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) to_src (Some to_tgt))
                    (TS: ~ (sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) from_src (Some from_tgt) /\ sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) to_src (Some to_tgt))),
               List.In (loc, to_tgt, from_tgt) reserves0).
  { clear. induction dom; auto.
    { exists []. i. ss. }
    destruct a as [loc to_tgt].
    hexploit IHdom; eauto. i. des.
    destruct (classic (exists from_tgt to_src from_src,
                          (<<GET: Memory.get loc to_tgt rsv_tgt = Some (from_tgt, Message.reserve)>>) /\
                          (<<FROM: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) from_src (Some from_tgt)>>) /\
                          (<<TO: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) to_src (Some to_tgt)>>) /\
                          (<<TS: ~ (sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) from_src (Some from_tgt) /\ sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) to_src (Some to_tgt))>>))).
    { des. exists ((loc, to_tgt, from_tgt)::reserves0). i. ss. des.
      { clarify. auto. }
      { right. esplits; eauto. }
    }
    { exists (reserves0). i. ss. des.
      { clarify. exfalso. eapply H0; eauto. esplits; eauto. }
      { eapply H; eauto. }
    }
  }
  des. hexploit (list_filter_exists
                   (fun '(loc, to_tgt, from_tgt) =>
                      exists to_src from_src,
                        (<<GET: Memory.get loc to_tgt rsv_tgt = Some (from_tgt, Message.reserve)>>) /\
                        (<<FROM: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) from_src (Some from_tgt)>>) /\
                        (<<TO: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) to_src (Some to_tgt)>>) /\
                        (<<TS: ~ (sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) from_src (Some from_tgt) /\ sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) to_src (Some to_tgt))>>)) reserves0).
  i. des.
  hexploit (to_NoDup _ l'). i. des.
  assert (RESERVECOMPLETE: forall loc to_tgt from_tgt to_src from_src
                                  (GET: Memory.get loc to_tgt rsv_tgt = Some (from_tgt, Message.reserve))
                                  (FROM: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) from_src (Some from_tgt))
                                  (TO: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) to_src (Some to_tgt))
                                  (TS: ~ (sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) from_src (Some from_tgt) /\ sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) to_src (Some to_tgt))),
             List.In (loc, to_tgt, from_tgt) l_nd).
  { i. eapply IFF. eapply COMPLETE. splits.
    { eapply H; eauto. }
    { esplits; eauto. }
  }
  assert (RESERVESOUND: forall loc to_tgt from_tgt
                               (IN: List.In (loc, to_tgt, from_tgt) l_nd),
             exists to_src from_src,
               (<<GET: Memory.get loc to_tgt rsv_tgt = Some (from_tgt, Message.reserve)>>) /\
               (<<FROM: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) from_src (Some from_tgt)>>) /\
               (<<TO: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) to_src (Some to_tgt)>>) /\
               (<<TS: ~ (sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) from_src (Some from_tgt) /\ sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) to_src (Some to_tgt))>>)).
  { i. eapply IFF in IN. eapply COMPLETE in IN. des. esplits; eauto. }
  assert (MESSAGENORMAL: forall loc to from msg_tgt
                     (GET: Memory.get loc to rsv_tgt = Some (from, msg_tgt))
                     (NIN: ~ List.In (loc, to, from) l_nd),
        exists fto ffrom,
          (<<FROM: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) ffrom (Some from)>>) /\
          (<<TO: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) fto (Some to)>>) /\
          (<<FROM0: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) ffrom (Some from)>>) /\
          (<<TO0: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) fto (Some to)>>) /\
          (<<GET: Memory.get loc fto rsv_src = Some (ffrom, Message.reserve)>>) /\
          (<<MSG: msg_tgt = Message.reserve>>)).
  { i. exploit ONLY; eauto. i. subst.
    hexploit sim_reserves_get; eauto. i. des.
    hexploit GET0; eauto. i.
    assert (sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) from_src (Some from) /\ sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) to_src (Some to)).
    { eapply NNPP. ii. eapply NIN. eapply RESERVECOMPLETE; eauto. }
    des. esplits; eauto.
  }
  assert (MESSAGERESERVE: forall loc to from msg_tgt
                                 (GET: Memory.get loc to rsv_tgt = Some (from, msg_tgt))
                                 (IN: List.In (loc, to, from) l_nd),
             exists fto ffrom,
               (<<FROM: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) ffrom (Some from)>>) /\
               (<<TO: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) fto (Some to)>>) /\
               (<<GET: Memory.get loc fto rsv_src = Some (ffrom, Message.reserve)>>) /\
               (<<RESERVE: msg_tgt = Message.reserve>>)).
  { i. hexploit RESERVESOUND; eauto. i. des. clarify.
    hexploit sim_reserves_get; eauto. i. des.
    hexploit GET; eauto. i. des. esplits; eauto.
  }
  exists l_nd. splits.
  { clear H COMPLETE. econs.
    { i. hexploit MESSAGENORMAL; eauto. i. des. esplits; eauto. }
    { auto. }
    { i. hexploit sim_reserves_get_if; eauto. i. des.
      { destruct (classic (List.In (loc, to_tgt, from_tgt) l_nd)).
        { right. esplits; eauto. }
        { left. esplits; eauto. eapply NNPP. ii. eapply H.
          eapply RESERVECOMPLETE; eauto.
          { ii. des. ss. }
        }
      }
    }
    { i. hexploit RESERVESOUND; eauto. i. des. eauto. }
    { ii. subst.
      hexploit RESERVESOUND; eauto. i. des.
      hexploit MESSAGERESERVE; eauto. i. des.
      eapply sim_timestamp_exact_inject in FROM; eauto. subst.
      eapply sim_timestamp_exact_inject in TO; eauto. subst.
      eapply sim_timestamp_exact_inject in TS0; eauto. subst.
      hexploit MESSAGENORMAL; [|eapply NIN|..]; eauto. i. des.
      eapply sim_timestamp_exact_inject in TS1; eauto. subst.
      eapply sim_timestamp_exact_unique in TO0; eauto. clarify.
    }
  }
  { revert NODUP RESERVESOUND. clear. induction l_nd.
    { i. econs. }
    { i. destruct a as [[loc to_tgt] from_tgt]. inv NODUP. econs.
      { eapply IHl_nd; eauto.
        i. hexploit RESERVESOUND; eauto. right. auto.
      }
      { eapply List.Forall_forall. intros [[loc0 to_tgt0] from_tgt0] IN0.
        i. subst. hexploit RESERVESOUND.
        { right. eauto. }
        i. des.
        hexploit RESERVESOUND.
        { left. eauto. }
        i. des.
        hexploit Memory.get_disjoint.
        { eapply GET0. }
        { eapply GET. }
        i. des; clarify.
      }
    }
  }
  { ii. eapply RESERVESOUND in IN. des.
    inv SPACE. hexploit SPACE0.
    { econs; eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { econs; eauto. }
    { i. des. subst. eapply TS; eauto. }
  }
Qed.

Lemma sim_memory_flag_D flag0 D0 flag1 D1 f mem_src mem_tgt
      (SIM: sim_memory flag0 D0 f mem_src mem_tgt)
      (FLAGS: forall loc,
          (D0 loc = true \/ flag0 loc = true) -> (D1 loc = true \/ flag1 loc = true))
  :
  sim_memory flag1 D1 f mem_src mem_tgt.
Proof.
  econs.
  { i. specialize (FLAGS loc). hexploit sim_memory_get; eauto.
    { destruct (flag0 loc); ss. hexploit FLAGS; auto. i. des; clarify. }
    { destruct (D0 loc); ss. hexploit FLAGS; auto. i. des; clarify. }
    i. des.
    { left. esplits; eauto. }
    { right. esplits; eauto. }
  }
  { i. hexploit sim_memory_sound; eauto. }
Qed.

Lemma sim_global_flag_D flag_tgt0 D0 flag_tgt1 D1 f gl_src gl_tgt
      (SIM: sim_global (fun _ => false) flag_tgt0 D0 f gl_src gl_tgt)
      (FLAGS: forall loc,
          (D0 loc = true \/ flag_tgt0 loc = true) -> (D1 loc = true \/ flag_tgt1 loc = true))
  :
  sim_global (fun _ => false) flag_tgt1 D1 f gl_src gl_tgt.
Proof.
  inv SIM. econs; eauto.
  eapply sim_memory_flag_D; eauto.
Qed.

Lemma sim_global_future prm_src flag_tgt f0 f1 mem_src0 mem_tgt0 mem_src1 mem_tgt1
      (SIM0: sim_global (fun _ => false) flag_tgt (BoolMap.minus (Global.promises mem_src0) prm_src) f0 mem_src0 mem_tgt0)
      (SIM1: sim_global (fun _ => false) (fun _ => false) (Global.promises mem_src1) f1 mem_src1 mem_tgt1)
      (OWNED: owned_future prm_src (f0, mem_src0, mem_tgt0) (f1, mem_src1, mem_tgt1))
      (MEMLESRC: Global.strong_le mem_src0 mem_src1)
      (MEMLETGT: Global.le mem_tgt0 mem_tgt1)
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wfs f1)
      (MAPLE: Mapping.les f0 f1)
  :
  sim_global (fun _ => false) flag_tgt (BoolMap.minus (Global.promises mem_src1) prm_src) f1 mem_src1 mem_tgt1.
Proof.
  inv SIM0. inv SIM1. econs; eauto. ss.
  econs.
  { unfold boolmap_plus, BoolMap.minus, orb, andb, negb.
    i. destruct (prm_src loc) eqn:EQP.
    { inv OWNED. hexploit FUTURE; eauto. i. des.
      inv GLTGT. des. ss.
      destruct msg_tgt; ss. eapply H in GET.
      clear MEM0. hexploit sim_memory_get; eauto.
      { unfold BoolMap.minus, andb, negb. rewrite EQP. des_ifs. }
      i. des.
      { dup MSG. inv MSG. left. esplits; eauto.
        { eapply sim_timestamp_exact_mon_strong; eauto. }
        { eapply MEMLESRC; eauto. }
        { eapply sim_message_mon_mapping_latest; eauto. }
      }
      { right. esplits; eauto.
        { eapply sim_timestamp_exact_mon_strong; eauto. }
        { eapply MEMLESRC; eauto. }
      }
    }
    { hexploit sim_memory_get; eauto.
      { des_ifs; auto. }
      i. des.
      { left. esplits; eauto. }
      { right. esplits; eauto. }
    }
  }
  { i. hexploit sim_memory_sound; eauto. }
Qed.

Lemma sim_thread_future
      f0 flag_tgt vs_src0 vs_tgt0
      mem_src0 mem_tgt0 lc_src0 lc_tgt0

      f1 mem_src1 mem_tgt1
      lang st
      (SIM: sim_thread
              f0 (fun _ => false) flag_tgt vs_src0 vs_tgt0
              mem_src0 mem_tgt0 lc_src0 lc_tgt0)

      (MEMLESRC: Global.strong_le mem_src0 mem_src1)
      (MEMLETGT: Global.le mem_tgt0 mem_tgt1)
      (SPACE: space_future_memory (Messages.of_memory lc_tgt0.(Local.reserves)) f0 mem_src0.(Global.memory) f1 mem_src1.(Global.memory))
      (OWNED: owned_future lc_src0.(Local.promises) (f0, mem_src0, mem_tgt0) (f1, mem_src1, mem_tgt1))

      (SIMMEM: sim_global (fun _ => false) (fun _ => false) mem_src1.(Global.promises) f1 mem_src1 mem_tgt1)

      (MAPLE: Mapping.les f0 f1)

      (LOCALSRC0: Local.wf lc_src0 mem_src0)
      (LOCALTGT0: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC0: Global.wf mem_src0)
      (MEMTGT0: Global.wf mem_tgt0)
      (WF0: Mapping.wfs f0)
      (MEMSRC1: Global.wf mem_src1)
      (MEMTGT1: Global.wf mem_tgt1)
      (WF1: Mapping.wfs f1)
      (LOCALSRC1: Local.wf lc_src0 mem_src1)
      (LOCALTGT1: Local.wf lc_tgt0 mem_tgt1)
  :
  exists lc_src2 mem_src2,
    (<<STEPS: rtc (@Thread.tau_step lang) (Thread.mk lang st lc_src0 mem_src1) (Thread.mk lang st lc_src2 mem_src2)>>) /\
      ((<<FAILURE: Thread.steps_failure (Thread.mk lang st lc_src2 mem_src2)>>) \/
         exists f2 vs_src1 vs_tgt1,
           (<<SIM: sim_thread
                     f2 (fun _ => false) flag_tgt vs_src1 vs_tgt1
                     mem_src2 mem_tgt1 lc_src2 lc_tgt0>>) /\
             (<<VALSRC: forall loc val (VAL: vs_src1 loc = Some val), vs_src0 loc = Some val>>) /\
             (<<VALTGT: forall loc val (VAL: vs_tgt1 loc = Some val), vs_tgt0 loc = Some val>>) /\
             (<<SPACE: space_future_memory (unchangable mem_tgt1.(Global.memory) lc_tgt0.(Local.reserves)) f1 mem_src1.(Global.memory) f2 mem_src2.(Global.memory)>>) /\
             (<<MAPLE: Mapping.les_strong f1 f2>>) /\
             (<<MAPWF: Mapping.wfs f2>>) /\
             (<<OWNED: owned_future (BoolMap.minus mem_src1.(Global.promises) lc_src0.(Local.promises)) (f1, mem_src1, mem_tgt1) (f2, mem_src2, mem_tgt1)>>))
.
Proof.
  pose proof mapping_latest_wf_loc as VERWF.
  hexploit (@max_values_src_exists mem_src1 lc_src0).
  intros [vs_src1 MAXSRC1]. des.
  inv SIM. inv LOCAL.
  assert (VALSRC: forall loc val (VAL: vs_src1 loc = Some val), vs_src0 loc = Some val).
  { i. specialize (MAXSRC loc). specialize (MAXSRC1 loc). inv MAXSRC. inv MAXSRC1.
    hexploit MAX0; eauto. i. des. destruct (vs_src0 loc) eqn:EQ.
    { hexploit MAX; eauto. i. des. inv MAX1. inv MAX2.
      inv MEMLESRC. inv LE. eapply MEMORY in GET0. ss. clarify.
    }
    { exfalso. hexploit non_max_readable_future; eauto. }
  }
  assert (OWNSRC: forall loc (PROM: prm_src loc = true), vs_src1 loc = vs_src0 loc).
  { i. eapply max_value_src_inj.
    { eauto. }
    { eapply owned_future_max_value_src; eauto.
      { inv OWNED. eapply FUTURE; ss. }
      { eapply MEMLESRC. }
    }
  }
  hexploit (choice (fun loc v_tgt =>
                      (<<MAX: max_value_tgt loc v_tgt mem_tgt1 (Local.mk tvw_tgt prm_tgt rsv_tgt)>>) /\
                      (<<OPTREL: option_rel (fun _ _ => True) (vs_src1 loc) v_tgt>>) /\
                      (<<VALTGT: forall val (VAL: v_tgt = Some val), vs_tgt0 loc = Some val>>))).
  { intros loc. destruct (prm_src loc) eqn:EQP.
    { esplits.
      { eapply owned_future_max_value_tgt; eauto.
        { inv OWNED. eapply FUTURE; ss. }
      }
      { rewrite OWNSRC; auto. }
      { auto. }
    }
    { destruct (vs_src1 loc) eqn:VSRC.
      2:{ exists None. splits; ss. }
      hexploit VALSRC; eauto. intros VS. des.
      specialize (MAXSRC loc). inv MAXSRC. hexploit MAX; eauto. i. des. inv MAX0.
      specialize (PERM loc). rewrite VS in PERM.
      destruct (vs_tgt0 loc) eqn:VTGT0; ss.
      specialize (MAXTGT loc). inv MAXTGT. hexploit MAX0; eauto. i. des. inv MAX2.
      specialize (MAXSRC1 loc). inv MAXSRC1. hexploit MAX2; eauto. i. des. inv MAX4.
      inv MEMLETGT. exploit MEMORY; eauto. i.
      eexists (Some _). splits; eauto.
      inv SIMMEM. econs. i. clarify. esplits. econs; ss.
      { eauto. }
      { inv PROMISES0. hexploit SIM; eauto. i.
        etrans; eauto. etrans; eauto.
      }
      { i. destruct msg; ss.
        hexploit sim_memory_get; ss.
        { eapply MEM0. }
        { eauto. }
        { ss. }
        { unfold boolmap_plus. ss. }
        { destruct (gprm_src loc); ss. }
        i. des.
        { inv MSG0. hexploit MAX5; eauto; ss.
          eapply sim_timestamp_lt.
          2:{ eauto. }
          { eapply sim_timestamp_mon_ver.
            { erewrite <- sim_timestamp_mon_mapping.
              { eapply TVIEW; eauto. }
              { eauto. }
              { eapply mapping_latest_wf_loc. }
              { eauto. }
            }
            { eapply MAPLE. }
            { eauto. }
            { eapply mapping_latest_wf_loc. }
          }
          { eauto. }
          { eauto. }
          { eapply mapping_latest_wf_loc. }
        }
        { hexploit MAX5; eauto; ss. eapply TimeFacts.le_lt_lt; eauto.
          eapply sim_timestamp_le.
          2:{ eauto. }
          { eapply sim_timestamp_mon_ver.
            { erewrite <- sim_timestamp_mon_mapping.
              { eapply TVIEW; eauto. }
              { eauto. }
              { eapply mapping_latest_wf_loc. }
              { eauto. }
            }
            { eapply MAPLE. }
            { eauto. }
            { eapply mapping_latest_wf_loc. }
          }
          { ss. left. eauto. }
          { eauto. }
          { eapply mapping_latest_wf_loc. }
        }
      }
    }
  }
  intros [vs_tgt1 MAXTGT1].
  hexploit sim_reserves_past_exists; eauto.
  { eapply LOCALTGT1. }
  { eapply LOCALTGT1. }
  { eapply LOCALSRC0. }
  i. des.
  hexploit sim_reserves_past_update; eauto.
  { eapply LOCALTGT1. }
  { eapply MEMTGT1. }
  { eapply LOCALTGT1. }
  { eapply LOCALSRC1. }
  { instantiate (1:=prm_src). instantiate (1:=flag_tgt).
    eapply sim_global_future; eauto.
  }
  i. des. ss. esplits.
  { eapply rtc_implies; [|eauto]. i. inv H. econs; [econs 1;eauto|]. inv LOCAL; ss. }  right. exists f1, vs_src1, vs_tgt1. splits.
  { econs.
    { eauto. }
    { econs; eauto. eapply sim_tview_mon_latest; eauto. }
    { eapply promise_steps_max_values_src in STEPS; eauto. }
    { ii. eapply MAXTGT1. }
    { i. hexploit (MAXTGT1 loc); eauto. i. des. auto. }
    { auto. }
    { i; ss. }
    { i. split; auto. destruct (flag_tgt loc) eqn:EQF; ss.
      rewrite OWNSRC in VAL; auto.
      { hexploit FLAGNONE; eauto. i. des; clarify. }
      { inv PROMISES. eauto. }
    }
  }
  { i. eauto. }
  { i. hexploit (MAXTGT1 loc); eauto. i. des. eapply VALTGT; auto. }
  { eapply space_future_memory_trans; eauto.
    { eapply space_future_memory_refl; eauto. refl. }
    { refl. }
    { refl. }
  }
  { refl. }
  { auto. }
  { econs. i. splits.
    { refl. }
    { eapply OWNED0; eauto. }
    { refl. }
  }
Qed.
