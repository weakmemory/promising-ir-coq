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


Record sim_tview
       (f: Mapping.ts)
       (flag: Loc.t -> bool)
       (tvw_src: TView.t) (tvw_tgt: TView.t)
  :
    Prop :=
  sim_tview_intro {
      sim_tview_rel: forall loc,
        sim_view (fun loc0 => loc0 <> loc) f (Mapping.vers f) (tvw_src.(TView.rel) loc) (tvw_tgt.(TView.rel) loc);
      sim_tview_cur: sim_view (fun loc => flag loc = false) f (Mapping.vers f) tvw_src.(TView.cur) tvw_tgt.(TView.cur);
      sim_tview_acq: sim_view (fun loc => flag loc = false) f (Mapping.vers f) tvw_src.(TView.acq) tvw_tgt.(TView.acq);
    }.

Lemma sim_tview_mon_latest f0 f1 flag_src tvw_src tvw_tgt
      (SIM: sim_tview f0 flag_src tvw_src tvw_tgt)
      (LE: Mapping.les f0 f1)
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wfs f1)
  :
    sim_tview f1 flag_src tvw_src tvw_tgt.
Proof.
  econs.
  { i. eapply sim_view_mon_mapping_latest; [eapply SIM|..]; eauto. }
  { eapply sim_view_mon_mapping_latest; [eapply SIM|..]; eauto. }
  { eapply sim_view_mon_mapping_latest; [eapply SIM|..]; eauto. }
Qed.

Lemma sim_tview_tgt_mon f flag_src tvw_src tvw_tgt0 tvw_tgt1
      (SIM: sim_tview f flag_src tvw_src tvw_tgt0)
      (TVIEW: TView.le tvw_tgt0 tvw_tgt1)
  :
    sim_tview f flag_src tvw_src tvw_tgt1.
Proof.
  econs.
  { i. eapply sim_view_mon_tgt.
    { eapply SIM. }
    { eapply TVIEW. }
  }
  { eapply sim_view_mon_tgt.
    { eapply SIM. }
    { eapply TVIEW. }
  }
  { eapply sim_view_mon_tgt.
    { eapply SIM. }
    { eapply TVIEW. }
  }
Qed.

Lemma sim_tview_src_mon f flag_src tvw_src0 tvw_src1 tvw_tgt
      (SIM: sim_tview f flag_src tvw_src1 tvw_tgt)
      (TVIEW: TView.le tvw_src0 tvw_src1)
  :
    sim_tview f flag_src tvw_src0 tvw_tgt.
Proof.
  econs.
  { i. eapply sim_view_mon_src.
    { eapply SIM. }
    { eapply TVIEW. }
  }
  { eapply sim_view_mon_src.
    { eapply SIM. }
    { eapply TVIEW. }
  }
  { eapply sim_view_mon_src.
    { eapply SIM. }
    { eapply TVIEW. }
  }
Qed.

Lemma sim_tview_mon_locs f flag0 flag1 tvw_src tvw_tgt
      (SIM: sim_tview f flag0 tvw_src tvw_tgt)
      (FLAGS: forall loc (FLAG: flag0 loc = true), flag1 loc = true)
  :
    sim_tview f flag1 tvw_src tvw_tgt.
Proof.
  inv SIM. econs; eauto.
  { eapply sim_view_mon_locs; eauto. i. ss.
    specialize (FLAGS x0). destruct (flag0 x0), (flag1 x0); ss. hexploit FLAGS; ss.
  }
  { eapply sim_view_mon_locs; eauto. i. ss.
    specialize (FLAGS x0). destruct (flag0 x0), (flag1 x0); ss. hexploit FLAGS; ss.
  }
Qed.

Variant sim_local
        (f: Mapping.ts)
        (flag_src: Loc.t -> bool)
        (flag_tgt: Loc.t -> bool)
        (srctm: Loc.t -> Time.t)
  :
    Local.t -> Local.t -> Prop :=
| sim_local_intro
    tvw_src tvw_tgt prm_src prm_tgt rsv_src rsv_tgt
    (TVIEW: sim_tview f flag_src tvw_src tvw_tgt)
    (RESERVES: sim_reserves f rsv_src rsv_tgt)
    (PROMISES: sim_promises_local flag_src flag_tgt prm_src prm_tgt)
    (FLAGSRC: forall loc (FLAG: flag_src loc = true),
        (<<RLX: tvw_src.(TView.cur).(View.rlx) loc = tvw_src.(TView.cur).(View.pln) loc>>))
    (SRCTM: forall loc, srctm loc = tvw_src.(TView.cur).(View.rlx) loc)
  :
    sim_local
      f flag_src flag_tgt
      srctm
      (Local.mk tvw_src prm_src rsv_src)
      (Local.mk tvw_tgt prm_tgt rsv_tgt)
.

Variant sim_global
        (flag_src: Loc.t -> bool)
        (flag_tgt: Loc.t -> bool)
        (D: Loc.t -> bool)
        (f: Mapping.ts)
  :
    Global.t -> Global.t -> Prop :=
| sim_global_intro
    sc_src sc_tgt gprm_src gprm_tgt mem_src mem_tgt
    (SC: sim_timemap (fun loc => True) f (Mapping.vers f) sc_src sc_tgt)
    (PROMISES: sim_promises_global flag_src gprm_src gprm_tgt)
    (MEM: sim_memory (boolmap_plus flag_src flag_tgt) D f mem_src mem_tgt)
  :
    sim_global
      flag_src
      flag_tgt
      D
      f
      (Global.mk sc_src gprm_src mem_src)
      (Global.mk sc_tgt gprm_tgt mem_tgt)
.

Lemma sim_global_mon_strong f1 f0 flag_src flag_tgt D gl_src gl_tgt
      (SIM: sim_global flag_src flag_tgt D f0 gl_src gl_tgt)
      (MAPLE: Mapping.les_strong f0 f1)
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wfs f1)
  :
  sim_global flag_src flag_tgt D f1 gl_src gl_tgt.
Proof.
  inv SIM. econs; eauto.
  { eapply sim_timemap_mon_mapping_latest; eauto. eapply Mapping.les_strong_les; eauto. }
  { eapply sim_memory_mon_strong; eauto. }
Qed.

Lemma sim_reserves_mon_strong f1 f0 rsv_src rsv_tgt
      (SIM: sim_reserves f0 rsv_src rsv_tgt)
      (MAPLE: Mapping.les_strong f0 f1)
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wfs f1)
  :
  sim_reserves f1 rsv_src rsv_tgt.
Proof.
  econs.
  { i. hexploit sim_reserves_get; eauto. i. des. esplits; eauto.
    { eapply sim_timestamp_exact_mon_strong; eauto. }
    { eapply sim_timestamp_exact_mon_strong; eauto. }
  }
  { i. hexploit sim_reserves_get_if; eauto. i. des. esplits; eauto.
    { eapply sim_timestamp_exact_mon_strong; eauto. }
  }
Qed.

Lemma sim_local_mon_strong f1 f0 flag_src flag_tgt srctm lc_src lc_tgt
      (SIM: sim_local f0 flag_src flag_tgt srctm lc_src lc_tgt)
      (MAPLE: Mapping.les_strong f0 f1)
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wfs f1)
  :
  sim_local f1 flag_src flag_tgt srctm lc_src lc_tgt.
Proof.
  inv SIM. econs; eauto.
  { eapply sim_tview_mon_latest; eauto. eapply Mapping.les_strong_les; eauto. }
  { eapply sim_reserves_mon_strong; eauto. }
Qed.

Lemma sim_local_tgt_mon f flag_src flag_tgt srctm lc_src lc_tgt0 lc_tgt1
      (SIM: sim_local f flag_src flag_tgt srctm lc_src lc_tgt0)
      (PROM: lc_tgt0.(Local.promises) = lc_tgt1.(Local.promises))
      (RESERVES: lc_tgt0.(Local.reserves) = lc_tgt1.(Local.reserves))
      (TVIEW: TView.le lc_tgt0.(Local.tview) lc_tgt1.(Local.tview))
  :
    sim_local f flag_src flag_tgt srctm lc_src lc_tgt1.
Proof.
  inv SIM. destruct lc_tgt1. ss. clarify. econs; eauto.
  eapply sim_tview_tgt_mon; eauto.
Qed.

Lemma other_promise_same_internal e lc0 gl0 lc1 gl1
      (STEP: Local.internal_step e lc0 gl0 lc1 gl1)
  :
  BoolMap.minus gl1.(Global.promises) lc1.(Local.promises)
  =
    BoolMap.minus gl0.(Global.promises) lc0.(Local.promises).
Proof.
  inv STEP.
  { inv LOCAL. inv PROMISE. inv ADD. inv GADD. ss. extensionality loc0.
    unfold BoolMap.minus, andb, negb. rewrite ! loc_fun_add_spec. des_ifs.
  }
  { inv LOCAL. ss. }
  { inv LOCAL. ss. }
Qed.

Lemma other_promise_same_fulfill lprm0 gprm0 loc ord lprm1 gprm1
      (STEP: Promises.fulfill lprm0 gprm0 loc ord lprm1 gprm1)
  :
  BoolMap.minus gprm1 lprm1
  =
    BoolMap.minus gprm0 lprm0.
Proof.
  inv STEP; ss. inv REMOVE. inv GREMOVE. extensionality loc0.
  unfold BoolMap.minus, andb, negb. rewrite ! loc_fun_add_spec. des_ifs.
Qed.

Lemma other_promise_same_write lc0 gl0 loc from to val releasedm released ord lc1 gl1
      (STEP: Local.write_step lc0 gl0 loc from to val releasedm released ord lc1 gl1)
  :
  BoolMap.minus gl1.(Global.promises) lc1.(Local.promises)
  =
    BoolMap.minus gl0.(Global.promises) lc0.(Local.promises).
Proof.
  inv STEP; ss. eapply other_promise_same_fulfill; eauto.
Qed.

Lemma other_promise_same_program e lc0 gl0 lc1 gl1
      (STEP: Local.program_step e lc0 gl0 lc1 gl1)
  :
  BoolMap.minus gl1.(Global.promises) lc1.(Local.promises)
  =
    BoolMap.minus gl0.(Global.promises) lc0.(Local.promises).
Proof.
  inv STEP; ss.
  { inv LOCAL; ss. }
  { eapply other_promise_same_write; eauto. }
  { inv LOCAL1. eapply other_promise_same_write in LOCAL2; eauto. }
  { inv LOCAL. ss. }
  { inv LOCAL. ss. }
Qed.

Lemma sim_local_racy f flag_src flag_tgt srctm lc_src lc_tgt gl_src gl_tgt loc to ord
      (MEM: sim_global flag_src flag_tgt (BoolMap.minus gl_src.(Global.promises) lc_src.(Local.promises)) f gl_src gl_tgt)
      (SIM: sim_local f flag_src flag_tgt srctm lc_src lc_tgt)
      (WF: Mapping.wfs f)
      (RACY: Local.is_racy lc_tgt gl_tgt loc to ord)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
  :
    exists to_src, Local.is_racy lc_src gl_src loc to_src ord.
Proof.
  destruct ((BoolMap.minus gl_src.(Global.promises) lc_src.(Local.promises)) loc) eqn:MINUS.
  { unfold BoolMap.minus, andb, negb in MINUS. des_ifs.
    esplits. econs 1; eauto.
  }
  inv MEM. inv RACY.
  { ss. inv PROMISES.
    hexploit SIM0; eauto. i. rewrite GET in H.
    inv SIM. ss. esplits. econs 1; ss.
    inv PROMISES. erewrite NOFLAG; eauto.
  }
  { hexploit sim_memory_get; eauto; ss.
    { unfold boolmap_plus, orb. des_ifs. }
    i. des.
    { inv MSG0. esplits. econs 2.
      { eauto. }
      { inv SIM. ss. unfold TView.racy_view in *. eapply sim_timestamp_lt.
        { eapply TVIEW. auto. }
        { eauto. }
        { ss. }
        { auto. }
        { apply mapping_latest_wf. }
      }
      { i. hexploit MSG; auto. i. subst. ss. }
    }
    { esplits. econs 2.
      { eauto. }
      { inv SIM. ss. unfold TView.racy_view in *.
        etrans; [|eauto].
        eapply sim_timestamp_lt.
        { eapply TVIEW. auto. }
        { eauto. }
        { ss. }
        { auto. }
        { apply mapping_latest_wf. }
      }
      { auto. }
    }
  }
Qed.

Variant max_value_src (loc: Loc.t) (v: option Const.t)
        (mem: Global.t)
  :
    forall (lc: Local.t), Prop :=
| max_value_src_intro
    tvw prom rsv
    (MAX: forall v0 (VAL: v = Some v0),
        exists released,
          (<<MAX: max_readable
                    mem
                    prom
                    loc
                    (tvw.(TView.cur).(View.pln) loc)
                    v0 released>>))
    (NONMAX: forall (VAL: v = None),
        forall val released,
          ~ max_readable mem prom loc (tvw.(TView.cur).(View.pln) loc) val released)
  :
    max_value_src loc v mem (Local.mk tvw prom rsv)
.

Definition max_values_src (vs: Loc.t -> option Const.t)
           (mem: Global.t) (lc: Local.t): Prop :=
  forall loc, max_value_src loc (vs loc) mem lc.

Variant max_value_tgt (loc: Loc.t) (v: option Const.t)
        (mem: Global.t)
  :
    forall (lc: Local.t), Prop :=
| max_value_tgt_intro
    tvw prom rsv
    (MAX: forall v0 (VAL: v = Some v0),
        exists released,
          (<<MAX: max_readable
                    mem
                    prom
                    loc
                    (tvw.(TView.cur).(View.pln) loc)
                    v0 released>>))
  :
    max_value_tgt loc v mem (Local.mk tvw prom rsv)
.

Definition max_values_tgt (vs: Loc.t -> option Const.t)
           (mem: Global.t) (lc: Local.t): Prop :=
  forall loc, max_value_tgt loc (vs loc) mem lc.

Lemma max_value_tgt_mon loc v mem lc0 lc1
      (MAXTGT: max_value_tgt loc v mem lc0)
      (PROM: lc0.(Local.promises) = lc1.(Local.promises))
      (TVIEW: TView.le lc0.(Local.tview) lc1.(Local.tview))
      (LOCAL: Local.wf lc1 mem)
  :
  max_value_tgt loc v mem lc1.
Proof.
  inv MAXTGT. ss. subst. destruct lc1. econs. i.
  hexploit MAX; eauto. i. des. ss.
  hexploit max_readable_view_mon; eauto.
Qed.

Lemma max_values_tgt_mon vs mem lc0 lc1
      (MAXTGT: max_values_tgt vs mem lc0)
      (PROM: lc0.(Local.promises) = lc1.(Local.promises))
      (TVIEW: TView.le lc0.(Local.tview) lc1.(Local.tview))
      (LOCAL: Local.wf lc1 mem)
  :
    max_values_tgt vs mem lc1.
Proof.
  ii. eapply max_value_tgt_mon; eauto.
Qed.

Lemma owned_future_max_value_src loc val gl_src0 gl_src1 lc_src
      (MAX: max_value_src loc val gl_src0 lc_src)
      (OWNED: owned_future_global_loc loc gl_src0 gl_src1)
      (LE: Global.le gl_src0 gl_src1)
  :
  max_value_src loc val gl_src1 lc_src.
Proof.
  inv MAX. econs.
  { i. hexploit MAX0; eauto. i. des. esplits.
    erewrite <- owned_future_max_readable; eauto.
  }
  { ii. eapply NONMAX; eauto. erewrite owned_future_max_readable; eauto. }
Qed.

Lemma owned_future_max_value_tgt loc val gl_tgt0 gl_tgt1 lc_tgt
      (MAX: max_value_tgt loc val gl_tgt0 lc_tgt)
      (OWNED: owned_future_global_loc loc gl_tgt0 gl_tgt1)
      (LE: Global.le gl_tgt0 gl_tgt1)
  :
  max_value_tgt loc val gl_tgt1 lc_tgt.
Proof.
  inv MAX. econs.
  { i. hexploit MAX0; eauto. i. des. esplits.
    erewrite <- owned_future_max_readable; eauto.
  }
Qed.

(* Definition reserved_space_empty (f: Mapping.ts) (flag_src: Loc.t -> bool) *)
(*            (prom_tgt: Memory.t) (mem_src: Memory.t): Prop := *)
(*   forall loc to_tgt from_tgt *)
(*          (GETTGT: Memory.get loc to_tgt prom_tgt = Some (from_tgt, Message.reserve)) *)
(*          (FLAG: flag_src loc = true), *)
(*   exists to_src from_src, *)
(*     (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src (Some from_tgt)>>) /\ *)
(*     (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt)>>) /\ *)
(*     (<<DISJOINT: forall from to msg *)
(*                         (GETSRC: Memory.get loc to mem_src = Some (from, msg)), *)
(*         Interval.disjoint (from_src, to_src) (from, to)>>). *)

(* Lemma reserved_space_empty_mon_strong f0 f1 flag_src prom_tgt mem_src *)
(*       (RESERVED: reserved_space_empty f0 flag_src prom_tgt mem_src) *)
(*       (MAPLE: Mapping.les_strong f0 f1) *)
(*       (MAPWF0: Mapping.wfs f0) *)
(*       (MAPWF1: Mapping.wfs f1) *)
(*   : *)
(*     reserved_space_empty f1 flag_src prom_tgt mem_src. *)
(* Proof. *)
(*   ii. exploit RESERVED; eauto. i. des. esplits; eauto. *)
(*   { eapply sim_timestamp_exact_mon_strong; eauto. } *)
(*   { eapply sim_timestamp_exact_mon_strong; eauto. } *)
(* Qed. *)

(* Lemma reserved_space_empty_reserve_decr f flag_src prom_tgt0 prom_tgt1 mem_src *)
(*       (RESERVED: reserved_space_empty f flag_src prom_tgt0 mem_src) *)
(*       (DECR: forall loc to from *)
(*                     (GET: Memory.get loc to prom_tgt1 = Some (from, Message.reserve)) *)
(*                     (FLAG: flag_src loc = true), *)
(*           Memory.get loc to prom_tgt0 = Some (from, Message.reserve)) *)
(*   : *)
(*     reserved_space_empty f flag_src prom_tgt1 mem_src. *)
(* Proof. *)
(*   ii. exploit RESERVED; eauto. *)
(* Qed. *)

(* Lemma reserved_space_empty_covered_decr f flag_src prom_tgt mem_src0 mem_src1 *)
(*       (RESERVED: reserved_space_empty f flag_src prom_tgt mem_src0) *)
(*       (DECR: forall loc ts (FLAG: flag_src loc = true) (COVER: covered loc ts mem_src1), covered loc ts mem_src0) *)
(*   : *)
(*     reserved_space_empty f flag_src prom_tgt mem_src1. *)
(* Proof. *)
(*   ii. exploit RESERVED; eauto. i. des. esplits; eauto. *)
(*   ii. exploit DECR; eauto. *)
(*   { econs; eauto. } *)
(*   intros x0. inv x0. eapply DISJOINT; eauto. *)
(* Qed. *)

(* Lemma reserved_space_empty_unchanged_loc *)
(*       f flag_src prom_tgt mem_src0 mem_src1 *)
(*       (RESERVED: reserved_space_empty f flag_src prom_tgt mem_src0) *)
(*       (UNCH: forall loc (FLAG: flag_src loc = true), unchanged_loc_memory loc mem_src0 mem_src1) *)
(*   : *)
(*     reserved_space_empty f flag_src prom_tgt mem_src1. *)
(* Proof. *)
(*   ii. exploit RESERVED; eauto. i. des. esplits; eauto. *)
(*   ii. hexploit UNCH; eauto. i. inv H. rewrite UNCH0 in GETSRC; eauto. *)
(*   eapply DISJOINT; eauto. *)
(* Qed. *)

(* Lemma reserved_space_empty_add f flag_src prom_tgt mem_src0 mem_src1 *)
(*       loc from to msg *)
(*       (RESERVED: reserved_space_empty f flag_src prom_tgt mem_src0) *)
(*       (ADD: Memory.add mem_src0 loc from to msg mem_src1) *)
(*       (TOP: top_time from (f loc)) *)
(*   : *)
(*     reserved_space_empty f flag_src prom_tgt mem_src1. *)
(* Proof. *)
(*   ii. exploit RESERVED; eauto. i. des. esplits; eauto. *)
(*   i. erewrite Memory.add_o in GETSRC; eauto. des_ifs; eauto. *)
(*   ss. des; clarify. eapply interval_le_disjoint. *)
(*   eapply TOP in TO. left. auto. *)
(* Qed. *)

(* Lemma cancel_future_memory_le loc prom0 mem0 prom1 mem1 *)
(*       (CANCEL: cancel_future_memory loc prom0 mem0 prom1 mem1) *)
(*   : *)
(*     Memory.le prom1 prom0. *)
(* Proof. *)
(*   induction CANCEL. *)
(*   { refl. } *)
(*   etrans; eauto. inv CANCEL. eapply remove_le; eauto. *)
(* Qed. *)

(* Lemma cancel_future_memory_get loc prom0 mem0 prom1 mem1 *)
(*       (CANCEL: cancel_future_memory loc prom0 mem0 prom1 mem1) *)
(*   : *)
(*     forall to, *)
(*       Memory.get loc to mem1 = *)
(*       match Memory.get loc to mem0 with *)
(*       | None => None *)
(*       | Some (from, msg) => *)
(*         match Memory.get loc to prom0 with *)
(*         | None => Some (from, msg) *)
(*         | Some _ => *)
(*           match Memory.get loc to prom1 with *)
(*           | None => None *)
(*           | Some _ => Some (from, msg) *)
(*           end *)
(*         end *)
(*       end. *)
(* Proof. *)
(*   induction CANCEL. *)
(*   { i. des_ifs. } *)
(*   i. inv CANCEL. rewrite IHCANCEL. *)
(*   erewrite (@Memory.remove_o mem1); eauto. *)
(*   erewrite (@Memory.remove_o prom1); eauto. des_ifs. *)
(*   { ss. des; clarify. destruct p0. *)
(*     eapply cancel_future_memory_le in Heq2; eauto. *)
(*     eapply Memory.remove_get0 in RSV. des; clarify. *)
(*   } *)
(*   { ss. des; clarify. *)
(*     eapply Memory.remove_get0 in RSV. des; clarify. *)
(*   } *)
(* Qed. *)

(* Lemma cancel_future_memory_memory_le loc prom0 mem0 prom1 mem1 *)
(*       (CANCEL: cancel_future_memory loc prom0 mem0 prom1 mem1) *)
(*       (MLE: Memory.le prom0 mem0) *)
(*   : *)
(*     Memory.le prom1 mem1. *)
(* Proof. *)
(*   revert MLE. induction CANCEL; auto. i. eapply IHCANCEL. *)
(*   eapply cancel_memory_le; eauto. *)
(* Qed. *)

(* Lemma reserved_space_empty_fulfilled_memory f srctm vers *)
(*       flag_src0 flag_src1 flag_tgt prom_tgt mem_src0 mem_src1 *)
(*       loc prom_src0 prom_src1 *)
(*       (RESERVED: reserved_space_empty f flag_src0 prom_tgt mem_src0) *)
(*       (CANCEL: cancel_future_memory loc prom_src0 mem_src0 prom_src1 mem_src1) *)
(*       (PROMISE: sim_promises srctm flag_src0 flag_tgt f vers prom_src0 prom_tgt) *)
(*       (MLE: Memory.le prom_src0 mem_src0) *)
(*       (NONE: forall from to msg *)
(*                     (GET: Memory.get loc to prom_src1 = Some (from, msg)), *)
(*           msg <> Message.reserve) *)
(*       (FLAGS: forall loc0 (FLAG: flag_src1 loc0 = true), flag_src0 loc0 = true \/ loc0 = loc) *)
(*   : *)
(*     reserved_space_empty f flag_src1 prom_tgt mem_src1. *)
(* Proof. *)
(*   destruct (flag_src0 loc) eqn:EQ. *)
(*   { revert RESERVED. clear MLE NONE PROMISE. induction CANCEL; auto. *)
(*     { ii. exploit RESERVED; eauto. exploit FLAGS; eauto. i. des; clarify. } *)
(*     i. eapply IHCANCEL. *)
(*     inv CANCEL. eapply reserved_space_empty_covered_decr; eauto. *)
(*     i. eapply remove_covered in COVER; eauto. des; eauto. *)
(*   } *)
(*   { ii. hexploit cancel_future_memory_memory_le; eauto. intros MLE1. *)
(*     destruct (Loc.eq_dec loc0 loc). *)
(*     { subst. hexploit sim_promises_get; eauto. i. des. esplits; eauto. *)
(*       i. hexploit GET; eauto. i. des. dup GET0. eapply MLE in GET0. *)
(*       dup GETSRC. erewrite cancel_future_memory_get in GETSRC; eauto. des_ifs. *)
(*       { hexploit Memory.get_disjoint. *)
(*         { eapply GET0. } *)
(*         { eapply Heq. } *)
(*         i. des; clarify. exfalso. *)
(*         destruct p0. dup Heq1. eapply MLE1 in Heq1. clarify. *)
(*         inv MSG. eapply NONE in Heq2; eauto. *)
(*       } *)
(*       { hexploit Memory.get_disjoint. *)
(*         { eapply GET0. } *)
(*         { eapply Heq. } *)
(*         i. des; clarify. *)
(*       } *)
(*     } *)
(*     { exploit RESERVED; eauto. *)
(*       { eapply FLAGS in FLAG. des; clarify. } *)
(*       i. des. esplits; eauto. *)
(*       i. eapply cancel_future_unchanged_loc in CANCEL; eauto. des. *)
(*       inv MEM. rewrite UNCH in GETSRC. eauto. *)
(*     } *)
(*   } *)
(* Qed. *)

Variant sim_thread
        (f: Mapping.ts)
        (flag_src: Loc.t -> bool)
        (flag_tgt: Loc.t -> bool)
        (vs_src: Loc.t -> option Const.t)
        (vs_tgt: Loc.t -> option Const.t)
        mem_src mem_tgt lc_src lc_tgt: Prop :=
| sim_thread_intro
      srctm
    (MEM: sim_global flag_src flag_tgt (BoolMap.minus mem_src.(Global.promises) lc_src.(Local.promises)) f mem_src mem_tgt)
    (LOCAL: sim_local f flag_src flag_tgt srctm lc_src lc_tgt)
    (MAXSRC: max_values_src vs_src mem_src lc_src)
    (MAXTGT: max_values_tgt vs_tgt mem_tgt lc_tgt)
    (PERM: forall loc, option_rel (fun _ _ => True) (vs_src loc) (vs_tgt loc))
    (FIN: __guard__(exists dom, (<<DOM: forall loc, (flag_src loc = true) <-> (List.In loc dom)>>)))
    (FLAGMAX: forall loc val (VAL: vs_src loc = Some val) (FLAG: flag_src loc = true),
        max_memory_val (f loc) loc (srctm loc) val mem_src.(Global.memory))
    (FLAGNONE: forall loc (VAL: vs_src loc = None),
        (<<FLAGSRC: flag_src loc = false>>) /\ (<<FLAGTGT: flag_tgt loc = false>>))
.

Lemma sim_thread_mon_strong f1 f0 flag_src flag_tgt vs_src vs_tgt mem_src mem_tgt lc_src lc_tgt
      (SIM: sim_thread f0 flag_src flag_tgt vs_src vs_tgt mem_src mem_tgt lc_src lc_tgt)
      (MAPLE: Mapping.les_strong f0 f1)
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wfs f1)
  :
  sim_thread f1 flag_src flag_tgt vs_src vs_tgt mem_src mem_tgt lc_src lc_tgt.
Proof.
  inv SIM. econs; eauto.
  { eapply sim_global_mon_strong; eauto. }
  { eapply sim_local_mon_strong; eauto. }
  { i. eapply max_memory_val_mon_strong; eauto. }
Qed.

Lemma max_value_src_exists loc mem lc
  :
    exists v,
      (<<MAX: max_value_src loc v mem lc>>).
Proof.
  destruct (classic (exists val released, max_readable mem lc.(Local.promises) loc (View.pln (TView.cur lc.(Local.tview)) loc) val released)).
  { des. exists (Some val). splits. destruct lc. econs; ss.
    i. clarify. esplits; eauto.
  }
  { exists None. splits. destruct lc. econs; ss.
    ii. eapply H. eauto.
  }
Qed.

Lemma max_values_src_exists mem lc
  :
    exists vs,
      (<<MAX: max_values_src vs mem lc>>).
Proof.
  eapply (choice (fun loc v => max_value_src loc v mem lc)).
  i. eapply max_value_src_exists.
Qed.

Lemma max_value_src_inj loc mem lc v0 v1
      (MAX0: max_value_src loc v0 mem lc)
      (MAX1: max_value_src loc v1 mem lc)
  :
    v0 = v1.
Proof.
  inv MAX0. inv MAX1. destruct v0, v1; auto.
  { hexploit MAX; eauto. hexploit MAX0; eauto. i. des.
    f_equal. eapply max_readable_inj; eauto.
  }
  { exfalso. hexploit MAX; eauto. i. des. eapply NONMAX0; eauto. }
  { exfalso. hexploit MAX0; eauto. i. des. eapply NONMAX; eauto. }
Qed.

Lemma max_value_src_mon loc v mem lc0 lc1
      (MAXSRC: max_value_src loc (Some v) mem lc0)
      (PROM: lc0.(Local.promises) = lc1.(Local.promises))
      (TVIEW: TView.le lc0.(Local.tview) lc1.(Local.tview))
      (LOCAL: Local.wf lc1 mem)
  :
    max_value_src loc (Some v) mem lc1.
Proof.
  inv MAXSRC. ss. subst. destruct lc1. econs; ss.
  i. clarify.
  hexploit MAX; eauto. i. des. esplits.
  hexploit max_readable_view_mon; eauto.
Qed.

Lemma race_non_max_readable mem prom tvw rsv loc to ord
      (MAX: Local.is_racy (Local.mk tvw prom rsv) mem loc to ord)
  :
    forall val released, ~ max_readable mem prom loc (tvw.(TView.cur).(View.pln) loc) val released.
Proof.
  ii. inv H. inv MAX.
  { ss. rewrite GETP in NONE. rewrite GET0 in NONE. ss. }
  { eapply MAX0 in RACE; eauto. ss. }
Qed.

(* Lemma sim_memory_src_flag_max_concrete *)
(*       f vers srctm flag_src *)
(*       mem_src mem_tgt *)
(*       (SIM: sim_memory srctm flag_src f vers mem_src mem_tgt) *)
(*       loc *)
(*       (FLAG: flag_src loc = true) *)
(*       (CLOSED: exists from msg, Memory.get loc (srctm loc) mem_src = Some (from, msg)) *)
(*   : *)
(*     Memory.max_ts loc mem_src = srctm loc. *)
(* Proof. *)
(*   des. hexploit Memory.max_ts_spec. *)
(*   { eapply CLOSED. } *)
(*   i. des. eapply TimeFacts.antisym; eauto. *)
(*   hexploit sim_memory_top; eauto. intros TOP. *)
(*   hexploit sim_memory_sound. *)
(*   { eauto. } *)
(*   { eapply GET. } *)
(*   i. des. *)
(*   { eapply TOP in TO. left. eapply TimeFacts.le_lt_lt; eauto. } *)
(*   { clarify. } *)
(* Qed. *)

(* Lemma max_value_src_flag_none f vers srctm flag_src flag_tgt lc_src lc_tgt mem_src mem_tgt loc *)
(*       (MEM: sim_memory srctm flag_src f vers mem_src mem_tgt) *)
(*       (LOCAL: sim_local f vers srctm flag_src flag_tgt lc_src lc_tgt) *)
(*       (MAX: max_value_src loc None mem_src lc_src) *)
(*       (LOCALWF: Local.wf lc_src mem_src) *)
(*       (WF: Mapping.wfs f) *)
(*   : *)
(*     flag_src loc = false. *)
(* Proof. *)
(*   destruct (flag_src loc) eqn:FLAG; auto. exfalso. *)
(*   inv LOCAL. hexploit FLAGSRC; eauto. i. des. subst. *)
(*   inv LOCALWF. inv TVIEW_CLOSED. *)
(*   inv CUR. exploit RLX; eauto. i. des. ss. *)
(*   inv MAX. hexploit NONMAX; eauto. ii. eapply H0. econs. *)
(*   { rewrite <- H. eauto. } *)
(*   { inv PROMISES. eapply NONE; eauto. } *)
(*   { i. hexploit sim_memory_src_flag_max_concrete; eauto. *)
(*     { rewrite SRCTM. eauto. } *)
(*     i. eapply Memory.max_ts_spec in GET. des. *)
(*     rewrite H1 in MAX. exfalso. *)
(*     eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt. *)
(*     { eapply TS. } *)
(*     { rewrite <- H. rewrite <- SRCTM. eauto. } *)
(*   } *)
(* Qed. *)

Lemma promise_max_readable
      lc0 gl0 loc lc1 gl1 tvw
      (PROMISE: Local.promise_step lc0 gl0 loc lc1 gl1)
  :
  forall loc0 val0 released0,
    max_readable gl0 lc0.(Local.promises) loc0 tvw val0 released0 <-> max_readable gl1 lc1.(Local.promises) loc0 tvw val0 released0.
Proof.
  i. split.
  { intros MAX. inv MAX. inv PROMISE. inv PROMISE0. inv ADD. inv GADD.
    econs; eauto. ss.
    setoid_rewrite LocFun.add_spec. des_ifs.
  }
  { intros MAX. inv MAX. inv PROMISE. inv PROMISE0. inv ADD. inv GADD.
    econs; eauto. ss.
    setoid_rewrite LocFun.add_spec in NONE. des_ifs.
  }
Qed.

Lemma reserve_max_readable
      lc0 gl0 loc from to lc1 gl1 tvw
      (PROMISE: Local.reserve_step lc0 gl0 loc from to lc1 gl1)
  :
  forall loc0 val0 released0,
    max_readable gl0 lc0.(Local.promises) loc0 tvw val0 released0 <-> max_readable gl1 lc1.(Local.promises) loc0 tvw val0 released0.
Proof.
  i. split.
  { intros MAX. inv MAX. inv PROMISE. inv RESERVE. econs; eauto.
    { eapply Memory.add_get1; eauto. }
    { i. ss. erewrite Memory.add_o in GET0; eauto. des_ifs. eauto. }
  }
  { intros MAX. inv MAX. inv PROMISE. inv RESERVE.
    erewrite Memory.add_o in GET; eauto. des_ifs. econs; eauto.
    i. eapply MAX0; eauto. eapply Memory.add_get1; eauto.
  }
Qed.

Lemma cancel_max_readable
      lc0 gl0 loc from to lc1 gl1 tvw
      (PROMISE: Local.cancel_step lc0 gl0 loc from to lc1 gl1)
  :
  forall loc0 val0 released0,
    max_readable gl0 lc0.(Local.promises) loc0 tvw val0 released0 <-> max_readable gl1 lc1.(Local.promises) loc0 tvw val0 released0.
Proof.
  i. split.
  { intros MAX. inv MAX. inv PROMISE. inv CANCEL. econs; eauto.
    { eapply Memory.remove_get1 in GET; eauto. ss. des; clarify. eauto. }
    { i. erewrite Memory.remove_o in GET0; eauto. des_ifs. eauto. }
  }
  { intros MAX. inv MAX. inv PROMISE. inv CANCEL.
    erewrite Memory.remove_o in GET; eauto. des_ifs. econs; eauto.
    i. eapply MAX0; eauto. eapply Memory.remove_get1 in GET0; eauto.
    ss. des; clarify; eauto.
  }
Qed.

Lemma internal_max_readable
      te lc0 gl0 lc1 gl1
      (PROMISE: Local.internal_step te lc0 gl0 lc1 gl1)
  :
  forall tvw loc0 val0 released0,
    max_readable gl0 lc0.(Local.promises) loc0 tvw val0 released0 <-> max_readable gl1 lc1.(Local.promises) loc0 tvw val0 released0.
Proof.
  inv PROMISE; i.
  { eapply promise_max_readable; eauto. }
  { eapply reserve_max_readable; eauto. }
  { eapply cancel_max_readable; eauto. }
Qed.

Lemma promise_max_values_src
      te lc0 gl0 lc1 gl1 vs
      (PROMISE: Local.internal_step te lc0 gl0 lc1 gl1)
      (MAX: max_values_src vs gl0 lc0)
  :
  max_values_src vs gl1 lc1.
Proof.
  ii. specialize (MAX loc). inv MAX. destruct lc1, gl1.
  pose proof (internal_max_readable _ _ _ _ _ PROMISE). econs; eauto.
  { i. hexploit MAX0; eauto. i. des.
    ss. esplits. eapply H.
    inv PROMISE; inv LOCAL; clarify; eauto.
  }
  { ii. eapply NONMAX; eauto. eapply H. ss.
    inv PROMISE; inv LOCAL; clarify; eauto.
  }
Qed.

Lemma promise_max_values_tgt
      te lc0 gl0 lc1 gl1 vs
      (PROMISE: Local.internal_step te lc0 gl0 lc1 gl1)
      (MAX: max_values_tgt vs gl0 lc0)
  :
  max_values_tgt vs gl1 lc1.
Proof.
  ii. specialize (MAX loc). inv MAX. destruct lc1, gl1.
  pose proof (internal_max_readable _ _ _ _ _ PROMISE). econs; eauto.
  { i. hexploit MAX0; eauto. i. des.
    ss. esplits. eapply H.
    inv PROMISE; inv LOCAL; clarify; eauto.
  }
Qed.

Lemma promise_steps_max_values_src
      lang st0 st1 lc0 lc1 gl0 gl1 vs
      (PROMISE: rtc (@Thread.internal_step _) (Thread.mk lang st0 lc0 gl0) (Thread.mk _ st1 lc1 gl1))
      (MAX: max_values_src vs gl0 lc0)
  :
  max_values_src vs gl1 lc1.
Proof.
  remember (Thread.mk lang st0 lc0 gl0).
  remember (Thread.mk lang st1 lc1 gl1).
  revert st0 st1 lc0 lc1 gl0 gl1 Heqt Heqt0 MAX. induction PROMISE; i; clarify.
  inv H. eapply promise_max_values_src in LOCAL; eauto.
Qed.

Lemma promise_steps_max_values_tgt
      lang st0 st1 lc0 lc1 gl0 gl1 vs
      (PROMISE: rtc (@Thread.internal_step _) (Thread.mk lang st0 lc0 gl0) (Thread.mk _ st1 lc1 gl1))
      (MAX: max_values_tgt vs gl0 lc0)
  :
  max_values_tgt vs gl1 lc1.
Proof.
  remember (Thread.mk lang st0 lc0 gl0).
  remember (Thread.mk lang st1 lc1 gl1).
  revert st0 st1 lc0 lc1 gl0 gl1 Heqt Heqt0 MAX. induction PROMISE; i; clarify.
  inv H. eapply promise_max_values_tgt in LOCAL; eauto.
Qed.

Lemma no_flag_max_value_same f flag_src flag_tgt srctm lc_src lc_tgt mem_src mem_tgt loc v_src
      (MEM: sim_global flag_src flag_tgt (BoolMap.minus mem_src.(Global.promises) lc_src.(Local.promises)) f mem_src mem_tgt)
      (LOCAL: sim_local f flag_src flag_tgt srctm lc_src lc_tgt)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
      (MAX: max_value_src loc (Some v_src) mem_src lc_src)
      (LOCALWF: Local.wf lc_tgt mem_tgt)
      (WF: Mapping.wfs f)
  :
  exists v_tgt,
    (<<MAX: max_value_tgt loc (Some v_tgt) mem_tgt lc_tgt>>) /\ (<<VAL: Const.le v_tgt v_src>>).
Proof.
  inv MAX. destruct lc_tgt. i. clarify.
  hexploit MAX0; eauto. i. des.
  assert (exists val released, max_readable mem_tgt promises loc (View.pln (TView.cur tview) loc) val released).
  { apply NNPP. ii. hexploit non_max_readable_race.
    { ii. eapply H; eauto. }
    { eauto. }
    { i. des. eapply sim_local_racy in H0; eauto. des.
      eapply race_non_max_readable in H0; eauto. }
  }
  des. exists val. esplits.
  { econs; eauto. i. clarify. esplits; eauto. }
  inv H. inv MEM. hexploit sim_memory_get; eauto; ss.
  { unfold boolmap_plus, orb. des_ifs. }
  { unfold BoolMap.minus, andb, negb. des_ifs.
    exfalso. eapply race_non_max_readable; [|eauto]. econs 1; ss.
  }
  i. des; cycle 1.
  { exfalso. eapply race_non_max_readable; [|eauto]. econs 2; eauto. ss.
    hexploit sim_timestamp_le.
    2:{ eapply TO. }
    2:{ refl. }
    { inv LOCAL. eapply TVIEW; ss. }
    { eauto. }
    { eapply mapping_latest_wf_loc. }
    i. eapply TimeFacts.le_lt_lt; eauto.
  }
  hexploit sim_timestamp_le.
  2:{ eapply TO. }
  2:{ refl. }
  { inv LOCAL. eapply TVIEW; ss. }
  { eauto. }
  { eapply mapping_latest_wf_loc. }
  i. inv MAX. inv H.
  { hexploit MAX2; eauto; ss. inv MSG; ss. }
  { inv H0. ss. clarify. inv MSG; auto. }
  Unshelve. all: ss. all: try exact Ordering.na.
Qed.

Lemma sim_thread_tgt_read_na
      f flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt0
      loc to_tgt val_tgt vw_tgt lc_tgt1
      (READ: Local.read_step lc_tgt0 mem_tgt loc to_tgt val_tgt vw_tgt Ordering.na lc_tgt1)
      (SIM: sim_thread
              f flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt0)
      (LOCAL: Local.wf lc_tgt0 mem_tgt)
      (MEM: Global.wf mem_tgt)
  :
    (<<SIM: sim_thread
              f flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt1>>) /\
    (<<VAL: forall val (VALS: vs_tgt loc = Some val), Const.le val_tgt val>>).
Proof.
  hexploit Local.read_step_future; eauto.
  i. des. splits.
  { inv SIM. econs; eauto.
    { eapply sim_local_tgt_mon; eauto.
      { inv READ; ss. }
      { inv READ; ss. }
    }
    { eapply max_values_tgt_mon; eauto.
      { inv READ; ss. }
    }
  }
  { i. inv SIM. specialize (MAXTGT loc). inv MAXTGT.
    hexploit MAX; eauto. i. des.
    hexploit max_readable_read_only; eauto.
    i. des; auto.
  }
Qed.

Lemma sim_thread_tgt_read_na_racy
      f flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt0
      loc to val_tgt ord
      (READ: Local.racy_read_step lc_tgt0 mem_tgt loc to val_tgt ord)
      (SIM: sim_thread
              f flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt0)
      (LOCAL: Local.wf lc_tgt0 mem_tgt)
  :
    vs_tgt loc = None.
Proof.
  destruct (vs_tgt loc) eqn:VAL; auto.
  inv SIM. specialize (MAXTGT loc). inv MAXTGT. hexploit MAX; eauto. i. des.
  exfalso. eapply max_readable_not_read_race; eauto.
  Unshelve.
Qed.

Lemma sim_thread_src_read_na
      f flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt
      loc val_src val
      (SIM: sim_thread
              f flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt)
      (VALS: vs_src loc = Some val)
      (VAL: Const.le val_src val)
      (LOCAL: Local.wf lc_src mem_src)
  :
    exists to vw,
      Local.read_step lc_src mem_src loc to val_src vw Ordering.na lc_src.
Proof.
  inv SIM. specialize (MAXSRC loc). inv MAXSRC. hexploit MAX; eauto. i. des.
  hexploit max_readable_read.
  { eauto. }
  { eauto. }
  { eauto. }
  { instantiate (1:=val_src). auto. }
  i. des. esplits; eauto.
Qed.

Lemma sim_thread_src_read_na_racy
      f flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt
      loc val_src
      (SIM: sim_thread
              f flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt)
      (LOCAL: Local.wf lc_src mem_src)
      (VALS: vs_src loc = None)
      (WF: Mapping.wfs f)
  :
    exists to_src, Local.racy_read_step lc_src mem_src loc to_src val_src Ordering.na.
Proof.
  inv SIM. specialize (MAXSRC loc). inv MAXSRC.
  hexploit non_max_readable_read; eauto.
Qed.

Lemma sim_thread_tgt_write_na_racy
      f flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt0
      loc to
      (WRITE: Local.racy_write_step lc_tgt0 mem_tgt loc to Ordering.na)
      (SIM: sim_thread
              f flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt0)
      (LOCAL: Local.wf lc_tgt0 mem_tgt)
  :
    vs_tgt loc = None.
Proof.
  destruct (vs_tgt loc) eqn:VAL; auto.
  inv SIM. specialize (MAXTGT loc). inv MAXTGT. hexploit MAX; eauto. i. des.
  exfalso. eapply max_readable_not_write_race; eauto.
Qed.

Lemma sim_thread_src_write_na_racy
      f flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt
      loc
      (SIM: sim_thread
              f flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt)
      (LOCAL: Local.wf lc_src mem_src)
      (VALS: vs_src loc = None)
      (WF: Mapping.wfs f)
  :
    exists to_src, Local.racy_write_step lc_src mem_src loc to_src Ordering.na.
Proof.
  inv SIM. specialize (MAXSRC loc). inv MAXSRC.
  hexploit non_max_readable_write; eauto.
Qed.

(* Lemma sim_thread_tgt_flag_up *)
(*       f flag_src flag_tgt vs_src vs_tgt mem_src0 mem_tgt lc_src0 lc_tgt loc *)
(*       (SIM: sim_thread *)
(*               f flag_src flag_tgt vs_src vs_tgt *)
(*               mem_src0 mem_tgt lc_src0 lc_tgt) *)
(*       (LOCAL: Local.wf lc_src0 mem_src0) *)
(*       (MEM: Global.wf mem_src0) *)
(*       (WF: Mapping.wfs f) *)
(*       lang st *)
(*   : *)
(*     exists mem_src1 lc_src1, *)
(*       (<<STEPS: rtc (@Thread.tau_step _) *)
(*                     (Thread.mk lang st lc_src0 sc_src mem_src0) *)
(*                     (Thread.mk _ st lc_src1 sc_src mem_src1)>>) /\ *)
(*       (<<NONE: forall to from val released (GET: Memory.get loc to lc_src1.(Local.promises) = Some (from, Message.concrete val released)), *)
(*           released = None>>) /\ *)
(*       (<<SIM: sim_thread *)
(*                 f vers flag_src (fun loc0 => if Loc.eq_dec loc0 loc *)
(*                                              then true *)
(*                                              else flag_tgt loc0) *)
(*                 vs_src vs_tgt *)
(*                 mem_src1 mem_tgt lc_src1 lc_tgt>>) /\ *)
(*       (<<SPACE: space_future_memory (unchangable mem_tgt lc_tgt.(Local.promises)) f mem_src0 f mem_src1>>) *)
(* . *)
(* Proof. *)
(*   inv SIM. dup LOCAL0. inv LOCAL0. *)
(*   hexploit tgt_flag_up_sim_promises. *)
(*   { eauto. } *)
(*   { eauto. } *)
(*   { eapply sim_local_consistent in CONSISTENT; eauto. *)
(*     i. rewrite SRCTM. eapply CONSISTENT; eauto. *)
(*   } *)
(*   { eapply LOCAL. } *)
(*   { eapply MEM. } *)
(*   { auto. } *)
(*   i. des. esplits; [eapply STEPS|..]. *)
(*   { i. ss. eapply NONE; eauto. } *)
(*   { econs; auto. *)
(*     { eauto. } *)
(*     { econs; eauto. } *)
(*     { ii. hexploit (MAXSRC loc0). i. inv H. econs. *)
(*       { i. hexploit MAX; eauto. i. des. esplits. eapply VALS; eauto. } *)
(*       { i. hexploit NONMAX; eauto. ii. eapply H. eapply VALS; eauto. } *)
(*     } *)
(*     { eapply sim_closed_memory_future; eauto. *)
(*       eapply Thread.rtc_tau_step_future in STEPS; eauto. *)
(*       ss. des. eapply Memory.future_future_weak; eauto. *)
(*     } *)
(*     { i. rewrite MAXTS. auto. } *)
(*     { eapply reserved_space_empty_covered_decr; eauto. *)
(*       i. eapply COVERED; eauto. *)
(*     } *)
(*   } *)
(*   { eapply space_future_covered_decr. i. eapply COVERED; eauto. } *)
(* Qed. *)

(* Lemma lower_write_memory_le prom0 mem0 loc from to msg prom1 mem1 kind *)
(*       (WRITE: Memory.write prom0 mem0 loc from to msg prom1 mem1 kind) *)
(*       (KIND: Memory.op_kind_is_lower kind) *)
(*   : *)
(*     Memory.le prom1 prom0. *)
(* Proof. *)
(*   destruct kind; ss. inv WRITE. inv PROMISE. ii. *)
(*   erewrite Memory.remove_o in LHS; eauto. *)
(*   erewrite Memory.lower_o in LHS; eauto. des_ifs. *)
(* Qed. *)

(* Lemma na_write_max_readable *)
(*       mem0 prom0 loc ts val_old released *)
(*       prom1 mem1 msgs kinds kind from to val_new *)
(*       (MAX: max_readable mem0 prom0 loc ts val_old released) *)
(*       (WRITE: Memory.write_na ts prom0 mem0 loc from to val_new prom1 mem1 msgs kinds kind) *)
(*       (LOWER: mem1 = mem0) *)
(*   : *)
(*     max_readable mem1 prom1 loc to val_new None. *)
(* Proof. *)
(*   hexploit write_na_lower_memory_lower; eauto. i. des. *)
(*   destruct MAX. *)
(*   remember (Message.concrete val_old released) as msg_old. clear Heqmsg_old. *)
(*   revert from0 msg_old GET NONE MAX KINDS KIND. induction WRITE. *)
(*   { i. destruct kind; ss. inv WRITE. inv PROMISE. *)
(*     hexploit lower_same_same; [apply PROMISES|]. i. subst. *)
(*     hexploit lower_same_same; [apply MEM|]. i. subst. *)
(*     econs. *)
(*     { eapply Memory.lower_get0; eauto. } *)
(*     { erewrite Memory.remove_o; eauto. des_ifs. ss. des; clarify. } *)
(*     { i. erewrite Memory.remove_o; eauto. des_ifs. *)
(*       { ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto. } *)
(*       { eapply MAX; eauto. } *)
(*     } *)
(*   } *)
(*   { i. inv KINDS. destruct kind'; ss. clarify. *)
(*     inv WRITE_EX. inv PROMISE. *)
(*     hexploit lower_same_same; [apply PROMISES|]. i. subst. *)
(*     hexploit lower_same_same; [apply MEM|]. i. subst. *)
(*     eapply IHWRITE; auto. *)
(*     { eapply Memory.lower_get0; eauto. } *)
(*     { erewrite Memory.remove_o; eauto. des_ifs. ss. des; clarify. } *)
(*     { i. erewrite Memory.remove_o; eauto. des_ifs. *)
(*       { ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto. } *)
(*       { eapply MAX; eauto. } *)
(*     } *)
(*   } *)
(* Qed. *)

(* Lemma na_write_step_max_readable *)
(*       mem0 lc0 loc ts val_old released ord *)
(*       lc1 mem1 msgs kinds kind sc0 sc1 from to val_new *)
(*       (MAX: max_readable mem0 lc0.(Local.promises) loc ts val_old released) *)
(*       (TS: lc0.(Local.tview).(TView.cur).(View.pln) loc = ts) *)
(*       (WRITE: Local.write_na_step lc0 sc0 mem0 loc from to val_new ord lc1 sc1 mem1 *)
(*                                   msgs kinds kind) *)
(*       (LOWER: mem1 = mem0) *)
(*       (WF: Local.wf lc0 mem0) *)
(*   : *)
(*     max_readable mem1 lc1.(Local.promises) loc (lc1.(Local.tview).(TView.cur).(View.pln) loc) val_new None. *)
(* Proof. *)
(*   inv WRITE. ss. *)
(*   exploit na_write_max_readable. *)
(*   { eauto. } *)
(*   { eapply ts_le_memory_write_na. *)
(*     { eauto. } *)
(*     { eapply WF. } *)
(*   } *)
(*   { auto. } *)
(*   i. *)
(*   match goal with *)
(*   | |- _ ?vw _ _ => replace vw with to *)
(*   end; auto. *)
(*   unfold TimeMap.join. *)
(*   replace ((TimeMap.singleton loc to) loc) with to. *)
(*   2:{ unfold TimeMap.singleton. setoid_rewrite LocFun.add_spec. des_ifs. } *)
(*   symmetry. eapply TimeFacts.le_join_r. *)
(*   etrans. *)
(*   2:{ left. eapply write_na_ts_lt; eauto. } *)
(*   eapply WF. *)
(* Qed. *)

(* Lemma write_promise_reserve_same *)
(*       prom0 mem0 loc from to msg prom1 mem1 kind *)
(*       loc0 to0 from0 *)
(*       (WRITE: Memory.write prom0 mem0 loc from to msg prom1 mem1 kind) *)
(*       (RESERVE: Memory.get loc0 to0 prom0 = Some (from0, Message.reserve)) *)
(*       (MSG: msg <> Message.reserve) *)
(*   : *)
(*   Memory.get loc0 to0 prom1 = Some (from0, Message.reserve). *)
(* Proof. *)
(*   inv WRITE. erewrite Memory.remove_o; eauto. inv PROMISE. *)
(*   { erewrite Memory.add_o; eauto. des_ifs. ss. des; clarify. *)
(*     eapply Memory.add_get0 in PROMISES. des; clarify. } *)
(*   { erewrite Memory.split_o; eauto. des_ifs. *)
(*     { ss. des; clarify. eapply Memory.split_get0 in PROMISES. des; clarify. } *)
(*     { ss. des; clarify. eapply Memory.split_get0 in PROMISES. des; clarify. } *)
(*   } *)
(*   { erewrite Memory.lower_o; eauto. des_ifs. ss. des; clarify. *)
(*     eapply Memory.lower_get0 in PROMISES. des; clarify. inv MSG_LE; ss. } *)
(*   { ss. } *)
(* Qed. *)

(* Lemma write_na_promise_reserve_same *)
(*       ts prom0 mem0 loc from to val prom1 mem1 msgs kinds kind *)
(*       loc0 to0 from0 *)
(*       (WRITE: Memory.write_na ts prom0 mem0 loc from to val prom1 mem1 msgs kinds kind) *)
(*       (RESERVE: Memory.get loc0 to0 prom0 = Some (from0, Message.reserve)) *)
(*   : *)
(*   Memory.get loc0 to0 prom1 = Some (from0, Message.reserve). *)
(* Proof. *)
(*   revert loc0 to0 from0 RESERVE. induction WRITE. *)
(*   { i. eapply write_promise_reserve_same; eauto. ss. } *)
(*   { i. eapply IHWRITE. eapply write_promise_reserve_same; eauto. *)
(*     unguard. des; clarify. *)
(*   } *)
(* Qed. *)

(* Lemma sim_thread_tgt_write_na_aux *)
(*       f vers flag_src flag_tgt vs_src vs_tgt *)
(*       mem_src mem_tgt0 lc_src lc_tgt00 *)
(*       loc from to val_old val_new lc_tgt1 sc_tgt1 mem_tgt1 ord msgs kinds kind *)
(*       (WRITE: Local.write_na_step lc_tgt0 sc_tgt0 mem_tgt0 loc from to val_new ord lc_tgt1 sc_tgt1 mem_tgt1 msgs kinds kind) *)
(*       (LOWER: mem_tgt1 = mem_tgt0) *)
(*       (SIM: sim_thread *)
(*               f vers flag_src flag_tgt vs_src vs_tgt *)
(*               mem_src mem_tgt0 lc_src lc_tgt00) *)
(*       (VAL: vs_tgt loc = Some val_old) *)
(*       (FLAG: flag_tgt loc = true) *)
(*       (CONSISTENT: Local.promise_consistent lc_tgt1) *)
(*       (LOCAL: Local.wf lc_tgt0 mem_tgt0) *)
(*       (MEM: Memory.closed mem_tgt0) *)
(*       (WF: Mapping.wfs f) *)
(*   : *)
(*     (<<SIM: sim_thread *)
(*               f vers flag_src flag_tgt vs_src (fun loc0 => if Loc.eq_dec loc0 loc then Some val_new else vs_tgt loc0) *)
(*               mem_src mem_tgt1 lc_src lc_tgt11>>) /\ *)
(*     (<<ORD: ord = Ordering.na>>) /\ *)
(*     (<<SC: sc_tgt1 = sc_tgt0>>) *)
(* . *)
(* Proof. *)
(*   subst. hexploit write_na_step_lower_memory_lower; eauto. i. des. *)
(*   assert ((<<MLE: Memory.le lc_tgt1.(Local.promises) lc_tgt0.(Local.promises)>>) /\ *)
(*           (<<OTHERS: forall loc0 (NEQ: loc0 <> loc) to, *)
(*               Memory.get loc0 to lc_tgt1.(Local.promises) *)
(*               = *)
(*               Memory.get loc0 to lc_tgt0.(Local.promises)>>)). *)
(*   { inv WRITE. ss. *)
(*     revert KINDS KIND. clear CONSISTENT. induction WRITE0; i. *)
(*     { splits. *)
(*       { eapply lower_write_memory_le; eauto. destruct kind; ss. } *)
(*       { i. inv WRITE. destruct kind; ss. inv PROMISE. *)
(*         erewrite (@Memory.remove_o promises2); eauto. *)
(*         erewrite (@Memory.lower_o promises0); eauto. *)
(*         des_ifs. des; clarify. *)
(*       } *)
(*     } *)
(*     { inv KINDS. splits. *)
(*       { transitivity promises'. *)
(*         { eapply IHWRITE0; eauto. } *)
(*         { eapply lower_write_memory_le; eauto. destruct kind'; ss. } *)
(*       } *)
(*       { i. inv WRITE_EX. destruct kind'; ss. inv PROMISE. *)
(*         transitivity (Memory.get loc0 to0 promises'). *)
(*         { eapply IHWRITE0; eauto. } *)
(*         { erewrite (@Memory.remove_o promises'); eauto. *)
(*           erewrite (@Memory.lower_o promises0); eauto. *)
(*           des_ifs. des; clarify. *)
(*         } *)
(*       } *)
(*     } *)
(*   } *)
(*   hexploit sim_local_consistent_ex. *)
(*   { eapply PromiseConsistent.write_na_step_promise_consistent; eauto. } *)
(*   { inv SIM. eauto. } *)
(*   { auto. } *)
(*   intros CONSSRC. des. splits. *)
(*   2:{ inv WRITE. destruct ord; ss. } *)
(*   2:{ inv WRITE. auto. } *)
(*   inv SIM. econs; auto. *)
(*   { inv WRITE. auto. } *)
(*   { eauto. } *)
(*   { inv WRITE. inv LOCAL0. econs; ss; auto. *)
(*     { eapply sim_tview_tgt_mon; eauto. *)
(*       eapply TViewFacts.write_tview_incr. eapply LOCAL. *)
(*     } *)
(*     { econs. *)
(*       { i. eapply MLE in GET. hexploit sim_promises_get; eauto. *)
(*         i. des. esplits; eauto. *)
(*       } *)
(*       { i. destruct (Loc.eq_dec loc0 loc). *)
(*         { subst. destruct (classic (msg_src = Message.reserve)). *)
(*           { subst. hexploit sim_promises_get_if; eauto. i. des; ss. *)
(*             left. inv MSG. esplits; eauto. *)
(*             eapply write_na_promise_reserve_same; eauto. *)
(*           } *)
(*           { right. esplits; eauto. *)
(*             { rewrite SRCTM. eapply CONSSRC; eauto. } *)
(*             { i. subst. eapply sim_promises_nonsynch_loc in GET; eauto; ss. *)
(*               rewrite FLAG. ss. *)
(*             } *)
(*           } *)
(*         } *)
(*         { hexploit sim_promises_get_if; eauto. i. des. *)
(*           { left. esplits; eauto. rewrite OTHERS; eauto. } *)
(*           { right. esplits; eauto. } *)
(*         } *)
(*       } *)
(*       { i. eapply sim_promises_none; eauto. } *)
(*     } *)
(*     { inv RELVERS. econs. i. eapply MLE in GET. eauto. } *)
(*   } *)
(*   { ii. des_ifs. *)
(*     { specialize (MAXTGT loc). inv MAXTGT. *)
(*       hexploit MAX; eauto. i. des. *)
(*       hexploit na_write_step_max_readable. *)
(*       { instantiate (5:=Local.mk _ _). eapply MAX0. } *)
(*       all: ss; eauto. *)
(*       i. destruct lc_tgt1. ss. econs. i. clarify. *)
(*       esplits; eauto. *)
(*     } *)
(*     { inv WRITE. ss. specialize (MAXTGT loc0). inv MAXTGT. econs; eauto. *)
(*       i. ss. hexploit MAX; eauto. i. des. esplits; eauto. *)
(*       match goal with *)
(*       | |- _ ?vw _ _ => replace vw with (tvw.(TView.cur).(View.pln) loc0) *)
(*       end. *)
(*       { inv MAX0. econs; eauto. *)
(*         { rewrite OTHERS; eauto. } *)
(*         { i. rewrite OTHERS; eauto. } *)
(*       } *)
(*       { symmetry. eapply TimeFacts.le_join_l. unfold TimeMap.singleton. *)
(*         setoid_rewrite LocFun.add_spec_neq; auto. eapply Time.bot_spec. *)
(*       } *)
(*     } *)
(*   } *)
(*   { i. des_ifs. specialize (PERM loc). *)
(*     rewrite VAL in PERM. unfold option_rel in *. des_ifs. *)
(*   } *)
(*   { eapply reserved_space_empty_reserve_decr; eauto. } *)
(* Qed. *)


Lemma sim_thread_some_no_race
      f flag_src flag_tgt vs_src vs_tgt mem_src mem_tgt lc_src lc_tgt loc val_old
      (SIM: sim_thread
              f flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt)
      (VAL: vs_tgt loc = Some val_old)
  :
  __guard__(mem_src.(Global.promises) loc = true -> lc_src.(Local.promises) loc = true).
Proof.
  inv SIM. specialize (MAXSRC loc). inv MAXSRC.
  specialize (PERM loc). unfold option_rel in *. des_ifs.
  hexploit MAX; auto. i. des. inv MAX0. ss.
  eapply Bool.le_implb in NONE. ii. rewrite H in NONE. ss.
Qed.

Lemma sim_thread_tgt_write_na
      f flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt0 lc_src0 lc_tgt0
      loc from to val_old val_new lc_tgt1 mem_tgt1
      releasedm released
      (WRITE: Local.write_step lc_tgt0 mem_tgt0 loc from to val_new releasedm released Ordering.na lc_tgt1 mem_tgt1)
      (SIM: sim_thread
              f flag_src flag_tgt vs_src vs_tgt
              mem_src0 mem_tgt0 lc_src0 lc_tgt0)
      (VAL: vs_tgt loc = Some val_old)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt0)
      (WF: Mapping.wfs f)
      lang st
  :
    exists mem_src1 lc_src1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk lang st lc_src0 mem_src0)
                    (Thread.mk _ st lc_src1 mem_src1)>>) /\
      (<<SIM: sim_thread
                f flag_src
                (fun loc0 => if Loc.eq_dec loc0 loc then true else flag_tgt loc0)
                vs_src
                (fun loc0 => if Loc.eq_dec loc0 loc then Some val_new else vs_tgt loc0)
                mem_src1 mem_tgt1 lc_src1 lc_tgt1>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) f mem_src0.(Global.memory) f mem_src1.(Global.memory)>>) /\
      (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f, mem_src0, mem_tgt0) (f, mem_src1, mem_tgt1)>>)
.
Proof.
  hexploit sim_thread_some_no_race; eauto. i.
  inv SIM. inv LOCAL. inv MEM. dup WRITE. inv WRITE. ss.
  hexploit sim_promises_tgt_fulfill; eauto.
  { eapply LOCALSRC. }
  { eapply LOCALTGT. }
  i. des.
  assert (STEPS: rtc (@Thread.internal_step _)
                     (Thread.mk lang st (Local.mk tvw_src prm_src rsv_src) (Global.mk sc_src gprm_src mem_src))
                     (Thread.mk lang st (Local.mk tvw_src lprm_src1 rsv_src) (Global.mk sc_src gprm_src1 mem_src))).
  { unguard. des.
    { econs 2; [|reflexivity]. econs.
      econs 1. econs; eauto.
    }
    { ss. subst. reflexivity. }
  }
  esplits.
  { eapply rtc_implies; [|apply STEPS]. i.
    inv H0. econs; [econs 1; eauto|]. inv LOCAL; ss.
  }
  { econs; ss.
    { econs; eauto.
      replace (boolmap_plus flag_src (fun loc0 => if LocSet.Facts.eq_dec loc0 loc then true else flag_tgt loc0)) with (LocFun.add loc true (boolmap_plus flag_src flag_tgt)).
      { eapply add_tgt_sim_memory; eauto. unguard. des; subst; auto.
        erewrite <- Promises.promise_minus; eauto.
      }
      { extensionality loc0. rewrite loc_fun_add_spec.
        unfold boolmap_plus, orb. des_ifs. }
    }
    { econs; eauto. eapply sim_tview_mon_locs.
      { eapply sim_tview_tgt_mon; eauto.
        eapply TViewFacts.write_tview_incr. eapply LOCALTGT. }
      { unfold boolmap_plus, orb. i. des_ifs. }
    }
    { eapply promise_steps_max_values_src; eauto. }
    { ii. des_ifs.
      { specialize (MAXTGT loc). inv MAXTGT.
        hexploit MAX; eauto. i. des. inv MAX0.
        econs. i. clarify.
        hexploit local_write_step_timestamp_pln; eauto.
        { apply LOCALTGT. }
        i. ss. rewrite H0. esplits. econs; ss.
        { eapply Memory.add_get0; eauto. }
        { inv FULFILL; ss. inv REMOVE. inv GREMOVE.
          rewrite ! loc_fun_add_spec. clear. des_ifs.
        }
        i. erewrite Memory.add_o in GET0; eauto. des_ifs.
        { ss. des; subst. timetac. }
        { eapply MAX1; eauto. inv WRITABLE.
          etrans; eauto. eapply TimeFacts.le_lt_lt; eauto. eapply LOCALTGT.
        }
      }
      { econs. i. specialize (MAXTGT loc0). inv MAXTGT.
        hexploit MAX; eauto. i. des.
        ss. unfold TimeMap.join, TimeMap.singleton, LocFun.init.
        rewrite loc_fun_add_spec. des_ifs; ss.
        rewrite TimeFacts.le_join_l; [|apply Time.bot_spec].
        esplits. hexploit promises_fulfill_unchanged_loc; eauto. i. des.
        erewrite <- unchanged_loc_max_readable; eauto.
        econs; auto.
        { ss. eapply add_unchanged_loc; eauto. }
      }
    }
    { i. specialize (PERM loc0). unfold option_rel in *. des_ifs. }
    { i. auto. }
    { i. hexploit FLAGNONE; eauto. i. des. des_ifs.
      specialize (PERM loc). rewrite VAL in PERM. rewrite VAL0 in PERM. ss.
    }
  }
  { ss. eapply space_future_memory_refl; eauto. refl. }
  { econs. i. splits.
    { refl. }
    { rr. splits; ss. eapply UNCH; eauto. }
    { rr. splits; ss.
      { eapply add_other_owned_future; eauto. ii. subst.
        specialize (PERM loc). rewrite VAL in PERM. unfold option_rel in PERM. des_ifs.
        specialize (MAXSRC loc). inv MAXSRC. hexploit MAX; eauto. i. des.
        inv MAX0. ss. unfold BoolMap.minus, andb, negb in OWN.
        destruct (gprm_src loc), (prm_src); ss.
      }
      { eapply UNCH; eauto. }
    }
  }
Qed.

Lemma reserve_future_steps rsv0 mem0 rsv1 mem1 prom gprm
      (FUTURE: reserve_future_memory rsv0 mem0 rsv1 mem1)
      tvw sc lang st
  :
    rtc (@Thread.tau_step _)
        (Thread.mk lang st (Local.mk tvw prom rsv0) (Global.mk sc gprm mem0))
        (Thread.mk _ st (Local.mk tvw prom rsv1) (Global.mk sc gprm mem1)).
Proof.
  induction FUTURE.
  { refl. }
  { econs; [|eauto]. econs.
    { econs. econs 2. econs; eauto. }
    { ss. }
  }
  { econs; [|eauto]. econs.
    { econs. econs 3. econs; eauto. }
    { ss. }
  }
Qed.

Lemma cap_max_readable mem prom loc ts val released
      (MEM: Global.wf mem)
  :
    max_readable mem prom loc ts val released
    <->
    max_readable (Global.cap_of mem) prom loc ts val released.
Proof.
  assert (CAP: Memory.cap (Global.memory mem) (Global.memory (Global.cap_of mem))).
  { apply Memory.cap_of_cap. }
  split.
  { i. inv H. econs; eauto.
    { eapply Memory.cap_le; [..|eauto]; eauto. }
    { i. eapply Memory.cap_inv in GET0; eauto.
      des; clarify.
      eapply MAX in GET0; eauto.
    }
  }
  { i. inv H. eapply Memory.cap_inv in GET; eauto. des; clarify.
    econs; eauto. i. eapply MAX; eauto.
    eapply Memory.cap_le; [..|eauto]; eauto.
  }
Qed.

Lemma cap_max_values_src vs mem lc
      (MAX: max_values_src vs mem lc)
      (MEM: Global.wf mem)
  :
    max_values_src vs (Global.cap_of mem) lc.
Proof.
  ii. specialize (MAX loc). inv MAX. econs.
  { i. hexploit MAX0; eauto. i. des. esplits; eauto.
    erewrite <- cap_max_readable; eauto.
  }
  { i. hexploit NONMAX; eauto. ii. eapply H.
    erewrite cap_max_readable; eauto.
  }
Qed.

Lemma cap_max_values_tgt vs mem lc
      (MAX: max_values_tgt vs mem lc)
      (MEM: Global.wf mem)
  :
    max_values_tgt vs (Global.cap_of mem) lc.
Proof.
  ii. specialize (MAX loc). inv MAX. econs.
  i. hexploit MAX0; eauto. i. des. esplits; eauto.
  erewrite <- cap_max_readable; eauto.
Qed.

Lemma sim_reserves_preserve
      prom_src prom_tgt f0 f1 mem
      (SIM: sim_reserves f0 prom_src prom_tgt)
      (MAPLE: Mapping.les f0 f1)
      (PRESERVE: forall loc to from msg
                        (GET: Memory.get loc to mem = Some (from, msg))
                        ts fts
                        (TS: Time.le ts to)
                        (MAP: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) fts (Some ts)),
          sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) fts (Some ts))
      (MLE: Memory.le prom_tgt mem)
      (WF: Mapping.wfs f0)
  :
    sim_reserves f1 prom_src prom_tgt.
Proof.
  econs.
  { i. hexploit sim_reserves_get; eauto. i. des. esplits.
    { eapply PRESERVE; eauto. eapply memory_get_ts_le; eauto. }
    { eapply PRESERVE; eauto. refl. }
    { auto. }
  }
  { i. hexploit sim_reserves_get_if; eauto. i. des.
    { esplits.
      { eapply PRESERVE; eauto. refl. }
      { eauto. }
    }
  }
Qed.

Lemma sim_thread_cap
      f0 flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt
      (SIM: sim_thread
              f0 (fun _ => false) flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt)
      (WF: Mapping.wfs f0)
      (MEMSRC: Global.wf mem_src)
      (MEMTGT: Global.wf mem_tgt)
      (LOCALSRC: Local.wf lc_src mem_src)
      (LOCALTGT: Local.wf lc_tgt mem_tgt)
  :
    exists f1,
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<MAPWF: Mapping.wfs f1>>) /\
      (<<SIM: sim_thread
                f1 (fun _ => false) flag_tgt vs_src vs_tgt
                (Global.cap_of mem_src) (Global.cap_of mem_tgt) lc_src lc_tgt>>)
.
Proof.
  assert (CAPSRC: Memory.cap (Global.memory mem_src) (Global.memory (Global.cap_of mem_src))).
  { apply Memory.cap_of_cap. }
  assert (CAPTGT: Memory.cap (Global.memory mem_tgt) (Global.memory (Global.cap_of mem_tgt))).
  { apply Memory.cap_of_cap. }
  inv SIM. inv MEM.
  hexploit cap_sim_memory; eauto. i. des. esplits; eauto.
  { eapply MEMTGT. }
  { eapply MEMSRC. }
  i. des. esplits; eauto. econs; eauto.
  { econs; eauto. eapply sim_timemap_mon_latest; eauto. }
  { inv LOCAL. econs; eauto.
    { eapply sim_tview_mon_latest; eauto. }
    { eapply sim_reserves_preserve; eauto. eapply LOCALTGT. }
  }
  { eapply cap_max_values_src; eauto. }
  { eapply cap_max_values_tgt; eauto. }
  { ss. }
Qed.

Lemma sim_readable L f vw_src vw_tgt loc to_src to_tgt ord
      (READABLE: TView.readable vw_tgt loc to_tgt ord)
      (SIM: sim_view L f (Mapping.vers f) vw_src vw_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt))
      (WF: Mapping.wfs f)
      (LOC: L loc)
  :
    TView.readable vw_src loc to_src ord.
Proof.
  inv READABLE. econs.
  { eapply sim_timestamp_le.
    { eapply SIM. auto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eapply mapping_latest_wf_loc. }
  }
  { i. eapply sim_timestamp_le.
    { eapply SIM. auto. }
    { eauto. }
    { ss. eauto. }
    { eauto. }
    { eapply mapping_latest_wf_loc. }
  }
Qed.

Lemma sim_writable L f vw_src vw_tgt loc to_src to_tgt ord
      (WRITABLE: TView.writable vw_tgt loc to_tgt ord)
      (SIM: sim_view L f (Mapping.vers f) vw_src vw_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt))
      (WF: Mapping.wfs f)
      (LOC: L loc)
  :
    TView.writable vw_src loc to_src ord.
Proof.
  inv WRITABLE. econs.
  eapply sim_timestamp_lt.
  { eapply SIM. auto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eapply mapping_latest_wf_loc. }
Qed.

Lemma semi_sim_timemap_join loc f v to_src to_tgt tm_src tm_tgt
      (SIM: sim_timemap (fun loc0 => loc0 <> loc) f v tm_src tm_tgt)
      (TS: sim_timestamp (f loc) (v loc) to_src (Some to_tgt))
      (LESRC: time_le_timemap loc to_src tm_src)
      (LETGT: time_le_timemap loc to_tgt tm_tgt)
      (WF: Mapping.wfs f)
      (VER: version_wf f v)
  :
    sim_timemap (fun _ => True) f v (TimeMap.join (TimeMap.singleton loc to_src) tm_src) (TimeMap.join (TimeMap.singleton loc to_tgt) tm_tgt).
Proof.
  ii. destruct (Loc.eq_dec l loc).
  { subst. unfold TimeMap.join.
    repeat rewrite TimeFacts.le_join_l.
    { eapply sim_timemap_singleton; ss. }
    { unfold TimeMap.singleton. setoid_rewrite LocFun.add_spec_eq.
      eapply LETGT. }
    { unfold TimeMap.singleton. setoid_rewrite LocFun.add_spec_eq.
      eapply LESRC. }
  }
  { unfold TimeMap.join.
    rewrite opt_time_join_some. eapply sim_timestamp_join; eauto.
    unfold TimeMap.singleton. setoid_rewrite LocFun.add_spec_neq; eauto.
    eapply sim_timestamp_bot; eauto.
  }
Qed.

Lemma semi_sim_view_join loc f v to_src to_tgt vw_src vw_tgt
      (SIM: sim_view (fun loc0 => loc0 <> loc) f v vw_src vw_tgt)
      (TS: sim_timestamp (f loc) (v loc) to_src (Some to_tgt))
      (LESRC: time_le_view loc to_src vw_src)
      (LETGT: time_le_view loc to_tgt vw_tgt)
      (WF: Mapping.wfs f)
      (VER: version_wf f v)
  :
    sim_view (fun _ => True) f v (View.join (View.singleton_ur loc to_src) vw_src) (View.join (View.singleton_ur loc to_tgt) vw_tgt).
Proof.
  econs.
  { eapply semi_sim_timemap_join; eauto.
    { eapply SIM. }
    { eapply LESRC. }
    { eapply LETGT. }
  }
  { eapply semi_sim_timemap_join; eauto.
    { eapply SIM. }
    { eapply LESRC. }
    { eapply LETGT. }
  }
Qed.

Lemma semi_sim_opt_view_join loc f v to_src to_tgt released_src released_tgt
      (SIM: sim_opt_view (fun loc0 => loc0 <> loc) f (Some v) released_src released_tgt)
      (TS: sim_timestamp (f loc) (v loc) to_src (Some to_tgt))
      (LESRC: time_le_opt_view loc to_src released_src)
      (LETGT: time_le_opt_view loc to_tgt released_tgt)
      (WF: Mapping.wfs f)
      (VER: version_wf f v)
  :
    sim_view (fun _ => True) f v (View.join (View.singleton_ur loc to_src) (View.unwrap released_src)) (View.join (View.singleton_ur loc to_tgt) (View.unwrap released_tgt)).
Proof.
  inv SIM; ss.
  { inv LESRC. inv LETGT. eapply semi_sim_view_join; eauto. }
  { eapply sim_view_join; eauto.
    { eapply sim_view_singleton_ur; eauto. }
    { eapply sim_view_bot; eauto. }
  }
Qed.

Lemma sim_opt_view_mon_opt_ver L f v0 v1 vw_src vw_tgt
      (SIM: sim_opt_view L f v0 vw_src vw_tgt)
      (VER: forall v0' (VER: v0 = Some v0'),
          exists v1', (<<VER: v1 = Some v1'>>) /\(<<VERLE: version_le v0' v1'>>))
      (WF: Mapping.wfs f)
      (VERWF: opt_version_wf f v1)
  :
    sim_opt_view L f v1 vw_src vw_tgt.
Proof.
  destruct v0.
  { hexploit VER; eauto. i. des. clarify.
    eapply sim_opt_view_mon_ver; eauto.
  }
  { inv SIM. econs. }
Qed.

Lemma sim_read_tview f flag_src  tvw_src tvw_tgt
      loc to_src released_src ord to_tgt released_tgt
      (SIM: sim_tview f flag_src tvw_src tvw_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt))
      (RELEASED: sim_opt_view (fun loc0 => loc0 <> loc) f (Some (Mapping.vers f)) released_src released_tgt)
      (WF: Mapping.wfs f)
      (LESRC: time_le_opt_view loc to_src released_src)
      (LETGT: time_le_opt_view loc to_tgt released_tgt)
  :
    sim_tview f flag_src (TView.read_tview tvw_src loc to_src released_src ord) (TView.read_tview tvw_tgt loc to_tgt released_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  assert (TM: sim_timestamp (f loc) (Mapping.vers f loc) to_src (Some to_tgt)).
  { eapply sim_timestamp_exact_sim; eauto. }
  assert (JOIN: sim_view (fun loc0 => flag_src loc0 = false) f (Mapping.vers f)
                         (View.join (View.singleton_ur loc to_src) (View.unwrap released_src))
                         (View.join (View.singleton_ur loc to_tgt) (View.unwrap released_tgt))).
  { eapply sim_view_mon_locs.
    { eapply semi_sim_opt_view_join; eauto.
    }
    { ss. }
  }
  econs.
  { eapply SIM. }
  { ss. rewrite View.join_assoc. rewrite View.join_assoc.
    eapply sim_view_join; eauto.
    { eapply SIM. }
    unfold View.singleton_ur_if. des_ifs.
    { eapply sim_view_join; eauto.
      { eapply sim_view_singleton_ur; eauto. }
      { eapply sim_view_bot; eauto. }
    }
    { destruct ord; ss. }
    { eapply sim_view_join; eauto.
      { eapply sim_view_singleton_rw; eauto. }
      { eapply sim_view_bot; eauto. }
    }
  }
  { ss. rewrite View.join_assoc. rewrite View.join_assoc.
    eapply sim_view_join; eauto.
    { eapply SIM. }
    unfold View.singleton_ur_if. des_ifs.
    { eapply sim_view_join; eauto.
      { eapply sim_view_singleton_rw; eauto. }
      { eapply sim_view_bot; eauto. }
    }
  }
Qed.

Lemma sim_write_tview_normal f flag_src tvw_src tvw_tgt
      loc to_src ord to_tgt
      (SIM: sim_tview f flag_src tvw_src tvw_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt))
      (ORD: ~ Ordering.le Ordering.acqrel ord)
      (WF: Mapping.wfs f)
  :
    sim_tview f flag_src (TView.write_tview tvw_src loc to_src ord) (TView.write_tview tvw_tgt loc to_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  assert (TM: sim_timestamp (f loc) (Mapping.vers f loc) to_src (Some to_tgt)).
  { eapply sim_timestamp_exact_sim; eauto. }
  assert (JOIN: sim_view (fun loc0 => flag_src loc0 = false) f (Mapping.vers f)
                         (View.singleton_ur loc to_src)
                         (View.singleton_ur loc to_tgt)).
  { apply sim_view_singleton_ur; eauto. }
  econs; ss.
  { ii. setoid_rewrite LocFun.add_spec. des_ifs.
    { eapply sim_view_join; eauto.
      { eapply SIM. }
      { apply sim_view_singleton_ur; eauto; ss. }
    }
    { eapply SIM. }
  }
  { eapply sim_view_join; eauto. eapply SIM. }
  { eapply sim_view_join; eauto. eapply SIM. }
Qed.

Lemma sim_write_tview_release f flag_src tvw_src tvw_tgt
      loc to_src ord to_tgt
      (SIM: sim_tview f flag_src tvw_src tvw_tgt)
      (TO: sim_timestamp (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt))
      (FLAG: forall loc, flag_src loc = false)
      (WF: Mapping.wfs f)
  :
    sim_tview f flag_src (TView.write_tview tvw_src loc to_src ord) (TView.write_tview tvw_tgt loc to_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  assert (JOIN: forall L, sim_view L f (Mapping.vers f)
                                   (View.singleton_ur loc to_src)
                                   (View.singleton_ur loc to_tgt)).
  { i. apply sim_view_singleton_ur; eauto. }
  econs; ss.
  { ii. setoid_rewrite LocFun.add_spec. des_ifs.
    { eapply sim_view_join; eauto.
      { eapply sim_view_mon_locs.
        { eapply SIM. }
        { i. ss. }
      }
    }
    { eapply sim_view_join; eauto.
      { eapply sim_view_mon_ver; auto.
        { eapply SIM. }
        { refl. }
      }
    }
    { eapply SIM. }
  }
  { eapply sim_view_join; eauto. eapply SIM. }
  { eapply sim_view_join; eauto. eapply SIM. }
Qed.

Lemma sim_read_fence_tview f flag_src tvw_src tvw_tgt
      ord
      (SIM: sim_tview f flag_src tvw_src tvw_tgt)
      (WF: Mapping.wfs f)
  :
    sim_tview f flag_src (TView.read_fence_tview tvw_src ord) (TView.read_fence_tview tvw_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  econs; ss.
  { eapply SIM. }
  { des_ifs.
    { eapply SIM. }
    { eapply SIM. }
  }
  { eapply SIM. }
Qed.

Lemma sim_write_fence_tview_normal f flag_src tvw_src tvw_tgt sc_src sc_tgt
      ord
      (SIM: sim_tview f flag_src tvw_src tvw_tgt)
      (ORD: ~ Ordering.le Ordering.acqrel ord)
      (WF: Mapping.wfs f)
  :
    sim_tview f flag_src (TView.write_fence_tview tvw_src sc_src ord) (TView.write_fence_tview tvw_tgt sc_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  econs; ss.
  { des_ifs. eapply SIM. }
  { des_ifs.
    { destruct ord; ss. }
    { eapply SIM. }
  }
  { des_ifs.
    { destruct ord; ss. }
    { rewrite ! View.join_bot_r. eapply SIM. }
  }
Qed.

Lemma sim_write_fence_tview_release f flag_src tvw_src tvw_tgt sc_src sc_tgt
      ord
      (SIM: sim_tview f flag_src tvw_src tvw_tgt)
      (SC: sim_timemap (fun _ => True) f (Mapping.vers f) sc_src sc_tgt)
      (FLAG: forall loc, flag_src loc = false)
      (WF: Mapping.wfs f)
  :
    sim_tview f flag_src (TView.write_fence_tview tvw_src sc_src ord) (TView.write_fence_tview tvw_tgt sc_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  assert (JOIN: forall L, sim_timemap L f (Mapping.vers f)
                                      (TView.write_fence_sc tvw_src sc_src ord)
                                      (TView.write_fence_sc tvw_tgt sc_tgt ord)).
  { i. unfold TView.write_fence_sc. des_ifs.
    { eapply sim_timemap_join; eauto.
      { eapply sim_timemap_mon_locs; eauto. ss. }
      { eapply sim_timemap_mon_locs.
        { eapply SIM. }
        { ss. }
      }
    }
    { eapply sim_timemap_mon_locs; eauto. ss. }
  }
  econs; ss.
  { des_ifs.
    { i. eapply sim_view_mon_locs.
      { eapply SIM. }
      { ss. }
    }
    { i. eapply sim_view_mon_locs.
      { eapply sim_view_mon_ver; auto.
        { eapply SIM. }
        { refl. }
      }
      { ss. }
    }
  }
  { des_ifs. eapply SIM. }
  { eapply sim_view_join; auto.
    { eapply SIM. }
    { des_ifs. eapply sim_view_bot; auto. }
  }
Qed.

Lemma sim_write_fence_sc f flag_src tvw_src tvw_tgt sc_src sc_tgt
      ord
      (SIM: sim_tview f flag_src tvw_src tvw_tgt)
      (SC: sim_timemap (fun loc => flag_src loc = false) f (Mapping.vers f) sc_src sc_tgt)
      (WF: Mapping.wfs f)
  :
    sim_timemap (fun loc => flag_src loc = false) f (Mapping.vers f) (TView.write_fence_sc tvw_src sc_src ord) (TView.write_fence_sc tvw_tgt sc_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  unfold TView.write_fence_sc. des_ifs. eapply sim_timemap_join; auto.
  eapply SIM.
Qed.

Lemma sim_write_released_normal f flag_src tvw_src tvw_tgt
      loc to_src ord to_tgt released_src released_tgt
      (SIM: sim_tview f flag_src tvw_src tvw_tgt)
      (RELEASED: sim_opt_view (fun loc0 => loc0 <> loc) f (Some (Mapping.vers f)) released_src released_tgt)
      (ORD: ~ Ordering.le Ordering.acqrel ord)
      (WF: Mapping.wfs f)
  :
    sim_opt_view (fun loc0 => loc0 <> loc) f
                 (Some (Mapping.vers f))
                 (TView.write_released tvw_src loc to_src released_src ord)
                 (TView.write_released tvw_tgt loc to_tgt released_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  unfold TView.write_released. des_ifs.
  { econs.
    eapply sim_view_join; auto.
    { eapply sim_opt_view_unwrap; eauto. i. clarify. }
    { ss. setoid_rewrite LocFun.add_spec_eq. des_ifs.
      eapply sim_view_join; auto.
      { eapply sim_view_mon_ver; eauto. eapply SIM. }
      { eapply sim_view_singleton_ur; auto; ss. }
    }
  }
  { econs. }
Qed.

Lemma sim_write_released_release f flag_src tvw_src tvw_tgt
      loc to_src ord to_tgt released_src released_tgt
      (SIM: sim_tview f flag_src tvw_src tvw_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt))
      (RELEASED: sim_opt_view (fun loc0 => loc0 <> loc) f (Some (Mapping.vers f)) released_src released_tgt)
      (FLAG: forall loc, flag_src loc = false)
      (WF: Mapping.wfs f)
  :
    sim_opt_view (fun loc0 => loc0 <> loc) f (Some (Mapping.vers f))
                 (TView.write_released tvw_src loc to_src released_src ord)
                 (TView.write_released tvw_tgt loc to_tgt released_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  unfold TView.write_released. des_ifs; econs.
  eapply sim_view_join; auto.
  { eapply sim_opt_view_unwrap; eauto. i. clarify. }
  { ss. setoid_rewrite LocFun.add_spec_eq. des_ifs.
    { eapply sim_view_join; auto.
      { eapply sim_view_mon_locs; eauto.
        { eapply SIM. }
        { i. ss. }
      }
      { eapply sim_view_singleton_ur; auto; ss. }
    }
    { eapply sim_view_join; auto.
      { eapply sim_view_mon_ver; auto.
        { eapply SIM. }
        { refl. }
      }
      { eapply sim_view_singleton_ur; auto; ss. }
    }
  }
Qed.

Lemma sim_src_na_write_tview f flag_src tvw_src tvw_tgt
      loc to
      (SIM: sim_tview f flag_src tvw_src tvw_tgt)
      (WF: Mapping.wfs f)
  :
    sim_tview f (fun loc0 => if Loc.eq_dec loc0 loc then Some to else flag_src loc0) (TView.write_tview tvw_src loc to Ordering.na) tvw_tgt.
Proof.
  pose proof (mapping_latest_wf f).
  econs; ss.
  { i. des_ifs. econs.
    { ii. setoid_rewrite LocFun.add_spec; auto. des_ifs; ss.
      { unfold TimeMap.join.
        erewrite timemap_singleton_neq; auto.
        erewrite TimeFacts.le_join_l; auto.
        { eapply SIM; auto. }
        { eapply Time.bot_spec. }
      }
      { eapply SIM; auto. }
    }
    { ii. setoid_rewrite LocFun.add_spec; auto. des_ifs; ss.
      { unfold TimeMap.join.
        erewrite timemap_singleton_neq; auto.
        erewrite TimeFacts.le_join_l; auto.
        { eapply SIM; auto. }
        { eapply Time.bot_spec. }
      }
      { eapply SIM; auto. }
    }
  }
  { i. econs.
    { ii. des_ifs. ss.
      unfold TimeMap.join.
      erewrite timemap_singleton_neq; auto.
      erewrite TimeFacts.le_join_l; auto.
      { eapply SIM; auto. }
      { eapply Time.bot_spec. }
    }
    { ii. des_ifs. ss.
      unfold TimeMap.join.
      erewrite timemap_singleton_neq; auto.
      erewrite TimeFacts.le_join_l; auto.
      { eapply SIM; auto. }
      { eapply Time.bot_spec. }
    }
  }
  { econs.
    { ii. des_ifs. ss. unfold TimeMap.join.
      erewrite timemap_singleton_neq; auto.
      erewrite TimeFacts.le_join_l; auto.
      { eapply SIM; auto. }
      { eapply Time.bot_spec. }
    }
    { ii. des_ifs. ss. unfold TimeMap.join.
      erewrite timemap_singleton_neq; auto.
      erewrite TimeFacts.le_join_l; auto.
      { eapply SIM; auto. }
      { eapply Time.bot_spec. }
    }
  }
Qed.

Lemma cancel_future_memory_decr loc prom0 mem0 prom1 mem1
      (FUTURE: cancel_future_memory loc prom0 mem0 prom1 mem1)
  :
  Memory.le mem1 mem0.
Proof.
  induction FUTURE; auto.
  { refl. }
  { etrans; eauto. inv CANCEL. eapply remove_le; eauto. }
Qed.

Lemma space_future_memory_trans_memory
      msgs mem0 mem1 mem2 f
      (FUTURE0: space_future_memory msgs f mem0 f mem1)
      (FUTURE1: space_future_memory msgs f mem1 f mem2)
      (MAPWF0: Mapping.wfs f)
  :
    space_future_memory msgs f mem0 f mem2.
Proof.
  eapply space_future_memory_trans; eauto.
  { refl. }
  { refl. }
  Qed.

Lemma unchanged_loc_max_ts mem0 mem1 loc
      (UNCH: unchanged_loc_memory loc mem0 mem1)
      (INHABITED: Memory.inhabited mem0)
  :
    Memory.max_ts loc mem0 = Memory.max_ts loc mem1.
Proof.
  specialize (INHABITED loc). eapply TimeFacts.antisym.
  { eapply Memory.max_ts_spec in INHABITED. des.
    inv UNCH. rewrite <- UNCH0 in GET.
    eapply Memory.max_ts_spec in GET. des. auto.
  }
  { inv UNCH. rewrite <- UNCH0 in INHABITED.
    eapply Memory.max_ts_spec in INHABITED. des.
    rewrite UNCH0 in GET.
    eapply Memory.max_ts_spec in GET. des. auto.
  }
Qed.

Lemma sim_thread_src_write_na
      f flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt lc_src0 lc_tgt
      loc val_old val_new
      (SIM: sim_thread
              f flag_src flag_tgt vs_src vs_tgt
              mem_src0 mem_tgt lc_src0 lc_tgt)
      (VAL: vs_src loc = Some val_old)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt mem_tgt)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt)
      (WF: Mapping.wfs f)
  :
    exists mem_src1 lc_src1 from to,
      (<<WRITE: Local.write_step lc_src0 mem_src0 loc from to val_new None None Ordering.na lc_src1 mem_src1>>) /\
      (<<SIM: sim_thread
                f
                (fun loc0 => if Loc.eq_dec loc0 loc then true else flag_src loc0)
                flag_tgt
                (fun loc0 => if Loc.eq_dec loc0 loc then Some val_new else vs_src loc0)
                vs_tgt
                mem_src1 mem_tgt lc_src1 lc_tgt>>) /\
        (<<SPACE: space_future_memory (unchangable mem_tgt.(Global.memory) lc_tgt.(Local.reserves)) f mem_src0.(Global.memory) f mem_src1.(Global.memory)>>) /\
        (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f, mem_src0, mem_tgt) (f, mem_src1, mem_tgt)>>)


.
Proof.
  hexploit top_time_exists.
  { eauto. }
  i. des.
  assert (TOP2: top_time (Time.join top (Memory.max_ts loc mem_src0.(Global.memory))) (f loc)).
  { eapply top_time_mon; eauto. eapply Time.join_l. }
  inv SIM. pose proof (MAXSRC loc). inv H.
  hexploit MAX; eauto. i. des. inv LOCAL. inv MEM.
  hexploit sim_promises_src_fulfill; eauto.
  { eapply LOCALSRC. }
  { eapply LOCALTGT. }
  { instantiate (1:=loc). inv MAX0. ss.
    i. rewrite H in NONE. destruct (prom loc); ss.
  }
  i. des; ss.
  hexploit max_readable_write.
  { eauto. }
  { eapply LOCALSRC. }
  { eauto. }
  { eapply Time.join_r. }
  { eapply Time.incr_spec. }
  { eauto. }
  { eapply View.opt_wf_none. }
  { ss. inv MAX0. ss. unfold implb in NONE. des_ifs. }
  i. des.
  assert (OTHERRLX: forall loc0 (NEQ: loc0 <> loc),
             View.rlx (TView.cur tvw1) loc0 = View.rlx (TView.cur tvw) loc0).
  { i. inv WRITE. clarify. ss.
    eapply TimeFacts.le_join_l. unfold TimeMap.singleton.
    setoid_rewrite LocFun.add_spec_neq; auto. eapply Time.bot_spec.
  }
  assert (OTHERPLN: forall loc0 (NEQ: loc0 <> loc),
             View.pln (TView.cur tvw1) loc0 = View.pln (TView.cur tvw) loc0).
  { i. inv WRITE. clarify. ss.
    eapply TimeFacts.le_join_l. unfold TimeMap.singleton.
    setoid_rewrite LocFun.add_spec_neq; auto. eapply Time.bot_spec.
  }
  esplits.
  { eauto. }
  { econs; eauto; ss.
    { econs; eauto.
      eapply other_promise_same_write in WRITE. ss. rewrite WRITE.
      replace ((boolmap_plus (fun loc0 => if LocSet.Facts.eq_dec loc0 loc then true else flag_src loc0) flag_tgt)) with (LocFun.add loc true (boolmap_plus flag_src flag_tgt)).
      { eapply add_src_sim_memory; eauto. }
      { extensionality loc0. rewrite loc_fun_add_spec.
        unfold boolmap_plus, orb. des_ifs.
      }
    }
    { inv WRITE. clarify. econs; eauto.
      { eapply sim_tview_mon_locs.
        { eapply sim_src_na_write_tview; eauto. }
        { unfold boolmap_plus, orb. i. des_ifs. }
      }
      { i. des_ifs.
        { rewrite VIEWRLX. rewrite VIEWPLN. auto. }
        { ss. rr. unfold TimeMap.join. f_equal. eapply FLAGSRC; auto. }
      }
    }
    { ii. specialize (MAXSRC loc0). inv MAXSRC. des_ifs.
      { econs; ss. i. clarify. rewrite VIEWPLN. eauto. }
      { eapply promises_fulfill_unchanged_loc in FULFULL; eauto. des.
        econs; ss.
        { i. hexploit MAX2; eauto. i. des.
          rewrite OTHERPLN; auto. esplits.
          erewrite unchanged_loc_max_readable; eauto.
          { symmetry. econs.
            { eapply add_unchanged_loc; eauto. }
            { auto. }
          }
          { symmetry. auto. }
        }
        { i. hexploit NONMAX0; eauto. i.
          rewrite OTHERPLN; auto.
          erewrite unchanged_loc_max_readable; eauto.
          { symmetry. econs.
            { eapply add_unchanged_loc; eauto. }
            { auto. }
          }
          { symmetry. auto. }
        }
      }
    }
    { i. specialize (PERM loc0). des_ifs. rewrite VAL in PERM. destruct (vs_tgt loc); ss. }
    { rr in FIN. des. exists (loc::dom). ii. split; i; ss.
      { des_ifs; auto. right. eapply DOM; eauto. }
      { des_ifs; auto. des; clarify. eapply DOM; eauto. }
    }
    { i. inv WRITE; clarify.
      hexploit max_memory_val_add_src; eauto.
      { eapply Time.join_r. }
      i. des. des_ifs.
      { rewrite VIEWRLX. auto. }
      { ss. unfold TimeMap.join. rewrite timemap_singleton_neq; auto.
        rewrite TimeFacts.le_join_l; [|apply Time.bot_spec].
        eapply MAXNEQ; eauto.
        hexploit FLAGMAX; eauto. rewrite SRCTM. auto.
      }
    }
    { i. des_ifs. auto. }
  }
  { ss. eapply space_future_memory_mon_msgs.
    { eapply add_src_sim_memory_space_future_aux; eauto. }
    { eapply unchangable_messages_of_memory. }
  }
  { econs. i. splits.
    { refl. }
    { rr. splits; ss.
      { eapply add_other_owned_future; eauto. ii. subst.
        specialize (MAXSRC loc). inv MAXSRC. hexploit MAX; eauto. i. des.
        inv MAX0. ss. unfold BoolMap.minus, andb, negb in OWN.
        destruct (gprm_src loc), (prom loc); ss.
      }
      { eapply UNCH; eauto. }
    }
    { rr. splits; ss. }
  }
  Unshelve. all: ss.
Qed.

Lemma sim_thread_acquire
      f flag_src flag_tgt vs_src0 vs_tgt0
      mem_src mem_tgt prom_src prom_tgt tvw_src0 tvw_tgt0
      tvw_src1 tvw_tgt1 rsv_src rsv_tgt
      (SIM: sim_thread
              f flag_src flag_tgt vs_src0 vs_tgt0
              mem_src mem_tgt (Local.mk tvw_src0 prom_src rsv_src) (Local.mk tvw_tgt0 prom_tgt rsv_tgt))
      (TVIEW: sim_tview f flag_src tvw_src1 tvw_tgt1)
      (LOCALSRC0: Local.wf (Local.mk tvw_src0 prom_src rsv_src) mem_src)
      (LOCALSRC1: Local.wf (Local.mk tvw_src1 prom_src rsv_src) mem_src)
      (LOCALTGT0: Local.wf (Local.mk tvw_tgt0 prom_tgt rsv_tgt) mem_tgt)
      (LOCALTGT1: Local.wf (Local.mk tvw_tgt1 prom_tgt rsv_tgt) mem_tgt)
      (MEMSRC: Global.wf mem_src)
      (WF: Mapping.wfs f)
      (LESRC: TView.le tvw_src0 tvw_src1)
      (LETGT: TView.le tvw_tgt0 tvw_tgt1)
      (FLAGS: forall loc
                     (SRC: flag_src loc = false)
                     (TGT: flag_tgt loc = true),
          (<<PLN: tvw_src1.(TView.cur).(View.pln) loc = tvw_src0.(TView.cur).(View.pln) loc>>) /\
          (<<RLX: tvw_src1.(TView.cur).(View.rlx) loc = tvw_src0.(TView.cur).(View.rlx) loc>>))
  :
    exists vs_src1 vs_tgt1,
      (<<SIM: sim_thread
                f flag_src flag_tgt vs_src1 vs_tgt1
                mem_src mem_tgt (Local.mk tvw_src1 prom_src rsv_src) (Local.mk tvw_tgt1 prom_tgt rsv_tgt)>>) /\
      (<<VALS: forall loc,
          ((<<SRC: vs_src1 loc = vs_src0 loc>>) /\ (<<TGT: vs_tgt1 loc = vs_tgt0 loc>>)) \/
          (exists val_src val_tgt,
              (<<FLAGSRC: flag_src loc = false>>) /\
                (<<FLAGTGT: flag_tgt loc = false>>) /\
                (<<NONESRC: vs_src0 loc = None>>) /\ (<<NONETGT: vs_tgt0 loc = None>>) /\
                (<<VALSRC: vs_src1 loc = Some val_src>>) /\ (<<VALTGT: vs_tgt1 loc = Some val_tgt>>) /\
                (<<VALLE: Const.le val_tgt val_src>>) /\
                (<<TS: Time.lt (tvw_src0.(TView.cur).(View.pln) loc) (tvw_src1.(TView.cur).(View.pln) loc)>>) /\
                (<<VALSRC: __guard__(exists from released na, Memory.get loc (tvw_src1.(TView.cur).(View.pln) loc) mem_src.(Global.memory) = Some (from, Message.message val_src released na))>>) /\
                (<<VALTGT: __guard__(exists from released na, Memory.get loc (tvw_tgt1.(TView.cur).(View.pln) loc) mem_tgt.(Global.memory) = Some (from, Message.message val_tgt released na))>>))>>)
.
Proof.
  assert (VIEWEQ: forall loc
                         (SRC: flag_src loc = true),
             (<<PLN: tvw_src1.(TView.cur).(View.pln) loc = tvw_src0.(TView.cur).(View.pln) loc>>) /\
             (<<RLX: tvw_src1.(TView.cur).(View.rlx) loc = tvw_src0.(TView.cur).(View.rlx) loc>>)).
  { inv SIM. inv LOCAL. i. hexploit FLAGSRC; eauto. i. des.
    destruct (vs_src0 loc) eqn:VAL.
    2:{ hexploit FLAGNONE; eauto. i. des; clarify. }
    hexploit FLAGMAX; eauto. i. rr in H0. des.
    inv LOCALSRC1. inv TVIEW_CLOSED. inv CUR. ss. splits.
    { eapply TimeFacts.antisym.
      { hexploit (PLN loc). i. des.
        eapply Memory.max_ts_spec in H0. des.
        rewrite MAXSRC0 in MAX. rewrite SRCTM in MAX. auto. rewrite H in MAX. auto.
      }
      { eapply LESRC. }
    }
    { eapply TimeFacts.antisym.
      { hexploit (RLX loc). i. des.
        eapply Memory.max_ts_spec in H0. des.
        rewrite MAXSRC0 in MAX. rewrite SRCTM in MAX. auto.
      }
      { eapply LESRC. }
    }
  }
  assert (SIMLOCAL: sim_local f flag_src flag_tgt tvw_src1.(TView.cur).(View.rlx) (Local.mk tvw_src1 prom_src rsv_src) (Local.mk tvw_tgt1 prom_tgt rsv_tgt)).
  { inv SIM. inv LOCAL. econs; eauto.
    { i. hexploit VIEWEQ; eauto. i. des.
      rewrite PLN. rewrite RLX. eapply FLAGSRC; eauto.
    }
  }
  hexploit (@max_values_src_exists mem_src (Local.mk tvw_src1 prom_src rsv_src)).
  i. des. rename vs into vs_src1.
  assert (VALSRC: forall loc,
             (<<SRC: vs_src1 loc = vs_src0 loc>>) \/
             (exists val,
                 (<<FLAGSRC: flag_src loc = false>>) /\
                 (<<NONESRC: vs_src0 loc = None>>) /\
                 (<<VALSRC: vs_src1 loc = Some val>>) /\
                 (<<TS: Time.lt (tvw_src0.(TView.cur).(View.pln) loc) (tvw_src1.(TView.cur).(View.pln) loc)>>) /\
                 (<<VALSRC: __guard__(exists from released na, Memory.get loc (tvw_src1.(TView.cur).(View.pln) loc) mem_src.(Global.memory) = Some (from, Message.message val released na))>>))).
  { inv SIM. i. destruct (vs_src0 loc) eqn:VAL0.
    { left. eapply max_value_src_inj; eauto.
      eapply max_value_src_mon.
      { rewrite <- VAL0. eapply MAXSRC. }
      { eauto. }
      { eauto. }
      { eauto. }
    }
    destruct (vs_src1 loc) eqn:VAL1; auto. right.
    esplits; eauto.
    { eapply FLAGNONE; eauto. }
    { assert (TS: Time.le (View.pln (TView.cur tvw_src0) loc) (View.pln (TView.cur tvw_src1) loc)).
      { eapply LESRC. }
      inv TS; auto. exfalso.
      specialize (MAXSRC loc). specialize (MAX loc).
      rewrite VAL0 in MAXSRC. rewrite VAL1 in MAX.
      inv MAX. inv MAXSRC. hexploit MAX0; eauto. i. des.
      eapply NONMAX0; eauto. rewrite H. eauto.
    }
    { specialize (MAX loc). rewrite VAL1 in MAX.
      inv MAX. hexploit MAX0; eauto. i. des. inv MAX.
      red. esplits; eauto.
    }
  }
  assert (MEM: sim_global flag_src flag_tgt (BoolMap.minus (Global.promises mem_src) prom_src) f mem_src mem_tgt).
  { inv SIM. auto. }
  hexploit (choice (fun loc v =>
                      (<<MAXTGT: max_value_tgt loc v mem_tgt (Local.mk tvw_tgt1 prom_tgt rsv_tgt)>>) /\
                      (((<<SRC: vs_src1 loc = vs_src0 loc>>) /\ (<<TGT: v = vs_tgt0 loc>>)) \/
                         (exists val_src val_tgt,
                             (<<FLAGSRC: flag_src loc = false>>) /\
                               (<<FLAGTGT: flag_tgt loc = false>>) /\
                               (<<NONESRC: vs_src0 loc = None>>) /\ (<<NONETGT: vs_tgt0 loc = None>>) /\
                               (<<VALSRC: vs_src1 loc = Some val_src>>) /\ (<<VALTGT: v = Some val_tgt>>) /\
                               (<<VALLE: Const.le val_tgt val_src>>) /\
                               (<<TS: Time.lt (tvw_src0.(TView.cur).(View.pln) loc) (tvw_src1.(TView.cur).(View.pln) loc)>>) /\
                               (<<VALRC: __guard__(exists from released na, Memory.get loc (tvw_src1.(TView.cur).(View.pln) loc) mem_src.(Global.memory) = Some (from, Message.message val_src released na))>>) /\
                               (<<VALTGT: __guard__(exists from released na, Memory.get loc (tvw_tgt1.(TView.cur).(View.pln) loc) mem_tgt.(Global.memory) = Some (from, Message.message val_tgt released na))>>))))).
  { intros loc. hexploit (VALSRC loc). i. des.
    { exists (vs_tgt0 loc). esplits; auto.
      { inv SIM. eapply max_value_tgt_mon; eauto. }
    }
    { assert (FLAG: flag_tgt loc = false).
      { destruct (flag_tgt loc) eqn:FLAG; auto.
        hexploit FLAGS; eauto. i. des. rewrite PLN in TS. timetac.
      }
      hexploit no_flag_max_value_same; eauto.
      { eauto. }
      { specialize (MAX loc). rewrite VALSRC0 in MAX. eauto. }
      i. des. exists (Some v_tgt). esplits; auto.
      right. esplits; eauto.
      { inv SIM. specialize (PERM loc).
        rewrite NONESRC in PERM. ss. des_ifs.
      }
      { inv MAX0. hexploit MAX1; eauto. i. des.
        inv MAX0. red. esplits; eauto.
      }
    }
  }
  clear VALSRC. intros [vs_tgt1 MAXTGT].
  exists vs_src1, vs_tgt1. splits; auto.
  { inv SIM. econs.
    { auto. }
    { eauto. }
    { eauto. }
    { ii. hexploit (MAXTGT loc). i. des; auto. }
    { i. hexploit (MAXTGT loc). i. des.
      { rewrite SRC. rewrite TGT. auto. }
      { rewrite VALSRC. rewrite VALTGT. ss. }
    }
    { auto. }
    { i. hexploit (MAXTGT loc). i. des; clarify.
      hexploit VIEWEQ; eauto. i. des. rewrite RLX.
      hexploit FLAGMAX; eauto.
      { rewrite <- SRC; eauto. }
      inv LOCAL. rewrite SRCTM. auto.
    }
    { i. hexploit (MAXTGT loc). i. des; auto.
      { rewrite SRC in VAL. eauto. }
    }
  }
  { i. hexploit (MAXTGT loc). i. des; eauto.
    right. esplits; eauto.
  }
Qed.

Lemma write_fence_tview_na tvw sc
  :
    TView.write_fence_tview tvw sc Ordering.na = tvw.
Proof.
  unfold TView.write_fence_tview. des_ifs.
  rewrite View.join_bot_r.
  destruct tvw; ss.
Qed.

Lemma write_fence_sc_na tvw sc
  :
    TView.write_fence_sc tvw sc Ordering.na = sc.
Proof.
  unfold TView.write_fence_sc. des_ifs.
Qed.

Lemma read_fence_tview_na tvw
  :
    TView.read_fence_tview tvw Ordering.na = tvw.
Proof.
  unfold TView.read_fence_tview. des_ifs.
  destruct tvw; ss.
Qed.

Lemma fence_step_merge
      lc0 sc0 ordr ordw lc1 sc1 lc2 sc2
      (STEP0: Local.fence_step lc0 sc0 ordr Ordering.na lc1 sc1)
      (STEP1: Local.fence_step lc1 sc1 Ordering.na ordw lc2 sc2)
  :
    Local.fence_step lc0 sc0 ordr ordw lc2 sc2.
Proof.
  inv STEP0. inv STEP1. ss. econs; eauto. f_equal.
  rewrite write_fence_tview_na. rewrite write_fence_sc_na.
  rewrite read_fence_tview_na. auto.
Qed.

Lemma fence_step_split
      lc0 sc0 ordr ordw lc2 sc2
      (STEP: Local.fence_step lc0 sc0 ordr ordw lc2 sc2)
  :
    exists lc1 sc1,
      (<<STEP0: Local.fence_step lc0 sc0 ordr Ordering.na lc1 sc1>>) /\
      (<<STEP1: Local.fence_step lc1 sc1 Ordering.na ordw lc2 sc2>>).
Proof.
  inv STEP. esplits.
  { econs; ss. }
  { econs; eauto. ss. f_equal.
    rewrite write_fence_tview_na. rewrite write_fence_sc_na.
    rewrite read_fence_tview_na. auto.
  }
Qed.

Definition local_read_fence_tview (tview1: TView.t) (sc1: TimeMap.t)
           (ordr ordw: Ordering.t): TView.t :=
  let tview2 := TView.read_fence_tview tview1 ordr in
  let sc2 := TView.write_fence_sc tview2 sc1 ordw in
  let cur2 :=
      if Ordering.le Ordering.seqcst ordw
      then View.mk sc2 sc2
      else TView.cur tview2 in
  let acq2 :=
      View.join
        (TView.acq tview2)
        (if Ordering.le Ordering.seqcst ordw
         then (View.mk sc2 sc2)
         else View.bot) in
  TView.mk
    (tview1.(TView.rel))
    cur2
    acq2.

Lemma local_read_fence_tview_wf tview sc ordr ordw
      (WF: TView.wf tview)
  :
    TView.wf (local_read_fence_tview tview sc ordr ordw).
Proof.
  econs; ss; des_ifs; ss; try by (eapply WF).
  { econs; ss. refl. }
  { econs; ss. eapply timemap_join_mon; [|refl]. eapply WF. }
  { rewrite View.join_bot_r. apply WF. }
  { i. unfold TView.write_fence_sc. des_ifs. econs; ss.
    { des_ifs.
      { etrans; [|eapply TimeMap.join_r].
        transitivity (View.pln (TView.cur tview)); [apply WF|].
        transitivity (View.rlx (TView.cur tview)); [apply WF|].
        apply WF.
      }
      { etrans; [|eapply TimeMap.join_r].
        transitivity (View.pln (TView.cur tview)); [apply WF|].
        apply WF.
      }
    }
    { des_ifs.
      { etrans; [|eapply TimeMap.join_r].
        transitivity (View.rlx (TView.cur tview)); [apply WF|].
        apply WF.
      }
      { etrans; [|eapply TimeMap.join_r]. apply WF. }
    }
  }
  { i. transitivity (TView.cur tview); apply WF. }
  { eapply View.join_r. }
  { apply View.join_l. }
  { rewrite View.join_bot_r. apply WF. }
Qed.

Lemma local_read_fence_tview_closed mem tview sc ordr ordw
      (TVIEW: TView.closed tview mem)
      (SC: Memory.closed_timemap sc mem)
  :
    TView.closed (local_read_fence_tview tview sc ordr ordw) mem.
Proof.
  unfold local_read_fence_tview, TView.write_fence_sc. econs; ss.
  { eapply TVIEW. }
  { des_ifs.
    { econs; ss.
      { eapply Memory.join_closed_timemap; eauto. eapply TVIEW. }
      { eapply Memory.join_closed_timemap; eauto. eapply TVIEW. }
    }
    { econs; ss.
      { eapply Memory.join_closed_timemap; eauto. eapply TVIEW. }
      { eapply Memory.join_closed_timemap; eauto. eapply TVIEW. }
    }
    { eapply TVIEW. }
    { eapply TVIEW. }
  }
  { des_ifs.
    { eapply Memory.join_closed_view.
      { eapply TVIEW. }
      econs; ss.
      { eapply Memory.join_closed_timemap; eauto. eapply TVIEW. }
      { eapply Memory.join_closed_timemap; eauto. eapply TVIEW. }
    }
    { eapply Memory.join_closed_view.
      { eapply TVIEW. }
      econs; ss.
      { eapply Memory.join_closed_timemap; eauto. eapply TVIEW. }
      { eapply Memory.join_closed_timemap; eauto. eapply TVIEW. }
    }
    { rewrite View.join_bot_r. apply TVIEW. }
  }
Qed.

Lemma local_read_fence_tview_incr tview sc ordr ordw
      (WF: TView.wf tview)
  :
    TView.le tview (local_read_fence_tview tview sc ordr ordw).
Proof.
  econs; ss.
  { i. refl. }
  { unfold TView.write_fence_sc. ss. des_ifs.
    { econs; ss.
      { etrans; [|eapply TimeMap.join_r].
        transitivity (View.rlx (TView.cur tview)); apply WF.
      }
      { etrans; [|eapply TimeMap.join_r]. apply WF.
      }
    }
    { econs; ss.
      { etrans; [|eapply TimeMap.join_r]. apply WF. }
      { eapply TimeMap.join_r. }
    }
    { apply WF. }
    { refl. }
  }
  { eapply View.join_l. }
Qed.

Definition local_write_fence_tview (tview1: TView.t) (ord: Ordering.t): TView.t :=
  TView.mk
    (fun loc =>
       if Ordering.le Ordering.acqrel ord
       then (TView.cur tview1) else (TView.rel tview1 loc))
    (TView.cur tview1)
    (TView.acq tview1)
.

Lemma local_write_fence_tview_wf tview ord
      (WF: TView.wf tview)
  :
    TView.wf (local_write_fence_tview tview ord).
Proof.
  econs; ss; des_ifs; ss; try by (eapply WF).
  { i. eapply WF. }
  { i. refl. }
Qed.

Lemma local_write_fence_tview_closed mem tview ord
      (TVIEW: TView.closed tview mem)
  :
    TView.closed (local_write_fence_tview tview ord) mem.
Proof.
  econs; ss.
  { i. des_ifs.
    { eapply TVIEW. }
    { eapply TVIEW. }
  }
  { eapply TVIEW. }
  { eapply TVIEW. }
Qed.

Lemma local_write_fence_tview_incr tview ord
      (WF: TView.wf tview)
  :
    TView.le tview (local_write_fence_tview tview ord).
Proof.
  econs; ss.
  { i. des_ifs.
    { eapply WF. }
    { refl. }
  }
  { refl. }
  { refl. }
Qed.

Definition local_write_fence_sc (tview1: TView.t) (sc: TimeMap.t) (ord: Ordering.t): TimeMap.t :=
  if Ordering.le Ordering.seqcst ord
  then (TimeMap.join sc (View.rlx (TView.cur tview1)))
  else sc
.

Lemma local_write_fence_sc_closed mem tview sc ord
      (TVIEW: TView.closed tview mem)
      (SC: Memory.closed_timemap sc mem)
  :
    Memory.closed_timemap (local_write_fence_sc tview sc ord) mem.
Proof.
  unfold local_write_fence_sc. des_ifs.
  eapply Memory.join_closed_timemap; auto. eapply TVIEW.
Qed.

Lemma local_write_fence_sc_incr tview sc ord
  :
    TimeMap.le sc (local_write_fence_sc tview sc ord).
Proof.
  unfold local_write_fence_sc. des_ifs.
  { eapply TimeMap.join_l. }
  { refl. }
Qed.

Lemma timemap_bot_join_l tm
  :
    TimeMap.join TimeMap.bot tm = tm.
Proof.
  eapply TimeMap.le_join_r. eapply TimeMap.bot_spec.
Qed.

Lemma timemap_bot_join_r tm
  :
    TimeMap.join tm TimeMap.bot = tm.
Proof.
  eapply TimeMap.le_join_l. eapply TimeMap.bot_spec.
Qed.

Lemma read_tview_incr_rlx
      tvw loc ts vw ord
      (WF: time_le_opt_view loc ts vw)
      (READABLE: Time.le (View.pln (TView.cur tvw) loc) ts)
      (ORD: Ordering.le Ordering.relaxed ord)
  :
    View.pln (TView.cur (TView.read_tview tvw loc ts vw ord)) loc = ts.
Proof.
  unfold TView.read_tview, View.singleton_ur_if in *. ss. des_ifs; ss.
  { unfold TimeMap.join. rewrite timemap_singleton_eq.
    rewrite TimeFacts.le_join_l.
    { apply TimeFacts.le_join_r. auto. }
    { inv WF; ss.
      { inv EXACT. unfold time_le_timemap in *. etrans; eauto.
        eapply Time.join_r.
      }
      { eapply Time.bot_spec. }
    }
  }
  { rewrite ! timemap_bot_join_r.
    unfold TimeMap.join. rewrite timemap_singleton_eq.
    eapply TimeFacts.le_join_r. auto.
  }
Qed.

Lemma read_tview_pln
      tvw loc ts vw ord
      (READABLE: Time.le (View.pln (TView.cur tvw) loc) ts)
      (ORD: ~ Ordering.le Ordering.relaxed ord)
  :
  View.pln (TView.cur (TView.read_tview tvw loc ts vw ord)) loc = View.pln (TView.cur tvw) loc.
Proof.
  unfold TView.read_tview, View.singleton_ur_if. ss. des_ifs; ss.
  { destruct ord; ss. }
  rewrite ! timemap_bot_join_r. auto.
Qed.

Variant local_fence_read_step lc1 gl1 ordr ordw lc2: Prop :=
| local_fence_read_step_intro
    (LOCAL: lc2 = Local.mk
                    (local_read_fence_tview lc1.(Local.tview) gl1.(Global.sc) ordr ordw)
                    (lc1.(Local.promises)) (lc1.(Local.reserves)))
    (PROMISES: Ordering.le Ordering.seqcst ordw -> lc1.(Local.promises) = BoolMap.bot)
.

Lemma local_fence_read_step_future mem lc1 ordr ordw lc2
      (STEP: local_fence_read_step lc1 mem ordr ordw lc2)
      (LOCAL: Local.wf lc1 mem)
      (SC: Global.wf mem)
  :
    (<<LOCAL: Local.wf lc2 mem>>) /\
    (<<INCR: TView.le lc1.(Local.tview) lc2.(Local.tview)>>).
Proof.
  inv STEP. splits.
  { inv LOCAL. econs; ss.
    { eapply local_read_fence_tview_wf; eauto. }
    { eapply local_read_fence_tview_closed; eauto. eapply SC. }
  }
  { eapply local_read_fence_tview_incr; eauto. eapply LOCAL. }
Qed.

Variant local_fence_write_step lc1 gl1 ord lc2 gl2: Prop :=
| local_fence_write_step_intro
    (LOCAL: lc2 = Local.mk
                    (local_write_fence_tview lc1.(Local.tview) ord)
                    (lc1.(Local.promises)) (lc1.(Local.reserves)))
    (SC: gl2 = Global.mk (local_write_fence_sc lc1.(Local.tview) gl1.(Global.sc) ord) gl1.(Global.promises) gl1.(Global.memory))
.

Lemma local_fence_write_step_future gl1 lc1 ord lc2 gl2
      (STEP: local_fence_write_step lc1 gl1 ord lc2 gl2)
      (LOCAL: Local.wf lc1 gl1)
      (SC: Global.wf gl1)
  :
    (<<LOCAL: Local.wf lc2 gl2>>) /\
    (<<SC: Global.wf gl2>>) /\
    (<<INCR: TView.le lc1.(Local.tview) lc2.(Local.tview)>>).
Proof.
  inv STEP. splits.
  { inv LOCAL. econs; ss.
    { eapply local_write_fence_tview_wf; eauto. }
    { eapply local_write_fence_tview_closed; eauto. }
  }
  { inv SC. econs; eauto. eapply local_write_fence_sc_closed; eauto. eapply LOCAL. }
  { eapply local_write_fence_tview_incr; eauto. eapply LOCAL. }
Qed.

Lemma local_fence_tview_merge
      tvw sc ordr ordw
      (WF: TView.wf tvw)
  :
    local_write_fence_tview (local_read_fence_tview tvw sc ordr ordw) ordw
    =
    TView.write_fence_tview (TView.read_fence_tview tvw ordr) sc ordw.
Proof.
  ss.
Qed.

Lemma local_fence_sc_merge
      tvw sc ordr ordw
      (WF: TView.wf tvw)
  :
    local_write_fence_sc (local_read_fence_tview tvw sc ordr ordw) sc ordw =
    TView.write_fence_sc (TView.read_fence_tview tvw ordr) sc ordw.
Proof.
  assert (IDEM: forall tm, TimeMap.join tm tm = tm).
  { i. apply TimeMap.le_join_l. refl. }
  Local Transparent Ordering.le.
  unfold local_write_fence_sc, local_read_fence_tview, TView.read_fence_tview, TView.write_fence_tview, TView.write_fence_sc.
  destruct ordr eqn:ORDR, ordw eqn:ORDW; ss.
  { rewrite <- TimeMap.join_assoc. f_equal. auto. }
  { rewrite <- TimeMap.join_assoc. f_equal. auto. }
  { rewrite <- TimeMap.join_assoc. f_equal. auto. }
  { rewrite <- TimeMap.join_assoc. f_equal. auto. }
  { rewrite <- TimeMap.join_assoc. f_equal. auto. }
  { rewrite <- TimeMap.join_assoc. f_equal. auto. }
  Local Opaque Ordering.le.
Qed.

Lemma local_fence_step_merge
      lc0 sc0 ordr lc1 ordw lc2 sc1
      (STEP0: local_fence_read_step lc0 sc0 ordr ordw lc1)
      (STEP1: local_fence_write_step lc1 sc0 ordw lc2 sc1)
      (WF: TView.wf lc0.(Local.tview))
  :
    Local.fence_step lc0 sc0 ordr ordw lc2 sc1.
Proof.
  inv STEP0. inv STEP1. ss. econs; ss.
  { rewrite local_fence_sc_merge; eauto. }
Qed.

Lemma local_fence_step_split
      lc0 sc0 ordr ordw lc2 sc1
      (STEP: Local.fence_step lc0 sc0 ordr ordw lc2 sc1)
      (WF: TView.wf lc0.(Local.tview))
  :
    exists lc1,
      (<<STEP0: local_fence_read_step lc0 sc0 ordr ordw lc1>>) /\
      (<<STEP1: local_fence_write_step lc1 sc0 ordw lc2 sc1>>).
Proof.
  inv STEP. esplits.
  { econs; eauto. }
  { econs; ss. rewrite local_fence_sc_merge; auto. }
Qed.

Lemma sim_local_read_fence_tview f flag_src tvw_src tvw_tgt sc_src sc_tgt
      ordr ordw
      (SIM: sim_tview f flag_src tvw_src tvw_tgt)
      (SC: sim_timemap (fun loc => flag_src loc = false) f (Mapping.vers f) sc_src sc_tgt)
      (WF: Mapping.wfs f)
  :
    sim_tview f flag_src (local_read_fence_tview tvw_src sc_src ordr ordw) (local_read_fence_tview tvw_tgt sc_tgt ordr ordw).
Proof.
  pose proof (mapping_latest_wf f).
  assert (READ: sim_tview f flag_src (TView.read_fence_tview tvw_src ordr) (TView.read_fence_tview tvw_tgt ordr)).
  { eapply sim_read_fence_tview; eauto. }
  assert (WRITE: sim_timemap (fun loc => flag_src loc = false) f (Mapping.vers f) (TView.write_fence_sc (TView.read_fence_tview tvw_src ordr) sc_src ordw) (TView.write_fence_sc (TView.read_fence_tview tvw_tgt ordr) sc_tgt ordw)).
  { eapply sim_write_fence_sc; eauto. }
  econs; ss.
  { eapply SIM. }
  { des_ifs.
    { eapply SIM. }
    { eapply SIM. }
  }
  { eapply sim_view_join; eauto.
    { eapply SIM. }
    { des_ifs. eapply sim_view_bot; eauto. }
  }
Qed.

Lemma sim_local_write_fence_tview_normal f flag_src tvw_src tvw_tgt
      ord
      (SIM: sim_tview f flag_src tvw_src tvw_tgt)
      (ORD: ~ Ordering.le Ordering.acqrel ord)
      (WF: Mapping.wfs f)
  :
    sim_tview f flag_src (local_write_fence_tview tvw_src ord) (local_write_fence_tview tvw_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  econs; ss.
  { i. des_ifs. eapply SIM. }
  { eapply SIM. }
  { eapply SIM. }
Qed.

Lemma sim_local_write_fence_tview_release f flag_src tvw_src tvw_tgt
      ord
      (SIM: sim_tview f flag_src tvw_src tvw_tgt)
      (FLAG: forall loc, flag_src loc = false)
      (WF: Mapping.wfs f)
  :
    sim_tview f flag_src (local_write_fence_tview tvw_src ord) (local_write_fence_tview tvw_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  econs; ss.
  { i. des_ifs.
    { eapply sim_view_mon_locs.
      { eapply SIM. }
      { i. ss. }
    }
    { eapply sim_view_mon_ver; auto.
      { eapply SIM. }
      { refl. }
    }
  }
  { eapply SIM. }
  { eapply SIM. }
Qed.

Lemma sim_local_write_fence_sc f flag_src tvw_src tvw_tgt sc_src sc_tgt
      ord
      (SIM: sim_tview f flag_src tvw_src tvw_tgt)
      (SC: sim_timemap (fun _ => True) f (Mapping.vers f) sc_src sc_tgt)
      (FLAG: Ordering.le Ordering.seqcst ord -> forall loc, flag_src loc = false)
      (WF: Mapping.wfs f)
  :
    sim_timemap (fun _ => True) f (Mapping.vers f) (local_write_fence_sc tvw_src sc_src ord) (local_write_fence_sc tvw_tgt sc_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  unfold local_write_fence_sc. des_ifs. eapply sim_timemap_join; auto.
  eapply sim_timemap_mon_locs.
  { eapply SIM. }
  { i. eapply FLAG. auto. }
Qed.

Lemma sim_thread_read
      f flag_src flag_tgt vs_src0 vs_tgt0
      mem_src mem_tgt lc_src0 lc_tgt0
      lc_tgt1 loc to_tgt val_tgt0 released_tgt ord
      (SIM: sim_thread
              f flag_src flag_tgt vs_src0 vs_tgt0
              mem_src mem_tgt lc_src0 lc_tgt0)
      (READ: Local.read_step lc_tgt0 mem_tgt loc to_tgt val_tgt0 released_tgt ord lc_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt)
      (MEMSRC: Global.wf mem_src)
      (MEMTGT: Global.wf mem_tgt)
      (WF: Mapping.wfs f)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
      (FLAG: forall loc
                    (SRC: flag_src loc = false) (TGT: flag_tgt loc = true),
          ~ Ordering.le Ordering.acqrel ord)
      (NORACE: forall to, ~ Local.is_racy lc_src0 mem_src loc to ord)
  :
    exists val_tgt1 val_src1 to_src released_src lc_src1 vs_src1 vs_tgt1,
      (<<READ: forall val (VAL: Const.le val val_src1), Local.read_step lc_src0 mem_src loc to_src val released_src ord lc_src1>>) /\
      (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt)>>) /\
      (<<RELEASED: sim_opt_view (fun loc0 => loc0 <> loc) f (Some (Mapping.vers f)) released_src released_tgt>>) /\
      (<<SIM: sim_thread
                f flag_src flag_tgt vs_src1 vs_tgt1
                mem_src mem_tgt lc_src1 lc_tgt1>>) /\
      (<<VAL: Const.le val_tgt1 val_src1>>) /\
      (<<VALTGT: Const.le val_tgt0 val_tgt1>>) /\
      (<<NUPDATESRC: forall val (VAL: vs_src0 loc = Some val), val = val_src1>>) /\
      (<<NUPDATETGT: forall val (VAL: vs_tgt0 loc = Some val), val = val_tgt1>>) /\
      (<<VALS: forall loc0,
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>)) \/
          (exists val_src val_tgt,
              (<<NONESRC: vs_src0 loc0 = None>>) /\ (<<NONETGT: vs_tgt0 loc0 = None>>) /\
              (<<VALSRC: vs_src1 loc0 = Some val_src>>) /\ (<<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) /\
              (<<VALLE: Const.le val_tgt val_src>>) /\
              (((<<LOC: loc0 <> loc>>) /\ (<<ORD: Ordering.le Ordering.acqrel ord>>)) \/
               ((<<LOC: loc0 = loc>>) /\ (<<SRC: val_src = val_src1>>) /\ (<<TGT: val_tgt = val_tgt1>>))))>>).
Proof.
  hexploit Local.read_step_future; eauto. i. des.
  destruct lc_src0 as [tvw_src0 prom_src].
  destruct lc_tgt0 as [tvw_tgt0 prom_tgt].
  dup SIM. inv SIM. inv MEM. inv LOCAL. inv READ.
  hexploit sim_memory_get; eauto; ss.
  { unfold boolmap_plus. rewrite FLAGSRC. rewrite FLAGTGT. auto. }
  { unfold BoolMap.minus, andb, negb. des_ifs.
    exfalso. eapply NORACE. econs 1; eauto.
  }
  i. des; cycle 1.
  { exfalso. eapply NORACE. econs 2; eauto. ss.
    inv TVIEW. hexploit sim_readable; eauto.
    { i. inv H. eapply TimeFacts.le_lt_lt; eauto. }
  }
  inv MSG; ss.
  assert (READSRC: exists tvw_src1, (<<READSRC: forall val (VAL: Const.le val val_src), Local.read_step (Local.mk tvw_src0 prom_src reserves) (Global.mk sc_src gprm_src mem_src0) loc to_src val vw_src ord (Local.mk tvw_src1 prom_src reserves)>>) /\
                                    (<<SIM: sim_tview f flag_src tvw_src1 (TView.read_tview tvw_tgt0 loc to_tgt released_tgt ord)>>)).
  { esplits.
    { i. econs; eauto.
      { ss. inv TVIEW. eapply sim_readable; eauto. }
    }
    { ss. eapply sim_read_tview; eauto.
      { eapply MEMSRC in GET0. des.
        eapply message_to_time_le_opt_view; eauto.
      }
      { eapply MEMTGT in GET. des.
        eapply message_to_time_le_opt_view; eauto.
      }
    }
  }
  des. hexploit READSRC0; [refl|..]. intros READSRC.
  hexploit Local.read_step_future; eauto. i. des. ss.
  hexploit sim_thread_acquire; eauto.
  { i. hexploit FLAG; eauto. i.
    assert (LOC: loc0 <> loc).
    { ii. subst. rewrite FLAGTGT in TGT. ss. }
    inv READSRC. ss. inv LC2. splits.
    { ss. destruct (Ordering.le Ordering.acqrel ord); ss.
      rewrite timemap_bot_join_r.
      unfold TimeMap.join.
      rewrite TimeFacts.le_join_l; auto.
      destruct (Ordering.le Ordering.relaxed ord); ss.
      { rewrite timemap_singleton_neq; auto. eapply Time.bot_spec. }
      { eapply Time.bot_spec. }
    }
    { ss. destruct (Ordering.le Ordering.acqrel ord); ss.
      rewrite timemap_bot_join_r.
      unfold TimeMap.join.
      rewrite TimeFacts.le_join_l; auto.
      destruct (Ordering.le Ordering.relaxed ord); ss.
      { rewrite timemap_singleton_neq; auto. eapply Time.bot_spec. }
      { rewrite timemap_singleton_neq; auto. eapply Time.bot_spec. }
    }
  }
  i. des. esplits; eauto.
  { i. specialize (MAXSRC loc). rewrite VAL1 in MAXSRC. inv MAXSRC.
    hexploit MAX; eauto. i. des.
    hexploit max_readable_read_only_aux; eauto.
    i. des. subst. inv MAX0.
    ss. rewrite GET1 in GET0. inv GET0. auto.
  }
  { i. specialize (MAXTGT loc). rewrite VAL1 in MAXTGT. inv MAXTGT.
    hexploit MAX; eauto. i. des.
    hexploit max_readable_read_only_aux; eauto.
    i. des. subst. inv MAX0.
    ss. rewrite GET1 in GET. inv GET. auto.
  }
  i. hexploit VALS; eauto. i. des.
  { left. eauto. }
  { right. esplits; eauto. destruct (Loc.eq_dec loc0 loc).
    { assert (ORD: Ordering.le Ordering.relaxed ord).
      { inv READSRC. inv LC2.
        eapply NNPP. ii. eapply read_tview_pln in H.
        { rewrite H in TS. timetac. }
        { inv READABLE0. ss. }
      }
      subst. right. splits; auto.
      { red in VALSRC0. des.
        replace (View.pln (TView.cur tvw_src1) loc) with to_src in VALSRC0.
        { ss. rewrite GET0 in VALSRC0. inv VALSRC0. auto. }
        symmetry. inv READSRC. inv LC2.
        ss. eapply read_tview_incr_rlx; eauto.
        { eapply message_to_time_le_opt_view; eauto. }
        { inv READABLE0. ss. }
      }
      { red in VALTGT0. des.
        replace (View.pln (TView.cur (TView.read_tview tvw_tgt0 loc to_tgt released_tgt ord)) loc) with to_tgt in VALTGT0.
        { ss. rewrite GET in VALTGT0. inv VALTGT0. auto. }
        symmetry. eapply read_tview_incr_rlx; eauto.
        { eapply message_to_time_le_opt_view; eauto. }
        { inv READABLE. ss. }
      }
    }
    { left. inv READSRC. inv LC2. ss.
      destruct (Ordering.le Ordering.acqrel ord); auto.
      ss. rewrite timemap_bot_join_r in TS.
      unfold TimeMap.join in TS. rewrite TimeFacts.le_join_l in TS; auto.
      { timetac. }
      { destruct (Ordering.le Ordering.relaxed ord); ss.
        { rewrite timemap_singleton_neq; auto. eapply Time.bot_spec. }
        { apply Time.bot_spec. }
      }
    }
  }
  Unshelve. all: ss.
Qed.

Lemma sim_thread_read_racy
      f flag_src flag_tgt vs_src0 vs_tgt0
      mem_src mem_tgt lc_src0 lc_tgt0
      lc_tgt1 loc to_tgt val_tgt0 released_tgt ord to
      (SIM: sim_thread
              f flag_src flag_tgt vs_src0 vs_tgt0
              mem_src mem_tgt lc_src0 lc_tgt0)
      (READ: Local.read_step lc_tgt0 mem_tgt loc to_tgt val_tgt0 released_tgt ord lc_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt)
      (MEMSRC: Global.wf mem_src)
      (MEMTGT: Global.wf mem_tgt)
      (WF: Mapping.wfs f)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
      (FLAG: forall loc
                    (SRC: flag_src loc = false) (TGT: flag_tgt loc = true),
          ~ Ordering.le Ordering.acqrel ord)
      (RACE: Local.is_racy lc_src0 mem_src loc to ord)
  :
  (<<READ: forall val, Local.racy_read_step lc_src0 mem_src loc to val ord>>) /\
    (<<SIM: sim_thread
              f flag_src flag_tgt vs_src0 vs_tgt0
              mem_src mem_tgt lc_src0 lc_tgt1>>) /\
    (<<VALSRC: vs_src0 loc = None>>) /\
    (<<VALTGT: vs_tgt0 loc = None>>).
Proof.
  hexploit Local.read_step_future; eauto. i. des.
  destruct lc_src0 as [tvw_src0 prom_src].
  destruct lc_tgt0 as [tvw_tgt0 prom_tgt].
  inv SIM. pose proof (PERM loc) as PLOC. unfold option_rel in PLOC. des_ifs.
  { exfalso. specialize (MAXSRC loc). inv MAXSRC.
    hexploit MAX; eauto. i. des.
    eapply race_non_max_readable; eauto.
  }
  inv READ. esplits; eauto. econs; eauto.
  { inv LOCAL. econs; eauto. eapply sim_tview_tgt_mon; eauto. }
  { eapply max_values_tgt_mon; eauto. }
Qed.

Lemma sim_thread_read_fence_step
      f flag_src flag_tgt vs_src0 vs_tgt0
      mem_src mem_tgt lc_src0 lc_tgt0
      lc_tgt1 ordr ordw
      (SIM: sim_thread
              f flag_src flag_tgt vs_src0 vs_tgt0
              mem_src mem_tgt lc_src0 lc_tgt0)
      (READ: local_fence_read_step lc_tgt0 mem_tgt ordr ordw lc_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt)
      (MEMSRC: Global.wf mem_src)
      (MEMTGT: Global.wf mem_tgt)
      (WF: Mapping.wfs f)
      (ACQFLAG: forall loc
                       (SRC: flag_src loc = false) (TGT: flag_tgt loc = true),
          ~ Ordering.le Ordering.acqrel ordr)
      (RELFLAG: forall loc
                       (SRC: flag_src loc = false) (TGT: flag_tgt loc = true),
          ~ Ordering.le Ordering.seqcst ordw)
  :
    exists lc_src1 vs_src1 vs_tgt1,
      (<<READ: local_fence_read_step lc_src0 mem_src ordr ordw lc_src1>>) /\
      (<<SIM: sim_thread
                f flag_src flag_tgt vs_src1 vs_tgt1
                mem_src mem_tgt lc_src1 lc_tgt1>>) /\
      (<<VALS: forall loc0,
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>)) \/
          (exists val_src val_tgt,
              (<<NONESRC: vs_src0 loc0 = None>>) /\ (<<NONETGT: vs_tgt0 loc0 = None>>) /\
              (<<VALSRC: vs_src1 loc0 = Some val_src>>) /\ (<<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) /\
              (<<VALLE: Const.le val_tgt val_src>>) /\
              (<<ORD: Ordering.le Ordering.acqrel ordr \/ Ordering.le Ordering.seqcst ordw>>))>>).
Proof.
  assert (exists lc_src1, (<<READ: local_fence_read_step lc_src0 mem_src ordr ordw lc_src1>>)).
  { inv READ. inv SIM. inv LOCAL. esplits. econs; eauto.
    { i. ss. extensionality loc. inv PROMISES0.
      destruct (flag_src loc) eqn:EQS.
      { rewrite FLAGSRC0; auto. }
      rewrite NOFLAG; auto.
      { rewrite PROMISES; auto. }
      { destruct (flag_tgt loc) eqn:EQT; auto.
        exfalso. eapply RELFLAG; eauto.
      }
    }
  }
  des. hexploit local_fence_read_step_future; [eapply READ|..]; eauto. i. des.
  hexploit local_fence_read_step_future; [eapply READ0|..]; eauto. i. des.
  destruct lc_src0 as [tvw_src0 prom_src].
  destruct lc_tgt0 as [tvw_tgt0 prom_tgt].
  inv READ. inv READ0. ss.
  dup SIM. inv SIM. inv LOCAL1.
  assert (VIEW: sim_tview f flag_src (local_read_fence_tview tvw_src0 mem_src.(Global.sc) ordr ordw) (local_read_fence_tview tvw_tgt0 mem_tgt.(Global.sc) ordr ordw)).
  { eapply sim_local_read_fence_tview; eauto.
    inv MEM. eapply sim_timemap_mon_locs; eauto; ss.
  }
  hexploit sim_thread_acquire; eauto.
  { i. hexploit ACQFLAG; eauto. hexploit RELFLAG; eauto. i. ss. des_ifs; ss. }
  i. des. esplits; eauto.
  { econs; eauto. }
  { i. hexploit (VALS loc0). i. des; eauto.
    right. esplits; eauto. clear - TS.
    unfold local_read_fence_tview, TView.write_fence_sc, TView.read_fence_tview in TS; ss.
    des_ifs; auto. timetac.
  }
Qed.

(* Lemma mapped_msgs_exists_aux f0 f1 vers msgs_tgt prom_tgt loc flag_new *)
(*       mem_src *)
(*       (PROM: exists srctm flag_src flag_tgt prom_src, sim_promises srctm flag_src flag_tgt f0 vers prom_src prom_tgt) *)
(*       (MAPLE: Mapping.le (f0 loc) f1) *)
(*       (MSGS: forall from to msg (IN: List.In (from, to, msg) msgs_tgt), Memory.get loc to prom_tgt = Some (from, msg)) *)
(*       (WF0: Mapping.wfs f0) *)
(*       (WF1: Mapping.wf f1) *)
(*       (VERSWF: versions_wf f0 vers) *)
(*       (BOTNONE: Memory.bot_none prom_tgt) *)
(*       (MSGSWF: wf_cell_msgs msgs_tgt) *)
(*       (SIM: sim_closed_memory f0 mem_src) *)

(*       ts_tgt ts_src *)
(*       (SIMTIME: sim_timestamp_exact f1 f1.(Mapping.ver) ts_src ts_tgt) *)
(*       (MAX: Time.le (Memory.max_ts loc mem_src) ts_src) *)
(*       (RESERVE: forall from_tgt to_tgt msg_tgt from_src to_src *)
(*                        (GET: Memory.get loc to_tgt prom_tgt = Some (from_tgt, msg_tgt)) *)
(*                        (TS: Time.lt from_tgt ts_tgt) *)
(*                        (TO: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) to_src to_tgt) *)
(*                        (FROM: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) from_src from_tgt), *)
(*           (<<RESERVE: msg_tgt = Message.reserve>>) /\ *)
(*           (<<TS: Time.lt to_tgt ts_tgt>>) /\ *)
(*           (<<DISJOINT: forall from to msg (GET: Memory.get loc to mem_src = Some (from, msg)), *)
(*               Interval.disjoint (from_src, to_src) (from, to)>>)) *)
(*       (SAME: forall to_tgt to_src *)
(*                     (TS: Time.lt to_tgt ts_tgt) *)
(*                     (MAP: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) to_src to_tgt), *)
(*           sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt) *)
(*   : *)
(*     exists msgs_src, *)
(*       (<<FORALL: List.Forall2 *)
(*                    (fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) => *)
(*                       (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\ *)
(*                       (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\ *)
(*                       (<<MESSAGE: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>)) *)
(*                    msgs_src msgs_tgt>>) /\ *)
(*       (<<DISJOINT: List.Forall *)
(*                      (fun '(from, to, msg) => (__guard__((<<MAX: Time.le (Memory.max_ts loc mem_src) from>>) \/ (<<RESERVE: msg = Message.reserve>>) /\ (<<DISJOINT: forall to2 from2 msg2 (GET: Memory.get loc to2 mem_src = Some (from2, msg2)), Interval.disjoint (from, to) (from2, to2)>>))) /\ (<<TS: Time.lt from to>>) /\ (<<MSGTO: Memory.message_to msg loc to>>) /\ (<<WF: Message.wf msg>>) /\ (<<CLOSED: semi_closed_message msg mem_src loc to>>)) msgs_src>>) /\ *)
(*       (<<MSGSWF: wf_cell_msgs msgs_src>>) *)
(* . *)
(* Proof. *)
(*   pose proof mapping_latest_wf_loc as VERWF. *)
(*   revert MSGS MSGSWF. induction msgs_tgt; i. *)
(*   { exists []. splits. *)
(*     { econs. } *)
(*     { econs. } *)
(*     { red. splits; econs. } *)
(*   } *)
(*   des. destruct a as [[from_tgt to_tgt] msg_tgt]. *)
(*   hexploit MSGS. *)
(*   { left. eauto. } *)
(*   intros GETTGT. hexploit sim_promises_get; eauto. i. des. *)
(*   hexploit sim_timestamp_exact_mon_exists; [eapply FROM|..]; eauto. i. des. *)
(*   hexploit sim_timestamp_exact_mon_exists; [eapply TO|..]; eauto. i. des. *)
(*   hexploit (@sim_message_max_exists flag_new loc ts_src0 f0 (vers loc to_tgt) msg_tgt); eauto. *)
(*   { i. hexploit VERS; eauto. i. des. esplits; eauto. *)
(*     exploit VERSWF. rewrite VER. ss. *)
(*   } *)
(*   i. des. red in MSGSWF. des. inv DISJOINT. inv MSGSWF0. *)
(*   hexploit IHmsgs_tgt; eauto. *)
(*   { i. eapply MSGS. right. auto. } *)
(*   { red. splits; auto. } *)
(*   i. destruct H1 as [MSGWF TIMEWF]. guardH TIMEWF. *)
(*   des. *)
(*   assert (FROMTO: Time.lt ts_src1 ts_src0). *)
(*   { eapply sim_timestamp_exact_lt; eauto. *)
(*     hexploit memory_get_ts_strong; eauto. i. des; clarify. *)
(*     rewrite BOTNONE in GETTGT. ss. *)
(*   } *)
(*   exists ((ts_src1, ts_src0, msg_src)::msgs_src). splits. *)
(*   { econs; eauto. } *)
(*   { econs; eauto. splits. *)
(*     { destruct (Time.le_lt_dec ts_tgt from_tgt). *)
(*       { left. transitivity ts_src; auto. eapply sim_timestamp_exact_le; eauto. } *)
(*       { right. hexploit RESERVE; eauto. i. des. subst. *)
(*         hexploit (@SAME to_tgt to_src); eauto. i. *)
(*         eapply sim_timestamp_exact_inject in SIM1; eauto. subst. *)
(*         hexploit (@SAME from_tgt from_src); eauto. i. *)
(*         eapply sim_timestamp_exact_inject in SIM0; eauto. subst. *)
(*         splits. *)
(*         { inv MAX0; ss. } *)
(*         { i. eauto. } *)
(*       } *)
(*     } *)
(*     { auto. } *)
(*     { eapply sim_message_max_msg_to; eauto. } *)
(*     { eapply sim_message_max_msg_wf; eauto. } *)
(*     { eapply sim_closed_memory_sim_message; eauto. } *)
(*   } *)
(*   { red in MSGSWF. des. red. splits. *)
(*     { econs; eauto. *)
(*       eapply List.Forall_forall. intros [[from_src0 to_src0] msg_src0] IN. *)
(*       eapply list_Forall2_in2 in IN; eauto. des. *)
(*       destruct b as [[from_tgt0 to_tgt0] msg_tgt0]. des. *)
(*       eapply List.Forall_forall in HD; eauto. ss. *)
(*       eapply sim_timestamp_exact_le; eauto. *)
(*     } *)
(*     { econs; eauto. splits; auto. *)
(*       eapply sim_message_max_msg_wf; eauto. *)
(*     } *)
(*   } *)
(* Qed. *)

(* Lemma messages_times_exists (msgs: list (Time.t * Time.t * Message.t)) (f0: Mapping.t) ts *)
(*       (MAPWF: Mapping.wf f0) *)
(*   : *)
(*     exists (f1: Mapping.t), *)
(*       (<<MAPWF: Mapping.wf f1>>) /\ *)
(*       (<<MAPLE: Mapping.le_strong f0 f1>>) /\ *)
(*       (<<CLOSEDIF: forall to (CLOSED: Mapping.closed f1 f1.(Mapping.ver) to), *)
(*           (<<CLOSED: Mapping.closed f0 f0.(Mapping.ver) to>>) \/ *)
(*           (exists from val released, (<<IN: List.In (from, to, Message.concrete val released) msgs>>)) \/ *)
(*           (<<TS: to = ts>>)>>) /\ *)
(*       (<<CLOSED: List.Forall (fun '(from_src, to_src, msg_src) => *)
(*                                 forall val released (MSG: msg_src = Message.concrete val released), *)
(*                                   Mapping.closed f1 f1.(Mapping.ver) to_src) msgs>>) /\ *)
(*       (<<CLOSEDTS: Mapping.closed f1 f1.(Mapping.ver) ts>>) *)
(* . *)
(* Proof. *)
(*   hexploit (@mapping_update_times f0 (fun to => to = ts \/ exists from val released, List.In (from, to, Message.concrete val released) msgs)). *)
(*   { eauto. } *)
(*   { induction msgs. *)
(*     { exists [ts]. i. des; ss; auto. } *)
(*     { des. destruct a as [[from to] msg]. destruct msg. *)
(*       { exists (to::l). i. ss. des; clarify. *)
(*         { right. eapply IHmsgs. left. auto. } *)
(*         { auto. } *)
(*         { right. eapply IHmsgs. right. eauto. } *)
(*       } *)
(*       { exists l. i. eapply IHmsgs. ss. des; clarify; eauto. } *)
(*       { exists l. i. eapply IHmsgs. ss. des; clarify; eauto. } *)
(*     } *)
(*   } *)
(*   i. des. exists f1. splits; eauto. *)
(*   { i. eapply TIMES in CLOSED. des; auto. *)
(*     right. esplits; eauto. *)
(*   } *)
(*   { eapply List.Forall_forall. intros [[from to] msg] IN. i. subst. *)
(*     eapply TIMES. right. esplits; eauto. *)
(*   } *)
(*   { eapply TIMES. right. left. auto. } *)
(* Qed. *)

(* Lemma mapped_msgs_complete f0 f1 msgs_src msgs_tgt loc vers flag_new *)
(*       (WF1: Mapping.wf f1) *)
(*       (FORALL: List.Forall2 *)
(*                  (fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) => *)
(*                     (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\ *)
(*                     (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\ *)
(*                     (<<MESSAGE: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>)) *)
(*                  msgs_src msgs_tgt) *)
(*       (CLOSED: List.Forall (fun '(from_src, to_src, msg_src) => *)
(*                               forall val released (MSG: msg_src = Message.concrete val released), *)
(*                                 Mapping.closed f1 f1.(Mapping.ver) to_src) msgs_src) *)
(*   : *)
(*     forall to_tgt from_tgt msg_tgt *)
(*            (RESERVE: msg_tgt <> Message.reserve) *)
(*            (GETTGT: List.In (from_tgt, to_tgt, msg_tgt) msgs_tgt), *)
(*     exists to_src from_src msg_src, *)
(*       (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\ *)
(*       (<<MSG: sim_message false loc f0 (vers loc to_tgt) msg_src msg_tgt>>) /\ *)
(*       (<<CLOSED: forall val released (MSG: msg_tgt = Message.concrete val released), Mapping.closed f1 f1.(Mapping.ver) to_src>>) /\ *)
(*       (<<IN: List.In (from_src, to_src, msg_src) msgs_src>>). *)
(* Proof. *)
(*   i. eapply list_Forall2_in in GETTGT; eauto. des. *)
(*   destruct a as [[from_src to_src] msg_src]. des. esplits; eauto. *)
(*   { eapply sim_message_flag_mon. eapply sim_message_max_sim; eauto. } *)
(*   { i. subst. eapply List.Forall_forall in CLOSED; eauto. ss. *)
(*     inv MESSAGE; eauto. *)
(*   } *)
(* Qed. *)

(* Lemma mapped_msgs_sound f0 f1 msgs_src msgs_tgt loc vers flag_new *)
(*       (WF1: Mapping.wf f1) *)
(*       (FORALL: List.Forall2 *)
(*                  (fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) => *)
(*                     (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\ *)
(*                     (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\ *)
(*                     (<<MESSAGE: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>)) *)
(*                  msgs_src msgs_tgt) *)
(*   : *)
(*     forall to_src from_src msg_src *)
(*            (IN: List.In (from_src, to_src, msg_src) msgs_src), *)
(*     exists to_tgt from_tgt msg_tgt, *)
(*       (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\ *)
(*       (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\ *)
(*       (<<GET: List.In (from_tgt, to_tgt, msg_tgt) msgs_tgt>>). *)
(* Proof. *)
(*   i. eapply list_Forall2_in2 in IN; eauto. des. *)
(*   destruct b as [[from_tgt to_tgt] msg_tgt]. des. esplits; eauto. *)
(* Qed. *)

(* Lemma mapped_msgs_complete_promise f0 f1 msgs_src msgs_tgt loc vers flag_new *)
(*       (WF1: Mapping.wf f1) *)
(*       (FORALL: List.Forall2 *)
(*                  (fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) => *)
(*                     (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\ *)
(*                     (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\ *)
(*                     (<<MESSAGE: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>)) *)
(*                  msgs_src msgs_tgt) *)
(*       (CLOSED: List.Forall (fun '(from_src, to_src, msg_src) => *)
(*                               forall val released (MSG: msg_src = Message.concrete val released), *)
(*                                 Mapping.closed f1 f1.(Mapping.ver) to_src) msgs_src) *)
(*   : *)
(*     forall to_tgt from_tgt msg_tgt *)
(*            (GETTGT: List.In (from_tgt, to_tgt, msg_tgt) msgs_tgt), *)
(*     exists to_src from_src msg_src, *)
(*       (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\ *)
(*       (<<MSG: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>) /\ *)
(*       (<<CLOSED: forall val released (MSG: msg_tgt = Message.concrete val released), Mapping.closed f1 f1.(Mapping.ver) to_src>>) /\ *)
(*       (<<IN: List.In (from_src, to_src, msg_src) msgs_src>>). *)
(* Proof. *)
(*   i. eapply list_Forall2_in in GETTGT; eauto. des. *)
(*   destruct a as [[from_src to_src] msg_src]. des. esplits; eauto. *)
(*   eapply List.Forall_forall in CLOSED; eauto. ss. *)
(*   inv MESSAGE; eauto. *)
(* Qed. *)

(* Lemma mapped_msgs_sound_promise f0 f1 msgs_src msgs_tgt loc vers flag_new *)
(*       (WF1: Mapping.wf f1) *)
(*       (FORALL: List.Forall2 *)
(*                  (fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) => *)
(*                     (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\ *)
(*                     (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\ *)
(*                     (<<MESSAGE: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>)) *)
(*                  msgs_src msgs_tgt) *)
(*       (CLOSED: List.Forall (fun '(from_src, to_src, msg_src) => *)
(*                               forall val released (MSG: msg_src = Message.concrete val released), *)
(*                                 Mapping.closed f1 f1.(Mapping.ver) to_src) msgs_src) *)
(*   : *)
(*     forall to_src from_src msg_src *)
(*            (IN: List.In (from_src, to_src, msg_src) msgs_src), *)
(*     exists to_tgt from_tgt msg_tgt, *)
(*       (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\ *)
(*       (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\ *)
(*       (<<GET: List.In (from_tgt, to_tgt, msg_tgt) msgs_tgt>>). *)
(* Proof. *)
(*   i. eapply list_Forall2_in2 in IN; eauto. des. *)
(*   destruct b as [[from_tgt to_tgt] msg_tgt]. des. esplits; eauto. *)
(* Qed. *)

(* Lemma shited_mapping_space_future_memory srctm flag_src f0 vers mem_src mem_tgt *)
(*       loc f1 ts_src ts_tgt from val released *)
(*       (SIM: sim_memory srctm flag_src f0 vers mem_src mem_tgt) *)
(*       (MAPLE: Mapping.le (f0 loc) f1) *)
(*       (MAPWF0: Mapping.wfs f0) *)
(*       (MAPWF1: Mapping.wf f1) *)
(*       (PRESERVE: forall to_tgt to_src *)
(*                         (TS: Time.lt to_tgt ts_tgt) *)
(*                         (SIM: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) to_src to_tgt), *)
(*           sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt) *)
(*       (SIMTS: sim_timestamp_exact f1 f1.(Mapping.ver) ts_src ts_tgt) *)
(*       (MAX: ts_src = Memory.max_ts loc mem_src) *)
(*       (GET: Memory.get loc ts_tgt mem_tgt = Some (from, Message.concrete val released)) *)
(*   : *)
(*     space_future_memory *)
(*       (Messages.of_memory mem_tgt) *)
(*       f0 mem_src *)
(*       (fun loc0 => if Loc.eq_dec loc0 loc then f1 else f0 loc0) mem_src. *)
(* Proof. *)
(*   pose proof mapping_latest_wf_loc as VERWF. *)
(*   econs. i. inv MSGS. destruct (Loc.eq_dec loc0 loc); cycle 1. *)
(*   { eapply sim_timestamp_exact_inject in FROM0; eauto. *)
(*     eapply sim_timestamp_exact_inject in TO0; eauto. *)
(*   } *)
(*   subst. destruct (Time.le_lt_dec to_tgt ts_tgt). *)
(*   { inv l. *)
(*     2:{ inv H. clarify. } *)
(*     hexploit PRESERVE; [|eapply TO0|..]; eauto. *)
(*     i. eapply sim_timestamp_exact_inject in TO1; eauto. *)
(*     hexploit PRESERVE; [|eapply FROM0|..]; eauto. *)
(*     { eapply TimeFacts.le_lt_lt; eauto. eapply memory_get_ts_le; eauto. } *)
(*     i. eapply sim_timestamp_exact_inject in FROM1; eauto. *)
(*   } *)
(*   { hexploit memory_get_from_mon. *)
(*     { eapply GET. } *)
(*     { eapply GET0. } *)
(*     { eauto. } *)
(*     i. exfalso. *)
(*     hexploit sim_timestamp_exact_le; [| |eapply H|..]; eauto. i. *)
(*     inv COVERED. eapply Memory.max_ts_spec in GET1. des. *)
(*     inv ITV0. ss. inv ITV. ss. eapply Time.lt_strorder. *)
(*     eapply TimeFacts.le_lt_lt. *)
(*     { eapply TO. } *)
(*     eapply TimeFacts.le_lt_lt. *)
(*     { eapply MAX. } *)
(*     eapply TimeFacts.le_lt_lt. *)
(*     { eapply H0. } *)
(*     { eapply FROM2. } *)
(*   } *)
(* Qed. *)

(* Lemma added_memory_space_future_memory f loc msgs_src prom_tgt mem_src0 mem_src1 mem_tgt *)
(*       (MAPWF: Mapping.wfs f) *)
(*       (ADDED: added_memory loc msgs_src mem_src0 mem_src1) *)
(*       (SOUND: forall to_src from_src msg_src *)
(*                      (IN: List.In (from_src, to_src, msg_src) msgs_src), *)
(*           exists to_tgt from_tgt msg_tgt, *)
(*             (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt>>) /\ *)
(*             (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt>>) /\ *)
(*             (<<GET: Memory.get loc to_tgt prom_tgt = Some (from_tgt, msg_tgt)>>)) *)
(*       (MLE: Memory.le prom_tgt mem_tgt) *)
(*   : *)
(*     space_future_memory *)
(*       (unchangable mem_tgt prom_tgt) *)
(*       f mem_src0 *)
(*       f mem_src1. *)
(* Proof. *)
(*   pose proof mapping_latest_wf_loc as VERWF. *)
(*   inv ADDED. econs. i. *)
(*   eapply sim_timestamp_exact_inject in FROM0; eauto. *)
(*   eapply sim_timestamp_exact_inject in TO0; eauto. subst. splits; auto. *)
(*   inv COVERED. econs; eauto. *)
(*   destruct (Loc.eq_dec loc0 loc); subst. *)
(*   2:{ rewrite OTHER in GET; eauto. } *)
(*   eapply SOUND0 in GET. des; eauto. exfalso. *)
(*   eapply SOUND in IN. des. inv MSGS. *)
(*   hexploit Memory.get_disjoint. *)
(*   { eapply GET0. } *)
(*   { eapply MLE. eapply GET. } *)
(*   i. des; clarify. *)
(*   hexploit sim_disjoint; [..|eapply H|]; eauto. *)
(* Qed. *)

Lemma sim_thread_flag_src_view
      f flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt
      loc
      (SIM: sim_thread
              f flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt)
      (LOCALSRC: Local.wf lc_src mem_src)
      (FLAG: flag_src loc = true)
  :
    (<<ACQRLX: lc_src.(Local.tview).(TView.acq).(View.rlx) loc = lc_src.(Local.tview).(TView.cur).(View.rlx) loc>>) /\
    (<<ACQPLN: lc_src.(Local.tview).(TView.acq).(View.pln) loc = lc_src.(Local.tview).(TView.cur).(View.rlx) loc>>).
Proof.
  inv SIM. inv LOCAL. ss.
  hexploit FLAGSRC; eauto. i.
  destruct (vs_src loc) eqn:VAL.
  2:{ hexploit FLAGNONE; eauto. i. des; clarify. }
  hexploit FLAGMAX; eauto. unfold max_memory_val. i. des.
  rewrite SRCTM in *.
  inv LOCALSRC. inv TVIEW_CLOSED. inv CUR. inv ACQ. ss. splits; auto.
  { eapply TimeFacts.antisym.
    { rewrite <- MAXSRC0.
      specialize (RLX0 loc). des. eapply Memory.max_ts_spec in RLX0. des. eauto.
    }
    { eapply TVIEW_WF. }
  }
  { eapply TimeFacts.antisym.
    { rewrite <- MAXSRC0.
      specialize (PLN0 loc). des. eapply Memory.max_ts_spec in PLN0. des. eauto.
    }
    { rewrite H. eapply TVIEW_WF. }
  }
Qed.

Lemma sim_timemap_shifted (L0 L1: Loc.t -> Prop) f0 f1 tm_src tm_tgt
      loc ts_src ts_tgt
      (SIM: sim_timemap L0 f0 (Mapping.vers f0) tm_src tm_tgt)
      (MAPLE: Mapping.les f0 f1)
      (MAPWF0: Mapping.wfs f0)
      (MAPWF1: Mapping.wfs f1)
      (TS: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) ts_src (Some ts_tgt))
      (TMSRC: Time.le (tm_src loc) ts_src)
      (TMTGT: Time.le ts_tgt (tm_tgt loc))
      (LOCS: forall loc0 (IN: L1 loc0), L0 loc0 \/ loc0 = loc)
  :
    sim_timemap L1 f1 (Mapping.vers f1) tm_src tm_tgt.
Proof.
  pose proof mapping_latest_wf_loc as VERWF.
  ii. eapply LOCS in LOC. des.
  { eapply sim_timestamp_mon_ver.
    { erewrite <- sim_timestamp_mon_mapping.
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
    }
    { eapply MAPLE. }
    { eauto. }
    { eauto. }
  }
  subst. red. esplits; eauto. ss.
Qed.

Lemma sim_view_shifted (L0 L1: Loc.t -> Prop) f0 f1 vw_src vw_tgt
      loc ts_src ts_tgt
      (SIM: sim_view L0 f0 (Mapping.vers f0) vw_src vw_tgt)
      (MAPLE: Mapping.les f0 f1)
      (MAPWF0: Mapping.wfs f0)
      (MAPWF1: Mapping.wfs f1)
      (TS: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) ts_src (Some ts_tgt))
      (TMSRC: Time.le (vw_src.(View.rlx) loc) ts_src)
      (TMTGT: Time.le ts_tgt (vw_tgt.(View.pln) loc))
      (LOCS: forall loc0 (IN: L1 loc0), L0 loc0 \/ loc0 = loc)
      (VIEWWF: View.wf vw_tgt)
      (SRCMAX: vw_src.(View.rlx) loc = vw_src.(View.pln) loc)
  :
    sim_view L1 f1 (Mapping.vers f1) vw_src vw_tgt.
Proof.
  econs.
  { eapply sim_timemap_shifted; eauto.
    { eapply SIM. }
    { rewrite <- SRCMAX. auto. }
  }
  { eapply sim_timemap_shifted; eauto.
    { eapply SIM. }
    { etrans; eauto. eapply VIEWWF. }
  }
Qed.

Lemma sim_tview_shifted flag_src0 flag_src1 f0 f1 tvw_src tvw_tgt
      loc ts_src ts_tgt
      (SIM: sim_tview f0 flag_src0 tvw_src tvw_tgt)
      (MAPLE: Mapping.les f0 f1)
      (MAPWF0: Mapping.wfs f0)
      (MAPWF1: Mapping.wfs f1)
      (TS: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) ts_src (Some ts_tgt))
      (TMSRC: Time.le (tvw_src.(TView.cur).(View.rlx) loc) ts_src)
      (TMTGT: Time.le ts_tgt (tvw_tgt.(TView.cur).(View.pln) loc))
      (LOCS: forall loc0 (IN: flag_src1 loc0 = false), flag_src0 loc0 = false \/ loc0 = loc)
      (VIEWWF: TView.wf tvw_tgt)
      (SRCMAX0: tvw_src.(TView.cur).(View.pln) loc = tvw_src.(TView.cur).(View.rlx) loc)
      (SRCMAX1: tvw_src.(TView.acq).(View.rlx) loc = tvw_src.(TView.cur).(View.rlx) loc)
      (SRCMAX2: tvw_src.(TView.acq).(View.pln) loc = tvw_src.(TView.cur).(View.rlx) loc)
  :
    sim_tview f1 flag_src1 tvw_src tvw_tgt.
Proof.
  inv SIM. econs.
  { i. eapply sim_view_mon_mapping_latest; eauto. }
  { eapply sim_view_shifted; eauto. eapply VIEWWF. }
  { eapply sim_view_shifted; eauto.
    { rewrite SRCMAX1. auto. }
    { etrans; eauto. eapply VIEWWF. }
    { eapply VIEWWF. }
    { rewrite SRCMAX1. auto. }
  }
Qed.

Definition is_reserve (te: ThreadEvent.t): Prop :=
  match te with
  | ThreadEvent.reserve _ _ _ => True
  | _ => False
  end.

Definition is_cancel (te: ThreadEvent.t): Prop :=
  match te with
  | ThreadEvent.cancel _ _ _ => True
  | _ => False
  end.

Lemma memory_remove_add mem0 loc from to mem1 mem
      (REMOVE: Memory.remove mem0 loc from to Message.reserve mem1)
      (MEMLE: Memory.le mem0 mem)
      (CLOSED: Memory.inhabited mem)
  :
  Memory.add mem1 loc from to Message.reserve mem0.
Proof.
  hexploit Memory.remove_get0; eauto. i. des.
  hexploit Memory.add_exists.
  { i. erewrite Memory.remove_o in GET2; eauto.
    des_ifs. guardH o.
    hexploit Memory.get_disjoint.
    { eapply GET. }
    { eapply GET2. }
    i. des; eauto. subst. rr in o. des; ss.
  }
  { hexploit memory_get_ts_strong; eauto. i. des; auto.
    subst. eapply MEMLE in GET. rewrite CLOSED in GET. ss.
  }
  { eapply mem0. eapply Memory.remove_get0 in REMOVE. des; eauto. }
  i. des. replace mem0 with mem2; auto. eapply Memory.ext.
  i. erewrite (@Memory.add_o mem2); eauto.
  erewrite (@Memory.remove_o mem1); eauto. des_ifs.
  ss. des; subst. symmetry. eapply Memory.remove_get0; eauto.
Qed.

Lemma cancels_and_reserves lang st lc gl
      (LOCAL: Local.wf lc gl)
      (GLOBAL: Global.wf gl)
  :
  exists lc' gl',
    (<<CANCELS: rtc (pstep (@Thread.step _) is_cancel) (Thread.mk lang st lc gl) (Thread.mk lang st lc' gl')>>) /\
      (<<NORESERVE: lc'.(Local.reserves) = Memory.bot>>) /\
      (<<RESERVES: rtc (pstep (@Thread.step _) is_reserve) (Thread.mk lang st lc' gl') (Thread.mk lang st lc gl)>>).
Proof.
  assert (FIN: exists dom, forall loc to from msg (GET: Memory.get loc to lc.(Local.reserves) = Some (from, msg)),
             (<<RESERVE: msg = Message.reserve>>) /\ (<<IN: List.In (loc, to) dom>>)).
  { inv LOCAL. rr in RESERVES_FINITE. des. esplits; eauto. }
  des. revert lc gl LOCAL GLOBAL FIN. induction dom; i.
  { esplits; [refl| |refl]. eapply Memory.ext. i.
    rewrite Memory.bot_get.
    destruct (Memory.get loc ts (Local.reserves lc)) eqn:GET; ss.
    destruct p. hexploit FIN; eauto. i. des. ss.
  }
  destruct a as [loc ts].
  destruct (Memory.get loc ts lc.(Local.reserves)) eqn:GET.
  { destruct p as [from msg]. hexploit FIN; eauto. i. des. subst.
    hexploit Memory.remove_exists.
    { eapply GET. }
    intros [rsv1 REMOVELC].
    hexploit Memory.remove_exists.
    { eapply LOCAL. eapply GET. }
    intros [mem1 REMOVEGL].
    assert (CANCEL: Local.cancel_step lc gl loc from ts (Local.mk lc.(Local.tview) lc.(Local.promises) rsv1) (Global.mk gl.(Global.sc) gl.(Global.promises) mem1)).
    { econs; eauto. }
    hexploit Local.cancel_step_future; eauto. i. des.
    hexploit IHdom; eauto.
    { i. ss. erewrite Memory.remove_o in GET0; eauto. des_ifs.
      hexploit FIN; eauto. i. des; clarify.
    }
    i. des. esplits.
    { econs 2; [|eapply CANCELS]. econs; eauto. ss. }
    { auto. }
    destruct lc, gl.
    etrans; [eapply RESERVES|]. econs 2; [|refl]. econs.
    { econs 1. econs 2. econs; ss. econs.
      { eapply memory_remove_add; eauto.
        { eapply LOCAL. }
        { eapply GLOBAL. }
      }
      { eapply memory_remove_add; eauto.
        { refl. }
        { eapply GLOBAL. }
      }
    }
    { ss. }
  }
  { eapply IHdom; eauto. i. hexploit FIN; eauto. i. ss; des; clarify. }
Qed.

Lemma sim_reserves_bot f rsv_src rsv_tgt
      (SIM: sim_reserves f rsv_src rsv_tgt)
      (BOT: rsv_tgt = Memory.bot)
      (ONLY: Memory.reserve_only rsv_src)
  :
  rsv_src = Memory.bot.
Proof.
  subst. eapply Memory.ext. i. rewrite Memory.bot_get.
  destruct (Memory.get loc ts rsv_src) eqn:GET; auto.
  destruct p. exploit ONLY; eauto. i. subst.
  hexploit sim_reserves_get_if; eauto. i. des.
  rewrite Memory.bot_get in GET0. ss.
Qed.

Lemma bot_sim_reserves f
  :
  sim_reserves f Memory.bot Memory.bot.
Proof.
  econs.
  { i. rewrite Memory.bot_get in GET. ss. }
  { i. rewrite Memory.bot_get in GET. ss. }
Qed.

Lemma sim_thread_reserve_step
      f0 flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt0 lc_src0 lc_tgt0
      lc_tgt1 mem_tgt1 loc from_tgt to_tgt
      (SIM: sim_thread
              f0 flag_src flag_tgt vs_src vs_tgt
              mem_src0 mem_tgt0 lc_src0 lc_tgt0)
      (PROMISE: Local.reserve_step lc_tgt0 mem_tgt0 loc from_tgt to_tgt lc_tgt1 mem_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt0)
      (MAPWF: Mapping.wfs f0)
  :
  exists f1 from_src to_src lc_src1 mem_src1,
    (<<PROMISE: Local.reserve_step lc_src0 mem_src0 loc from_src to_src lc_src1 mem_src1>>) /\
    (<<SIM: sim_thread
              f1 flag_src flag_tgt vs_src vs_tgt
              mem_src1 mem_tgt1 lc_src1 lc_tgt1>>) /\
    (<<WF: Mapping.wfs f1>>) /\
    (<<MAPLE: Mapping.les_strong f0 f1>>) /\
    (<<SPACE: space_future_memory (unchangable mem_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) f0 mem_src0.(Global.memory) f1 mem_src1.(Global.memory)>>) /\
    (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt0) (f1, mem_src1, mem_tgt1)>>)
.
Proof.
  inv PROMISE.
  hexploit (@mapping_add (f0 loc) (Some from_tgt)); auto. i. des.
  hexploit (@mapping_add f1 (Some to_tgt)); auto. i. des.
  set (f := fun loc0 => if Loc.eq_dec loc0 loc then f2 else f0 loc0).
  assert (MAPWF2: Mapping.wfs f).
  { unfold f. ii. des_ifs. }
  assert (MAPLES: Mapping.les_strong f0 f).
  { unfold f. ii. des_ifs.
    { etrans; eauto. }
    { refl. }
  }
  assert (SIM2: sim_thread
                  f flag_src flag_tgt vs_src vs_tgt
                  mem_src0 mem_tgt0 lc_src0 lc_tgt0).
  { eapply sim_thread_mon_strong; eauto. }
  assert (TS0: sim_timestamp_exact (f loc) (Mapping.ver (f loc)) fts (Some from_tgt)).
  { unfold f. des_ifs; eauto. }
  assert (TS1: sim_timestamp_exact (f loc) (Mapping.ver (f loc)) fts0 (Some to_tgt)).
  { unfold f. des_ifs; eauto. }
  inv SIM2. inv MEM. inv LOCAL. ss.
  hexploit sim_reserve_promise; eauto.
  { eapply LOCALSRC. }
  i. des.
  assert (STEP: Local.reserve_step
                  (Local.mk tvw_src prm_src rsv_src)
                  (Global.mk sc_src gprm_src mem_src)
                  loc fts fts0
                  (Local.mk tvw_src prm_src prom_src1)
                  (Global.mk sc_src gprm_src mem_src1)).
  { econs; eauto. }
  esplits.
  { eauto. }
  { econs; eauto.
    { econs; eauto. }
    { econs; eauto. }
    { eapply promise_max_values_src; eauto. }
    { eapply promise_max_values_tgt; eauto. econs 2; eauto. }
    { i. inv ADD. eapply max_memory_val_add; eauto. }
  }
  { auto. }
  { eauto. }
  { eapply space_future_memory_trans.
    { eapply space_future_memory_refl; eauto. }
    { eauto. }
    all: eauto.
    { eapply Mapping.les_strong_les; eauto. }
    { refl. }
  }
  { econs. i. splits; ss.
    { rr. splits; ss. inv ADD. eapply add_reserve_owned_future; eauto. }
    { rr. splits; ss. inv RESERVE. eapply add_reserve_owned_future; eauto. }
  }
Qed.

Lemma sim_thread_cancel_step
      f0 flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt0 lc_src0 lc_tgt0
      lc_tgt1 mem_tgt1 loc from_tgt to_tgt
      (SIM: sim_thread
              f0 flag_src flag_tgt vs_src vs_tgt
              mem_src0 mem_tgt0 lc_src0 lc_tgt0)
      (PROMISE: Local.cancel_step lc_tgt0 mem_tgt0 loc from_tgt to_tgt lc_tgt1 mem_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt0)
      (MAPWF: Mapping.wfs f0)
  :
  exists from_src to_src lc_src1 mem_src1,
    (<<PROMISE: Local.cancel_step lc_src0 mem_src0 loc from_src to_src lc_src1 mem_src1>>) /\
    (<<SIM: sim_thread
              f0 flag_src flag_tgt vs_src vs_tgt
              mem_src1 mem_tgt1 lc_src1 lc_tgt1>>) /\
    (<<SPACE: space_future_memory (unchangable mem_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) f0 mem_src0.(Global.memory) f0 mem_src1.(Global.memory)>>) /\
    (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt0) (f0, mem_src1, mem_tgt1)>>)
.
Proof.
  inv PROMISE. inv CANCEL. ss.
  inv SIM. inv MEM0. inv LOCAL. ss.
  hexploit sim_cancel_promise; [|eauto|eauto|..]; eauto.
  { eapply LOCALSRC. }
  i. des.
  assert (STEP: Local.cancel_step
                  (Local.mk tvw_src prm_src rsv_src)
                  (Global.mk sc_src gprm_src mem_src)
                  loc from_src to_src
                  (Local.mk tvw_src prm_src prom_src1)
                  (Global.mk sc_src gprm_src mem_src1)).
  { econs; eauto. }
  esplits.
  { eauto. }
  { econs; eauto.
    { econs; eauto. }
    { econs; eauto. }
    { eapply promise_max_values_src; eauto. }
    { eapply promise_max_values_tgt; eauto. econs 3; eauto. }
    { i. inv CANCEL. eapply max_memory_val_cancel; eauto. }
  }
  { auto. }
  { econs. i. splits; ss.
    { refl. }
    { rr. splits; ss. inv CANCEL. eapply remove_owned_future; eauto. }
    { rr. splits; ss. eapply remove_owned_future; eauto. }
  }
Qed.

Lemma sim_thread_reserve_steps
      lang_src lang_tgt st_src st_tgt
      f0 flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt0 lc_src0 lc_tgt0
      lc_tgt1 mem_tgt1
      (SIM: sim_thread
              f0 flag_src flag_tgt vs_src vs_tgt
              mem_src0 mem_tgt0 lc_src0 lc_tgt0)
      (PROMISES: rtc (pstep (@Thread.step _) is_reserve) (Thread.mk lang_tgt st_tgt lc_tgt0 mem_tgt0) (Thread.mk _ st_tgt lc_tgt1 mem_tgt1))
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt0)
      (MAPWF: Mapping.wfs f0)
  :
  exists f1 lc_src1 mem_src1,
    (<<PROMISE: rtc (@Thread.internal_step _) (Thread.mk lang_src st_src lc_src0 mem_src0) (Thread.mk _ st_src lc_src1 mem_src1)>>) /\
      (<<SIM: sim_thread
                f1 flag_src flag_tgt vs_src vs_tgt
                mem_src1 mem_tgt1 lc_src1 lc_tgt1>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les_strong f0 f1>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) f0 mem_src0.(Global.memory) f1 mem_src1.(Global.memory)>>) /\
    (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt0) (f1, mem_src1, mem_tgt1)>>)
.
Proof.
  remember (Thread.mk lang_tgt st_tgt lc_tgt0 mem_tgt0).
  remember (Thread.mk _ st_tgt lc_tgt1 mem_tgt1).
  revert mem_src0 mem_tgt0 lc_src0 lc_tgt0
         lc_tgt1 mem_tgt1 f0 SIM LOCALSRC LOCALTGT MEMSRC MEMTGT MAPWF Heqt0 Heqt.
  induction PROMISES; i; clarify.
  { esplits; eauto.
    { refl. }
    { eapply space_future_memory_refl; eauto. refl. }
    { refl. }
  }
  inv H. hexploit Thread.step_future; eauto. i. des.
  destruct e; ss. dup STEP. inv STEP; inv LOCAL; ss.
  hexploit sim_thread_reserve_step; eauto. i. des.
  hexploit Local.reserve_step_future; eauto. i. des.
  hexploit IHPROMISES; eauto. i. des. esplits.
  { econs 2; eauto. econs. econs 2; eauto. }
  { eauto. }
  { eauto. }
  { etrans; eauto. }
  { eapply space_future_memory_trans; eauto.
    { eapply space_future_memory_mon_msgs; eauto.
      i. eapply unchangable_increase in STEP0; eauto.
    }
    { eapply Mapping.les_strong_les; eauto. }
    { eapply Mapping.les_strong_les; eauto. }
  }
  { etrans.
    { eauto. }
    erewrite <- other_promise_same_internal; eauto.
  }
Qed.

Lemma sim_thread_cancel_steps
      lang_src lang_tgt st_src st_tgt
      f0 flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt0 lc_src0 lc_tgt0
      lc_tgt1 mem_tgt1
      (SIM: sim_thread
              f0 flag_src flag_tgt vs_src vs_tgt
              mem_src0 mem_tgt0 lc_src0 lc_tgt0)
      (PROMISES: rtc (pstep (@Thread.step _) is_cancel) (Thread.mk lang_tgt st_tgt lc_tgt0 mem_tgt0) (Thread.mk _ st_tgt lc_tgt1 mem_tgt1))
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt0)
      (MAPWF: Mapping.wfs f0)
  :
  exists lc_src1 mem_src1,
    (<<PROMISE: rtc (@Thread.internal_step _) (Thread.mk lang_src st_src lc_src0 mem_src0) (Thread.mk _ st_src lc_src1 mem_src1)>>) /\
      (<<SIM: sim_thread
                f0 flag_src flag_tgt vs_src vs_tgt
                mem_src1 mem_tgt1 lc_src1 lc_tgt1>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) f0 mem_src0.(Global.memory) f0 mem_src1.(Global.memory)>>) /\
    (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt0) (f0, mem_src1, mem_tgt1)>>)
.
Proof.
  remember (Thread.mk lang_tgt st_tgt lc_tgt0 mem_tgt0).
  remember (Thread.mk _ st_tgt lc_tgt1 mem_tgt1).
  revert mem_src0 mem_tgt0 lc_src0 lc_tgt0
         lc_tgt1 mem_tgt1 f0 SIM LOCALSRC LOCALTGT MEMSRC MEMTGT MAPWF Heqt0 Heqt.
  induction PROMISES; i; clarify.
  { esplits; eauto.
    { eapply space_future_memory_refl; eauto. refl. }
    { refl. }
  }
  inv H. hexploit Thread.step_future; eauto. i. des.
  destruct e; ss. dup STEP. inv STEP; inv LOCAL; ss.
  hexploit sim_thread_cancel_step; eauto. i. des.
  hexploit Local.cancel_step_future; eauto. i. des.
  hexploit IHPROMISES; eauto. i. des. esplits.
  { econs 2; eauto. econs. econs 3; eauto. }
  { eauto. }
  { eapply space_future_memory_trans; eauto.
    { eapply space_future_memory_mon_msgs; eauto.
      i. eapply unchangable_increase in STEP0; eauto.
    }
    { refl. }
    { refl. }
  }
  { etrans.
    { eauto. }
    erewrite <- other_promise_same_internal; eauto.
  }
Qed.

Lemma sim_thread_promise_step
      lang_src st_src
      f0 flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt0 lc_src0 lc_tgt0
      lc_tgt1 mem_tgt1 loc
      (SIM: sim_thread
              f0 flag_src flag_tgt vs_src vs_tgt
              mem_src0 mem_tgt0 lc_src0 lc_tgt0)
      (PROMISE: Local.promise_step lc_tgt0 mem_tgt0 loc lc_tgt1 mem_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt0)
      (MAPWF: Mapping.wfs f0)
      (NORACE: mem_src0.(Global.promises) loc = true -> lc_src0.(Local.promises) loc = true)
  :
  exists lc_src1 mem_src1,
    (<<PROMISE: rtc (@Thread.internal_step _) (Thread.mk lang_src st_src lc_src0 mem_src0) (Thread.mk lang_src st_src lc_src1 mem_src1)>>) /\
    (<<SIM: sim_thread
              f0 flag_src flag_tgt vs_src vs_tgt
              mem_src1 mem_tgt1 lc_src1 lc_tgt1>>) /\
    (<<SPACE: space_future_memory (unchangable mem_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) f0 mem_src0.(Global.memory) f0 mem_src1.(Global.memory)>>) /\
    (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt0) (f0, mem_src1, mem_tgt1)>>)

.
Proof.
  inv PROMISE. inv SIM. inv MEM. inv LOCAL. ss.
  hexploit sim_promises_tgt_promise; eauto.
  { eapply LOCALSRC. }
  { eapply LOCALTGT. }
  i. des. rr in PROMISE. des.
  { esplits.
    { econs 2; [|refl]. econs 1. econs 1; eauto. }
    { econs; eauto; ss.
      { econs; eauto. erewrite <- Promises.promise_minus; eauto. }
      { eapply promise_max_values_src; eauto. econs 1; eauto. }
      { eapply promise_max_values_tgt; eauto. econs 1; eauto. }
    }
    { ss. eapply space_future_memory_refl; eauto. refl. }
    { econs. i. splits; ss.
      { refl. }
      { rr. splits; ss. eapply UNCH; eauto. }
      { rr. splits; ss. eapply UNCH; eauto. }
    }
  }
  { subst. esplits.
    { refl. }
    { econs; eauto.
      { econs; eauto. }
      { econs; eauto. }
      { eapply promise_max_values_tgt; eauto. econs 1; eauto. }
    }
    { ss. eapply space_future_memory_refl; eauto. refl. }
    { econs. i. splits; ss.
      { refl. }
      { refl. }
      { rr. splits; ss. eapply UNCH; eauto. }
    }
  }
Qed.

Lemma sim_thread_deflag_aux_no_reserve
      b f0 flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt lc_src0 lc_tgt
      loc
      (SIM: sim_thread
              f0 flag_src flag_tgt vs_src vs_tgt
              mem_src0 mem_tgt lc_src0 lc_tgt)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt mem_tgt)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt)
      (WF: Mapping.wfs f0)
      (FLAG: flag_src loc = true)
      (VAL: b = false -> option_rel Const.le (vs_tgt loc) (vs_src loc))
      (NORESERVE: lc_tgt.(Local.reserves) = Memory.bot)
      lang st
  :
    exists lc_src1 mem_src1 f1,
      (<<STEPS: rtc (@Thread.internal_step _)
                    (Thread.mk lang st lc_src0 mem_src0)
                    (Thread.mk _ st lc_src1 mem_src1)>>) /\
      (<<SIM: sim_thread
                f1
                (fun loc0 => if Loc.eq_dec loc0 loc then false else flag_src loc0)
                (fun loc0 => if Loc.eq_dec loc0 loc then b else flag_tgt loc0)
                vs_src vs_tgt
                mem_src1 mem_tgt lc_src1 lc_tgt>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<UNCH: forall loc0 (NEQ: loc0 <> loc), f1 loc0 = f0 loc0>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt.(Global.memory) lc_tgt.(Local.reserves)) f0 mem_src0.(Global.memory) f1 mem_src1.(Global.memory)>>) /\
    (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt) (f1, mem_src1, mem_tgt)>>)
.
Proof.
  inv SIM. inv MEM. inv LOCAL.
  pose proof (PERM loc) as VALP. unfold option_rel in VALP. des_ifs.
  2:{ exfalso. hexploit FLAGNONE; eauto. i. des. clarify. }
  hexploit (MAXSRC loc); eauto. i. inv H. hexploit MAX; eauto. i. des.
  hexploit (MAXTGT loc); eauto. i. inv H. hexploit MAX1; eauto. i. des.
  inv MAX0. inv MAX2.
  hexploit FLAGMAX; eauto. i. des. rr in H. des; ss.
  hexploit sim_promises_deflag; eauto.
  { eapply LOCALSRC. }
  { eapply LOCALTGT. }
  { i. rewrite H in NONE0. destruct (prm_tgt loc); ss. }
  i. des. ss.
  hexploit deflag_sim_memory; eauto.
  { i. destruct (Time.le_lt_dec to0 (View.pln (TView.cur tvw_tgt) loc)); ss.
    hexploit MAX0; eauto; ss.
  }
  i. des.
  assert (STEPS: rtc (@Thread.internal_step _)
                     (Thread.mk _ st (Local.mk tvw_src prm_src rsv_src) (Global.mk sc_src gprm_src mem_src))
                     (Thread.mk _ st (Local.mk tvw_src lprm_src1 rsv_src) (Global.mk sc_src gprm_src1 mem_src))).
  { rr in PROMISE. des.
    { econs 2; [|refl]. econs. econs 1; eauto. }
    { subst. ss. refl. }
  }
  esplits; eauto.
  { econs; eauto; ss.
    { econs; eauto.
      { eapply sim_timemap_mon_latest; eauto. }
      { replace (BoolMap.minus gprm_src1 lprm_src1) with (BoolMap.minus gprm_src prm_src); cycle 1.
        { rr in PROMISE. des; subst; auto.
          eapply Promises.promise_minus; eauto.
        }
        replace (boolmap_plus
                   (fun loc0 =>
                      if LocSet.Facts.eq_dec loc0 loc then false else flag_src loc0)
                   (fun loc0 =>
                      if LocSet.Facts.eq_dec loc0 loc then b else flag_tgt loc0)) with (LocFun.add loc b (boolmap_plus flag_src flag_tgt)); auto.
        extensionality loc0. rewrite loc_fun_add_spec.
        unfold boolmap_plus, orb. des_ifs.
      }
    }
    { econs; eauto.
      { eapply sim_tview_shifted; eauto.
        { rewrite SRCTM. refl. }
        { refl. }
        { unfold boolmap_plus, orb. clear. i. des_ifs; auto. }
        { eapply LOCALTGT. }
        { symmetry. eapply FLAGSRC; auto. }
        { apply TimeFacts.antisym.
          { rewrite <- SRCTM. rewrite <- MAXSRC0.
            inv LOCALSRC. inv TVIEW_CLOSED. inv ACQ.
            specialize (RLX loc). des.
            eapply Memory.max_ts_spec in RLX. des; auto.
          }
          { eapply LOCALSRC. }
        }
        { apply TimeFacts.antisym.
          { rewrite <- SRCTM. rewrite <- MAXSRC0.
            inv LOCALSRC. inv TVIEW_CLOSED. inv ACQ.
            specialize (PLN loc). des.
            eapply Memory.max_ts_spec in PLN. des; auto.
          }
          { rewrite FLAGSRC; auto. eapply LOCALSRC. }
        }
      }
      { hexploit sim_reserves_bot; eauto.
        { eapply LOCALSRC. }
        i. subst. eapply bot_sim_reserves.
      }
      { i. des_ifs. eapply FLAGSRC; eauto. }
    }
    { eapply promise_steps_max_values_src in STEPS; eauto. }
    { rr in FIN. des. hexploit list_filter_exists.
      instantiate (2:=fun loc0 => loc0 <> loc).
      i. des. exists l'. ii. split; i.
      { des_ifs. eapply COMPLETE. split; eauto. eapply DOM; eauto. }
      { eapply COMPLETE in H. des. des_ifs. eapply DOM in IN; eauto. }
    }
    { i. des_ifs. eapply MAXNEQ; eauto. }
    { i. des_ifs. eapply FLAGNONE; eauto. }
  }
  { eapply space_future_memory_mon_msgs; eauto. eapply unchangable_messages_of_memory. }
  { econs. i. assert (NEQ: loc0 <> loc).
    { ii. subst. unfold BoolMap.minus in OWN.
      destruct (gprm_src loc), (prm_src loc); ss.
    }
    splits.
    { rewrite UNCH0; auto. refl. }
    { rr. splits; ss. eapply UNCH; eauto. }
    { refl. }
  }
Qed.

Lemma sim_thread_deflag_aux
      b f0 flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt lc_src0 lc_tgt
      loc
      (SIM: sim_thread
              f0 flag_src flag_tgt vs_src vs_tgt
              mem_src0 mem_tgt lc_src0 lc_tgt)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt mem_tgt)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt)
      (WF: Mapping.wfs f0)
      (FLAG: flag_src loc = true)
      (VAL: b = false -> option_rel Const.le (vs_tgt loc) (vs_src loc))
      lang st
  :
    exists lc_src1 mem_src1 f1,
      (<<STEPS: rtc (@Thread.internal_step _)
                    (Thread.mk lang st lc_src0 mem_src0)
                    (Thread.mk _ st lc_src1 mem_src1)>>) /\
      (<<SIM: sim_thread
                f1
                (fun loc0 => if Loc.eq_dec loc0 loc then false else flag_src loc0)
                (fun loc0 => if Loc.eq_dec loc0 loc then b else flag_tgt loc0)
                vs_src vs_tgt
                mem_src1 mem_tgt lc_src1 lc_tgt>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<UNCH: forall loc0 (NEQ: loc0 <> loc), Mapping.le_strong (f0 loc0) (f1 loc0)>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt.(Global.memory) lc_tgt.(Local.reserves)) f0 mem_src0.(Global.memory) f1 mem_src1.(Global.memory)>>) /\
    (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt) (f1, mem_src1, mem_tgt)>>)
.
Proof.
  hexploit cancels_and_reserves; eauto. i. des.
  hexploit rtc_implies; [|eapply CANCELS|].
  { instantiate (1:=tau (@Thread.step _ )). i. inv H. econs; eauto. destruct e; ss. }
  intros STEPS0.
  hexploit rtc_implies; [|eapply RESERVES|].
  { instantiate (1:=tau (@Thread.step _ )). i. inv H. econs; eauto. destruct e; ss. }
  intros STEPS1.
  hexploit Thread.rtc_tau_step_future;[eapply STEPS0|..]; eauto. i. des; ss.
  hexploit sim_thread_cancel_steps; eauto. i. des.
  hexploit Thread.rtc_tau_step_future;[eapply rtc_implies; [|eapply PROMISE]|..]; eauto.
  { i. inv H. econs; [econs 1; eauto|]. inv LOCAL; ss. }
  i. des; ss.
  hexploit sim_thread_deflag_aux_no_reserve; eauto. i. des.
  hexploit Thread.rtc_tau_step_future;[eapply rtc_implies; [|eapply STEPS]|..]; eauto.
  { i. inv H. econs; [econs 1; eauto|]. inv LOCAL; ss. }
  i. des; ss.
  hexploit sim_thread_reserve_steps; eauto. i. des.
  esplits.
  { etrans; [eauto|]. etrans; eauto. }
  { eauto. }
  { eauto. }
  { etrans; eauto. eapply Mapping.les_strong_les; eauto. }
  { i. etrans; [|eapply MAPLE0]. rewrite UNCH; auto. refl. }
  { eapply space_future_memory_trans; eauto.
    { eapply space_future_memory_mon_msgs.
      { eapply space_future_memory_trans; eauto.
        { eapply Mapping.les_strong_les; eauto. }
      }
      { i. eapply unchangable_rtc_tau_step_increase in STEPS0; eauto. }
    }
    { refl. }
    { etrans; eauto. eapply Mapping.les_strong_les; eauto. }
  }
  { etrans.
    { eauto. }
    hexploit Thread.rtc_tau_step_promises_minus.
    { eapply rtc_implies; [|eapply STEPS]. i. inv H. econs; [econs 1; eauto|]. inv LOCAL; ss. }
    i. ss.
    hexploit Thread.rtc_tau_step_promises_minus.
    { eapply rtc_implies; [|eapply PROMISE]. i. inv H0. econs; [econs 1; eauto|]. inv LOCAL; ss. }
    i. ss.
    rewrite H0. etrans.
    { eauto. }
    { rewrite H. auto. }
  }
  Unshelve. all: eauto.
Qed.

Lemma sim_thread_deflag
      b f0 flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt lc_src0 lc_tgt
      loc
      (SIM: sim_thread
              f0 flag_src flag_tgt vs_src vs_tgt
              mem_src0 mem_tgt lc_src0 lc_tgt)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt mem_tgt)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt)
      (WF: Mapping.wfs f0)
      (FLAG: b = false -> flag_src loc = false -> flag_tgt loc = false)
      (VAL: b = false -> (option_rel Const.le (vs_tgt loc) (vs_src loc) \/ flag_src loc = false))
      lang st
  :
    exists lc_src1 mem_src1 f1 f,
      (<<STEPS: rtc (@Thread.internal_step _)
                    (Thread.mk lang st lc_src0 mem_src0)
                    (Thread.mk _ st lc_src1 mem_src1)>>) /\
      (<<SIM: sim_thread
                f1
                (fun loc0 => if Loc.eq_dec loc0 loc then false else flag_src loc0)
                (fun loc0 => if Loc.eq_dec loc0 loc then f else flag_tgt loc0)
                vs_src vs_tgt
                mem_src1 mem_tgt lc_src1 lc_tgt>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<FLAG: b = false -> f = false>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<UNCH: forall loc0 (NEQ: loc0 <> loc), Mapping.le_strong (f0 loc0) (f1 loc0)>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt.(Global.memory) lc_tgt.(Local.reserves)) f0 mem_src0.(Global.memory) f1 mem_src1.(Global.memory)>>) /\
    (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt) (f1, mem_src1, mem_tgt)>>)
.
Proof.
  destruct (flag_src loc) eqn:EQ.
  { des; ss. hexploit sim_thread_deflag_aux; eauto.
    { i. hexploit VAL; eauto. i. des; ss. }
    i. des. esplits; eauto.
  }
  { esplits.
    { refl. }
    { replace (fun (loc0: Loc.t) => if LocSet.Facts.eq_dec loc0 loc then false else flag_src loc0) with flag_src.
      2:{ extensionality loc0. des_ifs. }
      instantiate (1:=flag_tgt loc).
      replace (fun (loc0: Loc.t) => if LocSet.Facts.eq_dec loc0 loc then flag_tgt loc else flag_tgt loc0) with flag_tgt.
      2:{ extensionality loc0. des_ifs. }
      { eauto. }
    }
    { eauto. }
    { i. eauto. }
    { refl. }
    { i. refl. }
    { eapply space_future_memory_refl; eauto. refl. }
    { refl. }
  }
Qed.

Lemma sim_thread_deflag_all_aux
      dom
  :
    forall
      f0 flag_src flag_tgt0 vs_src vs_tgt
      mem_src0 mem_tgt lc_src0 lc_tgt
      (D: Loc.t -> Prop)
      (SIM: sim_thread
              f0 flag_src flag_tgt0 vs_src vs_tgt
              mem_src0 mem_tgt lc_src0 lc_tgt)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt mem_tgt)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt)
      (WF: Mapping.wfs f0)
      (DEBT: forall loc, (<<DEBT: D loc>>) \/
                         ((<<FLAG: flag_src loc = false -> flag_tgt0 loc = false>>) /\
                          (<<VAL: option_rel Const.le (vs_tgt loc) (vs_src loc) \/ flag_src loc = false>>)))
      (FIN: forall loc (FLAG: flag_src loc = true), List.In loc dom)
      lang st,
    exists lc_src1 mem_src1 f1 flag_tgt1,
      (<<STEPS: rtc (@Thread.internal_step _)
                    (Thread.mk lang st lc_src0 mem_src0)
                    (Thread.mk _ st lc_src1 mem_src1)>>) /\
      (<<SIM: sim_thread
                f1
                (fun _ => false)
                flag_tgt1
                vs_src vs_tgt
                mem_src1 mem_tgt lc_src1 lc_tgt>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<FLAG: forall loc, (<<DEBT: D loc>>) \/ (<<FLAG: flag_tgt1 loc = false>>)>>) /\
      (<<UNCH: forall loc (NIN: ~ List.In loc dom), Mapping.le_strong (f0 loc) (f1 loc)>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt.(Global.memory) lc_tgt.(Local.reserves)) f0 mem_src0.(Global.memory) f1 mem_src1.(Global.memory)>>) /\
    (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt) (f1, mem_src1, mem_tgt)>>)
.
Proof.
  induction dom.
  { i. assert (FLAG: flag_src = fun _ => false).
    { extensionality loc. destruct (flag_src loc) eqn:FLAG; auto.
      hexploit (FIN loc); eauto. ss.
    }
    subst. esplits.
    { refl. }
    { eauto. }
    { auto. }
    { refl. }
    { i. hexploit DEBT; eauto. i. des; eauto. }
    { i. refl. }
    { eapply space_future_memory_refl; eauto. refl. }
    { refl. }
  }
  i.
  cut (exists lc_src1 mem_src1 f1 flag,
          (<<STEPS: rtc (@Thread.internal_step _)
                        (Thread.mk lang st lc_src0 mem_src0)
                        (Thread.mk _ st lc_src1 mem_src1)>>) /\
          (<<SIM: sim_thread
                    f1
                    (fun loc0 => if Loc.eq_dec loc0 a then false else flag_src loc0)
                    (fun loc0 => if Loc.eq_dec loc0 a then flag else flag_tgt0 loc0)
                    vs_src vs_tgt
                    mem_src1 mem_tgt lc_src1 lc_tgt>>) /\
          (<<WF: Mapping.wfs f1>>) /\
          (<<MAPLE: Mapping.les f0 f1>>) /\
          (<<FLAG: __guard__(flag = false \/ D a)>>) /\
          (<<UNCH: forall loc (NEQ: loc <> a), Mapping.le_strong (f0 loc) (f1 loc)>>) /\
          (<<SPACE: space_future_memory (unchangable mem_tgt.(Global.memory) lc_tgt.(Local.reserves)) f0 mem_src0.(Global.memory) f1 mem_src1.(Global.memory)>>) /\
          (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt) (f1, mem_src1, mem_tgt)>>)).
  { i. des.
    hexploit Thread.rtc_tau_step_future.
    { eapply rtc_implies; [|eapply STEPS]. i.
      inv H. econs; [econs 1; eauto|]. inv LOCAL; ss.
    }
    { eauto. }
    { eauto. }
    i. ss. des.
    hexploit IHdom; eauto.
    { instantiate (1:=D). i. destruct (classic (D loc)); auto.
      hexploit (DEBT loc). intros [|]; ss.
      right. des_ifs. splits; auto.
      i. red in FLAG. des; ss.
    }
    { i. ss. des_ifs.
      eapply FIN in FLAG0. des; ss. intuition.
    }
    i. des. esplits.
    { etrans; eauto. }
    { eauto. }
    { eauto. }
    { etrans; eauto. }
    { auto. }
    { i. etrans; eauto. }
    { eapply space_future_memory_trans; eauto. }
    { etrans; eauto.
      hexploit Thread.rtc_tau_step_promises_minus.
      { eapply rtc_implies; [|eapply STEPS]. i. inv H. econs; [econs 1; eauto|]. inv LOCAL; ss. }
      i. ss. rewrite H. auto.
    }
  }
  hexploit (DEBT a). intros [|[]].
  { hexploit (@sim_thread_deflag true); eauto; ss. i. des.
    esplits; eauto.
    { right. auto. }
  }
  { guardH H0. hexploit (@sim_thread_deflag false); eauto. i. des.
    esplits; eauto.
    { left. eauto. }
  }
Qed.

Lemma sim_thread_deflag_all
      (D: Loc.t -> Prop)
      f0 flag_src flag_tgt0 vs_src vs_tgt
      mem_src0 mem_tgt lc_src0 lc_tgt
      (SIM: sim_thread
              f0 flag_src flag_tgt0 vs_src vs_tgt
              mem_src0 mem_tgt lc_src0 lc_tgt)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt mem_tgt)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt)
      (WF: Mapping.wfs f0)
      (DEBT: forall loc, (<<DEBT: D loc>>) \/
                         ((<<FLAG: flag_src loc = false -> flag_tgt0 loc = false>>) /\
                          (<<VAL: option_rel Const.le (vs_tgt loc) (vs_src loc) \/ flag_src loc = false>>)))
      lang st
  :
    exists lc_src1 mem_src1 f1 flag_tgt1,
      (<<STEPS: rtc (@Thread.internal_step _)
                    (Thread.mk lang st lc_src0 mem_src0)
                    (Thread.mk _ st lc_src1 mem_src1)>>) /\
      (<<SIM: sim_thread
                f1
                (fun _ => false)
                flag_tgt1
                vs_src vs_tgt
                mem_src1 mem_tgt lc_src1 lc_tgt>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<FLAG: forall loc, (<<DEBT: D loc>>) \/ (<<FLAG: flag_tgt1 loc = false>>)>>) /\
      (<<UNCH: forall loc (FLAG: flag_src loc = false), Mapping.le_strong (f0 loc) (f1 loc)>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt.(Global.memory) lc_tgt.(Local.reserves)) f0 mem_src0.(Global.memory) f1 mem_src1.(Global.memory)>>) /\
      (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt) (f1, mem_src1, mem_tgt)>>)
.
Proof.
  dup SIM. inv SIM. red in FIN. des.
  hexploit (@sim_thread_deflag_all_aux dom); eauto.
  { i. eapply DOM. eauto. }
  i. des. esplits; eauto.
  { i. eapply UNCH. ii. eapply DOM in H. des. clarify. }
Qed.

Lemma local_write_fence_step_promise_step
      lc0 ordw lc1
      mem0 e lc2 mem1 mem2
      (PROMISE: Local.internal_step e lc0 mem0 lc1 mem1)
      (FENCE: local_fence_write_step lc1 mem1 ordw lc2 mem2)
  :
    exists lc1' mem1',
      (<<FENCE: local_fence_write_step lc0 mem0 ordw lc1' mem1'>>) /\
      (<<PROMISE: Local.internal_step e lc1' mem1' lc2 mem2>>).
Proof.
  inv FENCE. inv PROMISE.
  { inv LOCAL; ss; esplits.
    { econs; eauto. }
    { econs 1; eauto; ss. }
  }
  { inv LOCAL; ss; esplits.
    { econs; eauto. }
    { econs 2; eauto; ss. }
  }
  { inv LOCAL; ss; esplits.
    { econs; eauto. }
    { econs 3; eauto; ss. }
  }
Qed.

Lemma local_write_fence_step_promise_steps
      lc0 ordw lc1
      mem0 lc2 mem1 mem2
      lang st
      (STEPS: rtc (@Thread.internal_step _)
                  (Thread.mk lang st lc0 mem0)
                  (Thread.mk _ st lc1 mem1))
      (FENCE: local_fence_write_step lc1 mem1 ordw lc2 mem2)
  :
    exists lc1' mem1',
      (<<FENCE: local_fence_write_step lc0 mem0 ordw lc1' mem1'>>) /\
      (<<STEPS: rtc (@Thread.internal_step _)
                    (Thread.mk lang st lc1' mem1')
                    (Thread.mk _ st lc2 mem2)>>).
Proof.
  remember (Thread.mk lang st lc0 mem0).
  remember (Thread.mk lang st lc1 mem1).
  revert lc0 st lc1 lc2 mem0 mem1 mem2 Heqt Heqt0 FENCE.
  induction STEPS; i; clarify.
  { esplits.
    { eauto. }
    { refl. }
  }
  { inv H. hexploit IHSTEPS; eauto. i. des.
    hexploit local_write_fence_step_promise_step; eauto. i. des.
    esplits; [eauto|]. etrans.
    { eauto. }
    { econs; eauto. econs; eauto. }
  }
Qed.

Lemma promise_step_local_read_step lc0 lc1 lc2 mem0 mem1
      loc0 ts val released ord e
      (READ: Local.read_step lc0 mem0 loc0 ts val released ord lc1)
      (PROMISE: Local.internal_step e lc1 mem0 lc2 mem1)
  :
    exists lc1',
      (<<PROMISE: Local.internal_step e lc0 mem0 lc1' mem1>>) /\
      (<<READ: Local.read_step lc1' mem1 loc0 ts val released ord lc2>>).
Proof.
  inv READ. inv PROMISE.
  { inv LOCAL. esplits.
    { econs 1; eauto. }
    { ss. econs; eauto. }
  }
  { inv LOCAL. inv RESERVE. esplits.
    { econs 2; eauto. }
    { ss. econs; eauto. eapply Memory.add_get1; eauto. }
  }
  { inv LOCAL. inv CANCEL. esplits.
    { econs 3; eauto. }
    { ss. econs; eauto. eapply Memory.remove_get1 in GET; eauto.
      des; eauto. clarify. }
  }
Qed.

Lemma promise_steps_local_read_step lc0 lc1 lc2 mem0 mem1
      loc ts val released ord
      lang st0 st1
      (READ: Local.read_step lc0 mem0 loc ts val released ord lc1)
      (STEPS: rtc (@Thread.internal_step _)
                  (Thread.mk lang st0 lc1 mem0)
                  (Thread.mk _ st1 lc2 mem1))
  :
    exists lc1',
      (<<STEPS: rtc (@Thread.internal_step _)
                    (Thread.mk lang st0 lc0 mem0)
                    (Thread.mk _ st1 lc1' mem1)>>) /\
      (<<READ: Local.read_step lc1' mem1 loc ts val released ord lc2>>)
.
Proof.
  remember (Thread.mk lang st0 lc1 mem0).
  remember (Thread.mk lang st1 lc2 mem1).
  revert lc0 st0 st1 lc1 lc2 mem0 mem1 Heqt Heqt0 READ.
  induction STEPS; i; clarify.
  { esplits.
    { refl. }
    { eauto. }
  }
  { inv H. hexploit promise_step_local_read_step; eauto.
    i. des. hexploit IHSTEPS; eauto.
    i. des. esplits; [|eauto].
    econs 2; [|eauto]. econs; eauto.
  }
Qed.

Lemma sim_thread_write_fence_step
      f flag_src flag_tgt vs_src0 vs_tgt0
      mem_src0 mem_tgt0 lc_src0 lc_tgt0 mem_tgt1
      lc_tgt1 ordw
      (SIM: sim_thread
              f flag_src flag_tgt vs_src0 vs_tgt0
              mem_src0 mem_tgt0 lc_src0 lc_tgt0)
      (WRITE: local_fence_write_step lc_tgt0 mem_tgt0 ordw lc_tgt1 mem_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt0)
      (WF: Mapping.wfs f)
      (RELFLAG: forall loc (ORD: Ordering.le Ordering.acqrel ordw), flag_src loc = false)
  :
    exists lc_src1 mem_src1,
      (<<READ: local_fence_write_step lc_src0 mem_src0 ordw lc_src1 mem_src1>>) /\
      (<<SIM: sim_thread
                f flag_src flag_tgt vs_src0 vs_tgt0
                mem_src1 mem_tgt1 lc_src1 lc_tgt1>>) /\
      (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f, mem_src0, mem_tgt0) (f, mem_src1, mem_tgt1)>>)
.
Proof.
  assert (exists lc_src1 mem_src1, (<<WRITE: local_fence_write_step lc_src0 mem_src0 ordw lc_src1 mem_src1>>)).
  { esplits. econs; eauto. }
  des. hexploit local_fence_write_step_future; [eapply WRITE|..]; eauto. i. des.
  hexploit local_fence_write_step_future; [eapply WRITE0|..]; eauto. i. des.
  destruct lc_src0 as [tvw_src0 prom_src].
  destruct lc_tgt0 as [tvw_tgt0 prom_tgt].
  inv WRITE. inv WRITE0. ss.
  dup SIM. inv SIM. inv LOCAL1.
  esplits; eauto.
  { econs; eauto. }
  { inv MEM. econs; eauto; ss.
    { econs; eauto.
      eapply sim_local_write_fence_sc; eauto.
      i. eapply RELFLAG. destruct ordw; ss.
    }
    { econs; eauto.
      { destruct (Ordering.le Ordering.acqrel ordw) eqn:ORD.
        { eapply sim_local_write_fence_tview_release; eauto. }
        { eapply sim_local_write_fence_tview_normal; eauto.
          rewrite ORD. auto.
        }
      }
    }
    { ii. hexploit (MAXSRC loc). i. inv H. econs; eauto.
      { i. hexploit MAX; eauto. i. des. inv MAX0. esplits. econs; eauto. }
      { ii. inv H. eapply NONMAX; eauto. econs; eauto. }
    }
    { ii. hexploit (MAXTGT loc). i. inv H. econs; eauto.
      { i. hexploit MAX; eauto. i. des. inv MAX0. esplits. econs; eauto. }
    }
  }
  { econs. i. splits.
    { refl. }
    { rr. splits; ss. }
    { rr. splits; ss. }
  }
Qed.

Lemma sim_thread_fence_step_normal
      f flag_src flag_tgt vs_src0 vs_tgt0
      mem_src0 mem_tgt0 lc_src0 lc_tgt0 mem_tgt1
      lc_tgt1 ordr ordw
      (SIM: sim_thread
              f flag_src flag_tgt vs_src0 vs_tgt0
              mem_src0 mem_tgt0 lc_src0 lc_tgt0)
      (WRITE: Local.fence_step lc_tgt0 mem_tgt0 ordr ordw lc_tgt1 mem_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt0)
      (WF: Mapping.wfs f)
      (ACQFLAG: forall loc
                       (SRC: flag_src loc = false) (TGT: flag_tgt loc = true),
          ~ Ordering.le Ordering.acqrel ordr)
      (ORD: ~ Ordering.le Ordering.acqrel ordw)
  :
    exists lc_src1 mem_src1 vs_src1 vs_tgt1,
      (<<READ: Local.fence_step lc_src0 mem_src0 ordr ordw lc_src1 mem_src1>>) /\
      (<<SIM: sim_thread
                f flag_src flag_tgt vs_src1 vs_tgt1
                mem_src1 mem_tgt1 lc_src1 lc_tgt1>>) /\

      (<<VALS: forall loc0,
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>)) \/
          (exists val_src val_tgt,
              (<<NONESRC: vs_src0 loc0 = None>>) /\ (<<NONETGT: vs_tgt0 loc0 = None>>) /\
              (<<VALSRC: vs_src1 loc0 = Some val_src>>) /\ (<<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) /\
              (<<VALLE: Const.le val_tgt val_src>>) /\
              (<<ORD: Ordering.le Ordering.acqrel ordr \/ Ordering.le Ordering.seqcst ordw>>))>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) f mem_src0.(Global.memory) f mem_src1.(Global.memory)>>) /\
      (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f, mem_src0, mem_tgt0) (f, mem_src1, mem_tgt1)>>).
Proof.
  hexploit local_fence_step_split; eauto.
  { eapply LOCALTGT. }
  i. des.
  hexploit local_fence_read_step_future; eauto. i. des.
  hexploit sim_thread_read_fence_step; eauto.
  { i. destruct ordw; ss. }
  i. des.
  hexploit local_fence_read_step_future; eauto. i. des.
  hexploit sim_thread_write_fence_step; eauto.
  { i. destruct ordw; ss. }
  i. des. esplits; eauto.
  { eapply local_fence_step_merge; eauto. eapply LOCALSRC. }
  { inv READ0; ss. eapply space_future_memory_refl; eauto. refl. }
  { inv READ; ss. }
Qed.

Lemma sim_thread_fence_step_release
      f0 flag_src flag_tgt vs_src0 vs_tgt0
      mem_src0 mem_tgt0 lc_src0 lc_tgt0 mem_tgt1
      lc_tgt1 ordr ordw D
      (SIM: sim_thread
              f0 flag_src flag_tgt vs_src0 vs_tgt0
              mem_src0 mem_tgt0 lc_src0 lc_tgt0)
      (WRITE: Local.fence_step lc_tgt0 mem_tgt0 ordr ordw lc_tgt1 mem_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt0)
      (WF: Mapping.wfs f0)
      (ACQFLAG: forall loc
                       (SRC: flag_src loc = false) (TGT: flag_tgt loc = true),
          ~ Ordering.le Ordering.acqrel ordr)
      (RELFLAG: forall loc
                       (SRC: flag_src loc = false) (TGT: flag_tgt loc = true),
          ~ Ordering.le Ordering.seqcst ordw)
      (DEBT: forall loc, (<<DEBT: D loc>>) \/
                         ((<<FLAG: flag_src loc = false -> flag_tgt loc = false>>) /\
                          (<<VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc) \/ flag_src loc = false>>)))
      lang st
  :
    exists lc_src1 lc_src2 mem_src1 vs_src1 vs_tgt1 f1 flag_tgt1 mem_src2,
      (<<READ: Local.fence_step lc_src0 mem_src0 ordr ordw lc_src1 mem_src1>>) /\
      (<<STEPS: rtc (@Thread.internal_step _)
                    (Thread.mk lang st lc_src1 mem_src1)
                    (Thread.mk _ st lc_src2 mem_src2)>>) /\
      (<<SIM: sim_thread
                f1 (fun _ => false) flag_tgt1 vs_src1 vs_tgt1
                mem_src2 mem_tgt1 lc_src2 lc_tgt1>>) /\
      (<<VALS: forall loc0,
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>)) \/
          (exists val_src val_tgt,
              (<<NONESRC: vs_src0 loc0 = None>>) /\ (<<NONETGT: vs_tgt0 loc0 = None>>) /\
              (<<VALSRC: vs_src1 loc0 = Some val_src>>) /\ (<<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) /\
              (<<VALLE: Const.le val_tgt val_src>>) /\
              (<<ORD: Ordering.le Ordering.acqrel ordr \/ Ordering.le Ordering.seqcst ordw>>))>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<FLAG: forall loc, (<<DEBT: D loc>>) \/ (<<FLAG: flag_tgt1 loc = false>>)>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) f0 mem_src0.(Global.memory) f1 mem_src2.(Global.memory)>>) /\
      (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt0) (f1, mem_src2, mem_tgt1)>>)
.
Proof.
  hexploit local_fence_step_split; eauto.
  { eapply LOCALTGT. }
  i. des.
  hexploit local_fence_read_step_future; eauto. i. des.
  hexploit sim_thread_read_fence_step; eauto.
  i. des.
  hexploit local_fence_read_step_future; eauto. i. des.
  hexploit sim_thread_deflag_all; eauto.
  { i. hexploit (DEBT loc). i. des; eauto. right. esplits; eauto.
    hexploit (VALS loc). i. des.
    { rewrite SRC. rewrite TGT. auto. }
    { left. rewrite VALTGT. rewrite VALSRC. ss. }
    { left. rewrite VALTGT. rewrite VALSRC. ss. }
  }
  i. des. hexploit Thread.rtc_tau_step_future.
  { eapply rtc_implies; [|eauto]. i. inv H. econs; [econs 1; eauto|]. inv LOCAL1; ss. }
  { eauto. }
  { eauto. }
  i. des.
  hexploit sim_thread_write_fence_step; eauto.
  i. des. hexploit local_write_fence_step_promise_steps; eauto. i. des.
  esplits.
  { eapply local_fence_step_merge; eauto. eapply LOCALSRC. }
  { eauto. }
  { eauto. }
  { i. hexploit (VALS loc0). i. des; eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { inv READ0. inv STEP0. eauto. }
  { inv READ; ss. etrans; eauto.
    hexploit Thread.rtc_tau_step_promises_minus.
    { eapply rtc_implies; [|eapply STEPS]. i. inv H. econs; [econs 1; eauto|]. inv LOCAL1; ss. }
    i. ss. rewrite H. eauto.
  }
Qed.

Lemma write_max_readable_none
      lc0 mem0 loc from to val releasedm released ord lc1 mem1
      val0 released0
      (WRITE: Local.write_step lc0 mem0 loc from to val releasedm released ord lc1 mem1)
      (WF: Local.wf lc0 mem0)
      (MAX: max_readable mem0 lc0.(Local.promises) loc (lc0.(Local.tview).(TView.cur).(View.pln) loc) val0 released0)
  :
  max_readable mem1 lc1.(Local.promises) loc (lc1.(Local.tview).(TView.cur).(View.pln) loc) val released.
Proof.
  hexploit local_write_step_timestamp_pln; eauto.
  { eapply WF. }
  i. destruct lc0, lc1. ss; clarify.
  inv WRITE.
  hexploit Memory.add_get0; eauto. i. des. clarify.
  inv MAX. econs; eauto.
  { ss. inv FULFILL; eauto. inv REMOVE. inv GREMOVE.
    setoid_rewrite LocFun.add_spec_eq. ss.
  }
  i. ss. erewrite Memory.add_o in GET2; eauto. des_ifs.
  { ss. des; clarify. timetac. }
  { exfalso. hexploit MAX0; eauto. eapply TimeFacts.le_lt_lt; eauto.
    rewrite H2. ss. eapply Time.join_l.
  }
Qed.

Lemma writable_message_to tvw loc from to releasedm ord
      (WRITABLE: TView.writable (TView.cur tvw) loc to ord)
      (WF: TView.wf tvw)
      (TS: Time.lt from to)
      (MSG: Time.le (View.rlx (View.unwrap releasedm) loc) from)
  :
  Time.le (View.rlx (View.unwrap (TView.write_released tvw loc to releasedm ord)) loc) to.
Proof.
  assert (TIME: Time.le (View.rlx (View.unwrap releasedm) loc) to).
  { etrans; eauto. left. auto. }
  unfold TView.write_released. ss. des_ifs; ss.
  { eapply Time.join_spec; auto.
    setoid_rewrite LocFun.add_spec_eq.
    eapply Time.join_spec; auto; ss.
    { left. eapply WRITABLE. }
    { rewrite timemap_singleton_eq. refl. }
  }
  { eapply Time.join_spec; auto.
    setoid_rewrite LocFun.add_spec_eq.
    eapply Time.join_spec; auto; ss.
    { etrans.
      { eapply WF. }
      { left. eapply WRITABLE. }
    }
    { rewrite timemap_singleton_eq. refl. }
  }
  { eapply Time.bot_spec. }
Qed.

Lemma sim_thread_mapping_add
      loc ts_tgt
      f0 flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt
      (SIM: sim_thread
              f0 flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt)
      (WF: Mapping.wfs f0)
  :
  exists f1 ts_src,
      (<<SIM: sim_thread
                f1 flag_src flag_tgt vs_src vs_tgt
                mem_src mem_tgt lc_src lc_tgt>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les_strong f0 f1>>) /\
      (<<TS: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) ts_src ts_tgt>>)
.
Proof.
  hexploit (@mapping_add (f0 loc) ts_tgt); eauto. i. des.
  set (f' := (fun loc0 => if Loc.eq_dec loc0 loc then f1 else f0 loc0)).
  assert (LES: Mapping.les_strong f0 f').
  { unfold f'. ii. des_ifs. refl. }
  assert (LE: Mapping.les f0 f').
  { eapply Mapping.les_strong_les. auto. }
  assert (WF1: Mapping.wfs f').
  { unfold f'. ii. des_ifs. }
  exists f', fts. splits; auto.
  { eapply sim_thread_mon_strong; eauto. }
  { unfold f'. des_ifs. }
Qed.

Lemma space_future_memory_mon_map msgs f0 f1 f2 mem0 mem1
      (SPACE: space_future_memory msgs f1 mem0 f2 mem1)
      (MAP0: Mapping.les_strong f0 f1)
      (MAP1: Mapping.les f1 f2)
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wfs f1)
      (WF2: Mapping.wfs f2)
  :
  space_future_memory msgs f0 mem0 f2 mem1.
Proof.
  eapply space_future_memory_trans.
  2:{ eauto. }
  { eapply space_future_memory_refl; eauto. }
  { eapply Mapping.les_strong_les; auto. }
  { auto. }
  { auto. }
  { auto. }
  { auto. }
Qed.

Lemma sim_thread_write_aux
      f0 flag_src flag_tgt vs_src0 vs_tgt0
      mem_src0 mem_tgt0 lc_src0 lc_tgt0
      val_tgt val_src releasedm_tgt releasedm_src
      lc_tgt1 mem_tgt1 loc from_tgt to_tgt to_src from_src
      released_tgt ord
      (SIM: sim_thread
              f0 flag_src flag_tgt vs_src0 vs_tgt0
              mem_src0 mem_tgt0 lc_src0 lc_tgt0)
      (WRITE: Local.write_step lc_tgt0 mem_tgt0 loc from_tgt to_tgt val_tgt releasedm_tgt released_tgt ord lc_tgt1 mem_tgt1)
      (RELEASEDM: sim_opt_view (fun loc0 => loc0 <> loc) f0 (Some (Mapping.vers f0)) releasedm_src releasedm_tgt)
      (MSGTOTGT: Time.le (View.rlx (View.unwrap releasedm_tgt) loc) from_tgt)
      (TO: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) to_src (Some to_tgt))
      (FROM: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) from_src (Some from_tgt))
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt0)
      (WF: Mapping.wfs f0)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
      (VAL: Const.le val_tgt val_src)
      (ORD: ~ Ordering.le Ordering.acqrel ord)
      (ATOMIC: ~ Ordering.le ord Ordering.na)
      (WFSRC: View.opt_wf releasedm_src)
      (WFTGT: View.opt_wf releasedm_tgt)
      (CLOSEDMSRC: Memory.closed_opt_view releasedm_src mem_src0.(Global.memory))
      (CLOSEDMTGT: Memory.closed_opt_view releasedm_tgt mem_tgt0.(Global.memory))
      (NORACE: BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises) loc = false)
  :
  exists released_src lc_src1 vs_src1 vs_tgt1 mem_src1,
    (<<WRITE: Local.write_step lc_src0 mem_src0 loc from_src to_src val_src releasedm_src released_src ord lc_src1 mem_src1>>) /\
      (<<SIM: sim_thread
                f0 flag_src flag_tgt vs_src1 vs_tgt1
                mem_src1 mem_tgt1 lc_src1 lc_tgt1>>) /\
      (<<VALS: forall loc0,
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>) /\ (<<LOC: loc0 <> loc>>)) \/
            ((<<LOC: loc0 = loc>>) /\
               ((<<VALSRC: vs_src1 loc0 = Some val_src>> /\ <<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) \/
                  (<<VALSRC0: vs_src0 loc0 = None>> /\ <<VALTGT0: vs_tgt0 loc0 = None>> /\ <<VALSRC1: vs_src1 loc0 = None>> /\ <<VALTGT1: vs_tgt1 loc0 = None>>)))>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) f0 mem_src0.(Global.memory) f0 mem_src1.(Global.memory)>>) /\
      (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt0) (f0, mem_src1, mem_tgt1)>>)
.
Proof.
  hexploit Local.write_step_future; eauto.
  { etrans; eauto. inv WRITE. eapply add_succeed_wf in WRITE0. des. left. auto. }
  i. des.
  destruct lc_src0 as [tvw_src0 prom_src rsv_src].
  destruct lc_tgt0 as [tvw_tgt0 prom_tgt rsv_tgt].
  dup SIM. inv SIM. inv LOCAL. inv MEM. dup WRITE. guardH WRITE. inv WRITE. ss.
  inv FULFILL; ss.
  set (msg_src := Message.message val_tgt (TView.write_released tvw_tgt0 loc to_tgt releasedm_tgt ord) false).
  assert (SIMMSG: sim_message loc f0 (Some (Mapping.vers f0))
                              (Message.message val_src (TView.write_released tvw_src0 loc to_src releasedm_src ord) (Ordering.le ord Ordering.na))
                              (Message.message val_tgt (TView.write_released tvw_tgt0 loc to_tgt releasedm_tgt ord) (Ordering.le ord Ordering.na))).
  { clear WRITE0. econs; auto.
    eapply sim_write_released_normal; eauto.
    { refl. }
  }
  assert (WRITABLE0: TView.writable (TView.cur tvw_src0) loc to_src ord).
  { eapply sim_writable; eauto.
    { inv TVIEW. eauto. }
    { ss. }
  }
  hexploit sim_memory_add; eauto.
  { econs; eauto. eapply TViewFacts.write_future0; eauto. eapply LOCALSRC. }
  i. des.
  set (tvw_src1 := TView.write_tview tvw_src0 loc to_src ord).
  set (tvw_tgt1 := TView.write_tview tvw_tgt0 loc to_tgt ord).
  assert (exists released_src,
             (<<WRITE: Local.write_step (Local.mk tvw_src0 prom_src rsv_src) (Global.mk sc_src gprm_src mem_src) loc from_src
                                        to_src val_src releasedm_src released_src ord (Local.mk tvw_src1 prom_src rsv_src) (Global.mk sc_src gprm_src mem_src1)>>) /\
               (<<LOCAL: sim_local f0 flag_src flag_tgt tvw_src1.(TView.cur).(View.rlx) (Local.mk tvw_src1 prom_src rsv_src) (Local.mk (TView.write_tview tvw_tgt0 loc to_tgt ord) prom_tgt rsv_tgt)>>)).
  { esplits.
    { econs; eauto. }
    { ss. econs; eauto.
      { eapply sim_write_tview_normal; eauto. }
      { i. ss. unfold TimeMap.join. rewrite FLAGSRC0; ss. }
    }
  }
  des.
  hexploit max_value_src_exists. i. des.
  set (vs_src1 := fun loc0 => if Loc.eq_dec loc0 loc then v else vs_src0 loc0).
  set (vs_tgt1 := fun loc0 => if Loc.eq_dec loc0 loc then match v with
                                                          | Some _ => Some val_tgt
                                                          | None => None
                                                          end else vs_tgt0 loc0).
  assert (MEM1: sim_memory (boolmap_plus flag_src flag_tgt) (BoolMap.minus gprm_src prom_src) f0 mem_src1 mem2).
  { eapply add_sim_memory; eauto. }
  assert (PLNTS: forall loc0 (NEQ: loc0 <> loc), View.pln (TView.cur tvw_src1) loc0 = View.pln (TView.cur tvw_src0) loc0).
  { i. ss. unfold TimeMap.join. rewrite timemap_singleton_neq; auto.
    rewrite TimeFacts.le_join_l; auto. eapply Time.bot_spec.
  }
  assert (RLXTS: forall loc0 (NEQ: loc0 <> loc), View.rlx (TView.cur tvw_src1) loc0 = View.rlx (TView.cur tvw_src0) loc0).
  { i. ss. unfold TimeMap.join. rewrite timemap_singleton_neq; auto.
    rewrite TimeFacts.le_join_l; auto. eapply Time.bot_spec.
  }
  esplits.
  { eauto. }
  { econs.
    { econs; eauto. }
    { eauto. }
    { instantiate (1:=vs_src1). ii. unfold vs_src1.
      clear WRITE0. des_ifs.
      { eauto. }
      { specialize (MAXSRC loc0). inv MAXSRC. econs.
        { i. hexploit MAX0; eauto. i. des. esplits; eauto. rewrite PLNTS; eauto.
          eapply add_unchanged_loc in ADD; eauto. des.
          erewrite <- unchanged_loc_max_readable; eauto.
          { econs; eauto; ss. }
          { refl. }
        }
        { rewrite PLNTS; eauto. i.
          eapply add_unchanged_loc in ADD; eauto. des.
          erewrite <- unchanged_loc_max_readable; eauto.
          { econs; eauto; ss. }
          { refl. }
        }
      }
    }
    { instantiate (1:=vs_tgt1). ii. unfold vs_tgt1. condtac.
      { econs. i. destruct v; ss. subst. inv VAL0.
        hexploit no_flag_max_value_same; eauto.
        { ss. }
        i. des. inv MAX0. hexploit MAX1; auto. i. des.
        eapply write_max_readable in WRITE0; eauto.
        des. subst. esplits; eauto.
      }
      { assert (TS: View.pln (TView.cur (tvw_tgt1)) loc0 = View.pln (TView.cur tvw_tgt0) loc0).
        { ss. unfold TimeMap.join. rewrite timemap_singleton_neq; auto.
          rewrite TimeFacts.le_join_l; auto. eapply Time.bot_spec.
        }
        specialize (MAXTGT loc0). inv MAXTGT. econs. i. hexploit MAX0; eauto.
        i. des. esplits. rewrite TS.
        eapply add_unchanged_loc in WRITE1; eauto. des.
        erewrite <- unchanged_loc_max_readable; eauto.
        { econs; eauto; ss. }
        { refl. }
      }
    }
    { unfold vs_src1, vs_tgt1. i. clear WRITE0. des_ifs. }
    { eauto. }
    { unfold vs_src1. i. ss. destruct (LocSet.Facts.eq_dec loc0 loc); subst.
      { rewrite FLAG in *. ss. }
      { unfold TimeMap.join. rewrite TimeFacts.le_join_l.
        { rewrite <- SRCTM. eapply max_memory_val_add; eauto. }
        { rewrite timemap_singleton_neq; auto. eapply Time.bot_spec. }
      }
    }
    { unfold vs_src1. i. destruct (LocSet.Facts.eq_dec loc0 loc); subst; auto. }
  }
  { i. unfold vs_src1, vs_tgt1. clear WRITE0. des_ifs.
    { right. splits; auto. left. splits; auto. f_equal.
      inv MAX. hexploit MAX0; eauto. i. des.
      eapply write_max_readable in WRITE; eauto. des; auto.
    }
    { right. splits; auto. right.
      assert (NONE: vs_src0 loc = None).
      { destruct (vs_src0 loc) eqn:SOME; auto.
        specialize (MAXSRC loc). inv MAXSRC. hexploit MAX0; eauto.
        i. des. eapply write_max_readable_none in WRITE; eauto.
        inv MAX. exfalso. eapply NONMAX0; eauto.
      }
      splits; auto. specialize (PERM loc).
      rewrite NONE in PERM. destruct (vs_tgt0 loc); ss.
    }
    { left. auto. }
  }
  { eapply space_future_memory_mon_msgs.
    { eapply add_space_future_memory; eauto. }
    { eapply unchangable_messages_of_memory. }
  }
  { econs. i; ss. splits.
    { refl. }
    { rr. splits; ss. eapply add_other_owned_future; eauto.
      ii. subst. rewrite OWN in *. ss.
    }
    { rr. splits; ss. eapply add_other_owned_future; eauto.
      ii. subst. rewrite OWN in *. ss.
    }
  }
Qed.

Lemma sim_thread_write_step_normal_aux
      f0 flag_src flag_tgt vs_src0 vs_tgt0
      mem_src0 mem_tgt0 lc_src0 lc_tgt0
      val_tgt val_src
      lc_tgt1 mem_tgt1 loc from_tgt to_tgt
      released_tgt ord
      (SIM: sim_thread
              f0 flag_src flag_tgt vs_src0 vs_tgt0
              mem_src0 mem_tgt0 lc_src0 lc_tgt0)
      (WRITE: Local.write_step lc_tgt0 mem_tgt0 loc from_tgt to_tgt val_tgt None released_tgt ord lc_tgt1 mem_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt0)
      (WF: Mapping.wfs f0)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
      (VAL: Const.le val_tgt val_src)
      (ORD: ~ Ordering.le Ordering.acqrel ord)
      (ATOMIC: ~ Ordering.le ord Ordering.na)
      (NORACE: BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises) loc = false)
  :
  exists f1 released_src lc_src1 vs_src1 vs_tgt1 mem_src1 from_src to_src,
    (<<WRITE: Local.write_step lc_src0 mem_src0 loc from_src to_src val_src None released_src ord lc_src1 mem_src1>>) /\
      (<<SIM: sim_thread
                f1 flag_src flag_tgt vs_src1 vs_tgt1
                mem_src1 mem_tgt1 lc_src1 lc_tgt1>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les_strong f0 f1>>) /\
      (<<VALS: forall loc0,
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>) /\ (<<LOC: loc0 <> loc>>)) \/
            ((<<LOC: loc0 = loc>>) /\
               ((<<VALSRC: vs_src1 loc0 = Some val_src>> /\ <<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) \/
                  (<<VALSRC0: vs_src0 loc0 = None>> /\ <<VALTGT0: vs_tgt0 loc0 = None>> /\ <<VALSRC1: vs_src1 loc0 = None>> /\ <<VALTGT1: vs_tgt1 loc0 = None>>)))>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) f0 mem_src0.(Global.memory) f1 mem_src1.(Global.memory)>>) /\
      (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt0) (f1, mem_src1, mem_tgt1)>>).
Proof.
  hexploit (@sim_thread_mapping_add loc (Some from_tgt)); eauto. i. des.
  hexploit (@sim_thread_mapping_add loc (Some to_tgt)); eauto. i. des.
  hexploit sim_thread_write_aux; eauto.
  { econs. }
  { eapply Time.bot_spec. }
  { eapply sim_timestamp_exact_mon_strong; [..|eapply TS]; eauto. }
  i. des. esplits; eauto.
  { etrans; eauto. }
  { eapply space_future_memory_mon_map; eauto.
    { etrans; eauto. }
    { refl. }
  }
  { etrans; eauto. econs. i; splits.
    { etrans; eauto. }
    { refl. }
    { refl. }
  }
Qed.

Lemma sim_thread_write_step_normal
      f0 flag_src flag_tgt vs_src0 vs_tgt0
      mem_src0 mem_tgt0 lc_src0 lc_tgt0
      val_tgt val_src
      lc_tgt1 mem_tgt1 loc from_tgt to_tgt
      released_tgt ord
      (SIM: sim_thread
              f0 flag_src flag_tgt vs_src0 vs_tgt0
              mem_src0 mem_tgt0 lc_src0 lc_tgt0)
      (WRITE: Local.write_step lc_tgt0 mem_tgt0 loc from_tgt to_tgt val_tgt None released_tgt ord lc_tgt1 mem_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt0)
      (WF: Mapping.wfs f0)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
      (VAL: Const.le val_tgt val_src)
      (ORD: ~ Ordering.le Ordering.acqrel ord)
      (ATOMIC: ~ Ordering.le ord Ordering.na)
  :
  (<<RACE: Local.racy_write_step lc_src0 mem_src0 loc None ord>>) \/
  exists f1 released_src lc_src1 vs_src1 vs_tgt1 mem_src1 from_src to_src,
    (<<WRITE: Local.write_step lc_src0 mem_src0 loc from_src to_src val_src None released_src ord lc_src1 mem_src1>>) /\
      (<<SIM: sim_thread
                f1 flag_src flag_tgt vs_src1 vs_tgt1
                mem_src1 mem_tgt1 lc_src1 lc_tgt1>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les_strong f0 f1>>) /\
      (<<VALS: forall loc0,
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>) /\ (<<LOC: loc0 <> loc>>)) \/
            ((<<LOC: loc0 = loc>>) /\
               ((<<VALSRC: vs_src1 loc0 = Some val_src>> /\ <<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) \/
                  (<<VALSRC0: vs_src0 loc0 = None>> /\ <<VALTGT0: vs_tgt0 loc0 = None>> /\ <<VALSRC1: vs_src1 loc0 = None>> /\ <<VALTGT1: vs_tgt1 loc0 = None>>)))>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) f0 mem_src0.(Global.memory) f1 mem_src1.(Global.memory)>>) /\
      (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt0) (f1, mem_src1, mem_tgt1)>>).
Proof.
  destruct (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises) loc) eqn:RACE.
  { left. econs.
    unfold BoolMap.minus, andb, negb in RACE.
    destruct (Global.promises mem_src0 loc) eqn:EQG, (Local.promises lc_src0 loc) eqn:EQL; ss.
    econs 1; eauto.
  }
  right. eapply sim_thread_write_step_normal_aux; eauto.
Qed.

Lemma sim_thread_write_update_normal
      f0 flag_src flag_tgt vs_src0 vs_tgt0
      mem_src0 mem_tgt0 lc_src0 lc_tgt0
      val_tgt val_src releasedm_tgt releasedm_src
      lc_tgt1 mem_tgt1 loc from_tgt to_tgt from_src
      released_tgt ord
      (SIM: sim_thread
              f0 flag_src flag_tgt vs_src0 vs_tgt0
              mem_src0 mem_tgt0 lc_src0 lc_tgt0)
      (WRITE: Local.write_step lc_tgt0 mem_tgt0 loc from_tgt to_tgt val_tgt releasedm_tgt released_tgt ord lc_tgt1 mem_tgt1)
      (RELEASEDM: sim_opt_view (fun loc0 => loc0 <> loc) f0 (Some (Mapping.vers f0)) releasedm_src releasedm_tgt)
      (MSGTOTGT: Time.le (View.rlx (View.unwrap releasedm_tgt) loc) from_tgt)
      (FROM: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) from_src (Some from_tgt))
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt0)
      (WF: Mapping.wfs f0)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
      (VAL: Const.le val_tgt val_src)
      (ORD: ~ Ordering.le Ordering.acqrel ord)
      (ATOMIC: ~ Ordering.le ord Ordering.na)
      (WFSRC: View.opt_wf releasedm_src)
      (WFTGT: View.opt_wf releasedm_tgt)
      (CLOSEDMSRC: Memory.closed_opt_view releasedm_src mem_src0.(Global.memory))
      (CLOSEDMTGT: Memory.closed_opt_view releasedm_tgt mem_tgt0.(Global.memory))
      (NORACE: BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises) loc = false)
  :
  exists f1 released_src lc_src1 vs_src1 vs_tgt1 mem_src1 to_src,
    (<<WRITE: Local.write_step lc_src0 mem_src0 loc from_src to_src val_src releasedm_src released_src ord lc_src1 mem_src1>>) /\
      (<<SIM: sim_thread
                f1 flag_src flag_tgt vs_src1 vs_tgt1
                mem_src1 mem_tgt1 lc_src1 lc_tgt1>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les_strong f0 f1>>) /\
      (<<VALS: forall loc0,
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>) /\ (<<LOC: loc0 <> loc>>)) \/
            ((<<LOC: loc0 = loc>>) /\
               ((<<VALSRC: vs_src1 loc0 = Some val_src>> /\ <<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) \/
                  (<<VALSRC0: vs_src0 loc0 = None>> /\ <<VALTGT0: vs_tgt0 loc0 = None>> /\ <<VALSRC1: vs_src1 loc0 = None>> /\ <<VALTGT1: vs_tgt1 loc0 = None>>)))>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) f0 mem_src0.(Global.memory) f1 mem_src1.(Global.memory)>>) /\
      (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt0) (f1, mem_src1, mem_tgt1)>>)
.
Proof.
  hexploit (@sim_thread_mapping_add loc (Some to_tgt)); eauto. i. des.
  eapply sim_opt_view_mon_mapping_latest in RELEASEDM; eauto.
  2:{ eapply Mapping.les_strong_les; eauto. }
  hexploit sim_thread_write_aux; eauto.
  { eapply sim_timestamp_exact_mon_strong; eauto. }
  i. des. esplits; eauto.
  { eapply space_future_memory_mon_map; eauto. refl. }
  { etrans; eauto. econs. i; splits.
    { eauto. }
    { refl. }
    { refl. }
  }
Qed.

Definition local_write_sync_tview (tview1: TView.t) (loc: Loc.t) (ord: Ordering.t): TView.t :=
  TView.mk
    (if Ordering.le Ordering.acqrel ord
     then fun loc0 =>
            if (Loc.eq_dec loc0 loc)
            then tview1.(TView.cur)
            else tview1.(TView.rel) loc0
     else tview1.(TView.rel))
    (tview1.(TView.cur))
    (tview1.(TView.acq)).

Lemma local_write_sync_tview_wf tview loc ord
      (WF: TView.wf tview)
  :
  TView.wf (local_write_sync_tview tview loc ord).
Proof.
  econs; ss; i; des_ifs; try by (eapply WF). refl.
Qed.

Lemma local_write_sync_tview_closed mem tview loc ord
      (TVIEW: TView.closed tview mem)
  :
  TView.closed (local_write_sync_tview tview loc ord) mem.
Proof.
  unfold local_write_sync_tview.
  econs; i; ss; des_ifs; try by (eapply TVIEW).
Qed.

Lemma local_write_sync_tview_incr tview loc ord
      (WF: TView.wf tview)
  :
    TView.le tview (local_write_sync_tview tview loc ord).
Proof.
  econs; ss.
  { i. des_ifs.
    { unfold LocFun.find. des_ifs.
      { eapply WF. }
      { refl. }
    }
    { refl. }
  }
  { refl. }
  { refl. }
Qed.

Variant local_write_sync_step lc1 loc ord lc2: Prop :=
| local_write_sync_step_intro
    (LOCAL: lc2 = Local.mk
                    (local_write_sync_tview lc1.(Local.tview) loc ord)
                    (lc1.(Local.promises)) (lc1.(Local.reserves)))
.

Definition non_sync_ord (ord: Ordering.t): Ordering.t :=
  if Ordering.le Ordering.relaxed ord then Ordering.relaxed else ord.

Lemma local_write_sync_tview_merge tvw loc ord to
  :
  TView.write_tview (local_write_sync_tview tvw loc ord) loc to (non_sync_ord ord) = TView.write_tview tvw loc to ord.
Proof.
  unfold TView.write_tview. f_equal.
  unfold LocFun.add, LocFun.find. extensionality loc0.
  ss. des_ifs. destruct ord; ss.
Qed.

Lemma local_write_released_merge tvw loc ord to releasedm
  :
  TView.write_released (local_write_sync_tview tvw loc ord) loc to releasedm (non_sync_ord ord) = TView.write_released tvw loc to releasedm ord.
Proof.
  unfold TView.write_released. des_ifs.
  { f_equal. f_equal. rewrite local_write_sync_tview_merge. auto. }
  { destruct ord; ss. }
  { destruct ord; ss. }
Qed.

Lemma local_write_step_merge
      lc0 mem0 loc from to val releasedm released ord lc1 mem1 lc2
      (STEP0: local_write_sync_step lc0 loc ord lc1)
      (STEP1: Local.write_step lc1 mem0 loc from to val releasedm released (non_sync_ord ord) lc2 mem1)
  :
  Local.write_step lc0 mem0 loc from to val releasedm released ord lc2 mem1.
Proof.
  inv STEP0. inv STEP1. ss. econs; ss; eauto.
  { eapply local_write_released_merge; eauto. }
  { inv WRITABLE. econs; eauto. }
  { instantiate (1:=prm2). inv FULFILL; eauto. econs 2; eauto.
    destruct ord; ss.
  }
  { replace (Ordering.le ord Ordering.na) with (Ordering.le (non_sync_ord ord) Ordering.na); auto.
    destruct ord; ss.
  }
  { f_equal. eapply local_write_sync_tview_merge; auto. }
Qed.

Lemma local_write_step_split
      lc0 mem0 loc from to val releasedm released ord mem1 lc2
      (STEP: Local.write_step lc0 mem0 loc from to val releasedm released ord lc2 mem1)
  :
  exists lc1,
    (<<STEP0: local_write_sync_step lc0 loc ord lc1>>) /\
    (<<STEP1: Local.write_step lc1 mem0 loc from to val releasedm released (non_sync_ord ord) lc2 mem1>>).
Proof.
  inv STEP. esplits.
  { econs; eauto. }
  { econs; ss; eauto.
    { symmetry. apply local_write_released_merge. }
    { inv WRITABLE. econs; auto. }
    { instantiate (1:=prm2). inv FULFILL; eauto. econs 2; eauto.
      destruct ord; ss.
    }
    { replace (Ordering.le ord Ordering.na) with (Ordering.le (non_sync_ord ord) Ordering.na) in WRITE; auto.
      destruct ord; ss.
    }
    { f_equal. symmetry. apply local_write_sync_tview_merge. }
  }
Qed.

Lemma local_write_sync_step_future lc1 loc ord lc2 mem
      (STEP: local_write_sync_step lc1 loc ord lc2)
      (LOCAL: Local.wf lc1 mem)
  :
    (<<LOCAL: Local.wf lc2 mem>>) /\
    (<<INCR: TView.le lc1.(Local.tview) lc2.(Local.tview)>>).
Proof.
  inv STEP. splits.
  { inv LOCAL. econs; ss.
    { eapply local_write_sync_tview_wf; eauto. }
    { eapply local_write_sync_tview_closed; eauto. }
  }
  { eapply local_write_sync_tview_incr. eapply LOCAL. }
Qed.

Lemma sim_write_sync_tview_normal f flag_src tvw_src tvw_tgt
      loc ord
      (SIM: sim_tview f flag_src tvw_src tvw_tgt)
      (WF: Mapping.wfs f)
      (ORD: ~ Ordering.le Ordering.acqrel ord)
  :
  sim_tview f flag_src (local_write_sync_tview tvw_src loc ord) (local_write_sync_tview tvw_tgt loc ord).
Proof.
  unfold local_write_sync_tview. econs; ss.
  { des_ifs. i. eapply SIM. }
  { eapply SIM. }
  { eapply SIM. }
Qed.

Lemma sim_write_sync_tview_release f flag_src tvw_src tvw_tgt
      loc ord
      (SIM: sim_tview f flag_src tvw_src tvw_tgt)
      (FLAG: forall loc, flag_src loc = false)
      (WF: Mapping.wfs f)
  :
  sim_tview f flag_src (local_write_sync_tview tvw_src loc ord) (local_write_sync_tview tvw_tgt loc ord).
Proof.
  pose proof (mapping_latest_wf f) as VERWF.
  unfold local_write_sync_tview. econs; ss.
  { i. des_ifs.
    { eapply sim_view_mon_locs.
      { eapply SIM. }
      i. ss.
    }
    { eapply sim_view_mon_ver; [eapply SIM|..]; eauto. }
    { eapply SIM. }
  }
  { eapply SIM. }
  { eapply SIM. }
Qed.

Lemma sim_thread_write_sync_step
      f flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src0 lc_tgt0
      lc_tgt1 loc ord
      (SIM: sim_thread
              f flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src0 lc_tgt0)
      (WRITE: local_write_sync_step lc_tgt0 loc ord lc_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt)
      (MEMSRC: Global.wf mem_src)
      (MEMTGT: Global.wf mem_tgt)
      (WF: Mapping.wfs f)
      (RELFLAG: forall loc (ORD: Ordering.le Ordering.acqrel ord), flag_src loc = false)
      (ATOMIC: ~ Ordering.le ord Ordering.na)
  :
    exists lc_src1,
      (<<READ: local_write_sync_step lc_src0 loc ord lc_src1>>) /\
      (<<SIM: sim_thread
                f flag_src flag_tgt vs_src vs_tgt
                mem_src mem_tgt lc_src1 lc_tgt1>>)
.
Proof.
  hexploit local_write_sync_step_future; eauto. i. des.
  esplits.
  { econs; eauto. }
  inv SIM. inv WRITE. econs; eauto.
  { inv LOCAL0. ss.
    destruct (Ordering.le Ordering.acqrel ord) eqn:ORD.
    { econs; eauto.
      { eapply sim_write_sync_tview_release; eauto. }
    }
    { econs; eauto. eapply sim_write_sync_tview_normal; eauto.
      destruct ord; ss.
    }
  }
  { ii. hexploit (MAXSRC loc0). i. inv H. econs; ss. }
  { eapply max_values_tgt_mon; eauto. }
Qed.

Lemma sim_thread_write_step_release
      f0 flag_src flag_tgt0 vs_src0 vs_tgt0
      mem_src0 mem_tgt0 lc_src0 lc_tgt0
      val_tgt val_src
      lc_tgt1 mem_tgt1 loc from_tgt to_tgt
      released_tgt ord D
      (SIM: sim_thread
              f0 flag_src flag_tgt0 vs_src0 vs_tgt0
              mem_src0 mem_tgt0 lc_src0 lc_tgt0)
      (WRITE: Local.write_step lc_tgt0 mem_tgt0 loc from_tgt to_tgt val_tgt None released_tgt ord lc_tgt1 mem_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt0)
      (WF: Mapping.wfs f0)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt0 loc = false)
      (VAL: Const.le val_tgt val_src)
      (DEBT: forall loc, (<<DEBT: D loc>>) \/
                           ((<<FLAG: flag_src loc = false -> flag_tgt0 loc = false>>) /\
                            (<<VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc) \/ flag_src loc = false>>)))
      (ATOMIC: ~ Ordering.le ord Ordering.na)
lang st
  :
  (<<RACE: Local.racy_write_step lc_src0 mem_src0 loc None ord>>) \/
  exists f1 released_src lc_src1 lc_src2 vs_src1 vs_tgt1 mem_src1 mem_src2 from_src to_src flag_tgt1,
    (<<STEPS: rtc (@Thread.internal_step _)
                    (Thread.mk lang st lc_src0 mem_src0)
                    (Thread.mk _ st lc_src1 mem_src1)>>) /\
      (<<WRITE: Local.write_step lc_src1 mem_src1 loc from_src to_src val_src None released_src ord lc_src2 mem_src2>>) /\
      (<<SIM: sim_thread
                f1 (fun _ => false) flag_tgt1 vs_src1 vs_tgt1
                mem_src2 mem_tgt1 lc_src2 lc_tgt1>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<VALS: forall loc0,
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>) /\ (<<LOC: loc0 <> loc>>)) \/
            ((<<LOC: loc0 = loc>>) /\
               ((<<VALSRC: vs_src1 loc0 = Some val_src>> /\ <<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) \/
                  (<<VALSRC0: vs_src0 loc0 = None>> /\ <<VALTGT0: vs_tgt0 loc0 = None>> /\ <<VALSRC1: vs_src1 loc0 = None>> /\ <<VALTGT1: vs_tgt1 loc0 = None>>)))>>) /\
      (<<FLAG: forall loc, (<<DEBT: D loc>>) \/ (<<FLAG: flag_tgt1 loc = false>>)>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) f0 mem_src0.(Global.memory) f1 mem_src2.(Global.memory)>>) /\
      (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt0) (f1, mem_src2, mem_tgt1)>>)
.
Proof.
  destruct (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises) loc) eqn:RACE.
  { left. econs.
    unfold BoolMap.minus, andb, negb in RACE.
    destruct (Global.promises mem_src0 loc) eqn:EQG, (Local.promises lc_src0 loc) eqn:EQL; ss.
    econs 1; eauto.
  }
  right.
  hexploit (@sim_thread_deflag_all (fun loc0 => D loc0 /\ loc0 <> loc)); eauto.
  { i. hexploit (DEBT loc0). i. des; auto.
    destruct (Loc.eq_dec loc0 loc); auto. subst. right. splits; auto.
  }
  i. des.
  hexploit local_write_step_split; eauto. i. des.
  hexploit local_write_sync_step_future; eauto. i. des.
  hexploit Thread.rtc_tau_step_future.
  { eapply rtc_implies; [|eauto]. i. inv H. econs; [econs 1; eauto|]. inv LOCAL0; ss. }
  { eauto. }
  { eauto. }
  i. des. ss.
  hexploit sim_thread_write_sync_step; eauto.
  i. des.
  hexploit local_write_sync_step_future; eauto. i. des.
  hexploit sim_thread_write_step_normal_aux; eauto.
  { specialize (FLAG loc). des; ss. }
  { destruct ord; ss. }
  { destruct ord; ss. }
  { hexploit Thread.rtc_tau_step_promises_minus.
    { eapply rtc_implies; [|eapply STEPS]. i. inv H. econs; [econs 1; eauto|]. inv LOCAL1; ss. }
    inv READ. i. ss. rewrite H in RACE. auto.
  }
  i. des. esplits; eauto.
  { eapply local_write_step_merge; eauto. }
  { etrans; eauto. eapply Mapping.les_strong_les; eauto. }
  { i. specialize (FLAG loc0). des; auto. }
  { eapply space_future_memory_trans; eauto.
    { inv STEP0. auto. }
    { eapply Mapping.les_strong_les; eauto. }
  }
  { etrans; eauto.
    hexploit Thread.rtc_tau_step_promises_minus.
    { eapply rtc_implies; [|eapply STEPS]. i. inv H. econs; [econs 1; eauto|]. inv LOCAL1; ss. }
    i. ss. rewrite H. inv READ; auto.
  }
Qed.

Lemma sim_thread_update_step_normal
      f0 flag_src flag_tgt vs_src0 vs_tgt0
      mem_src0 mem_tgt0 lc_src0 lc_tgt0
      valr_tgt valw_tgt valw_src
      lc_tgt1 lc_tgt2 mem_tgt1 loc from_tgt to_tgt releasedm_tgt
      released_tgt ordr ordw
      (SIM: sim_thread
              f0 flag_src flag_tgt vs_src0 vs_tgt0
              mem_src0 mem_tgt0 lc_src0 lc_tgt0)
      (READ: Local.read_step lc_tgt0 mem_tgt0 loc from_tgt valr_tgt releasedm_tgt ordr lc_tgt1)
      (WRITE: Local.write_step lc_tgt1 mem_tgt0 loc from_tgt to_tgt valw_tgt releasedm_tgt released_tgt ordw lc_tgt2 mem_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt0)
      (WF: Mapping.wfs f0)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
      (FLAG: forall loc
                    (SRC: flag_src loc = false) (TGT: flag_tgt loc = true),
          ~ Ordering.le Ordering.acqrel ordr)
      (VAL: Const.le valw_tgt valw_src)
      (ORD: ~ Ordering.le Ordering.acqrel ordw)
      (ATOMIC: ~ Ordering.le ordw Ordering.na)
      (NORACE: forall to, ~ Local.is_racy lc_src0 mem_src0 loc to ordr)
  :
    exists f1 val_tgt1 val_src1 from_src to_src releasedm_src released_src mem_src1 lc_src1 lc_src2 vs_src1 vs_tgt1,
      (<<READ: forall val (VAL: Const.le val val_src1), Local.read_step lc_src0 mem_src0 loc from_src val releasedm_src ordr lc_src1>>) /\
      (<<WRITE: Local.write_step lc_src1 mem_src0 loc from_src to_src valw_src releasedm_src released_src ordw lc_src2 mem_src1>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les_strong f0 f1>>) /\
      (<<SIM: sim_thread
                f1 flag_src flag_tgt vs_src1 vs_tgt1
                mem_src1 mem_tgt1 lc_src2 lc_tgt2>>) /\
      (<<VAL: Const.le val_tgt1 val_src1>>) /\
      (<<VALTGT: Const.le valr_tgt val_tgt1>>) /\
      (<<NUPDATESRC: forall val (VAL: vs_src0 loc = Some val), val = val_src1>>) /\
      (<<NUPDATETGT: forall val (VAL: vs_tgt0 loc = Some val), val = val_tgt1>>) /\
      (<<VALS: forall loc0 (LOC: loc0 <> loc),
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>)) \/
          (exists val_src val_tgt,
              (<<NONESRC: vs_src0 loc0 = None>>) /\ (<<NONETGT: vs_tgt0 loc0 = None>>) /\
              (<<VALSRC: vs_src1 loc0 = Some val_src>>) /\ (<<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) /\
              (<<VALLE: Const.le val_tgt val_src>>) /\
              (<<ORD: Ordering.le Ordering.acqrel ordr>>))>>) /\
      (<<UPDATED:
        __guard__(((<<SRC: vs_src1 loc = Some valw_src>>) /\ (<<TGT: vs_tgt1 loc = Some valw_tgt>>)) \/
        ((<<SRCNONE0: vs_src0 loc = None>>) /\ (<<TGTNONE0: vs_tgt0 loc = None>>) /\
         (<<SRCNONE1: vs_src1 loc = None>>) /\ (<<TGTNONE0: vs_tgt1 loc = None>>)))>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) f0 mem_src0.(Global.memory) f1 mem_src1.(Global.memory)>>) /\
      (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt0) (f1, mem_src1, mem_tgt1)>>)
.
Proof.
  hexploit Local.read_step_future; eauto. i. des.
  hexploit Local.write_step_future; eauto.
  { etrans; eauto. inv WRITE. eapply add_succeed_wf in WRITE0. des. left. auto. }
  i. des. ss.
  hexploit sim_thread_read; eauto.
  i. des.
  hexploit READ0.
  { refl. }
  intros READSRC.
  hexploit Local.read_step_future; eauto. i. des.
  hexploit sim_thread_write_update_normal; eauto.
  { inv READSRC. ss. unfold BoolMap.minus, andb, negb.
    destruct (Global.promises mem_src0 loc) eqn:EQG, (Local.promises lc_src0 loc) eqn:EQL; ss.
    exfalso. eapply NORACE. econs 1; eauto.
  }
  i. des. esplits; eauto.
  { i. hexploit (VALS loc0). hexploit (VALS0 loc0). i. des; subst; ss.
    { left. esplits; etrans; eauto. }
    { right. esplits; eauto.
      { rewrite SRC. auto. }
      { rewrite TGT. auto. }
    }
  }
  { red. specialize (VALS loc). specialize (VALS0 loc).
    des; ss; auto. right. splits; auto.
    { rewrite <- SRC. auto. }
    { rewrite <- TGT. auto. }
  }
  { inv READ. auto. }
  { inv READSRC; auto. }
Qed.

Lemma sim_thread_update_step_release
      f0 flag_src flag_tgt0 vs_src0 vs_tgt0
      mem_src0 mem_tgt0 lc_src0 lc_tgt0
      valr_tgt valw_tgt valw_src
      lc_tgt1 lc_tgt2 mem_tgt1 loc from_tgt to_tgt releasedm_tgt
      released_tgt ordr ordw D
      (SIM: sim_thread
              f0 flag_src flag_tgt0 vs_src0 vs_tgt0
              mem_src0 mem_tgt0 lc_src0 lc_tgt0)
      (READ: Local.read_step lc_tgt0 mem_tgt0 loc from_tgt valr_tgt releasedm_tgt ordr lc_tgt1)
      (WRITE: Local.write_step lc_tgt1 mem_tgt0 loc from_tgt to_tgt valw_tgt releasedm_tgt released_tgt ordw lc_tgt2 mem_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt0)
      (WF: Mapping.wfs f0)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt0 loc = false)
      (FLAG: forall loc
                    (SRC: flag_src loc = false) (TGT: flag_tgt0 loc = true),
          ~ Ordering.le Ordering.acqrel ordr)
      (DEBT: forall loc, (<<DEBT: D loc>>) \/
                           ((<<FLAG: flag_src loc = false -> flag_tgt0 loc = false>>) /\
                            (<<VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc) \/ flag_src loc = false>>)))
      (VAL: Const.le valw_tgt valw_src)
      (ATOMIC: ~ Ordering.le ordw Ordering.na)
      (NORACE: forall to, ~ Local.is_racy lc_src0 mem_src0 loc to ordr)
      lang st
  :
    exists val_src1 f1 val_tgt1 from_src to_src releasedm_src released_src mem_src1 mem_src2 lc_src1 lc_src2 lc_src3 vs_src1 vs_tgt1 flag_tgt1,
      (<<STEPS: rtc (@Thread.internal_step _)
                    (Thread.mk lang st lc_src0 mem_src0)
                    (Thread.mk _ st lc_src1 mem_src1)>>) /\
      (<<READ: forall val (VAL: Const.le val val_src1), Local.read_step lc_src1 mem_src1 loc from_src val releasedm_src ordr lc_src2>>) /\
      (<<WRITE: Local.write_step lc_src2 mem_src1 loc from_src to_src valw_src releasedm_src released_src ordw lc_src3 mem_src2>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<SIM: sim_thread
                f1 (fun _ => false) flag_tgt1 vs_src1 vs_tgt1
                mem_src2 mem_tgt1 lc_src3 lc_tgt2>>) /\
      (<<VAL: Const.le val_tgt1 val_src1>>) /\
      (<<VALTGT: Const.le valr_tgt val_tgt1>>) /\
      (<<NUPDATESRC: forall val (VAL: vs_src0 loc = Some val), val = val_src1>>) /\
      (<<NUPDATETGT: forall val (VAL: vs_tgt0 loc = Some val), val = val_tgt1>>) /\
      (<<VALS: forall loc0 (LOC: loc0 <> loc),
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>)) \/
          (exists val_src val_tgt,
              (<<NONESRC: vs_src0 loc0 = None>>) /\ (<<NONETGT: vs_tgt0 loc0 = None>>) /\
              (<<VALSRC: vs_src1 loc0 = Some val_src>>) /\ (<<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) /\
              (<<VALLE: Const.le val_tgt val_src>>) /\
              (<<ORD: Ordering.le Ordering.acqrel ordr>>))>>) /\
      (<<UPDATED:
        __guard__(((<<SRC: vs_src1 loc = Some valw_src>>) /\ (<<TGT: vs_tgt1 loc = Some valw_tgt>>)) \/
        ((<<SRCNONE0: vs_src0 loc = None>>) /\ (<<TGTNONE0: vs_tgt0 loc = None>>) /\
           (<<SRCNONE1: vs_src1 loc = None>>) /\ (<<TGTNONE0: vs_tgt1 loc = None>>)))>>) /\
      (<<FLAG: forall loc, (<<DEBT: D loc>>) \/ (<<FLAG: flag_tgt1 loc = false>>)>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) f0 mem_src0.(Global.memory) f1 mem_src2.(Global.memory)>>) /\
      (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt0) (f1, mem_src2, mem_tgt1)>>)
.
Proof.
  eapply local_write_step_split in WRITE. des.
  hexploit Local.read_step_future; eauto. i. des.
  hexploit local_write_sync_step_future; eauto. i. des.
  hexploit Local.write_step_future; eauto.
  { etrans; eauto. inv STEP1. eapply add_succeed_wf in WRITE. des. left. auto. }
  i. des. ss.
  hexploit sim_thread_read; eauto. i. des.
  hexploit READ0.
  { refl. }
  intros READSRC.
  hexploit Local.read_step_future; eauto. i. des.
  hexploit (@sim_thread_deflag_all (fun loc0 => D loc0 /\ loc0 <> loc)); eauto.
  { i. destruct (Loc.eq_dec loc0 loc).
    { right. subst. splits; auto. }
    hexploit (DEBT loc0). i. des; auto. right. splits; auto.
    hexploit (VALS loc0). i. des.
    { rewrite SRC. rewrite TGT. auto. }
    { left. rewrite VALTGT0. rewrite VALSRC. ss. }
    { left. rewrite VALTGT0. rewrite VALSRC. ss. }
  }
  i. des. hexploit Thread.rtc_tau_step_future.
  { eapply rtc_implies; [|eauto]. i. inv H. econs; [econs 1; eauto|]. inv LOCAL0; ss. }
  { eauto. }
  { eauto. }
  ss. i. des.
  hexploit sim_thread_write_sync_step; eauto.
  i. des.
  hexploit local_write_sync_step_future; eauto. i. des.
  assert (RELEASEDM: sim_opt_view (fun loc0 => loc0 <> loc) f1 (Some (Mapping.vers f1)) released_src releasedm_tgt).
  { eapply sim_opt_view_mon_mapping_latest; eauto. }
  hexploit sim_thread_write_update_normal; eauto.
  { eapply sim_timestamp_exact_mon_strong; eauto. }
  { specialize (FLAG0 loc). des; ss. }
  { destruct ordw; ss. }
  { destruct ordw; ss. }
  { inv GL_FUTURE0. eapply Memory.future_closed_opt_view; eauto. }
  { hexploit Thread.rtc_tau_step_promises_minus.
    { eapply rtc_implies; [|eapply STEPS]. i. inv H. econs; [econs 1; eauto|]. inv LOCAL1; ss. }
    i. ss. inv READ1. inv READSRC. ss.
    rewrite <- H. unfold BoolMap.minus, andb, negb.
    destruct (Global.promises mem_src0 loc) eqn:EQG, (Local.promises lc_src0 loc) eqn:EQL; ss.
    exfalso. eapply NORACE. econs 1; eauto.
  }
  i. des.
  hexploit promise_steps_local_read_step; eauto.
  i. des. exists val_src1. esplits; eauto.
  { inv READ2. i. econs; eauto. etrans; eauto. }
  { eapply local_write_step_merge; eauto. }
  { etrans; eauto. eapply Mapping.les_strong_les; eauto. }
  { i. hexploit (VALS loc0). hexploit (VALS0 loc0). i. des; subst; ss.
    { left. esplits; etrans; eauto. }
    { right. esplits; eauto.
      { rewrite SRC. auto. }
      { rewrite TGT. auto. }
    }
  }
  { red. specialize (VALS loc). specialize (VALS0 loc).
    des; ss; auto. right. splits; auto.
    { rewrite <- SRC. auto. }
    { rewrite <- TGT. auto. }
  }
  { i. specialize (FLAG0 loc0). des; auto. }
  { eapply space_future_memory_trans.
    { inv READ. eauto. }
    { inv READ. inv STEP0. eauto. }
    { eauto. }
    { eapply Mapping.les_strong_les; eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
  }
  { hexploit Thread.rtc_tau_step_promises_minus.
    { eapply rtc_implies; [|eapply STEPS]. i. inv H. econs; [econs 1; eauto|]. inv LOCAL1; ss. }
    i. ss. inv READ1. inv READSRC. ss. etrans; eauto.
    rewrite H. auto.
  }
Qed.

(* Lemma semi_closed_timemap_closed *)
(*       tm mem loc ts *)
(*       (SEMI: semi_closed_timemap tm mem loc ts) *)
(*       (CLOSED: exists from val released, Memory.get loc ts mem = Some (from, Message.concrete val released)) *)
(*   : *)
(*   Memory.closed_timemap tm mem. *)
(* Proof. *)
(*   ii. exploit SEMI. i. des; eauto. *)
(*   subst. esplits; eauto. *)
(* Qed. *)

(* Lemma semi_closed_view_closed *)
(*       vw mem loc ts *)
(*       (SEMI: semi_closed_view vw mem loc ts) *)
(*       (CLOSED: exists from val released, Memory.get loc ts mem = Some (from, Message.concrete val released)) *)
(*   : *)
(*   Memory.closed_view vw mem. *)
(* Proof. *)
(*   econs. *)
(*   { eapply semi_closed_timemap_closed; eauto. eapply SEMI. } *)
(*   { eapply semi_closed_timemap_closed; eauto. eapply SEMI. } *)
(* Qed. *)

(* Lemma semi_closed_opt_view_closed *)
(*       vw mem loc ts *)
(*       (SEMI: semi_closed_opt_view vw mem loc ts) *)
(*       (CLOSED: exists from val released, Memory.get loc ts mem = Some (from, Message.concrete val released)) *)
(*   : *)
(*   Memory.closed_opt_view vw mem. *)
(* Proof. *)
(*   inv SEMI; econs. *)
(*   eapply semi_closed_view_closed; eauto. *)
(* Qed. *)

(* Lemma semi_closed_message_closed *)
(*       msg mem loc ts *)
(*       (SEMI: semi_closed_message msg mem loc ts) *)
(*       (CLOSED: forall val released (MSG: msg = Message.concrete val released), *)
(*         exists from val released, Memory.get loc ts mem = Some (from, Message.concrete val released)) *)
(*   : *)
(*   Memory.closed_message msg mem. *)
(* Proof. *)
(*   inv SEMI; econs. *)
(*   eapply semi_closed_opt_view_closed; eauto. *)
(* Qed. *)

(* Lemma sim_thread_promise_step *)
(*       f0 vers0 flag_src flag_tgt vs_src vs_tgt *)
(*       mem_src0 mem_tgt0 lc_src0 lc_tgt0 *)
(*       lc_tgt1 mem_tgt1 loc from_tgt to_tgt *)
(*       msg_tgt kind_tgt *)
(*       (SIM: sim_thread *)
(*               f0 vers0 flag_src flag_tgt vs_src vs_tgt *)
(*               mem_src0 mem_tgt0 lc_src0 lc_tgt0) *)
(*       (PROMISE: Local.promise_step lc_tgt0 mem_tgt0 loc from_tgt to_tgt msg_tgt lc_tgt1 mem_tgt1 kind_tgt) *)
(*       (CONSISTENT: Local.promise_consistent lc_tgt1) *)
(*       (LOCALSRC: Local.wf lc_src0 mem_src0) *)
(*       (LOCALTGT: Local.wf lc_tgt0 mem_tgt0) *)
(*       (MEMSRC: Memory.closed mem_src0) *)
(*       (MEMTGT: Memory.closed mem_tgt0) *)
(*       (SCSRC: Memory.closed_timemap sc_src mem_src0) *)
(*       (SCTGT: Memory.closed_timemap sc_tgt mem_tgt0) *)
(*       (WF: Mapping.wfs f0) *)
(*       (VERS: versions_wf f0 vers0) *)
(*       (FLAGSRC: flag_src loc = false) *)
(*   : *)
(*   exists f1 vers1 from_src to_src msg_src lc_src1 mem_src1 kind_src, *)
(*     (<<PROMISE: Local.promise_step lc_src0 mem_src0 loc from_src to_src msg_src lc_src1 mem_src1 kind_src>>) /\ *)
(*     (<<SIM: sim_thread *)
(*               f1 vers1 flag_src flag_tgt vs_src vs_tgt *)
(*               mem_src1 mem_tgt1 lc_src1 lc_tgt1>>) /\ *)
(*     (<<WF: Mapping.wfs f1>>) /\ *)
(*     (<<MAPLE: Mapping.les_strong f0 f1>>) /\ *)
(*     (<<VERSLE: versions_le vers0 vers1>>) /\ *)
(*     (<<VERSWF: versions_wf f1 vers1>>) /\ *)
(*     (<<SPACE: space_future_memory (unchangable mem_tgt0 lc_tgt0.(Local.promises)) f0 mem_src0 f1 mem_src1>>) *)
(* . *)
(* Proof. *)
(*   inv SIM. inv LOCAL. inv PROMISE. *)
(*   hexploit sim_memory_promise; eauto. *)
(*   { eapply LOCALSRC. } *)
(*   { eapply TVIEW. } *)
(*   i. des. *)
(*   assert (MAPLES: Mapping.les f0 f1). *)
(*   { eapply Mapping.les_strong_les; eauto. } *)
(*   esplits; eauto. *)
(*   { econs; eauto. hexploit sim_closed_memory_sim_message; eauto. i. *)
(*     eapply semi_closed_message_closed; eauto. i. subst. *)
(*     eapply Memory.promise_get0 in CANCEL. *)
(*     { des; eauto. } *)
(*     { inv CANCEL; ss. } *)
(*   } *)
(*   { econs; eauto; ss. *)
(*     { eapply sim_timemap_mon_latest; eauto. } *)
(*     { econs; eauto. ss. eapply sim_tview_mon_latest; eauto. } *)
(*     { ii. specialize (MAXSRC loc0). inv MAXSRC. *)
(*       destruct (Loc.eq_dec loc0 loc). *)
(*       { subst. econs. *)
(*         { i. hexploit MAX; eauto. i. des. *)
(*           esplits. erewrite <- promise_max_readable; eauto. *)
(*         } *)
(*         { ii. eapply NONMAX; auto. erewrite promise_max_readable; eauto. } *)
(*       } *)
(*       { eapply promise_unchanged_loc in CANCEL; eauto. *)
(*         des. econs. *)
(*         { i. hexploit MAX; eauto. i. des. *)
(*           esplits. erewrite <- unchanged_loc_max_readable; eauto. *)
(*         } *)
(*         { ii. eapply NONMAX; auto. erewrite unchanged_loc_max_readable; eauto. } *)
(*       } *)
(*     } *)
(*     { ii. specialize (MAXTGT loc0). inv MAXTGT. *)
(*       destruct (Loc.eq_dec loc0 loc). *)
(*       { subst. econs. *)
(*         i. hexploit MAX; eauto. i. des. *)
(*         esplits. erewrite <- promise_max_readable; eauto. *)
(*       } *)
(*       { eapply promise_unchanged_loc in PROMISE0; eauto. *)
(*         des. econs. i. hexploit MAX; eauto. i. des. *)
(*         esplits. erewrite <- unchanged_loc_max_readable; eauto. *)
(*       } *)
(*     } *)
(*     { i. assert (NEQ: loc0 <> loc). *)
(*       { ii. subst. rewrite FLAG in *. ss. } *)
(*       rewrite MAXTIMES; auto. eapply unchanged_loc_max_ts. *)
(*       2:{ eapply MEMSRC. } *)
(*       { eapply promise_unchanged_loc in CANCEL; eauto. des; eauto. } *)
(*     } *)
(*     { eapply reserved_space_empty_mon_strong; eauto. *)
(*       eapply reserved_space_empty_reserve_decr. *)
(*       { eapply reserved_space_empty_covered_decr; eauto. *)
(*         i. eapply promise_unchanged_loc in CANCEL. *)
(*         { des. inv MEM1. inv COVER. erewrite UNCH in GET. econs; eauto. } *)
(*         { ii. subst. rewrite FLAG in *. ss. } *)
(*       } *)
(*       { i. eapply promise_unchanged_loc in PROMISE0. *)
(*         { des. inv PROM0. erewrite UNCH in GET. eauto. } *)
(*         { ii. subst. rewrite FLAG in *. ss. } *)
(*       } *)
(*     } *)
(*   } *)
(* Qed. *)

Lemma sim_thread_racy_write_step
      f flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt
      loc to_tgt ord
      (SIM: sim_thread
              f flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt)
      (RACE: Local.racy_write_step lc_tgt mem_tgt loc to_tgt ord)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
      (WF: Mapping.wfs f)
  :
  exists to_src, Local.racy_write_step lc_src mem_src loc to_src ord.
Proof.
  inv SIM. inv RACE.
  exploit sim_local_racy; eauto. i. des.
  esplits. econs; eauto.
Qed.

Lemma sim_thread_racy_update_step
      f flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt
      loc to_tgt ordr ordw
      (SIM: sim_thread
              f flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt)
      (RACE: Local.racy_update_step lc_tgt mem_tgt loc to_tgt ordr ordw)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
      (WF: Mapping.wfs f)
  :
  exists to_src, Local.racy_update_step lc_src mem_src loc to_src ordr ordw.
Proof.
  inv SIM. inv RACE.
  { esplits. econs 1; eauto. }
  { esplits. econs 2; eauto. }
  { exploit sim_local_racy; eauto. i. des.
    esplits. econs 3; eauto.
  }
Qed.

Lemma sim_thread_racy_read_step
      f flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt
      loc to_tgt val_tgt ord
      (SIM: sim_thread
              f flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt)
      (READ: Local.racy_read_step lc_tgt mem_tgt loc to_tgt val_tgt ord)
      (WF: Mapping.wfs f)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
  :
    exists to_src,
      (<<RACE: forall val_src, Local.racy_read_step lc_src mem_src loc to_src val_src ord>>) /\
        (<<VALSRC: vs_src loc = None>>) /\
        (<<VALSRC: vs_tgt loc = None>>).
Proof.
  inv SIM. inv READ. exploit sim_local_racy; eauto. i. des.
  specialize (PERM loc). unfold option_rel in *. des_ifs.
  { exfalso. specialize (MAXSRC loc). inv MAXSRC.
    hexploit MAX; eauto. i. des.
    hexploit race_non_max_readable; eauto.
  }
  esplits; eauto.
Qed.

Lemma sim_thread_match
      f0 flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt lc_src0 lc_tgt
      loc
      (SIM: sim_thread
              f0 flag_src flag_tgt vs_src vs_tgt
              mem_src0 mem_tgt lc_src0 lc_tgt)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt mem_tgt)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt)
      (WF: Mapping.wfs f0)
      (FLAG: flag_src loc = false -> flag_tgt loc = false)
      (VAL: option_rel Const.le (vs_tgt loc) (vs_src loc))
      lang st
  :
    exists lc_src1 mem_src1 f1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk lang st lc_src0 mem_src0)
                    (Thread.mk _ st lc_src1 mem_src1)>>) /\
      (<<SIM: sim_thread
                f1
                (fun loc0 => if Loc.eq_dec loc0 loc then false else flag_src loc0)
                (fun loc0 => if Loc.eq_dec loc0 loc then false else flag_tgt loc0)
                vs_src vs_tgt
                mem_src1 mem_tgt lc_src1 lc_tgt>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<UNCH: forall loc0 (NEQ: loc0 <> loc), Mapping.le_strong (f0 loc0) (f1 loc0)>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt.(Global.memory) lc_tgt.(Local.reserves)) f0 mem_src0.(Global.memory) f1 mem_src1.(Global.memory)>>) /\
    (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt) (f1, mem_src1, mem_tgt)>>)
.
Proof.
  hexploit (@sim_thread_deflag false); eauto. i. des.
  rewrite FLAG0 in *; eauto. esplits.
  { eapply rtc_implies; [|eauto]. i. inv H. econs; [econs 1; eauto|]. inv LOCAL; ss. }
  all: eauto.
Qed.

Lemma sim_thread_read_full
      f0 flag_src flag_tgt vs_src0 vs_tgt0
      mem_src0 mem_tgt lc_src0 lc_tgt0
      lc_tgt1 loc to_tgt val_tgt0 released_tgt ord
      (SIM: sim_thread
              f0 flag_src flag_tgt vs_src0 vs_tgt0
              mem_src0 mem_tgt lc_src0 lc_tgt0)
      (READ: Local.read_step lc_tgt0 mem_tgt loc to_tgt val_tgt0 released_tgt ord lc_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt)
      (WF: Mapping.wfs f0)
      (FLAG: flag_src loc = false -> flag_tgt loc = false)
      (VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc))
      (FLAGS: forall loc
                    (SRC: flag_src loc = false) (TGT: flag_tgt loc = true),
          ~ Ordering.le Ordering.acqrel ord)
      lang st
  :
    exists val_tgt1 val_src1 to_src released_src lc_src1 lc_src2 mem_src1 vs_src1 vs_tgt1 f1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk lang st lc_src0 mem_src0)
                    (Thread.mk _ st lc_src1 mem_src1)>>) /\
      (<<STEP: __guard__((<<READ: forall val (VAL: Const.le val val_src1), Local.read_step lc_src1 mem_src1 loc to_src val released_src ord lc_src2>>) \/
                           (exists to, (<<RACE: forall val, Local.racy_read_step lc_src1 mem_src1 loc to val ord>>) /\ (<<LCSAME: lc_src2 = lc_src1>>)))>>) /\
      (<<SIM: sim_thread
                f1
                (fun loc0 => if Loc.eq_dec loc0 loc then false else flag_src loc0)
                (fun loc0 => if Loc.eq_dec loc0 loc then false else flag_tgt loc0)
                vs_src1 vs_tgt1
                mem_src1 mem_tgt lc_src2 lc_tgt1>>) /\
      (<<VAL: Const.le val_tgt1 val_src1>>) /\
      (<<VALTGT: Const.le val_tgt0 val_tgt1>>) /\
      (<<NUPDATESRC: forall val (VAL: vs_src0 loc = Some val), val = val_src1>>) /\
      (<<NUPDATETGT: forall val (VAL: vs_tgt0 loc = Some val), val = val_tgt1>>) /\
      (<<VALS: forall loc0,
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>)) \/
          (exists val_src val_tgt,
              (<<NONESRC: vs_src0 loc0 = None>>) /\ (<<NONETGT: vs_tgt0 loc0 = None>>) /\
              (<<VALSRC: vs_src1 loc0 = Some val_src>>) /\ (<<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) /\
              (<<VALLE: Const.le val_tgt val_src>>) /\
              (((<<LOC: loc0 <> loc>>) /\ (<<ORD: Ordering.le Ordering.acqrel ord>>)) \/
               ((<<LOC: loc0 = loc>>) /\ (<<SRC: val_src = val_src1>>) /\ (<<TGT: val_tgt = val_tgt1>>))))>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt.(Global.memory) lc_tgt0.(Local.reserves)) f0 mem_src0.(Global.memory) f1 mem_src1.(Global.memory)>>) /\
      (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt) (f1, mem_src1, mem_tgt)>>)
.
Proof.
  hexploit Local.read_step_future; eauto. i. des.
  hexploit sim_thread_match; eauto. i. des.
  hexploit Thread.rtc_tau_step_future; eauto. i. des. ss.
  destruct (classic (exists to, Local.is_racy lc_src1 mem_src1 loc to ord)).
  { des. hexploit sim_thread_read_racy; eauto.
    { ss. des_ifs. }
    { ss. des_ifs. }
    { i. ss. des_ifs. eapply FLAGS; eauto. }
    i. des. esplits; eauto.
    { unguard. right. esplits; eauto. }
    { refl. }
    { refl. }
    { i. clarify. }
    { i. clarify. }
  }
  hexploit sim_thread_read; eauto.
  { ss. des_ifs. }
  { ss. des_ifs. }
  { i. ss. des_ifs. eapply FLAGS; eauto. }
  i. des. esplits.
  { eauto. }
  { unguard. left. i. eapply READ0; eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  Unshelve. all: ss.
Qed.

Lemma sim_thread_read_racy_full
      f0 flag_src flag_tgt vs_src0 vs_tgt0
      mem_src0 mem_tgt lc_src0 lc_tgt
      loc to_tgt val_tgt ord
      (SIM: sim_thread
              f0 flag_src flag_tgt vs_src0 vs_tgt0
              mem_src0 mem_tgt lc_src0 lc_tgt)
      (READ: Local.racy_read_step lc_tgt mem_tgt loc to_tgt val_tgt ord)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt mem_tgt)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt)
      (WF: Mapping.wfs f0)
      (FLAG: flag_src loc = false -> flag_tgt loc = false)
      (VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc))
      lang st
  :
  exists lc_src1 mem_src1 f1 to,
    (<<STEPS: rtc (@Thread.tau_step _)
                  (Thread.mk lang st lc_src0 mem_src0)
                  (Thread.mk _ st lc_src1 mem_src1)>>) /\
      (<<READ: forall val, Local.racy_read_step lc_src1 mem_src1 loc to val ord>>) /\
      (<<SIM: sim_thread
                f1
                (fun loc0 => if Loc.eq_dec loc0 loc then false else flag_src loc0)
                (fun loc0 => if Loc.eq_dec loc0 loc then false else flag_tgt loc0)
                vs_src0 vs_tgt0
                mem_src1 mem_tgt lc_src1 lc_tgt>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt.(Global.memory) lc_tgt.(Local.reserves)) f0 mem_src0.(Global.memory) f1 mem_src1.(Global.memory)>>) /\
      (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt) (f1, mem_src1, mem_tgt)>>) /\
      (<<VALSRC: vs_src0 loc = None>>) /\
      (<<VALTGT: vs_tgt0 loc = None>>)
.
Proof.
  hexploit sim_thread_match; eauto. i. des.
  hexploit Thread.rtc_tau_step_future; eauto. i. des. ss.
  hexploit sim_thread_racy_read_step; eauto.
  { ss. des_ifs. }
  { ss. des_ifs. }
  i. des. esplits; eauto.
Qed.

Lemma sim_thread_write_racy_full
      f0 flag_src flag_tgt vs_src0 vs_tgt0
      mem_src0 mem_tgt lc_src0 lc_tgt
      loc to_tgt ord
      (SIM: sim_thread
              f0 flag_src flag_tgt vs_src0 vs_tgt0
              mem_src0 mem_tgt lc_src0 lc_tgt)
      (READ: Local.racy_write_step lc_tgt mem_tgt loc to_tgt ord)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt mem_tgt)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt)
      (WF: Mapping.wfs f0)
      (FLAG: flag_src loc = false -> flag_tgt loc = false)
      (VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc))
      lang st
  :
  exists lc_src1 mem_src1 to,
    (<<STEPS: rtc (@Thread.tau_step _)
                  (Thread.mk lang st lc_src0 mem_src0)
                  (Thread.mk _ st lc_src1 mem_src1)>>) /\
      (<<READ: Local.racy_write_step lc_src1 mem_src1 loc to ord>>).
Proof.
  hexploit sim_thread_match; eauto. i. des.
  hexploit Thread.rtc_tau_step_future; eauto. i. des. ss.
  hexploit sim_thread_racy_write_step; eauto.
  { ss. des_ifs. }
  { ss. des_ifs. }
  i. des. esplits; eauto.
Qed.

Lemma sim_thread_update_racy_full
      f0 flag_src flag_tgt vs_src0 vs_tgt0
      mem_src0 mem_tgt lc_src0 lc_tgt
      loc to_tgt ordr ordw
      (SIM: sim_thread
              f0 flag_src flag_tgt vs_src0 vs_tgt0
              mem_src0 mem_tgt lc_src0 lc_tgt)
      (READ: Local.racy_update_step lc_tgt mem_tgt loc to_tgt ordr ordw)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt mem_tgt)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt)
      (WF: Mapping.wfs f0)
      (FLAG: flag_src loc = false -> flag_tgt loc = false)
      (VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc))
      lang st
  :
  exists lc_src1 mem_src1 to,
    (<<STEPS: rtc (@Thread.tau_step _)
                  (Thread.mk lang st lc_src0 mem_src0)
                  (Thread.mk _ st lc_src1 mem_src1)>>) /\
      (<<READ: Local.racy_update_step lc_src1 mem_src1 loc to ordr ordw>>).
Proof.
  hexploit sim_thread_match; eauto. i. des.
  hexploit Thread.rtc_tau_step_future; eauto. i. des. ss.
  hexploit sim_thread_racy_update_step; eauto.
  { ss. des_ifs. }
  { ss. des_ifs. }
  i. des. esplits; eauto.
Qed.

Lemma sim_thread_write_step_release_full
      f0 flag_src flag_tgt0 vs_src0 vs_tgt0
      mem_src0 mem_tgt0 lc_src0 lc_tgt0
      val_tgt val_src
      lc_tgt1 mem_tgt1 loc from_tgt to_tgt
      released_tgt ord D
      (SIM: sim_thread
              f0 flag_src flag_tgt0 vs_src0 vs_tgt0
              mem_src0 mem_tgt0 lc_src0 lc_tgt0)
      (WRITE: Local.write_step lc_tgt0 mem_tgt0 loc from_tgt to_tgt val_tgt None released_tgt ord lc_tgt1 mem_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt0)
      (WF: Mapping.wfs f0)
      (FLAG: flag_src loc = false -> flag_tgt0 loc = false)
      (VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc))
      (VALW: Const.le val_tgt val_src)
      (DEBT: forall loc, (<<DEBT: D loc>>) \/
                           ((<<FLAG: flag_src loc = false -> flag_tgt0 loc = false>>) /\
                            (<<VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc) \/ flag_src loc = false>>)))
      (ATOMIC: ~ Ordering.le ord Ordering.na)
      lang st
  :
  (exists lc_src1 mem_src1,
    (<<STEPS: rtc (@Thread.tau_step _)
                  (Thread.mk lang st lc_src0 mem_src0)
                  (Thread.mk _ st lc_src1 mem_src1)>>) /\
      (<<RACE: Local.racy_write_step lc_src1 mem_src1 loc None ord>>)) \/
  exists f1 released_src lc_src1 lc_src2 vs_src1 vs_tgt1 mem_src1 mem_src2 from_src to_src flag_tgt1,
    (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk lang st lc_src0 mem_src0)
                    (Thread.mk _ st lc_src1 mem_src1)>>) /\
      (<<WRITE: Local.write_step lc_src1 mem_src1 loc from_src to_src val_src None released_src ord lc_src2 mem_src2>>) /\
      (<<SIM: sim_thread
                f1 (fun _ => false) flag_tgt1 vs_src1 vs_tgt1
                mem_src2 mem_tgt1 lc_src2 lc_tgt1>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<VALS: forall loc0,
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>) /\ (<<LOC: loc0 <> loc>>)) \/
            ((<<LOC: loc0 = loc>>) /\
               ((<<VALSRC: vs_src1 loc0 = Some val_src>> /\ <<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) \/
                  (<<VALSRC0: vs_src0 loc0 = None>> /\ <<VALTGT0: vs_tgt0 loc0 = None>> /\ <<VALSRC1: vs_src1 loc0 = None>> /\ <<VALTGT1: vs_tgt1 loc0 = None>>)))>>) /\
      (<<FLAG: forall loc, (<<DEBT: D loc>>) \/ (<<FLAG: flag_tgt1 loc = false>>)>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) f0 mem_src0.(Global.memory) f1 mem_src2.(Global.memory)>>) /\
      (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt0) (f1, mem_src2, mem_tgt1)>>)
.
Proof.
  hexploit sim_thread_match; eauto. i. des.
  hexploit Thread.rtc_tau_step_future; eauto. i. des. ss.
  hexploit sim_thread_write_step_release; eauto.
  { ss. clear - FLAG. des_ifs. }
  { ss. clear - FLAG. des_ifs. }
  { instantiate (1:=D). i. hexploit DEBT; eauto. i. des.
    { left. eauto. }
    { right. splits; auto. clear - FLAG FLAG0. des_ifs. }
    { right. splits; auto.
      { clear - FLAG FLAG0. des_ifs. }
      { right. clear - VAL0. des_ifs. }
    }
  }
  i. des. esplits.
  { left. esplits; eauto. }
  right. esplits.
  { etrans; [eauto|]. eapply rtc_implies; [|eapply STEPS0].
    i. inv H. econs; [econs 1; eauto|]. inv LOCAL; ss.
  }
  { eauto. }
  { eauto. }
  { eauto. }
  { etrans; eauto. }
  { eauto. }
  { eauto. }
  { eapply space_future_memory_trans; eauto. }
  { etrans; eauto.
    eapply Thread.rtc_tau_step_promises_minus in STEPS. ss.
    rewrite STEPS. auto.
  }
Qed.

Lemma sim_thread_update_step_release_full
      f0 flag_src flag_tgt0 vs_src0 vs_tgt0
      mem_src0 mem_tgt0 lc_src0 lc_tgt0
      valr_tgt valw_tgt valw_src
      lc_tgt1 lc_tgt2 mem_tgt1 loc from_tgt to_tgt releasedm_tgt
      released_tgt ordr ordw D
      (SIM: sim_thread
              f0 flag_src flag_tgt0 vs_src0 vs_tgt0
              mem_src0 mem_tgt0 lc_src0 lc_tgt0)
      (READ: Local.read_step lc_tgt0 mem_tgt0 loc from_tgt valr_tgt releasedm_tgt ordr lc_tgt1)
      (WRITE: Local.write_step lc_tgt1 mem_tgt0 loc from_tgt to_tgt valw_tgt releasedm_tgt released_tgt ordw lc_tgt2 mem_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Global.wf mem_src0)
      (MEMTGT: Global.wf mem_tgt0)
      (WF: Mapping.wfs f0)
      (FLAG: flag_src loc = false -> flag_tgt0 loc = false)
      (VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc))
      (FLAGS: forall loc
                     (SRC: flag_src loc = false) (TGT: flag_tgt0 loc = true),
          ~ Ordering.le Ordering.acqrel ordr)
      (DEBT: forall loc, (<<DEBT: D loc>>) \/
                           ((<<FLAG: flag_src loc = false -> flag_tgt0 loc = false>>) /\
                            (<<VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc) \/ flag_src loc = false>>)))
      (VALW: Const.le valw_tgt valw_src)
      (ATOMIC: ~ Ordering.le ordw Ordering.na)
      lang st
  :
  (exists lc_src1 mem_src1 to,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk lang st lc_src0 mem_src0)
                    (Thread.mk _ st lc_src1 mem_src1)>>) /\
        (<<RACE: Local.racy_update_step lc_src1 mem_src1 loc to ordr ordw>>)) \/
    exists val_src1 f1 val_tgt1 from_src to_src releasedm_src released_src mem_src1 mem_src2 lc_src1 lc_src2 lc_src3 vs_src1 vs_tgt1 flag_tgt1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk lang st lc_src0 mem_src0)
                    (Thread.mk _ st lc_src1 mem_src1)>>) /\
      (<<READ: forall val (VAL: Const.le val val_src1), Local.read_step lc_src1 mem_src1 loc from_src val releasedm_src ordr lc_src2>>) /\
      (<<WRITE: Local.write_step lc_src2 mem_src1 loc from_src to_src valw_src releasedm_src released_src ordw lc_src3 mem_src2>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<SIM: sim_thread
                f1 (fun _ => false) flag_tgt1 vs_src1 vs_tgt1
                mem_src2 mem_tgt1 lc_src3 lc_tgt2>>) /\
      (<<VAL: Const.le val_tgt1 val_src1>>) /\
      (<<VALTGT: Const.le valr_tgt val_tgt1>>) /\
      (<<NUPDATESRC: forall val (VAL: vs_src0 loc = Some val), val = val_src1>>) /\
      (<<NUPDATETGT: forall val (VAL: vs_tgt0 loc = Some val), val = val_tgt1>>) /\
      (<<VALS: forall loc0 (LOC: loc0 <> loc),
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>)) \/
          (exists val_src val_tgt,
              (<<NONESRC: vs_src0 loc0 = None>>) /\ (<<NONETGT: vs_tgt0 loc0 = None>>) /\
              (<<VALSRC: vs_src1 loc0 = Some val_src>>) /\ (<<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) /\
              (<<VALLE: Const.le val_tgt val_src>>) /\
              (<<ORD: Ordering.le Ordering.acqrel ordr>>))>>) /\
      (<<UPDATED:
        __guard__(((<<SRC: vs_src1 loc = Some valw_src>>) /\ (<<TGT: vs_tgt1 loc = Some valw_tgt>>)) \/
        ((<<SRCNONE0: vs_src0 loc = None>>) /\ (<<TGTNONE0: vs_tgt0 loc = None>>) /\
           (<<SRCNONE1: vs_src1 loc = None>>) /\ (<<TGTNONE0: vs_tgt1 loc = None>>)))>>) /\
      (<<FLAG: forall loc, (<<DEBT: D loc>>) \/ (<<FLAG: flag_tgt1 loc = false>>)>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0.(Global.memory) lc_tgt0.(Local.reserves)) f0 mem_src0.(Global.memory) f1 mem_src2.(Global.memory)>>) /\
      (<<OWNED: owned_future (BoolMap.minus mem_src0.(Global.promises) lc_src0.(Local.promises)) (f0, mem_src0, mem_tgt0) (f1, mem_src2, mem_tgt1)>>)
.
Proof.
  hexploit sim_thread_match; eauto. i. des.
  hexploit Thread.rtc_tau_step_future; eauto. i. des. ss.
  destruct (classic (exists to, Local.is_racy lc_src1 mem_src1 loc to ordr)).
  { des. left. esplits; eauto. }
  hexploit sim_thread_update_step_release; eauto.
  { ss. clear - FLAG. des_ifs. }
  { ss. clear - FLAG. des_ifs. }
  { i. ss. destruct (LocSet.Facts.eq_dec loc0 loc); ss. eapply FLAGS; eauto. }
  { instantiate (1:=D). i. hexploit DEBT; eauto. i. des.
    { left. eauto. }
    { right. splits; auto. clear - FLAG FLAG0. des_ifs. }
    { right. splits; auto.
      { clear - FLAG FLAG0. des_ifs. }
      { right. clear - VAL0. des_ifs. }
    }
  }
  i. des. right. esplits.
  { etrans; [eauto|]. eapply rtc_implies; [|eapply STEPS0].
    i. inv H0. econs; [econs 1; eauto|]. inv LOCAL; ss.
  }
  { eauto. }
  { eauto. }
  { eauto. }
  { etrans; eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eapply space_future_memory_trans; eauto. }
  { etrans; eauto.
    eapply Thread.rtc_tau_step_promises_minus in STEPS. ss.
    rewrite STEPS. auto.
  }
Qed.

(* TODO: *)
(*   sim_thread_write_step_normal_full *)
(*     sim_thread_update_step_normal_full *)
