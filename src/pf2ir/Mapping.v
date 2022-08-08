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
Require Import Reserves.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Global.
Require Import Local.
Require Import Thread.

Set Implicit Arguments.


Definition map_t: Type := Loc.t -> Time.t -> Time.t -> Prop.

Section Mapping.
  Variable f: map_t.

  Definition map_inhabited: Prop :=
    forall loc, f loc Time.bot Time.bot.

  Definition map_eq: Prop :=
    forall loc x y fx fy
      (EQ: x = y)
      (MAP1: f loc x fx)
      (MAP2: f loc y fy),
      fx = fy.

  Definition map_eq_inv: Prop :=
    forall loc x y fx fy
      (EQ: fx = fy)
      (MAP1: f loc x fx)
      (MAP2: f loc y fy),
      x = y.

  Definition map_lt: Prop :=
    forall loc x y fx fy
      (LT: Time.lt x y)
      (MAP1: f loc x fx)
      (MAP2: f loc y fy),
      Time.lt fx fy.

  Definition map_lt_inv: Prop :=
    forall loc x y fx fy
      (LT: Time.lt fx fy)
      (MAP1: f loc x fx)
      (MAP2: f loc y fy),
      Time.lt x y.

  Lemma map_le
        loc x y fx fy
        (MAP_EQ: map_eq)
        (MAP_LT: map_lt)
        (LE: Time.le x y)
        (MAP1: f loc x fx)
        (MAP2: f loc y fy):
    Time.le fx fy.
  Proof.
    inv LE.
    - left. eauto.
    - right. eapply MAP_EQ; eauto.
  Qed.

  Lemma map_le_inv
        loc x y fx fy
        (MAP_EQ_INV: map_eq_inv)
        (MAP_LT_INV: map_lt_inv)
        (LE: Time.le fx fy)
        (MAP1: f loc x fx)
        (MAP2: f loc y fy):
    Time.le x y.
  Proof.
    inv LE.
    - left. eauto.
    - right. eapply MAP_EQ_INV; eauto.
  Qed.

  Variant map_wf: Prop :=
    | map_wf_intro
        (MAP_INHABITED: map_inhabited)
        (MAP_EQ: map_eq)
        (MAP_EQ_INV: map_eq_inv)
        (MAP_LT: map_lt)
        (MAP_LT_INV: map_lt_inv)
  .

  Definition map_complete (mem fmem: Memory.t): Prop :=
    forall loc ts fts (MAP: f loc ts fts),
    exists from to msg ffrom fto fmsg,
      (<<GET: Memory.get loc to mem = Some (from, msg)>>) /\
      (<<FGET: Memory.get loc fto fmem = Some (ffrom, fmsg)>>) /\
      (__guard__ ((<<TS: ts = from>>) /\ (<<FTS: fts = ffrom>>) \/
                  (<<TS: ts = to>>) /\ (<<FTS: fts = fto>>)))
  .

  Definition timemap_map (tm ftm: TimeMap.t): Prop :=
    forall loc, f loc (tm loc) (ftm loc).

  Variant view_map (view fview: View.t): Prop :=
    | view_map_intro
        (RLX: timemap_map view.(View.rlx) (fview.(View.rlx)))
        (PLN: timemap_map view.(View.pln) (fview.(View.pln)))
  .

  Variant opt_view_map: forall (view fview: option View.t), Prop :=
    | opt_view_map_None:
      opt_view_map None None
    | opt_view_map_Some
        view fview
        (VIEW: view_map view fview):
      opt_view_map (Some view) (Some fview)
  .

  Variant tview_map (tview ftview: TView.t): Prop :=
    | tview_map_intro
        (REL: forall loc, view_map (TView.rel tview loc) (TView.rel ftview loc))
        (CUR: view_map (TView.cur tview) (TView.cur ftview))
        (ACQ: view_map (TView.acq tview) (TView.acq ftview))
  .

  Variant message_map: forall (msg fmsg: Message.t), Prop :=
    | message_map_intro
        val view fview na
        (RELEASED: opt_view_map view fview):
      message_map (Message.mk val view na) (Message.mk val fview na)
  .

  Variant memory_map_loc (loc: Loc.t) (max: Time.t): forall (rsv: bool) (mem fmem: Memory.t), Prop :=
    | memory_map_loc_reserved
        mem fmem
        fmax
        (SOUND: forall from to msg (GET: Memory.get loc to mem = Some (from, msg)),
          exists ffrom fto fmsg,
            (<<FGET: Memory.get loc fto fmem = Some (ffrom, fmsg)>>) /\
            (<<FROM: f loc from ffrom>>) /\
            (<<TO: f loc to fto>>) /\
            (<<MSG: message_map msg fmsg>>) /\
            (<<FTO_IN: Time.lt fto fmax>>))
        (COMPLETE: forall ffrom fto fmsg
                          (FGET: Memory.get loc fto fmem = Some (ffrom, fmsg)),
            (<<FFROM_OUT: Time.lt fmax ffrom>>) \/
            (<<FTO_IN: Time.lt fto fmax>>) /\
            exists from to msg,
              (<<GET: Memory.get loc to mem = Some (from, msg)>>) /\
              (<<FROM: f loc from ffrom>>) /\
              (<<TO: f loc to fto>>) /\
              (<<MSG: message_map msg fmsg>>)):
      memory_map_loc loc max true mem fmem
    | memory_map_loc_non_reserved
        mem fmem
        fmin
        (SOUND: forall from to msg (GET: Memory.get loc to mem = Some (from, msg)),
          exists ffrom fto fmsg,
            (<<FGET: Memory.get loc fto fmem = Some (ffrom, fmsg)>>) /\
            (<<FROM: f loc from ffrom>>) /\
            (<<TO: f loc to fto>>) /\
            (<<MSG: message_map msg fmsg>>) /\
            (<<FTO_IN: Time.lt max to -> Time.lt fmin fto>>))
        (COMPLETE: forall ffrom fto fmsg
                     (FGET: Memory.get loc fto fmem = Some (ffrom, fmsg))
                     (FTO_IN: Time.lt fmin fto),
            (<<FFROM_IN: Time.lt fmin ffrom>>) /\
            exists from to msg,
              (<<GET: Memory.get loc to mem = Some (from, msg)>>) /\
              (<<FROM: f loc from ffrom>>) /\
              (<<TO: f loc to fto>>) /\
              (<<MSG: message_map msg fmsg>>) /\
              (<<TO_IN: Time.lt max to>>)):
      memory_map_loc loc max false mem fmem
  .

  Definition memory_map (max: TimeMap.t) (rsv: BoolMap.t) (mem fmem: Memory.t): Prop :=
    forall loc, memory_map_loc loc (max loc) (rsv loc) mem fmem.

  Variant local_map (lc flc: Local.t): Prop :=
    | local_map_intro
        (TVIEW: tview_map (Local.tview lc) (Local.tview flc))
  .

  Variant global_map (max: TimeMap.t) (rsv: BoolMap.t) (gl fgl: Global.t): Prop :=
    | global_map_intro
        (MEMORY: memory_map max rsv (Global.memory gl) (Global.memory fgl))
  .

  Variant event_map: forall (e fe: ThreadEvent.t), Prop :=
    | event_map_promise
        loc:
      event_map (ThreadEvent.promise loc) (ThreadEvent.promise loc)
    | event_map_reserve
        loc:
      event_map (ThreadEvent.reserve loc) (ThreadEvent.reserve loc)
    | event_map_cancel
        loc:
      event_map (ThreadEvent.cancel loc) (ThreadEvent.cancel loc)
    | event_map_silent:
      event_map ThreadEvent.silent ThreadEvent.silent
    | event_map_read
        loc ts fts val released freleased ord
        (TS: f loc ts fts)
        (RELEASED: opt_view_map released freleased):
      event_map (ThreadEvent.read loc ts val released ord)
                (ThreadEvent.read loc fts val freleased ord)
    | event_map_write
        loc from ffrom to fto val released freleased ord
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (RELEASED: opt_view_map released freleased):
      event_map (ThreadEvent.write loc from to val released ord)
                (ThreadEvent.write loc ffrom fto val freleased ord)
    | event_map_update
        loc tsr ftsr tsw ftsw valr valw releasedr freleasedr releasedw freleasedw ordr ordw
        (TSR: f loc tsr ftsr)
        (TSW: f loc tsw ftsw)
        (RELEASEDR: opt_view_map releasedr freleasedr)
        (RELEASEDW: opt_view_map releasedw freleasedw):
      event_map (ThreadEvent.update loc tsr tsw valr valw releasedr releasedw ordr ordw)
                (ThreadEvent.update loc ftsr ftsw valr valw freleasedr freleasedw ordr ordw)
    | event_map_fence
        ordr ordw:
      event_map (ThreadEvent.fence ordr ordw) (ThreadEvent.fence ordr ordw)
    | event_map_syscall
        e:
      event_map (ThreadEvent.syscall e) (ThreadEvent.syscall e)
    | event_map_failure:
      event_map ThreadEvent.failure ThreadEvent.failure
    | event_map_racy_read
        loc to fto val ord
        (TO: option_rel (f loc) to fto):
      event_map (ThreadEvent.racy_read loc to val ord)
                (ThreadEvent.racy_read loc fto val ord)
    | event_map_racy_write
        loc to fto val ord
        (TO: option_rel (f loc) to fto):
      event_map (ThreadEvent.racy_write loc to val ord)
                (ThreadEvent.racy_write loc fto val ord)
    | event_map_racy_update
        loc to fto valr valw ordr ordw
        (TO: option_rel (f loc) to fto):
      event_map (ThreadEvent.racy_update loc to valr valw ordr ordw)
                (ThreadEvent.racy_update loc fto valr valw ordr ordw)
  .
End Mapping.

Lemma bot_timemap_map
      f
      (MAP_WF: map_wf f):
  timemap_map f TimeMap.bot TimeMap.bot.
Proof.
  ii. apply MAP_WF.
Qed.

Lemma bot_view_map
      f
      (MAP_WF: map_wf f):
  view_map f View.bot View.bot.
Proof.
  econs; eauto using bot_timemap_map.
Qed.

Lemma unwrap_map
      f v fv
      (MAP_WF: map_wf f)
      (VIEW: opt_view_map f v fv):
  view_map f (View.unwrap v) (View.unwrap fv).
Proof.
  inv VIEW; ss.
  apply bot_view_map; auto.
Qed.

Lemma time_join_map
      f loc t1 t2 ft1 ft2
      (MAP_WF: map_wf f)
      (TIME1: f loc t1 ft1)
      (TIME2: f loc t2 ft2):
  f loc (Time.join t1 t2) (Time.join ft1 ft2).
Proof.
  unfold Time.join. repeat condtac; ss.
  - exploit map_le; eauto; try apply MAP_WF. i. timetac.
  - exploit map_le_inv; eauto; try apply MAP_WF. i. timetac.
Qed.

Lemma timemap_join_map
      f tm1 tm2 ftm1 ftm2
      (MAP_WF: map_wf f)
      (TIMEMAP1: timemap_map f tm1 ftm1)
      (TIMEMAP2: timemap_map f tm2 ftm2):
  timemap_map f (TimeMap.join tm1 tm2) (TimeMap.join ftm1 ftm2).
Proof.
  ii. unfold TimeMap.join.
  eapply time_join_map; eauto.
Qed.

Lemma view_join_map
      f view1 view2 fview1 fview2
      (MAP_WF: map_wf f)
      (VIEW1: view_map f view1 fview1)
      (VIEW2: view_map f view2 fview2):
  view_map f (View.join view1 view2) (View.join fview1 fview2).
Proof.
  inv VIEW1. inv VIEW2.
  econs; ss; eauto using timemap_join_map.
Qed.

Lemma singleton_ur_map
      f loc to fto
      (MAP_WF: map_wf f)
      (MAP: f loc to fto):
  view_map f (View.singleton_ur loc to) (View.singleton_ur loc fto).
Proof.
  unfold View.singleton_ur, TimeMap.singleton, LocFun.add, LocFun.find, LocFun.init.
  econs; ss; ii; condtac; subst; ss; try apply MAP_WF.
Qed.

Lemma singleton_rw_map
      f loc to fto
      (MAP_WF: map_wf f)
      (MAP: f loc to fto):
  view_map f (View.singleton_rw loc to) (View.singleton_rw loc fto).
Proof.
  unfold View.singleton_rw, TimeMap.singleton, LocFun.add, LocFun.find, LocFun.init.
  econs; ss; ii; try condtac; subst; ss; try apply MAP_WF.
Qed.

Lemma singleton_ur_if_map
      f c loc to fto
      (MAP_WF: map_wf f)
      (MAP: f loc to fto):
  view_map f (View.singleton_ur_if c loc to) (View.singleton_ur_if c loc fto).
Proof.
  unfold View.singleton_ur_if.
  condtac; auto using singleton_ur_map, singleton_rw_map.
Qed.

Definition map_add (loc: Loc.t) (ts fts: Time.t) (f: map_t): map_t :=
  fun loc' ts' fts' =>
    (loc' = loc /\ ts' = ts /\ fts' = fts) \/ f loc' ts' fts'.
#[local] Hint Unfold map_add: core.

Lemma map_add_incr loc ts fts f:
  f <3= map_add loc ts fts f.
Proof.
  unfold map_add. auto.
Qed.

Lemma add_map_inhabited
      f loc ts fts
      (MAP_INHABITED: map_inhabited f):
  map_inhabited (map_add loc ts fts f).
Proof.
  ii. auto.
Qed.

Lemma add_map_eq
      f loc ts fts
      (MAP_EQ: map_eq f)
      (ADD_EX: forall fts' (MAP: f loc ts fts'), fts' = fts):
  map_eq (map_add loc ts fts f).
Proof.
  unfold map_add. ii. des; subst; ss.
  - exploit ADD_EX; eauto.
  - exploit ADD_EX; eauto.
  - exploit MAP_EQ; eauto.
Qed.

Lemma add_map_eq_inv
      f loc ts fts
      (MAP_EQ_INV: map_eq_inv f)
      (ADD_EX: forall ts' (MAP: f loc ts' fts), ts' = ts):
  map_eq_inv (map_add loc ts fts f).
Proof.
  unfold map_add. ii. des; subst; ss.
  - exploit ADD_EX; eauto.
  - exploit ADD_EX; eauto.
  - exploit MAP_EQ_INV; eauto.
Qed.

Lemma add_map_lt
      f loc ts fts
      (MAP_LT: map_lt f)
      (ADD_EX: forall ts' fts' (MAP: f loc ts' fts'),
          Time.lt ts' ts /\ Time.lt fts' fts \/
            ts' = ts /\ fts' = fts \/
            Time.lt ts ts' /\ Time.lt fts fts'):
  map_lt (map_add loc ts fts f).
Proof.
  unfold map_add. ii. des; subst; eauto; timetac.
  - exploit ADD_EX; try exact MAP1. i. des; timetac.
  - exploit ADD_EX; try exact MAP2. i. des; timetac.
Qed.

Lemma add_map_lt_inv
      f loc ts fts
      (MAP_LT_INV: map_lt_inv f)
      (ADD_EX: forall ts' fts' (MAP: f loc ts' fts'),
          Time.lt ts' ts /\ Time.lt fts' fts \/
            ts' = ts /\ fts' = fts \/
            Time.lt ts ts' /\ Time.lt fts fts'):
  map_lt_inv (map_add loc ts fts f).
Proof.
  unfold map_add. ii. des; subst; eauto; timetac.
  - exploit ADD_EX; try exact MAP1. i. des; timetac.
  - exploit ADD_EX; try exact MAP2. i. des; timetac.
Qed.

Lemma timemap_map_incr
      f1 f2
      (INCR: f1 <3= f2):
  timemap_map f1 <2= timemap_map f2.
Proof.
  ii. auto.
Qed.

Lemma view_map_incr
      f1 f2
      (INCR: f1 <3= f2):
  view_map f1 <2= view_map f2.
Proof.
  i. inv PR. econs; eauto using timemap_map_incr.
Qed.

Lemma opt_view_map_incr
      f1 f2
      (INCR: f1 <3= f2):
  opt_view_map f1 <2= opt_view_map f2.
Proof.
  i. inv PR; econs.
  eauto using view_map_incr.
Qed.

Lemma message_map_incr
      f1 f2
      (INCR: f1 <3= f2):
  message_map f1 <2= message_map f2.
Proof.
  i. inv PR. econs.
  eauto using opt_view_map_incr.
Qed.

Lemma tview_map_incr
      f1 f2
      (INCR: f1 <3= f2):
  tview_map f1 <2= tview_map f2.
Proof.
  i. inv PR. econs; eauto using view_map_incr.
Qed.

Lemma event_map_incr
      f1 f2
      (INCR: f1 <3= f2):
  event_map f1 <2= event_map f2.
Proof.
  i. inv PR.
  - econs 1.
  - econs 2.
  - econs 3.
  - econs 4.
  - econs 5; eauto using opt_view_map_incr.
  - econs 6; eauto using opt_view_map_incr.
  - econs 7; eauto using opt_view_map_incr.
  - econs 8.
  - econs 9.
  - econs 10.
  - econs 11. destruct to, fto; ss. auto.
  - econs 12. destruct to, fto; ss. auto.
  - econs 13. destruct to, fto; ss. auto.
Qed.

Lemma memory_map_get
      f max rsv mem fmem
      loc from to msg
      (MAP: memory_map f max rsv mem fmem)
      (GET: Memory.get loc to mem = Some (from, msg)):
  exists ffrom fto fmsg,
    (<<FGET: Memory.get loc fto fmem = Some (ffrom, fmsg)>>) /\
    (<<FROM: f loc from ffrom>>) /\
    (<<TO: f loc to fto>>) /\
    (<<MSG: message_map f msg fmsg>>).
Proof.
  destruct (MAP loc).
  - exploit SOUND; eauto. i. des. esplits; eauto.
  - exploit SOUND; eauto. i. des. esplits; eauto.
Qed.

Lemma memory_map_closed_timemap
      f max rsv mem fmem
      tm ftm
      (WF: map_wf f)
      (MEMORY: memory_map f max rsv mem fmem)
      (TIMEMAP: timemap_map f tm ftm)
      (CLOSED: Memory.closed_timemap tm mem):
  Memory.closed_timemap ftm fmem.
Proof.
  ii. specialize (CLOSED loc). des.
  exploit memory_map_get; eauto. i. des.
  specialize (TIMEMAP loc).
  inv WF. exploit MAP_EQ; [|exact TIMEMAP|exact TO|]; ss. i. subst.
  eauto.
Qed.

Lemma lt_get_from
      mem loc
      from1 to1 msg1
      from2 to2 msg2
      (LT: Time.lt to1 to2)
      (GET1: Memory.get loc to1 mem = Some (from1, msg1))
      (GET2: Memory.get loc to2 mem = Some (from2, msg2)):
  Time.le to1 from2.
Proof.
  exploit Memory.get_ts; try exact GET1. i. des.
  { subst. timetac. }
  exploit Memory.get_disjoint; [exact GET1|exact GET2|]. i. des.
  { subst. timetac. }
  destruct (TimeFacts.le_lt_dec to1 from2); ss. exfalso.
  apply (x1 to1); econs; ss; try refl. econs. ss.
Qed.

Lemma add_cases
      mem1 loc from to msg mem2
      (INHABITED: Memory.inhabited mem1)
      (ADD: Memory.add mem1 loc from to msg mem2):
  exists pfrom pto pmsg,
    (<<PGET: Memory.get loc pto mem1 = Some (pfrom, pmsg)>>) /\
    (<<PREV_FROM: Time.le pto from>>) /\
    (<<PREV_TO: Time.lt pto to>>) /\
    (<<PEMPTY: Memory.empty mem1 loc pto to>>) /\
    __guard__ (
        (exists nfrom nto nmsg,
            (<<NGET: Memory.get loc nto mem1 = Some (nfrom, nmsg)>>) /\
            (<<NEXT_FROM: Time.le to nfrom>>) /\
            (<<NEXT_TO: Time.lt to nto>>) /\
            (<<NEMPTY: Memory.empty mem1 loc to nto>>)) \/
        (<<LATEST: forall ts (LT: Time.lt to ts), Memory.get loc ts mem1 = None>>)).
Proof.
  exploit Memory.add_ts; eauto. i.
  hexploit Memory.add_inhabited; eauto. i. des.
  exploit Memory.add_get0; eauto. i. des.
  exploit (@Memory.prev_exists to mem2 loc); try apply H.
  { eapply TimeFacts.le_lt_lt; eauto. apply Time.bot_spec. }
  i. des.
  revert x1. erewrite Memory.add_o; eauto. condtac; ss.
  { des. subst. timetac. }
  clear o COND. i.
  esplits; try eapply x1; eauto.
  { exploit Memory.add_get1; try exact x1; eauto. i.
    eapply lt_get_from; eauto.
  }
  { ii. exploit x3; eauto.
    erewrite Memory.add_o; eauto. condtac; ss.
  }
  destruct (TimeFacts.le_lt_dec (Memory.max_ts loc mem1) to).
  { right. i.
    destruct (Memory.get loc ts mem1) as [[]|] eqn:GET'; ss.
    exploit Memory.max_ts_spec; try exact GET'. i. des.
    rewrite l in MAX. timetac.
  }
  { left.
    exploit Memory.next_exists; try exact l; eauto. i. des.
    esplits; eauto.
    exploit Memory.add_get1; try exact x6; eauto. i.
    eapply lt_get_from; eauto.
  }
Qed.

Lemma memory_map_add
      f1 max rsv mem1 fmem1
      loc from to msg mem2
      (WF1: map_wf f1)
      (COMPLETE1: map_complete f1 mem1 fmem1)
      (MAP1: memory_map f1 max rsv mem1 fmem1)
      (INHABITED1: Memory.inhabited mem1)
      (MAX: Memory.closed_timemap max mem1)
      (ADD: Memory.add mem1 loc from to msg mem2)
      (RESERVE: rsv loc = false -> Time.lt (max loc) from):
  exists ffrom fto f2,
    (<<F2: f2 = map_add loc from ffrom (map_add loc to fto f1)>>) /\
    (<<WF2: map_wf f2>>) /\
    forall fmsg
      (FMSG_WF: Message.wf fmsg)
      (MSG_MAP: message_map f2 msg fmsg),
    exists fmem2,
      (<<FADD: Memory.add fmem1 loc ffrom fto fmsg fmem2>>) /\
      (<<COMPLETE2: map_complete f2 mem2 fmem2>>) /\
      (<<MAP2: memory_map f2 max rsv mem2 fmem2>>).
Proof.
  inv WF1.
  exploit Memory.add_ts; eauto. intro TS.
  exploit add_cases; eauto. i. des.
  destruct (rsv loc) eqn:RSV.
  { (* reserved *)
    generalize (MAP1 loc). rewrite RSV. i. inv H.
    unguard. des.

    { (* non-latest *)
      assert (EMPTY: forall ts fts
                       (LT1: Time.lt pto ts)
                       (LT2: Time.lt ts nfrom)
                       (MAP: f1 loc ts fts),
                 False).
      { i. exploit COMPLETE1; try exact MAP. i. unguardH x0. des; subst.
        - destruct (TimeFacts.le_lt_dec to to0); cycle 1.
          { exploit PEMPTY; try exact l; try congr.
            exploit Memory.get_ts; try exact GET. i.
            des; subst; timetac. etrans; eauto.
          }
          inv l; cycle 1.
          { inv H. exploit Memory.add_get0; try exact ADD. i. des. congr. }
          destruct (TimeFacts.le_lt_dec nto to0); cycle 1.
          { exploit NEMPTY; try exact l; ss. congr. }
          exploit Memory.get_disjoint; [exact NGET|exact GET|].
          i. des; subst; timetac.
          exploit Memory.get_ts; try exact NGET. i. des; subst; timetac.
          apply (x0 nto); econs; ss; try refl.
          etrans; eauto.
        - destruct (TimeFacts.le_lt_dec to to0); cycle 1.
          { exploit PEMPTY; try exact l; try congr. }
          inv l; cycle 1.
          { inv H. exploit Memory.add_get0; try exact ADD. i. des. congr. }
          exploit NEMPTY; try exact H; try congr.
          exploit Memory.get_ts; try exact NGET. i. des; subst; timetac.
          etrans; eauto.
      }

      exploit Memory.get_ts; try exact NGET. i. des; subst; timetac.
      assert (Time.lt pto nfrom).
      { eapply TimeFacts.lt_le_lt; try exact PREV_TO. ss. }
      exploit SOUND; try exact PGET. i. des.
      rename ffrom into fpfrom, fto into fpto, fmsg into fpmsg.
      exploit SOUND; try exact NGET. i. des.
      rename ffrom into fnfrom, fto into fnto, fmsg into fnmsg.

      assert (FEMPTY: forall ts fts
                        (LT1: Time.lt fpto fts)
                        (LT2: Time.lt fts fnfrom)
                        (MAP: f1 loc ts fts),
                 False).
      { i. eapply EMPTY; try exact MAP.
        - eapply MAP_LT_INV; try exact LT1; eauto.
        - eapply MAP_LT_INV; try exact LT2; eauto.
      }

      (* find ffrom and fto *)
      assert (exists fto,
                 (<<FPREV_TO: Time.lt fpto fto>>) /\
                 (<<FNEXT_FROM: Time.le fto fnfrom>>) /\
                 (<<FNEXT_TO: Time.lt fto fnto>>) /\
                 (<<NEXT_EQ: __guard__ (to = nfrom <-> fto = fnfrom)>>)).
      { inv NEXT_FROM.
        - exploit MAP_LT; try exact H; eauto. i.
          exists (Time.middle fpto fnfrom).
          exploit Time.middle_spec; try exact x1. i. des.
          unguard. splits; ss.
          + econs. ss.
          + etrans; try exact x3. eapply MAP_LT; try exact x0; eauto.
          + split; i; subst; timetac.
            rewrite <- H1 in x3 at 2. timetac.
        - inv H0. exists fnfrom. unguard. splits; ss.
          + eapply MAP_LT; try exact H; eauto.
          + refl.
          + eapply MAP_LT; try exact x0; eauto.
      }
      des.
      assert (exists ffrom,
                 (<<FTS: Time.lt ffrom fto>>) /\
                 (<<FPREV_FROM: Time.le fpto ffrom>>) /\
                 (<<PREV_EQ: __guard__ (pto = from <-> fpto = ffrom)>>)).
      { inv PREV_FROM.
        - exists (Time.middle fpto fto).
          exploit Time.middle_spec; try exact FPREV_TO. i. des.
          unguard. splits; ss.
          + econs. ss.
          + split; i; subst; timetac.
            rewrite H1 in x1 at 1. timetac.
        - inv H0. exists fpto. unguard. splits; ss. refl.
      }
      des.
      exists ffrom, fto. esplits; [refl|..].

      { (* map_wf *)
        econs.
        - (* map_inhabited *)
          repeat apply add_map_inhabited. ss.
        - (* map_eq *)
          apply add_map_eq.
          { apply add_map_eq; ss. i.
            inv NEXT_FROM.
            - exfalso. eapply EMPTY; try exact MAP; ss.
            - inv H0. unguard. des. rewrite NEXT_EQ in *; ss.
              eapply MAP_EQ; try exact MAP; ss.
          }
          unfold map_add. i. des; subst; timetac.
          inv PREV_FROM.
          + exfalso. eapply EMPTY; try exact MAP; ss.
            exploit Memory.add_ts; try exact ADD. i.
            eapply TimeFacts.lt_le_lt; try exact x2; eassumption.
          + inv H0. unguard. des. rewrite PREV_EQ in *; ss.
            eapply MAP_EQ; try exact MAP; ss.
        - (* map_eq_inv *)
          apply add_map_eq_inv.
          { apply add_map_eq_inv; ss. i.
            inv FNEXT_FROM.
            - exfalso. eapply FEMPTY; try exact MAP; ss.
            - inv H0. unguard. des. rewrite NEXT_EQ0 in *; ss.
              eapply MAP_EQ_INV; try exact MAP; ss.
          }
          unfold map_add. i. des; subst; timetac.
          inv FPREV_FROM.
          + exfalso. eapply FEMPTY; try exact MAP; ss.
            exploit Memory.add_ts; try exact ADD. i.
            eapply TimeFacts.lt_le_lt; try exact x2; eassumption.
          + inv H0. unguard. des. rewrite PREV_EQ0 in *; ss.
            eapply MAP_EQ_INV; try exact MAP; ss.
        - (* map_lt *)
          apply add_map_lt.
          { apply add_map_lt; ss. i.
            destruct (TimeFacts.le_lt_dec ts' pto).
            { left. split.
              - eapply TimeFacts.le_lt_lt; try exact l.
                eapply TimeFacts.le_lt_lt; eauto.
              - exploit map_le; try exact l; try eassumption. i.
                eapply TimeFacts.le_lt_lt; try exact x1. ss.
            }
            destruct (TimeFacts.le_lt_dec nfrom ts'); cycle 1.
            { exploit EMPTY; try exact MAP; ss. }
            inv l0; cycle 1.
            { inv H0. inv NEXT_FROM.
              - right. right. split; ss.
                exploit MAP_EQ; [|exact FROM0|exact MAP|]; ss. i. subst.
                inv FNEXT_FROM; ss. inv H1. unguard. des.
                rewrite NEXT_EQ0 in *; ss. timetac.
              - inv H0. right. left. split; ss.
                unguard. des. rewrite NEXT_EQ in *; ss.
                eapply MAP_EQ; try eassumption. ss.
            }
            right. right. split.
            - eapply TimeFacts.le_lt_lt; try exact H0; ss.
            - exploit MAP_LT; try exact H0; try eassumption. i.
              eapply TimeFacts.le_lt_lt; try exact x1; ss.
          }
          unfold map_add. i. des; subst; timetac.
          destruct (TimeFacts.le_lt_dec pto ts'); cycle 1.
          { left. split.
            - eapply TimeFacts.lt_le_lt; try exact l; ss.
            - exploit MAP_LT; try exact l; try eassumption. i.
              eapply TimeFacts.lt_le_lt; try exact x1; ss.
          }
          inv l; cycle 1.
          { inv H0. inv PREV_FROM.
            - left. split; ss.
              exploit MAP_EQ;[|exact TO|exact MAP|]; ss. i. subst.
              inv FPREV_FROM; ss. inv H1. unguard. des.
              rewrite PREV_EQ0 in *; ss. timetac.
            - inv H0. right. left. split; ss.
              unguard. des. rewrite PREV_EQ in *; ss.
              eapply MAP_EQ; try eassumption; ss.
          }
          destruct (TimeFacts.le_lt_dec nfrom ts'); cycle 1.
          { exploit EMPTY; try exact MAP; ss. }
          right. right. split.
          + eapply TimeFacts.lt_le_lt; try exact l.
            eapply TimeFacts.lt_le_lt; eauto.
          + exploit map_le; try exact l; try eassumption. i.
            eapply TimeFacts.lt_le_lt; try exact x1.
            eapply TimeFacts.lt_le_lt; eauto.
        - (* map_lt_inv *)
          apply add_map_lt_inv.
          { apply add_map_lt_inv; ss. i.
            destruct (TimeFacts.le_lt_dec fts' fpto).
            { left. split.
              - exploit map_le_inv; try exact l; try eassumption. i.
                eapply TimeFacts.le_lt_lt; try exact x1. ss.
              - eapply TimeFacts.le_lt_lt; try exact l.
                eapply TimeFacts.le_lt_lt; eauto.
            }
            destruct (TimeFacts.le_lt_dec fnfrom fts'); cycle 1.
            { exploit FEMPTY; try exact MAP; ss. }
            inv l0; cycle 1.
            { inv H0. inv FNEXT_FROM.
              - right. right. split; ss.
                exploit MAP_EQ_INV; [|exact FROM0|exact MAP|]; ss. i. subst.
                inv NEXT_FROM; ss. inv H1. unguard. des.
                rewrite NEXT_EQ in *; ss. timetac.
              - inv H0. right. left. split; ss.
                unguard. des. rewrite NEXT_EQ0 in *; ss.
                eapply MAP_EQ_INV; try eassumption. ss.
            }
            right. right. split.
            - exploit MAP_LT_INV; try exact H0; try eassumption. i.
              eapply TimeFacts.le_lt_lt; try exact x1; ss.
            - eapply TimeFacts.le_lt_lt; try exact H0; ss.
          }
          unfold map_add. i. des; subst; timetac.
          destruct (TimeFacts.le_lt_dec fpto fts'); cycle 1.
          { left. split.
            - exploit MAP_LT_INV; try exact l; try eassumption. i.
              eapply TimeFacts.lt_le_lt; try exact x1; ss.
            - eapply TimeFacts.lt_le_lt; try exact l; ss.
          }
          inv l; cycle 1.
          { inv H0. inv FPREV_FROM.
            - left. split; ss.
              exploit MAP_EQ_INV;[|exact TO|exact MAP|]; ss. i. subst.
              inv PREV_FROM; ss. inv H1. unguard. des.
              rewrite PREV_EQ in *; ss. timetac.
            - inv H0. right. left. split; ss.
              unguard. des. rewrite PREV_EQ0 in *; ss.
              eapply MAP_EQ_INV; try eassumption; ss.
          }
          destruct (TimeFacts.le_lt_dec fnfrom fts'); cycle 1.
          { exploit FEMPTY; try exact MAP; ss. }
          right. right. split.
          + exploit map_le_inv; try exact l; try eassumption. i.
            eapply TimeFacts.lt_le_lt; try exact x1.
            eapply TimeFacts.lt_le_lt; eauto.
          + eapply TimeFacts.lt_le_lt; try exact l.
            eapply TimeFacts.lt_le_lt; eauto.
      }

      i. exploit (@Memory.add_exists fmem1 loc); try exact FTS; try exact FMSG_WF.
      { ii. inv LHS. inv RHS. ss.
        exploit TimeFacts.lt_le_lt; [exact FROM1|exact TO2|]. i.
        exploit TimeFacts.lt_le_lt; [exact FROM2|exact TO1|]. i.
        clear x FROM1 TO1 FROM2 TO2.
        exploit COMPLETE; try exact GET2. i. des.
        { rewrite x3 in FFROM_OUT.
          rewrite FFROM_OUT in FTO_IN0.
          timetac.
        }
        exploit TimeFacts.le_lt_lt; [exact FPREV_FROM|exact x2|]. i.
        exploit TimeFacts.lt_le_lt; [exact x3|exact FNEXT_FROM|]. i.
        exploit MAP_LT_INV; try exact x1; try eassumption. i.
        exploit MAP_LT_INV; try exact x4; try eassumption. i.
        destruct (TimeFacts.le_lt_dec to to0); cycle 1.
        { exploit PEMPTY; try exact l; try eassumption. i. congr. }
        inv l; cycle 1.
        { exploit Memory.add_get0; try eassumption. i. des. congr. }
        destruct (TimeFacts.le_lt_dec nto to0); cycle 1.
        { exploit NEMPTY; try exact l; try eassumption. i. congr. }
        exploit Memory.get_disjoint; [exact GET|exact NGET|]. i.
        des; subst; timetac.
        apply (x7 nto); econs; ss; try refl.
        etrans; eauto.
      }
      i. des. esplits; try exact x1.

      { (* map_complete *)
        exploit Memory.add_get0; try exact ADD. i. des.
        exploit Memory.add_get0; try exact x1. i. des.
        unfold map_add. ii. des; subst.
        - esplits; eauto. unguard. auto.
        - esplits; eauto. unguard. auto.
        - exploit COMPLETE1; try exact MAP. i. des.
          exploit Memory.add_get1; try exact GET3; eauto. i.
          exploit Memory.add_get1; try exact FGET1; eauto. i.
          esplits; try exact x2; try exact x3; eauto.
      }

      { (* memory_map *)
        ii. destruct (Loc.eq_dec loc0 loc); cycle 1.
        { destruct (MAP1 loc0).
          - econs 1.
            + instantiate (1:=fmax0). i. revert GET.
              erewrite Memory.add_o; eauto. condtac; ss.
              { des. subst. congr. }
              i. guardH o.
              exploit SOUND0; eauto. i. des.
              exploit Memory.add_get1; try exact FGET1; eauto. i.
              esplits; try exact x2; eauto using map_add_incr.
              do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
            + i. revert FGET1.
              erewrite Memory.add_o; eauto. condtac; ss.
              { des. subst. congr. }
              i. guardH o.
              exploit COMPLETE0; eauto. i. des; eauto. right.
              exploit Memory.add_get1; try exact GET; eauto. i.
              esplits; try exact x2; eauto using map_add_incr.
              do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
          - econs 2.
            + instantiate (1:=fmin). i. revert GET.
              erewrite Memory.add_o; eauto. condtac; ss.
              { des. subst. congr. }
              i. guardH o.
              exploit SOUND0; eauto. i. des.
              exploit Memory.add_get1; try exact FGET1; eauto. i.
              esplits; try exact x2; eauto using map_add_incr.
              do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
            + i. revert FGET1.
              erewrite Memory.add_o; eauto. condtac; ss.
              { des. subst. congr. }
              i. guardH o.
              exploit COMPLETE0; eauto. i. des.
              exploit Memory.add_get1; try exact GET; eauto. i.
              esplits; try exact x2; eauto using map_add_incr.
              do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
        }

        subst. rewrite RSV. econs.
        { instantiate (1:=fmax). i. revert GET.
          erewrite Memory.add_o; eauto. condtac; ss.
          - i. des. inv GET.
            exploit Memory.add_get0; try exact x1. i. des.
            esplits; try exact GET0; auto 6.
            etrans; eauto.
          - i. des; ss.
            exploit SOUND; eauto. i. des.
            exploit Memory.add_get1; try exact FGET1; eauto. i.
            esplits; try exact x2; auto.
            do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
        }
        { i. revert FGET1.
          erewrite Memory.add_o; eauto. condtac; ss.
          - i. des. inv FGET1.
            exploit Memory.add_get0; try exact ADD. i. des.
            right. esplits; try exact GET0; auto 6.
            etrans; eauto.
          - i. des; ss.
            exploit COMPLETE; try exact FGET1. i. des; auto.
            exploit Memory.add_get1; try exact GET; eauto. i.
            right. esplits; try exact x2; auto 6.
            do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
        }
      }
    }

    { (* latest *)
      assert (EMPTY: forall ts fts
                            (LT: Time.lt pto ts)
                            (MAP: f1 loc ts fts),
                 False).
      { i. exploit COMPLETE1; try exact MAP. i. unguardH x0. des; subst.
        - destruct (TimeFacts.le_lt_dec to to0); cycle 1.
          { exploit PEMPTY; try exact l; try congr.
            exploit Memory.get_ts; try exact GET. i.
            des; subst; timetac. etrans; eauto.
          }
          inv l; cycle 1.
          { inv H. exploit Memory.add_get0; try exact ADD. i. des. congr. }
          exploit LATEST; try exact H; congr.
        - destruct (TimeFacts.le_lt_dec to to0); cycle 1.
          { exploit PEMPTY; try exact l; try congr. }
          inv l; cycle 1.
          { inv H. exploit Memory.add_get0; try exact ADD. i. des. congr. }
          exploit LATEST; try exact H; congr.
      }

      exploit SOUND; try exact PGET. i. des.
      rename ffrom into fpfrom, fto into fpto, fmsg into fpmsg.

      assert (FEMPTY: forall ts fts
                             (LT: Time.lt fpto fts)
                             (MAP: f1 loc ts fts),
                 False).
      { i. eapply EMPTY; try exact MAP.
        eapply MAP_LT_INV; try exact LT1; eauto.
      }

      (* find ffrom and fto *)
      assert (exists fto,
                 (<<FPREV_TO: Time.lt fpto fto>>) /\
                 (<<FMAX: Time.lt fto fmax>>)).
      { exists (Time.middle fpto fmax). eapply Time.middle_spec. ss. }
      des.
      assert (exists ffrom,
                 (<<FTS: Time.lt ffrom fto>>) /\
                 (<<FPREV_FROM: Time.le fpto ffrom>>) /\
                 (<<PREV_EQ: __guard__ (pto = from <-> fpto = ffrom)>>)).
      { inv PREV_FROM.
        - exists (Time.middle fpto fto).
          exploit Time.middle_spec; try exact FPREV_TO. i. des.
          unguard. splits; ss.
          + econs. ss.
          + split; i; subst; timetac.
            rewrite H0 in x0 at 1. timetac.
        - inv H. exists fpto. unguard. splits; ss. refl.
      }
      des.
      exists ffrom, fto. esplits; [refl|..].

      { (* map_wf *)
        econs.
        - (* map_inhabited *)
          repeat apply add_map_inhabited. ss.
        - (* map_eq *)
          apply add_map_eq.
          { apply add_map_eq; ss. i. exfalso. eauto. }
          unfold map_add. i. des; subst; timetac.
          inv PREV_FROM.
          + exfalso. eauto.
          + inv H. unguard. des. rewrite PREV_EQ in *; ss. eauto.
        - (* map_eq_inv *)
          apply add_map_eq_inv.
          { apply add_map_eq_inv; ss. i.
            exfalso. eapply FEMPTY; eauto.
          }
          unfold map_add. i. des; subst; timetac.
          inv FPREV_FROM.
          + exfalso. eapply FEMPTY; eauto.
          + inv H. unguard. des. rewrite PREV_EQ0 in *; ss.
            eapply MAP_EQ_INV; try exact MAP; ss.
        - (* map_lt *)
          apply add_map_lt.
          { apply add_map_lt; ss. i.
            destruct (TimeFacts.le_lt_dec ts' pto).
            { left. split.
              - eapply TimeFacts.le_lt_lt; try exact l.
                eapply TimeFacts.le_lt_lt; eauto.
              - exploit map_le; try exact l; try eassumption. i.
                eapply TimeFacts.le_lt_lt; try exact x0. ss.
            }
            exploit EMPTY; try exact l; eauto. ss.
          }
          unfold map_add. i. des; subst; timetac.
          destruct (TimeFacts.le_lt_dec pto ts'); cycle 1.
          { left. split.
            - eapply TimeFacts.lt_le_lt; try exact l; ss.
            - exploit MAP_LT; try exact l; try eassumption. i.
              eapply TimeFacts.lt_le_lt; try exact x0; ss.
          }
          inv l; cycle 1.
          { inv H. inv PREV_FROM.
            - left. split; ss.
              exploit MAP_EQ;[|exact TO|exact MAP|]; ss. i. subst.
              inv FPREV_FROM; ss. inv H0. unguard. des.
              rewrite PREV_EQ0 in *; ss. timetac.
            - inv H. right. left. split; ss.
              unguard. des. rewrite PREV_EQ in *; ss.
              eapply MAP_EQ; try eassumption; ss.
          }
          exploit EMPTY; try exact H; eauto. ss.
        - (* map_lt_inv *)
          apply add_map_lt_inv.
          { apply add_map_lt_inv; ss. i.
            destruct (TimeFacts.le_lt_dec fts' fpto).
            { left. split.
              - exploit map_le_inv; try exact l; try eassumption. i.
                eapply TimeFacts.le_lt_lt; try exact x0. ss.
              - eapply TimeFacts.le_lt_lt; try exact l.
                eapply TimeFacts.le_lt_lt; eauto.
            }
            exploit FEMPTY; try exact l; eauto. ss.
          }
          unfold map_add. i. des; subst; timetac.
          destruct (TimeFacts.le_lt_dec fpto fts'); cycle 1.
          { left. split.
            - exploit MAP_LT_INV; try exact l; try eassumption. i.
              eapply TimeFacts.lt_le_lt; try exact x0; ss.
            - eapply TimeFacts.lt_le_lt; try exact l; ss.
          }
          inv l; cycle 1.
          { inv H. inv FPREV_FROM.
            - left. split; ss.
              exploit MAP_EQ_INV;[|exact TO|exact MAP|]; ss. i. subst.
              inv PREV_FROM; ss. inv H0. unguard. des.
              rewrite PREV_EQ in *; ss. timetac.
            - inv H. right. left. split; ss.
              unguard. des. rewrite PREV_EQ0 in *; ss.
              eapply MAP_EQ_INV; try eassumption; ss.
          }
          exploit FEMPTY; try exact H; eauto. ss.
      }

      i. exploit (@Memory.add_exists fmem1 loc); try exact FTS; try exact FMSG_WF.
      { ii. inv LHS. inv RHS. ss.
        exploit TimeFacts.lt_le_lt; [exact FROM0|exact TO1|]. i.
        exploit TimeFacts.lt_le_lt; [exact FROM1|exact TO0|]. i.
        clear x FROM0 TO0 FROM1 TO1.
        exploit COMPLETE; try exact GET2. i. des.
        { rewrite x2 in FFROM_OUT. timetac. }
        exploit TimeFacts.le_lt_lt; [exact FPREV_FROM|exact x1|]. i.
        exploit MAP_LT_INV; try exact x0; try eassumption. i. eauto.
      }
      i. des. esplits; try exact x0.

      { (* map_complete *)
        exploit Memory.add_get0; try exact ADD. i. des.
        exploit Memory.add_get0; try exact x0. i. des.
        unfold map_add. ii. des; subst.
        - esplits; eauto. unguard. auto.
        - esplits; eauto. unguard. auto.
        - exploit COMPLETE1; try exact MAP. i. des.
          exploit Memory.add_get1; try exact GET3; eauto. i.
          exploit Memory.add_get1; try exact FGET0; eauto. i.
          esplits; try exact x2; try exact x3; eauto.
      }

      { (* memory_map *)
        ii. destruct (Loc.eq_dec loc0 loc); cycle 1.
        { destruct (MAP1 loc0).
          - econs 1.
            + instantiate (1:=fmax0). i. revert GET.
              erewrite Memory.add_o; eauto. condtac; ss.
              { des. subst. congr. }
              i. guardH o.
              exploit SOUND0; eauto. i. des.
              exploit Memory.add_get1; try exact FGET1; eauto. i.
              esplits; try exact x1; eauto using map_add_incr.
              do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
            + i. revert FGET0.
              erewrite Memory.add_o; eauto. condtac; ss.
              { des. subst. congr. }
              i. guardH o.
              exploit COMPLETE0; eauto. i. des; eauto. right.
              exploit Memory.add_get1; try exact GET; eauto. i.
              esplits; try exact x1; eauto using map_add_incr.
              do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
          - econs 2.
            + instantiate (1:=fmin). i. revert GET.
              erewrite Memory.add_o; eauto. condtac; ss.
              { des. subst. congr. }
              i. guardH o.
              exploit SOUND0; eauto. i. des.
              exploit Memory.add_get1; try exact FGET1; eauto. i.
              esplits; try exact x1; eauto using map_add_incr.
              do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
            + i. revert FGET0.
              erewrite Memory.add_o; eauto. condtac; ss.
              { des. subst. congr. }
              i. guardH o.
              exploit COMPLETE0; eauto. i. des.
              exploit Memory.add_get1; try exact GET; eauto. i.
              esplits; try exact x1; eauto using map_add_incr.
              do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
        }

        subst. rewrite RSV. econs.
        { instantiate (1:=fmax). i. revert GET.
          erewrite Memory.add_o; eauto. condtac; ss.
          - i. des. inv GET.
            exploit Memory.add_get0; try exact x0. i. des.
            esplits; try exact GET0; auto 6.
          - i. des; ss.
            exploit SOUND; eauto. i. des.
            exploit Memory.add_get1; try exact FGET0; eauto. i.
            esplits; try exact x1; auto.
            do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
        }
        { i. revert FGET0.
          erewrite Memory.add_o; eauto. condtac; ss.
          - i. des. inv FGET0.
            exploit Memory.add_get0; try exact ADD. i. des.
            right. esplits; try exact GET0; auto 6.
          - i. des; ss.
            exploit COMPLETE; try exact FGET0. i. des; auto.
            exploit Memory.add_get1; try exact GET; eauto. i.
            right. esplits; try exact x1; auto 6.
            do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
        }
      }
    }
  }

  { (* non-reserved *)
    generalize (MAP1 loc). rewrite RSV. i. inv H.
    exploit RESERVE; ss. clear RESERVE. intro RESERVE.
    assert (PTO_MAX: Time.le (max loc) pto).
    { destruct (TimeFacts.le_lt_dec (max loc) pto); ss.
      specialize (MAX loc). des.
      exploit PEMPTY; try exact l; try congr.
      exploit Memory.add_ts; eauto.
    }
    unguard. des.

    { (* non-latest *)
      assert (EMPTY: forall ts fts
                            (LT1: Time.lt pto ts)
                            (LT2: Time.lt ts nfrom)
                            (MAP: f1 loc ts fts),
                 False).
      { i. exploit COMPLETE1; try exact MAP. i. unguardH x0. des; subst.
        - destruct (TimeFacts.le_lt_dec to to0); cycle 1.
          { exploit PEMPTY; try exact l; try congr.
            exploit Memory.get_ts; try exact GET. i.
            des; subst; timetac. etrans; eauto.
          }
          inv l; cycle 1.
          { inv H. exploit Memory.add_get0; try exact ADD. i. des. congr. }
          destruct (TimeFacts.le_lt_dec nto to0); cycle 1.
          { exploit NEMPTY; try exact l; ss. congr. }
          exploit Memory.get_disjoint; [exact NGET|exact GET|].
          i. des; subst; timetac.
          exploit Memory.get_ts; try exact NGET. i. des; subst; timetac.
          apply (x0 nto); econs; ss; try refl.
          etrans; eauto.
        - destruct (TimeFacts.le_lt_dec to to0); cycle 1.
          { exploit PEMPTY; try exact l; try congr. }
          inv l; cycle 1.
          { inv H. exploit Memory.add_get0; try exact ADD. i. des. congr. }
          exploit NEMPTY; try exact H; try congr.
          exploit Memory.get_ts; try exact NGET. i. des; subst; timetac.
          etrans; eauto.
      }

      exploit Memory.get_ts; try exact NGET. i. des; subst; timetac.
      assert (Time.lt pto nfrom).
      { eapply TimeFacts.lt_le_lt; try exact PREV_TO. ss. }
      exploit SOUND; try exact PGET. i. des.
      rename ffrom into fpfrom, fto into fpto, fmsg into fpmsg.
      exploit SOUND; try exact NGET. i. des.
      rename ffrom into fnfrom, fto into fnto, fmsg into fnmsg.

      assert (FEMPTY: forall ts fts
                             (LT1: Time.lt fpto fts)
                             (LT2: Time.lt fts fnfrom)
                             (MAP: f1 loc ts fts),
                 False).
      { i. eapply EMPTY; try exact MAP.
        - eapply MAP_LT_INV; try exact LT1; eauto.
        - eapply MAP_LT_INV; try exact LT2; eauto.
      }

      (* find ffrom and fto *)
      assert (exists fto,
                 (<<FPREV_TO: Time.lt fpto fto>>) /\
                 (<<FNEXT_FROM: Time.le fto fnfrom>>) /\
                 (<<FNEXT_TO: Time.lt fto fnto>>) /\
                 (<<FMIN_TO: Time.lt fmin fto>>) /\
                 (<<NEXT_EQ: __guard__ (to = nfrom <-> fto = fnfrom)>>)).
      { inv NEXT_FROM.
        - exploit MAP_LT; try exact H; eauto. i.
          inv PTO_MAX.
          + exists (Time.middle fpto fnfrom).
            exploit Time.middle_spec; try exact x1. i. des.
            unguard. splits; ss.
            * econs. ss.
            * etrans; try exact x3. eapply MAP_LT; try exact x0; eauto.
            * exploit FTO_IN; eauto.
            * split; i; subst; timetac.
              rewrite <- H2 in x3 at 2. timetac.
          + exists (Time.middle fmin fnfrom).
            exploit COMPLETE; try exact FGET0; eauto. i. inv x2. clear H3.
            exploit Time.middle_spec; try exact H2. i. des.
            unguard. splits; ss.
            * eapply TimeFacts.le_lt_lt; try exact x2.
              destruct (TimeFacts.le_lt_dec fpto fmin); ss.
              exploit COMPLETE; try exact FGET; eauto. i. des.
              exploit MAP_EQ_INV; [|exact TO|exact TO1|]; ss. i. subst.
              inv H1. timetac.
            * econs. ss.
            * etrans; try exact x3. eapply MAP_LT; try exact x0; eauto.
            * split; i; subst; timetac.
              rewrite <- H3 in x3 at 2. timetac.
        - inv H0. exists fnfrom. unguard. splits; ss.
          + eapply MAP_LT; try exact H; eauto.
          + refl.
          + eapply MAP_LT; try exact x0; eauto.
          + exploit FTO_IN0.
            { etrans; try exact RESERVE.
              exploit Memory.add_ts; eauto.
            }
            i. exploit COMPLETE; try exact FGET0; ss. i. des. ss.
      }
      des.
      assert (exists ffrom,
                 (<<FTS: Time.lt ffrom fto>>) /\
                 (<<FPREV_FROM: Time.le fpto ffrom>>) /\
                 (<<FMIN_FROM: Time.lt fmin ffrom>>) /\
                 (<<PREV_EQ: __guard__ (pto = from <-> fpto = ffrom)>>)).
      { inv PREV_FROM.
        - inv PTO_MAX.
          + exists (Time.middle fpto fto).
            exploit Time.middle_spec; try exact FPREV_TO. i. des.
            unguard. splits; ss.
            * econs. ss.
            * exploit FTO_IN; ss. i. etrans; eassumption.
            * split; i; subst; timetac.
              rewrite H2 in x1 at 1. timetac.
          + exists (Time.middle fmin fto).
            exploit Time.middle_spec; try exact FMIN_TO. i. des.
            unguard. splits; ss.
            * econs. eapply TimeFacts.le_lt_lt; try exact x1.
              destruct (TimeFacts.le_lt_dec fpto fmin); ss.
              exploit COMPLETE; try exact FGET; ss. i. des.
              exploit MAP_EQ_INV; [|exact TO|exact TO1|]; ss. i. subst.
              rewrite H1 in *. timetac.
            * split; i; subst; timetac.
              exploit COMPLETE; try exact FGET; ss. i. des.
              exploit MAP_EQ_INV; [|exact TO|exact TO1|]; ss. i. subst.
              rewrite H1 in *. timetac.
        - inv H0. exists fpto. unguard. splits; ss; try refl. auto.
      }
      des.
      exists ffrom, fto. esplits; [refl|..].

      { (* map_wf *)
        econs.
        - (* map_inhabited *)
          repeat apply add_map_inhabited. ss.
        - (* map_eq *)
          apply add_map_eq.
          { apply add_map_eq; ss. i.
            inv NEXT_FROM.
            - exfalso. eapply EMPTY; try exact MAP; ss.
            - inv H0. unguard. des. rewrite NEXT_EQ in *; ss.
              eapply MAP_EQ; try exact MAP; ss.
          }
          unfold map_add. i. des; subst; timetac.
          inv PREV_FROM.
          + exfalso. eapply EMPTY; try exact MAP; ss.
            exploit Memory.add_ts; try exact ADD. i.
            eapply TimeFacts.lt_le_lt; try exact x2; eassumption.
          + inv H0. unguard. des. rewrite PREV_EQ in *; ss.
            eapply MAP_EQ; try exact MAP; ss.
        - (* map_eq_inv *)
          apply add_map_eq_inv.
          { apply add_map_eq_inv; ss. i.
            inv FNEXT_FROM.
            - exfalso. eapply FEMPTY; try exact MAP; ss.
            - inv H0. unguard. des. rewrite NEXT_EQ0 in *; ss.
              eapply MAP_EQ_INV; try exact MAP; ss.
          }
          unfold map_add. i. des; subst; timetac.
          inv FPREV_FROM.
          + exfalso. eapply FEMPTY; try exact MAP; ss.
            exploit Memory.add_ts; try exact ADD. i.
            eapply TimeFacts.lt_le_lt; try exact x2; eassumption.
          + inv H0. unguard. des. rewrite PREV_EQ0 in *; ss.
            eapply MAP_EQ_INV; try exact MAP; ss.
        - (* map_lt *)
          apply add_map_lt.
          { apply add_map_lt; ss. i.
            destruct (TimeFacts.le_lt_dec ts' pto).
            { left. split.
              - eapply TimeFacts.le_lt_lt; try exact l.
                eapply TimeFacts.le_lt_lt; eauto.
              - exploit map_le; try exact l; try eassumption. i.
                eapply TimeFacts.le_lt_lt; try exact x1. ss.
            }
            destruct (TimeFacts.le_lt_dec nfrom ts'); cycle 1.
            { exploit EMPTY; try exact MAP; ss. }
            inv l0; cycle 1.
            { inv H0. inv NEXT_FROM.
              - right. right. split; ss.
                exploit MAP_EQ; [|exact FROM0|exact MAP|]; ss. i. subst.
                inv FNEXT_FROM; ss. inv H1. unguard. des.
                rewrite NEXT_EQ0 in *; ss. timetac.
              - inv H0. right. left. split; ss.
                unguard. des. rewrite NEXT_EQ in *; ss.
                eapply MAP_EQ; try eassumption. ss.
            }
            right. right. split.
            - eapply TimeFacts.le_lt_lt; try exact H0; ss.
            - exploit MAP_LT; try exact H0; try eassumption. i.
              eapply TimeFacts.le_lt_lt; try exact x1; ss.
          }
          unfold map_add. i. des; subst; timetac.
          destruct (TimeFacts.le_lt_dec pto ts'); cycle 1.
          { left. split.
            - eapply TimeFacts.lt_le_lt; try exact l; ss.
            - exploit MAP_LT; try exact l; try eassumption. i.
              eapply TimeFacts.lt_le_lt; try exact x1; ss.
          }
          inv l; cycle 1.
          { inv H0. inv PREV_FROM.
            - left. split; ss.
              exploit MAP_EQ;[|exact TO|exact MAP|]; ss. i. subst.
              inv FPREV_FROM; ss. inv H1. unguard. des.
              rewrite PREV_EQ0 in *; ss. timetac.
            - inv H0. right. left. split; ss.
              unguard. des. rewrite PREV_EQ in *; ss.
              eapply MAP_EQ; try eassumption; ss.
          }
          destruct (TimeFacts.le_lt_dec nfrom ts'); cycle 1.
          { exploit EMPTY; try exact MAP; ss. }
          right. right. split.
          + eapply TimeFacts.lt_le_lt; try exact l.
            eapply TimeFacts.lt_le_lt; eauto.
          + exploit map_le; try exact l; try eassumption. i.
            eapply TimeFacts.lt_le_lt; try exact x1.
            eapply TimeFacts.lt_le_lt; eauto.
        - (* map_lt_inv *)
          apply add_map_lt_inv.
          { apply add_map_lt_inv; ss. i.
            destruct (TimeFacts.le_lt_dec fts' fpto).
            { left. split.
              - exploit map_le_inv; try exact l; try eassumption. i.
                eapply TimeFacts.le_lt_lt; try exact x1. ss.
              - eapply TimeFacts.le_lt_lt; try exact l.
                eapply TimeFacts.le_lt_lt; eauto.
            }
            destruct (TimeFacts.le_lt_dec fnfrom fts'); cycle 1.
            { exploit FEMPTY; try exact MAP; ss. }
            inv l0; cycle 1.
            { inv H0. inv FNEXT_FROM.
              - right. right. split; ss.
                exploit MAP_EQ_INV; [|exact FROM0|exact MAP|]; ss. i. subst.
                inv NEXT_FROM; ss. inv H1. unguard. des.
                rewrite NEXT_EQ in *; ss. timetac.
              - inv H0. right. left. split; ss.
                unguard. des. rewrite NEXT_EQ0 in *; ss.
                eapply MAP_EQ_INV; try eassumption. ss.
            }
            right. right. split.
            - exploit MAP_LT_INV; try exact H0; try eassumption. i.
              eapply TimeFacts.le_lt_lt; try exact x1; ss.
            - eapply TimeFacts.le_lt_lt; try exact H0; ss.
          }
          unfold map_add. i. des; subst; timetac.
          destruct (TimeFacts.le_lt_dec fpto fts'); cycle 1.
          { left. split.
            - exploit MAP_LT_INV; try exact l; try eassumption. i.
              eapply TimeFacts.lt_le_lt; try exact x1; ss.
            - eapply TimeFacts.lt_le_lt; try exact l; ss.
          }
          inv l; cycle 1.
          { inv H0. inv FPREV_FROM.
            - left. split; ss.
              exploit MAP_EQ_INV;[|exact TO|exact MAP|]; ss. i. subst.
              inv PREV_FROM; ss. inv H1. unguard. des.
              rewrite PREV_EQ in *; ss. timetac.
            - inv H0. right. left. split; ss.
              unguard. des. rewrite PREV_EQ0 in *; ss.
              eapply MAP_EQ_INV; try eassumption; ss.
          }
          destruct (TimeFacts.le_lt_dec fnfrom fts'); cycle 1.
          { exploit FEMPTY; try exact MAP; ss. }
          right. right. split.
          + exploit map_le_inv; try exact l; try eassumption. i.
            eapply TimeFacts.lt_le_lt; try exact x1.
            eapply TimeFacts.lt_le_lt; eauto.
          + eapply TimeFacts.lt_le_lt; try exact l.
            eapply TimeFacts.lt_le_lt; eauto.
      }

      i. exploit (@Memory.add_exists fmem1 loc); try exact FTS; try exact FMSG_WF.
      { ii. inv LHS. inv RHS. ss.
        exploit TimeFacts.lt_le_lt; [exact FROM1|exact TO2|]. i.
        exploit TimeFacts.lt_le_lt; [exact FROM2|exact TO1|]. i.
        clear x FROM1 TO1 FROM2 TO2.
        exploit COMPLETE; try exact GET2.
        { etrans; eassumption. }
        i. des.
        exploit TimeFacts.le_lt_lt; [exact FPREV_FROM|exact x2|]. i.
        exploit TimeFacts.lt_le_lt; [exact x3|exact FNEXT_FROM|]. i.
        exploit MAP_LT_INV; try exact x1; try eassumption. i.
        exploit MAP_LT_INV; try exact x4; try eassumption. i.
        destruct (TimeFacts.le_lt_dec to to0); cycle 1.
        { exploit PEMPTY; try exact l; try eassumption. i. congr. }
        inv l; cycle 1.
        { exploit Memory.add_get0; try eassumption. i. des. congr. }
        destruct (TimeFacts.le_lt_dec nto to0); cycle 1.
        { exploit NEMPTY; try exact l; try eassumption. i. congr. }
        exploit Memory.get_disjoint; [exact GET|exact NGET|]. i.
        des; subst; timetac.
        apply (x7 nto); econs; ss; try refl.
        etrans; eauto.
      }
      i. des. esplits; try exact x1.

      { (* map_complete *)
        exploit Memory.add_get0; try exact ADD. i. des.
        exploit Memory.add_get0; try exact x1. i. des.
        unfold map_add. ii. des; subst.
        - esplits; eauto. unguard. auto.
        - esplits; eauto. unguard. auto.
        - exploit COMPLETE1; try exact MAP. i. des.
          exploit Memory.add_get1; try exact GET3; eauto. i.
          exploit Memory.add_get1; try exact FGET1; eauto. i.
          esplits; try exact x2; try exact x3; eauto.
      }

      { (* memory_map *)
        ii. destruct (Loc.eq_dec loc0 loc); cycle 1.
        { destruct (MAP1 loc0).
          - econs 1.
            + instantiate (1:=fmax). i. revert GET.
              erewrite Memory.add_o; eauto. condtac; ss.
              { des. subst. congr. }
              i. guardH o.
              exploit SOUND0; eauto. i. des.
              exploit Memory.add_get1; try exact FGET1; eauto. i.
              esplits; try exact x2; eauto using map_add_incr.
              do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
            + i. revert FGET1.
              erewrite Memory.add_o; eauto. condtac; ss.
              { des. subst. congr. }
              i. guardH o.
              exploit COMPLETE0; eauto. i. des; eauto. right.
              exploit Memory.add_get1; try exact GET; eauto. i.
              esplits; try exact x2; eauto using map_add_incr.
              do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
          - econs 2.
            + instantiate (1:=fmin0). i. revert GET.
              erewrite Memory.add_o; eauto. condtac; ss.
              { des. subst. congr. }
              i. guardH o.
              exploit SOUND0; eauto. i. des.
              exploit Memory.add_get1; try exact FGET1; eauto. i.
              esplits; try exact x2; auto using map_add_incr.
              do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
            + i. revert FGET1.
              erewrite Memory.add_o; eauto. condtac; ss.
              { des. subst. congr. }
              i. guardH o.
              exploit COMPLETE0; eauto. i. des.
              exploit Memory.add_get1; try exact GET; eauto. i.
              esplits; try exact x2; eauto using map_add_incr.
              do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
        }

        subst. rewrite RSV. econs.
        { instantiate (1:=fmin). i. revert GET.
          erewrite Memory.add_o; eauto. condtac; ss.
          - i. des. inv GET.
            exploit Memory.add_get0; try exact x1. i. des.
            esplits; try exact GET0; auto 6.
          - i. des; ss.
            exploit SOUND; eauto. i. des.
            exploit Memory.add_get1; try exact FGET1; eauto. i.
            esplits; try exact x2; auto.
            do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
        }
        { i. revert FGET1.
          erewrite Memory.add_o; eauto. condtac; ss.
          - i. des. inv FGET1.
            exploit Memory.add_get0; try exact ADD. i. des.
            esplits; try exact GET0; auto 6.
            etrans; eauto.
          - i. des; ss.
            exploit COMPLETE; try exact FGET1; ss. i. des; auto.
            exploit Memory.add_get1; try exact GET; eauto. i.
            esplits; try exact x2; auto 6.
            do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
        }
      }
    }

    { (* latest *)
      assert (EMPTY: forall ts fts
                            (LT: Time.lt pto ts)
                            (MAP: f1 loc ts fts),
                 False).
      { i. exploit COMPLETE1; try exact MAP. i. unguardH x0. des; subst.
        - destruct (TimeFacts.le_lt_dec to to0); cycle 1.
          { exploit PEMPTY; try exact l; try congr.
            exploit Memory.get_ts; try exact GET. i.
            des; subst; timetac. etrans; eauto.
          }
          inv l; cycle 1.
          { inv H. exploit Memory.add_get0; try exact ADD. i. des. congr. }
          exploit LATEST; try exact H; congr.
        - destruct (TimeFacts.le_lt_dec to to0); cycle 1.
          { exploit PEMPTY; try exact l; try congr. }
          inv l; cycle 1.
          { inv H. exploit Memory.add_get0; try exact ADD. i. des. congr. }
          exploit LATEST; try exact H; congr.
      }

      exploit SOUND; try exact PGET. i. des.
      rename ffrom into fpfrom, fto into fpto, fmsg into fpmsg.

      assert (FEMPTY: forall ts fts
                             (LT: Time.lt fpto fts)
                             (MAP: f1 loc ts fts),
                 False).
      { i. eapply EMPTY; try exact MAP.
        eapply MAP_LT_INV; try exact LT1; eauto.
      }

      (* find ffrom and fto *)
      assert (exists fto,
                 (<<FPREV_TO: Time.lt fpto fto>>) /\
                 (<<FMIN_TO: Time.lt fmin fto>>)).
      { inv PTO_MAX.
        - exists (Time.incr fpto). splits; try apply Time.incr_spec.
          etrans; [|apply Time.incr_spec]. auto.
        - exists (Time.incr fmin). splits; try apply Time.incr_spec.
          eapply TimeFacts.le_lt_lt; [|apply Time.incr_spec].
          destruct (TimeFacts.le_lt_dec fpto fmin); ss.
          exploit COMPLETE; try exact FGET; ss. i. des.
          exploit MAP_EQ_INV; [|exact TO|exact TO0|]; ss. i. subst.
          rewrite H in *. timetac.
      }
      des.
      assert (exists ffrom,
                 (<<FTS: Time.lt ffrom fto>>) /\
                 (<<FPREV_FROM: Time.le fpto ffrom>>) /\
                 (<<FMIN_FROM: Time.lt fmin ffrom>>) /\
                 (<<PREV_EQ: __guard__ (pto = from <-> fpto = ffrom)>>)).
      { inv PREV_FROM.
        - inv PTO_MAX.
          + exists (Time.middle fpto fto).
            exploit Time.middle_spec; try exact FPREV_TO. i. des.
            unguard. splits; ss.
            * econs. ss.
            * exploit FTO_IN; ss. i. etrans; eassumption.
            * split; i; subst; timetac.
              rewrite H1 in x0 at 1. timetac.
          + exists (Time.middle fmin fto).
            exploit Time.middle_spec; try exact FMIN_TO. i. des.
            unguard. splits; ss.
            * econs. eapply TimeFacts.le_lt_lt; try exact x0.
              destruct (TimeFacts.le_lt_dec fpto fmin); ss.
              exploit COMPLETE; try exact FGET; ss. i. des.
              exploit MAP_EQ_INV; [|exact TO|exact TO0|]; ss. i. subst.
              rewrite H0 in *. timetac.
            * split; i; subst; timetac.
              exploit COMPLETE; try exact FGET; ss. i. des.
              exploit MAP_EQ_INV; [|exact TO|exact TO0|]; ss. i. subst.
              rewrite H0 in *. timetac.
        - inv H. exists fpto. unguard. splits; ss; try refl. auto.
      }
      des.
      exists ffrom, fto. esplits; [refl|..].

      { (* map_wf *)
        econs.
        - (* map_inhabited *)
          repeat apply add_map_inhabited. ss.
        - (* map_eq *)
          apply add_map_eq.
          { apply add_map_eq; ss. i. exfalso. eauto. }
          unfold map_add. i. des; subst; timetac.
          inv PREV_FROM.
          + exfalso. eauto.
          + inv H. unguard. des. rewrite PREV_EQ in *; ss. eauto.
        - (* map_eq_inv *)
          apply add_map_eq_inv.
          { apply add_map_eq_inv; ss. i.
            exfalso. eapply FEMPTY; eauto.
          }
          unfold map_add. i. des; subst; timetac.
          inv FPREV_FROM.
          + exfalso. eapply FEMPTY; eauto.
          + inv H. unguard. des. rewrite PREV_EQ0 in *; ss.
            eapply MAP_EQ_INV; try exact MAP; ss.
        - (* map_lt *)
          apply add_map_lt.
          { apply add_map_lt; ss. i.
            destruct (TimeFacts.le_lt_dec ts' pto).
            { left. split.
              - eapply TimeFacts.le_lt_lt; try exact l.
                eapply TimeFacts.le_lt_lt; eauto.
              - exploit map_le; try exact l; try eassumption. i.
                eapply TimeFacts.le_lt_lt; try exact x0. ss.
            }
            exploit EMPTY; try exact l; eauto. ss.
          }
          unfold map_add. i. des; subst; timetac.
          destruct (TimeFacts.le_lt_dec pto ts'); cycle 1.
          { left. split.
            - eapply TimeFacts.lt_le_lt; try exact l; ss.
            - exploit MAP_LT; try exact l; try eassumption. i.
              eapply TimeFacts.lt_le_lt; try exact x0; ss.
          }
          inv l; cycle 1.
          { inv H. inv PREV_FROM.
            - left. split; ss.
              exploit MAP_EQ;[|exact TO|exact MAP|]; ss. i. subst.
              inv FPREV_FROM; ss. inv H0. unguard. des.
              rewrite PREV_EQ0 in *; ss. timetac.
            - inv H. right. left. split; ss.
              unguard. des. rewrite PREV_EQ in *; ss.
              eapply MAP_EQ; try eassumption; ss.
          }
          exploit EMPTY; try exact H; eauto. ss.
        - (* map_lt_inv *)
          apply add_map_lt_inv.
          { apply add_map_lt_inv; ss. i.
            destruct (TimeFacts.le_lt_dec fts' fpto).
            { left. split.
              - exploit map_le_inv; try exact l; try eassumption. i.
                eapply TimeFacts.le_lt_lt; try exact x0. ss.
              - eapply TimeFacts.le_lt_lt; try exact l.
                eapply TimeFacts.le_lt_lt; eauto.
            }
            exploit FEMPTY; try exact l; eauto. ss.
          }
          unfold map_add. i. des; subst; timetac.
          destruct (TimeFacts.le_lt_dec fpto fts'); cycle 1.
          { left. split.
            - exploit MAP_LT_INV; try exact l; try eassumption. i.
              eapply TimeFacts.lt_le_lt; try exact x0; ss.
            - eapply TimeFacts.lt_le_lt; try exact l; ss.
          }
          inv l; cycle 1.
          { inv H. inv FPREV_FROM.
            - left. split; ss.
              exploit MAP_EQ_INV;[|exact TO|exact MAP|]; ss. i. subst.
              inv PREV_FROM; ss. inv H0. unguard. des.
              rewrite PREV_EQ in *; ss. timetac.
            - inv H. right. left. split; ss.
              unguard. des. rewrite PREV_EQ0 in *; ss.
              eapply MAP_EQ_INV; try eassumption; ss.
          }
          exploit FEMPTY; try exact H; eauto. ss.
      }

      i. exploit (@Memory.add_exists fmem1 loc); try exact FTS; try exact FMSG_WF.
      { ii. inv LHS. inv RHS. ss.
        exploit TimeFacts.lt_le_lt; [exact FROM0|exact TO1|]. i.
        exploit TimeFacts.lt_le_lt; [exact FROM1|exact TO0|]. i.
        clear x FROM0 TO0 FROM1 TO1.
        exploit COMPLETE; try exact GET2.
        { etrans; eassumption. }
        i. des.
        exploit TimeFacts.le_lt_lt; [exact FPREV_FROM|exact x1|]. i.
        exploit MAP_LT_INV; try exact x0; try eassumption. i.
        exploit COMPLETE; try exact GET2.
        { etrans; try exact x1. ss. }
        i. des.
        exploit TimeFacts.le_lt_lt; [exact FPREV_FROM|exact x1|]. i.
        exploit MAP_LT_INV; try exact x0; try eassumption. i. eauto.
      }
      i. des. esplits; try exact x0.

      { (* map_complete *)
        exploit Memory.add_get0; try exact ADD. i. des.
        exploit Memory.add_get0; try exact x0. i. des.
        unfold map_add. ii. des; subst.
        - esplits; eauto. unguard. auto.
        - esplits; eauto. unguard. auto.
        - exploit COMPLETE1; try exact MAP. i. des.
          exploit Memory.add_get1; try exact GET3; eauto. i.
          exploit Memory.add_get1; try exact FGET0; eauto. i.
          esplits; try exact x2; try exact x3; eauto.
      }

      { (* memory_map *)
        ii. destruct (Loc.eq_dec loc0 loc); cycle 1.
        { destruct (MAP1 loc0).
          - econs 1.
            + instantiate (1:=fmax). i. revert GET.
              erewrite Memory.add_o; eauto. condtac; ss.
              { des. subst. congr. }
              i. guardH o.
              exploit SOUND0; eauto. i. des.
              exploit Memory.add_get1; try exact FGET1; eauto. i.
              esplits; try exact x1; eauto using map_add_incr.
              do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
            + i. revert FGET0.
              erewrite Memory.add_o; eauto. condtac; ss.
              { des. subst. congr. }
              i. guardH o.
              exploit COMPLETE0; eauto. i. des; eauto. right.
              exploit Memory.add_get1; try exact GET; eauto. i.
              esplits; try exact x1; eauto using map_add_incr.
              do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
          - econs 2.
            + instantiate (1:=fmin0). i. revert GET.
              erewrite Memory.add_o; eauto. condtac; ss.
              { des. subst. congr. }
              i. guardH o.
              exploit SOUND0; eauto. i. des.
              exploit Memory.add_get1; try exact FGET1; eauto. i.
              esplits; try exact x1; eauto using map_add_incr.
              do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
            + i. revert FGET0.
              erewrite Memory.add_o; eauto. condtac; ss.
              { des. subst. congr. }
              i. guardH o.
              exploit COMPLETE0; eauto. i. des.
              exploit Memory.add_get1; try exact GET; eauto. i.
              esplits; try exact x1; eauto using map_add_incr.
              do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
        }

        subst. rewrite RSV. econs.
        { instantiate (1:=fmin). i. revert GET.
          erewrite Memory.add_o; eauto. condtac; ss.
          - i. des. inv GET.
            exploit Memory.add_get0; try exact x0. i. des.
            esplits; try exact GET0; auto 6.
          - i. des; ss.
            exploit SOUND; eauto. i. des.
            exploit Memory.add_get1; try exact FGET0; eauto. i.
            esplits; try exact x1; auto.
            do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
        }
        { i. revert FGET0.
          erewrite Memory.add_o; eauto. condtac; ss.
          - i. des. inv FGET0.
            exploit Memory.add_get0; try exact ADD. i. des.
            esplits; try exact GET0; auto 6.
            etrans; eauto.
          - i. des; ss.
            exploit COMPLETE; try exact FGET0; ss. i. des; auto.
            exploit Memory.add_get1; try exact GET; eauto. i.
            esplits; try exact x1; auto 6.
            do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
        }
      }
    }
  }
Qed.

Lemma map_readable
      f tview ftview
      loc to fto ord
      (MAP_WF: map_wf f)
      (TVIEW: tview_map f tview ftview)
      (TO: f loc to fto)
      (READABLE: TView.readable (TView.cur tview) loc to ord):
  TView.readable (TView.cur ftview) loc fto ord.
Proof.
  inv READABLE. econs.
  - eapply map_le; try exact PLN; try apply MAP_WF; eauto. apply TVIEW.
  - i. eapply map_le; try eapply RLX; try apply MAP_WF; eauto. apply TVIEW.
Qed.

Lemma read_tview_map
      f tview ftview
      loc to fto released freleased ord
      (MAP_WF: map_wf f)
      (TVIEW: tview_map f tview ftview)
      (TO: f loc to fto)
      (RELEASED: opt_view_map f released freleased):
  tview_map f
            (TView.read_tview tview loc to released ord)
            (TView.read_tview ftview loc fto freleased ord).
Proof.
  unfold TView.read_tview.
  econs; s; (try condtac); (repeat apply view_join_map); ss;
    try apply TVIEW; try apply bot_view_map; ss;
    try apply unwrap_map; ss;
    eauto using singleton_rw_map, singleton_ur_map, singleton_ur_if_map.
Qed.

Lemma map_read_step
      max rsv
      f1 lc1 gl1 flc1 fgl1
      loc to val released ord lc2
      (MAP_WF1: map_wf f1)
      (MAP_COMPLETE1: map_complete f1 (Global.memory gl1) (Global.memory fgl1))
      (LC_MAP1: local_map f1 lc1 flc1)
      (GL_MAP1: global_map f1 max rsv gl1 fgl1)
      (MAX: Memory.closed_timemap max (Global.memory gl1))
      (STEP: Local.read_step lc1 gl1 loc to val released ord lc2):
  exists fto freleased flc2,
    (<<FSTEP: Local.read_step flc1 fgl1 loc fto val freleased ord flc2>>) /\
    (<<TO_MAP: f1 loc to fto>>) /\
    (<<RELEASED_MAP: opt_view_map f1 released freleased>>) /\
    (<<LC_MAP2: local_map f1 lc2 flc2>>).
Proof.
  inv STEP. exploit memory_map_get; try apply GL_MAP1; eauto. i. des. inv MSG.
  esplits; eauto.
  - econs; eauto.
    eapply map_readable; try apply LC_MAP1; eauto.
  - econs; s; try apply LC_MAP1.
    apply read_tview_map; ss. apply LC_MAP1.
Qed.

Lemma map_writable
      f tview ftview
      loc to fto ord
      (MAP_WF: map_wf f)
      (TVIEW: tview_map f tview ftview)
      (TO: f loc to fto)
      (WRITABLE: TView.writable (TView.cur tview) loc to ord):
  TView.writable (TView.cur ftview) loc fto ord.
Proof.
  inv MAP_WF. inv WRITABLE. econs.
  eapply MAP_LT; try exact TS; eauto. apply TVIEW.
Qed.

Lemma write_tview_map
      f tview ftview
      loc to fto ord
      (MAP_WF: map_wf f)
      (TVIEW: tview_map f tview ftview)
      (TO: f loc to fto):
  tview_map f (TView.write_tview tview loc to ord) (TView.write_tview ftview loc fto ord).
Proof.
  econs; s; i.
  - unfold LocFun.add.
    repeat condtac; try apply TVIEW.
    + apply view_join_map; ss; try apply TVIEW.
      apply singleton_ur_map; ss.
    + apply view_join_map; ss; try apply TVIEW.
      apply singleton_ur_map; ss.
  - apply view_join_map; ss; try apply TVIEW.
    apply singleton_ur_map; ss.
  - apply view_join_map; ss; try apply TVIEW.
    apply singleton_ur_map; ss.
Qed.

Lemma write_released_map
      f tview ftview
      loc to fto releasedm freleasedm ord
      (MAP_WF: map_wf f)
      (TVIEW: tview_map f tview ftview)
      (TO: f loc to fto)
      (RELEASEDM: opt_view_map f releasedm freleasedm):
  opt_view_map f
               (TView.write_released tview loc to releasedm ord)
               (TView.write_released ftview loc fto freleasedm ord).
Proof.
  unfold TView.write_released. condtac; econs.
  apply view_join_map; ss.
  - apply unwrap_map; ss.
  - unfold LocFun.add. condtac; ss.
    condtac; apply view_join_map; ss;
      try apply TVIEW; apply singleton_ur_map; ss.
Qed.

Lemma map_write_step
      reserved freserved rsv
      f1 lc1 gl1 flc1 fgl1
      loc from to val releasedm released ord lc2 gl2
      freleasedm
      (MAP_WF1: map_wf f1)
      (MAP_COMPLETE1: map_complete f1 (Global.memory gl1) (Global.memory fgl1))
      (LC_MAP1: local_map f1 lc1 flc1)
      (GL_MAP1: global_map f1 reserved rsv gl1 fgl1)
      (LC_WF1: Local.wf lc1 gl1)
      (GL_WF1: Global.wf gl1)
      (FLC_WF1: Local.wf flc1 fgl1)
      (RESERVED: Memory.closed_timemap reserved (Global.memory gl1))
      (RESERVES: Local.reserves lc1 = rsv)
      (GRESERVES: Global.reserves gl1 = BoolMap.top)
      (FGRESERVES: Global.reserves fgl1 = BoolMap.bot)
      (RELEASEDM_MAP: opt_view_map f1 releasedm freleasedm)
      (FRELEASEDM: View.opt_wf freleasedm)
      (STEP: Local.write_step reserved lc1 gl1 loc from to val releasedm released ord lc2 gl2):
  exists f2 ffrom fto freleased flc2 fgl2,
    (<<FSTEP: Local.write_step freserved flc1 fgl1 loc ffrom fto val freleasedm freleased ord flc2 fgl2>>) /\
    (<<F2: f2 = map_add loc from ffrom (map_add loc to fto f1)>>) /\
    (<<MAP_WF2: map_wf f2>>) /\
    (<<MAP_COMPLETE2: map_complete f2 (Global.memory gl2) (Global.memory fgl2)>>) /\
    (<<FROM_MAP: f2 loc from ffrom>>) /\
    (<<TO_MAP: f2 loc to fto>>) /\
    (<<RELEASED_MAP: opt_view_map f2 released freleased>>) /\
    (<<LC_MAP2: local_map f2 lc2 flc2>>) /\
    (<<GL_MAP2: global_map f2 reserved rsv gl2 fgl2>>).
Proof.
  destruct lc1 as [tview1 prm1 rsv1].
  destruct flc1 as [ftview1 fprm1 frsv1].
  destruct gl1 as [sc1 gprm1 grsv1 mem1].
  destruct fgl1 as [fsc1 fgprm1 fgrsv1 fmem1].
  inv LC_MAP1. inv GL_MAP1. ss. subst.
  inv STEP. ss.
  exploit memory_map_add; try exact MEMORY; eauto; try apply GL_WF1. i. des.
  assert (REL: opt_view_map
                 f2
                 (TView.write_released tview1 loc to releasedm ord)
                 (TView.write_released ftview1 loc fto freleasedm ord)).
  { subst. eapply write_released_map; ss.
    - eapply tview_map_incr; try exact TVIEW.
      i. repeat apply map_add_incr. ss.
    - auto 6.
    - eapply opt_view_map_incr; try exact RELEASEDM_MAP.
      i. repeat apply map_add_incr. ss.
  }
  exploit x0; [|econs; eauto|].
  { econs. eapply TViewFacts.write_future0; ss. apply FLC_WF1. }
  i. des. clear x0. subst.
  esplits; eauto 6.
  - econs; try exact FADD; eauto; s.
    + eapply map_writable; try exact WRITABLE; try exact WF2; auto 6.
      eapply tview_map_incr; try exact TVIEW.
      i. repeat apply map_add_incr. ss.
    + i. des. ss.
  - ss.
  - econs; ss.
    apply write_tview_map; ss; auto 6.
    eapply tview_map_incr; try apply TVIEW.
    i. repeat apply map_add_incr. ss.
  - econs; ss.
Qed.

Lemma write_fence_tview_map
      f tview ftview sc fsc ord
      (MAP_WF: map_wf f)
      (TVIEW: tview_map f tview ftview)
      (ORD: Ordering.le ord Ordering.acqrel):
  tview_map f (TView.write_fence_tview tview sc ord) (TView.write_fence_tview ftview fsc ord).
Proof.
  econs; ss; i; repeat condtac;
    try apply view_join_map; ss; try apply TVIEW;
    try apply bot_view_map; ss;
    destruct ord; ss.
Qed.

Lemma read_fence_tview_map
      f tview ftview ord
      (MAP_WF: map_wf f)
      (TVIEW: tview_map f tview ftview):
  tview_map f (TView.read_fence_tview tview ord) (TView.read_fence_tview ftview ord).
Proof.
  econs; ss; i; repeat condtac;
    try apply view_join_map; ss; try apply TVIEW;
    try apply bot_view_map; ss.
Qed.

Lemma map_fence_step
      reserved rsv
      f1 lc1 gl1 flc1 fgl1
      ordr ordw lc2 gl2
      (MAP_WF1: map_wf f1)
      (MAP_COMPLETE1: map_complete f1 (Global.memory gl1) (Global.memory fgl1))
      (LC_MAP1: local_map f1 lc1 flc1)
      (GL_MAP1: global_map f1 reserved rsv gl1 fgl1)
      (FPROMISES: Local.promises flc1 = BoolMap.bot)
      (ORD: Ordering.le ordw Ordering.acqrel)
      (STEP: Local.fence_step lc1 gl1 ordr ordw lc2 gl2):
  exists flc2 fgl2,
    (<<FSTEP: Local.fence_step flc1 fgl1 ordr ordw flc2 fgl2>>) /\
    (<<MAP_COMPLETE2: map_complete f1 (Global.memory gl2) (Global.memory fgl2)>>) /\
    (<<LC_MAP2: local_map f1 lc2 flc2>>) /\
    (<<GL_MAP2: global_map f1 reserved rsv gl2 fgl2>>).
Proof.
  inv STEP.
  esplits.
  - econs; eauto.
  - ss.
  - econs; try apply LC_MAP1. s.
    apply write_fence_tview_map; ss; try apply GL_MAP1.
    apply read_fence_tview_map; ss. apply LC_MAP1.
  - econs; try apply GL_MAP1.
Qed.

Lemma map_racy_view
      f view fview loc ts fts
      (MAP_WF: map_wf f)
      (VIEW: view_map f view fview)
      (TS: f loc ts fts)
      (RACY: TView.racy_view view loc ts):
  TView.racy_view fview loc fts.
Proof.
  inv MAP_WF. unfold TView.racy_view in *.
  eapply MAP_LT; try exact RACY; eauto.
  apply VIEW.
Qed.

Lemma map_is_racy
      reserved rsv
      f1 lc1 gl1 flc1 fgl1
      loc to ord
      (MAP_WF1: map_wf f1)
      (LC_MAP1: local_map f1 lc1 flc1)
      (GL_MAP1: global_map f1 reserved rsv gl1 fgl1)
      (STEP: Local.is_racy lc1 gl1 loc (Some to) ord):
  exists fto,
    (<<FSTEP: Local.is_racy flc1 fgl1 loc (Some fto) ord>>) /\
    (<<TO: f1 loc to fto>>).
Proof.
  inv LC_MAP1. inv GL_MAP1.
  inv STEP.
  exploit memory_map_get; eauto. i. des. inv MSG0.
  esplits; [econs 2|]; eauto.
  eapply map_racy_view; try apply TVIEW; eauto.
Qed.

Lemma map_racy_read_step
      reserved rsv
      f1 lc1 gl1 flc1 fgl1
      loc to val ord
      (MAP_WF1: map_wf f1)
      (LC_MAP1: local_map f1 lc1 flc1)
      (GL_MAP1: global_map f1 reserved rsv gl1 fgl1)
      (STEP: Local.racy_read_step lc1 gl1 loc (Some to) val ord):
  exists fto,
    (<<FSTEP: Local.racy_read_step flc1 fgl1 loc (Some fto) val ord>>) /\
    (<<TO: f1 loc to fto>>).
Proof.
  inv STEP.
  exploit map_is_racy; eauto. i. des.
  esplits; eauto.
Qed.

Lemma map_racy_write_step
      reserved rsv
      f1 lc1 gl1 flc1 fgl1
      loc to ord
      (MAP_WF1: map_wf f1)
      (LC_MAP1: local_map f1 lc1 flc1)
      (GL_MAP1: global_map f1 reserved rsv gl1 fgl1)
      (STEP: Local.racy_write_step lc1 gl1 loc (Some to) ord):
  exists fto,
    (<<FSTEP: Local.racy_write_step flc1 fgl1 loc (Some fto) ord>>) /\
    (<<TO: f1 loc to fto>>).
Proof.
  inv STEP.
  exploit map_is_racy; eauto. i. des.
  esplits; eauto.
Qed.

Lemma map_racy_update_step
      reserved rsv
      f1 lc1 gl1 flc1 fgl1
      loc to ordr ordw
      (MAP_WF1: map_wf f1)
      (LC_MAP1: local_map f1 lc1 flc1)
      (GL_MAP1: global_map f1 reserved rsv gl1 fgl1)
      (RACE: to = None -> Ordering.le ordr Ordering.na \/ Ordering.le ordw Ordering.na)
      (STEP: Local.racy_update_step lc1 gl1 loc to ordr ordw):
  exists fto,
    (<<FSTEP: Local.racy_update_step flc1 fgl1 loc fto ordr ordw>>) /\
    (<<TO: option_rel (f1 loc) to fto>>).
Proof.
  inv STEP.
  - esplits; eauto. ss.
  - esplits; eauto. ss.
  - destruct to.
    + exploit map_is_racy; eauto. i. des. eauto.
    + exploit RACE; eauto.
      i. des; esplits; eauto; ss.
Qed.

Lemma map_program_step
      reserved freserved
      rsv
      f1 lc1 gl1 flc1 fgl1
      e lc2 gl2
      (MAP_WF1: map_wf f1)
      (MAP_COMPLETE1: map_complete f1 (Global.memory gl1) (Global.memory fgl1))
      (LC_MAP1: local_map f1 lc1 flc1)
      (GL_MAP1: global_map f1 reserved rsv gl1 fgl1)
      (LC_WF1: Local.wf lc1 gl1)
      (GL_WF1: Global.wf gl1)
      (FLC_WF1: Local.wf flc1 fgl1)
      (FGL_WF1: Global.wf fgl1)
      (RESERVED: Memory.closed_timemap reserved (Global.memory gl1))
      (FPROMISES: Local.promises flc1 = BoolMap.bot)
      (RESERVES: Local.reserves lc1 = rsv)
      (GRESERVES: Global.reserves gl1 = BoolMap.top)
      (FGRESERVES: Global.reserves fgl1 = BoolMap.bot)
      (STEP: Local.program_step reserved e lc1 gl1 lc2 gl2)
      (EVENT1: ~ ThreadEvent.is_racy_promise e)
      (EVENT2: ~ ThreadEvent.is_sc e):
  exists f2 fe flc2 fgl2,
    (<<FSTEP: Local.program_step freserved fe flc1 fgl1 flc2 fgl2>>) /\
    (<<EVENT: event_map f2 e fe>>) /\
    (<<MAP_INCR: f1 <3= f2>>) /\
    (<<MAP_WF2: map_wf f2>>) /\
    (<<MAP_COMPLETE2: map_complete f2 (Global.memory gl2) (Global.memory fgl2)>>) /\
    (<<LC_MAP2: local_map f2 lc2 flc2>>) /\
    (<<GL_MAP2: global_map f2 reserved rsv gl2 fgl2>>).
Proof.
  inv STEP.
  - esplits; [econs 1|..]; eauto. econs.
  - exploit map_read_step; eauto. i. des.
    esplits; [econs 2|..]; eauto. econs; ss.
  - exploit map_write_step; eauto; try by econs. i. des.
    esplits; [econs 3|..]; try exact MAP_WF2; eauto.
    + econs; ss.
    + i. subst. repeat apply map_add_incr; ss.
  - exploit map_read_step; eauto. i. des.
    exploit Local.read_step_future; try exact LOCAL1; eauto. i. des.
    exploit Local.read_step_future; try exact FSTEP; eauto. i. des.
    exploit map_write_step; try exact LOCAL2; eauto.
    { inv LOCAL1. ss. }
    i. des.
    replace fto with ffrom in *; cycle 1.
    { inv MAP_WF2. eapply MAP_EQ; [refl|exact FROM_MAP|..]. auto. }
    esplits; [econs 4|..]; try exact MAP_WF2; eauto.
    + econs; ss.
      eapply opt_view_map_incr; try exact RELEASED_MAP.
      i. subst. repeat apply map_add_incr; ss.
    + i. subst. repeat apply map_add_incr; ss.
  - exploit map_fence_step; eauto.
    { destruct ordw; ss. }
    i. des.
    esplits; [econs 5|..]; eauto. econs; ss.
  - exploit map_fence_step; eauto; ss.
  - esplits; [econs 7|..]; eauto. econs.
  - destruct to; ss.
    exploit map_racy_read_step; eauto. i. des.
    esplits; [econs 8|..]; eauto. econs; ss.
  - destruct to; ss.
    exploit map_racy_write_step; eauto. i. des.
    esplits; [econs 9|..]; eauto. econs; ss.
  - exploit map_racy_update_step; eauto.
    { i. subst. ss.
      apply not_and_or in EVENT1. des.
      - left. destruct ordr; ss.
      - right. destruct ordw; ss.
    }
    i. des.
    esplits; [econs 10|..]; eauto. econs; ss.
Qed.
