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

Require Import Cover.

Set Implicit Arguments.
Set Nested Proofs Allowed.


Definition map_t: Type := Loc.t -> Time.t -> Time.t -> Prop.

Ltac ett := eapply TimeFacts.le_lt_lt.
Ltac tet := eapply TimeFacts.lt_le_lt.

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

  Definition map_finite: Prop :=
    exists dom,
    forall loc ts fts (MAP: f loc ts fts),
      List.In ts dom.

  Variant map_wf: Prop :=
    | map_wf_intro
        (MAP_INHABITED: map_inhabited)
        (MAP_FINITE: map_finite)
        (MAP_EQ: map_eq)
        (MAP_EQ_INV: map_eq_inv)
        (MAP_LT: map_lt)
        (MAP_LT_INV: map_lt_inv)
  .

  (* TODO: remove *)
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
    | message_map_message
        val view fview na
        (RELEASED: opt_view_map view fview):
      message_map (Message.message val view na) (Message.message val fview na)
    | message_map_reserve:
      message_map Message.reserve Message.reserve
  .

  (* Variant memory_map (rsv: Memory.t) (mem fmem: Memory.t): Prop := *)
  (*   | memory_map_intro *)
  (*       (SOUND: forall loc from to msg *)
  (*                      (GET: Memory.get loc to mem = Some (from, msg)), *)
  (*           (<<RESERVE: msg = Message.reserve>>) \/ *)
  (*           exists ffrom fto fmsg, *)
  (*             (<<FGET: Memory.get loc fto fmem = Some (ffrom, fmsg)>>) /\ *)
  (*             (<<FROM: f loc from ffrom>>) /\ *)
  (*             (<<TO: f loc to fto>>) /\ *)
  (*             (<<MSG: message_map msg fmsg>>)) *)
  (*       (COMPLETE: forall loc ffrom fto fmsg *)
  (*                         (FGET: Memory.get loc fto fmem = Some (ffrom, fmsg)), *)
  (*           exists ffrom' fto' from to msg, *)
  (*             (<<RSV: Memory.get loc to rsv = None>>) /\ *)
  (*             (<<GET: Memory.get loc to mem = Some (from, msg)>>) /\ *)
  (*             (<<FFROM: Time.le ffrom' ffrom>>) /\ *)
  (*             (<<FTO: Time.le fto fto'>>) /\ *)
  (*             (<<FROM: f loc from ffrom'>>) /\ *)
  (*             (<<TO: f loc to fto'>>)) *)
  (* . *)

  Variant memory_map (rsv: Memory.t) (mem fmem: Memory.t): Prop :=
    | memory_map_intro
        (SOUND: forall loc from to msg
                       (GET: Memory.get loc to mem = Some (from, msg)),
            (<<RESERVE: msg = Message.reserve>>) \/
            exists ffrom fto fmsg,
              (<<FGET: Memory.get loc fto fmem = Some (ffrom, fmsg)>>) /\
              (<<FROM: f loc from ffrom>>) /\
              (<<TO: f loc to fto>>) /\
              (<<MSG: message_map msg fmsg>>))
        (COMPLETE: forall loc ffrom fto fmsg
                          (FGET: Memory.get loc fto fmem = Some (ffrom, fmsg)),
            exists ffrom' fto' from to,
              (<<FFROM: Time.le ffrom' ffrom>>) /\
              (<<FTO: Time.le fto fto'>>) /\
              (<<FROM: f loc from ffrom'>>) /\
              (<<TO: f loc to fto'>>) /\
              (<<COVERED: forall ts (ITV: Interval.mem (from, to) ts), covered loc ts mem>>) /\
              (<<RESERVED: forall f t m
                             (GET: Memory.get loc t rsv = Some (f, m)),
                  Interval.disjoint (f, t) (from, to)>>))
  .

  Variant local_map (lc flc: Local.t): Prop :=
    | local_map_intro
        (TVIEW: tview_map (Local.tview lc) (Local.tview flc))
  .

  Variant global_map (rsv: Memory.t) (gl fgl: Global.t): Prop :=
    | global_map_intro
        (MEMORY: memory_map rsv (Global.memory gl) (Global.memory fgl))
  .

  Variant event_map: forall (e fe: ThreadEvent.t), Prop :=
    | event_map_promise
        loc:
      event_map (ThreadEvent.promise loc) (ThreadEvent.promise loc)
    | event_map_reserve
        loc from to ffrom fto
        (FROM: f loc from ffrom)
        (TO: f loc to fto):
      event_map (ThreadEvent.reserve loc from to) (ThreadEvent.reserve loc ffrom fto)
    | event_map_cancel
        loc from to ffrom fto
        (FROM: f loc from ffrom)
        (TO: f loc to fto):
      event_map (ThreadEvent.cancel loc from to) (ThreadEvent.cancel loc ffrom fto)
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
  i. inv PR; econs.
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
  - econs 2; eauto.
  - econs 3; eauto.
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
      f rsv mem fmem
      loc from to msg
      (MAP: memory_map f rsv mem fmem)
      (GET: Memory.get loc to mem = Some (from, msg))
      (RESERVE: msg <> Message.reserve):
  exists ffrom fto fmsg,
    (<<FGET: Memory.get loc fto fmem = Some (ffrom, fmsg)>>) /\
    (<<FROM: f loc from ffrom>>) /\
    (<<TO: f loc to fto>>) /\
    (<<MSG: message_map f msg fmsg>>).
Proof.
  destruct MAP.
  exploit SOUND; eauto. i. des; try congr.
  esplits; eauto.
Qed.

Lemma memory_map_closed_timemap
      f rsv mem fmem
      tm ftm
      (WF: map_wf f)
      (MEMORY: memory_map f rsv mem fmem)
      (TIMEMAP: timemap_map f tm ftm)
      (CLOSED: Memory.closed_timemap tm mem):
  Memory.closed_timemap ftm fmem.
Proof.
  ii. specialize (CLOSED loc). des.
  exploit memory_map_get; eauto; ss. i. des. inv MSG.
  specialize (TIMEMAP loc).
  inv WF. exploit MAP_EQ; [|exact TIMEMAP|exact TO|]; ss. i. subst.
  esplits; eauto.
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
    (<<PREV: Time.le pto from>>) /\
    (<<PREV_TS: Time.le pfrom pto>>) /\
    (<<PEMPTY: Memory.empty mem1 loc pto to>>) /\
    __guard__ (
        (exists nfrom nto nmsg,
            (<<NGET: Memory.get loc nto mem1 = Some (nfrom, nmsg)>>) /\
            (<<NEXT: Time.le to nfrom>>) /\
            (<<NEXT_TS: Time.lt nfrom nto>>) /\
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
  { exploit Memory.get_ts; try exact x1. i. des; timetac. }
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
    exploit Memory.get_ts; try exact x4. i. des; timetac.
    esplits; eauto.
    exploit Memory.add_get1; try exact x4; eauto. i.
    eapply lt_get_from; eauto.
  }
Qed.

(* Lemma memory_map_add *)
(*       f1 rsv mem1 fmem1 *)
(*       loc from to msg mem2 *)
(*       (WF1: map_wf f1) *)
(*       (COMPLETE1: map_complete f1 mem1 fmem1) *)
(*       (MAP1: memory_map f1 rsv mem1 fmem1) *)
(*       (LE: Memory.le rsv mem1) *)
(*       (INHABITED1: Memory.inhabited mem1) *)
(*       (ADD: Memory.add mem1 loc from to msg mem2): *)
(*   exists ffrom fto f2, *)
(*     (<<F2: f2 = map_add loc from ffrom (map_add loc to fto f1)>>) /\ *)
(*     (<<WF2: map_wf f2>>) /\ *)
(*     forall fmsg *)
(*       (FMSG_WF: Message.wf fmsg) *)
(*       (MSG_MAP: message_map f2 msg fmsg), *)
(*     exists fmem2, *)
(*       (<<FADD: Memory.add fmem1 loc ffrom fto fmsg fmem2>>) /\ *)
(*       (<<COMPLETE2: map_complete f2 mem2 fmem2>>) /\ *)
(*       (<<MAP2: memory_map f2 rsv mem2 fmem2>>). *)
(* Proof. *)
(*   inv WF1. inv MAP1. *)
(*   exploit Memory.add_ts; eauto. intro TS. *)
(*   exploit add_cases; eauto. i. unguard. des. *)

(*   { (* target non-latest *) *)
(*     assert (EMPTY: Memory.empty mem1 loc pto nto). *)
(*     { ii. destruct (TimeFacts.le_lt_dec ts to); cycle 1. *)
(*       { eapply NEMPTY; eauto. } *)
(*       inv l. *)
(*       { eapply PEMPTY; eauto. } *)
(*       inv H. *)
(*       exploit Memory.add_get0; eauto. i. des. congr. *)
(*     } *)

(*     assert (MAP_EMPTY: forall ts fts *)
(*                          (LT1: Time.lt pto ts) *)
(*                          (LT2: Time.lt ts nfrom) *)
(*                          (MAP: f1 loc ts fts), *)
(*                False). *)
(*     { i. exploit COMPLETE1; try exact MAP. i. unguardH x0. des; subst. *)
(*       - destruct (TimeFacts.le_lt_dec to to0); cycle 1. *)
(*         { exploit PEMPTY; try exact l; try congr. *)
(*           exploit Memory.get_ts; try exact GET. i. *)
(*           des; subst; timetac. etrans; eauto. *)
(*         } *)
(*         inv l; cycle 1. *)
(*         { inv H. exploit Memory.add_get0; try exact ADD. i. des. congr. } *)
(*         destruct (TimeFacts.le_lt_dec nto to0); cycle 1. *)
(*         { exploit NEMPTY; try exact l; ss. congr. } *)
(*         exploit Memory.get_disjoint; [exact NGET|exact GET|]. *)
(*         i. des; subst; timetac. *)
(*         exploit Memory.get_ts; try exact NGET. i. des; subst; timetac. *)
(*         apply (x0 nto); econs; ss; try refl. *)
(*         etrans; eauto. *)
(*       - destruct (TimeFacts.le_lt_dec to to0); cycle 1. *)
(*         { exploit PEMPTY; try exact l; try congr. } *)
(*         inv l; cycle 1. *)
(*         { inv H. exploit Memory.add_get0; try exact ADD. i. des. congr. } *)
(*         exploit NEMPTY; try exact H; try congr. *)
(*         exploit Memory.get_ts; try exact NGET. i. des; subst; timetac. *)
(*         etrans; eauto. *)
(*     } *)

(*     assert (Time.lt pto nfrom). *)
(*     { eapply TimeFacts.le_lt_lt; try exact PREV. *)
(*       eapply TimeFacts.lt_le_lt; eauto. *)
(*     } *)

(*     specialize (Memory.max_exists *)
(*                   (fun fpto => exists ts fts, f1 loc ts fts /\ Time.le ts pto /\ Time.le fpto fts) *)
(*                   loc fmem1). *)
(*     i. des. *)
(*     { exploit SOUND; try eapply INHABITED1. i. des; ss. *)
(*       exploit MAP_EQ; [|exact TO|eapply MAP_INHABITED|]; ss. i. subst. *)
(*       exploit NONE; try exact FGET; ss. *)
(*       esplits; eauto; timetac. *)
(*     } *)
(*     rename from_max into fpfrom, to_max into fpto, msg_max into fpmsg. *)
(*     rename GET into FPGET, SAT into PTO_MAP, SAT0 into PTO_LE, SAT1 into FPTO_LE, MAX into PTO_MAX. *)

(*     specialize (Memory.min_exists *)
(*                   (fun fnto => exists ts fts, f1 loc ts fts /\ Time.le nfrom ts /\ Time.lt fts fnto) *)
(*                   loc fmem1). *)
(*     i. des. *)

(*     { (* source latest *) *)
(*       assert (FEMPTY: forall fto (FTO: Time.lt fpto fto), *)
(*                  Memory.get loc fto fmem1 = None). *)
(*       { i. destruct (Memory.get loc fto fmem1) as [[ffrom fmsg]|] eqn:FGET; ss. *)
(*         exfalso. *)
(*         exploit Memory.lt_get; try exact FTO; try eassumption. i. *)
(*         exploit Memory.get_ts; try exact FGET. i. des; subst; timetac. *)
(*         exploit COMPLETE; try exact FGET. i. des. *)
(*         Lemma covered_get *)
(*               mem loc from to *)
(*               (ITV: Time.lt from to) *)
(*               (COVERED: forall ts (ITV: Interval.mem (from, to) ts), *)
(*                   covered loc ts mem) *)
(*               (FROM: exists from' to' msg, *)
(*                   Memory.get loc to' mem = Some (from', msg) /\ *)
(*                   __guard__ (from' = from \/ to' = from)) *)
(*               (TO: exists from' to' msg, *)
(*                   Memory.get loc to' mem = Some (from', msg) /\ *)
(*                   __guard__ (from' = to \/ to' = to)): *)
(*           (<<GET_FROM: exists to' msg_from, *)
(*               Memory.get loc to' mem = Some (from, msg_from)>>) /\ *)
(*           (<<GET_TO: exists from' msg_to, *)
(*               Memory.get loc to mem = Some (from', msg_to)>>). *)
(*         Proof. *)
(*           split. *)
(*           { clear TO. unguard. des; subst; eauto. *)
(*             specialize (Memory.min_exists (Time.lt from) loc mem). i. des. *)
(*             { exfalso. exploit COVERED. *)
(*               { econs; s; [|refl]. ss. } *)
(*               i. inv x0. inv ITV0. ss. *)
(*               eapply NONE; try exact GET. *)
(*               tet; eassumption. *)
(*             } *)
(*             exploit Memory.lt_get; try exact SAT; eauto. i. *)
(*             inv x0; cycle 1. *)
(*             { inv H. eauto. } *)
(*             exfalso. *)
(*             exploit Memory.get_ts; try exact GET. i. des; timetac. *)
(*             destruct (TimeFacts.le_lt_dec from_min to). *)
(*             - exploit (COVERED from_min); ss. *)
(*               i. inv x1. inv ITV0. ss. *)
(*               exploit Memory.lt_from_get. *)
(*               { etrans; try exact FROM0. exact x0. } *)
(*               { eauto. } *)
(*               { eauto. } *)
(*               i. des; timetac. *)
(*               exploit TimeFacts.antisym; try exact TO; eauto. i. subst. *)
(*               exploit MIN; try exact GET0; ss. i. timetac. *)
(*             - exploit (COVERED to). *)
(*               { econs; ss. refl. } *)
(*               i. inv x1. inv ITV0. ss. *)
(*               exploit Memory.lt_from_get. *)
(*               { etrans; try exact FROM0. *)
(*                 etrans; try exact l. apply x0. *)
(*               } *)
(*               { eauto. } *)
(*               { eauto. } *)
(*               i. des; subst; timetac. *)
(*               exploit MIN; try exact GET0; timetac. i. *)
(*               exploit TimeFacts.le_lt_lt; try exact x1; try exact x0. i. timetac. *)
(*           } *)
(*           { clear FROM. unguard. des; subst; eauto. *)
(*             exploit Memory.get_ts; try exact TO. i. des; timetac. *)
(*             exploit COVERED. *)
(*             { econs; s; [|refl]. ss. } *)
(*             i. inv x1. inv ITV0. ss. *)
(*             exploit Memory.lt_from_get. *)
(*             { etrans; try exact FROM. apply x0. } *)
(*             { eauto. } *)
(*             { eauto. } *)
(*             i. des; timetac. *)
(*             exploit TimeFacts.antisym; try exact TO0; ss. i. subst. eauto. *)
(*           } *)
(*         Qed. *)
(*         exploit covered_get; try exact COVERED. *)
(*         { eapply MAP_LT_INV; try exact FROM; try exact TO. *)
(*           ett; try eassumption. tet; eassumption. *)
(*         } *)
(*         { exploit COMPLETE1; try exact FROM. i. des. *)
(*           esplits; try exact GET. *)
(*           unguard. des; subst; auto. *)
(*         } *)
(*         { exploit COMPLETE1; try exact TO. i. des. *)
(*           esplits; try exact GET. *)
(*           unguard. des; subst; auto. *)
(*         } *)
(*         i. des. *)
(*         exploit COVERED. *)
(*         { econs; [|refl]. s. *)
(*           eapply MAP_LT_INV; try exact FROM; try exact TO. *)
(*           ett; [eassumption|]. tet; [|eassumption]. ss. *)
(*         } *)
(*         s. i. inv x2. inv ITV. ss. *)
(*         destruct (TimeFacts.le_lt_dec to1 pto). *)
(*         { exploit PTO_MAX; try exact FGET; i; timetac. *)
(*           esplits; try exact TO; ss. etrans; eauto. *)
(*         } *)
(*         destruct (TimeFacts.le_lt_dec nto to1); cycle 1. *)
(*         { exploit EMPTY; try exact l; ss. congr. } *)
(*         inv l0. *)
(*         - exploit Memory.lt_get; try exact H0; try eassumption. i. *)
(*           eapply NONE; try exact FGET. *)
(*           esplits; try exact FROM. *)
(*         -  *)
(*         inv l0. *)
(*         { subst. eapply NONE; try exact FGET. *)
(*           esplits; try exact FROM; try refl. *)
(*           eapply TimeFacts.le_lt_lt; [eassumption|]. *)
(*           exploit Memory.get_ts; try exact FGET. i. des; ss. *)
(*           subst. timetac. *)
(*         } *)
(*         eapply NONE; try exact FGET. *)
(*         esplits; try exact FROM. *)
(*         - etrans; try exact x1. econs. ss. *)
(*         - eapply TimeFacts.le_lt_lt; try exact FFROM. *)
(*           exploit Memory.get_ts; try exact FGET. i. des; timetac. *)
(*       } *)

(*       assert (FMAP_EMPTY: forall ts fts *)
(*                             (LT: Time.lt fpto fts) *)
(*                             (MAP: f1 loc ts fts), *)
(*                  False). *)
(*       { i. exploit COMPLETE1; try exact MAP. i. des. *)
(*         assert (FPTO_FTO: Time.lt fpto fto). *)
(*         { unguard. des; subst; ss. *)
(*           exploit Memory.get_ts; try exact FGET. *)
(*           i. des; subst; timetac. etrans; eauto. *)
(*         } *)
(*         exploit FEMPTY; try exact FPTO_FTO. congr. *)
(*       } *)
(*       inv FPTO_LE. *)
(*       { exploit FMAP_EMPTY; try exact H0; eauto. ss. } *)
(*       symmetry in H0. inv H0. *)

(*       (* find ffrom and fto *) *)
(*       assert (exists ffrom fto, *)
(*                  (<<FPREV: Time.le fpto ffrom>>) /\ *)
(*                  (<<FPREV_EQ: __guard__ (ts = from <-> fpto = ffrom)>>) /\ *)
(*                  (<<FTS: Time.lt ffrom fto>>)). *)
(*       { destruct (Time.eq_dec ts from). *)
(*         { subst. inv PREV; timetac. inv H0. *)
(*           exists fpto, (Time.incr fpto). *)
(*           splits; ss; try refl. apply Time.incr_spec. *)
(*         } *)
(*         exists (Time.incr fpto), (Time.incr (Time.incr fpto)). *)
(*         splits. *)
(*         - econs. apply Time.incr_spec. *)
(*         - unguard. split; ss. i. *)
(*           specialize (Time.incr_spec fpto). *)
(*           rewrite H0 at 1. i. timetac. *)
(*         - apply Time.incr_spec. *)
(*       } *)
(*       des. *)
(*       exists ffrom, fto. esplits; [refl|..]. *)

(*       { (* map_wf *) *)
(*         econs. *)
(*         - (* map_inhabited *) *)
(*           repeat apply add_map_inhabited. ss. *)
(*         - (* map_eq *) *)
(*           apply add_map_eq. *)
(*           { apply add_map_eq; ss. i. *)
(*             exploit FMAP_EMPTY; try exact MAP; ss. *)
(*             eapply MAP_LT; try exact PTO_MAP; try exact MAP. *)
(*             eapply TimeFacts.le_lt_lt; [eassumption|]. *)
(*             eapply TimeFacts.le_lt_lt; eassumption. *)
(*           } *)
(*           unfold map_add. i. des; subst; timetac. *)
(*           rewrite PREV in PTO_LE. inv PTO_LE. *)
(*           { exfalso. eauto. } *)
(*           inv H0. unguard. des. *)
(*           exploit FPREV_EQ; try refl. i. subst. *)
(*           exploit MAP_EQ; [|exact PTO_MAP|exact MAP|]; ss. *)
(*         - (* map_eq_inv *) *)
(*           apply add_map_eq_inv. *)
(*           { apply add_map_eq_inv; ss. i. *)
(*             exploit FMAP_EMPTY; try exact MAP; ss. *)
(*             eapply TimeFacts.le_lt_lt; eassumption. *)
(*           } *)
(*           unfold map_add. i. des; subst; timetac. *)
(*           inv FPREV. *)
(*           { exfalso. eauto. } *)
(*           inv H0. unguard. des. *)
(*           exploit FPREV_EQ0; try refl. i. subst. *)
(*           exploit MAP_EQ_INV; [|exact PTO_MAP|exact MAP|]; ss. *)
(*         - (* map_lt *) *)
(*           apply add_map_lt. *)
(*           { apply add_map_lt; ss. i. *)
(*             destruct (TimeFacts.le_lt_dec ts' ts). *)
(*             { left. split. *)
(*               - eapply TimeFacts.le_lt_lt; try exact l. *)
(*                 eapply TimeFacts.le_lt_lt; try exact PTO_LE. *)
(*                 eapply TimeFacts.le_lt_lt; eauto. *)
(*               - exploit map_le; try exact l; try eassumption. i. *)
(*                 eapply TimeFacts.le_lt_lt; try exact x0. *)
(*                 eapply TimeFacts.le_lt_lt; eauto. *)
(*             } *)
(*             exploit FMAP_EMPTY; try exact MAP; ss. *)
(*             eapply MAP_LT; try exact l; eassumption. *)
(*           } *)
(*           unfold map_add. i. des; subst; timetac. *)
(*           destruct (TimeFacts.le_lt_dec ts ts'); cycle 1. *)
(*           { left. split. *)
(*             - eapply TimeFacts.lt_le_lt; try exact l. *)
(*               etrans; eauto. *)
(*             - exploit MAP_LT; try exact l; try eassumption. i. *)
(*               eapply TimeFacts.lt_le_lt; eauto. *)
(*           } *)
(*           inv l. *)
(*           { exploit FMAP_EMPTY; try exact MAP; ss. *)
(*             eapply MAP_LT; try exact H0; eassumption. *)
(*           } *)
(*           symmetry in H0. inv H0. *)
(*           exploit MAP_EQ; [|exact PTO_MAP|exact MAP|]; ss. i. subst. *)
(*           rewrite PREV in PTO_LE. inv PTO_LE; inv FPREV; eauto. *)
(*           { inv H1. inv FPREV_EQ. exploit H2; ss. i. subst. timetac. } *)
(*           { inv H0. inv FPREV_EQ. exploit H0; ss. i. subst. timetac. } *)
(*         - (* map_lt_inv *) *)
(*           apply add_map_lt_inv. *)
(*           { apply add_map_lt_inv; ss. i. *)
(*             destruct (TimeFacts.le_lt_dec ts' ts). *)
(*             { left. split. *)
(*               - eapply TimeFacts.le_lt_lt; try exact l. *)
(*                 eapply TimeFacts.le_lt_lt; try exact PTO_LE. *)
(*                 eapply TimeFacts.le_lt_lt; eauto. *)
(*               - exploit map_le; try exact l; try eassumption. i. *)
(*                 eapply TimeFacts.le_lt_lt; try exact x0. *)
(*                 eapply TimeFacts.le_lt_lt; eauto. *)
(*             } *)
(*             exploit FMAP_EMPTY; try exact MAP; ss. *)
(*             eapply MAP_LT; try exact l; eassumption. *)
(*           } *)
(*           unfold map_add. i. des; subst; timetac. *)
(*           destruct (TimeFacts.le_lt_dec ts ts'); cycle 1. *)
(*           { left. split. *)
(*             - eapply TimeFacts.lt_le_lt; try exact l. *)
(*               etrans; eauto. *)
(*             - exploit MAP_LT; try exact l; try eassumption. i. *)
(*               eapply TimeFacts.lt_le_lt; eauto. *)
(*           } *)
(*           inv l. *)
(*           { exploit FMAP_EMPTY; try exact MAP; ss. *)
(*             eapply MAP_LT; try exact H0; eassumption. *)
(*           } *)
(*           symmetry in H0. inv H0. *)
(*           exploit MAP_EQ; [|exact PTO_MAP|exact MAP|]; ss. i. subst. *)
(*           rewrite PREV in PTO_LE. inv PTO_LE; inv FPREV; eauto. *)
(*           { inv H1. inv FPREV_EQ. exploit H2; ss. i. subst. timetac. } *)
(*           { inv H0. inv FPREV_EQ. exploit H0; ss. i. subst. timetac. } *)
(*       } *)

(*       i. exploit (@Memory.add_exists fmem1 loc); try exact FTS; try exact FMSG_WF. *)
(*       { ii. inv LHS. inv RHS. ss. *)
(*         exploit TimeFacts.lt_le_lt; [exact FROM|exact TO0|]. i. *)
(*         rewrite FEMPTY in GET2; ss. *)
(*         eapply TimeFacts.le_lt_lt; try exact x1. ss. *)
(*       } *)
(*       i. des. rename x0 into FADD. *)
(*       esplits; try exact FADD. *)

(*       { (* map_complete *) *)
(*         exploit Memory.add_get0; try exact ADD. i. des. *)
(*         exploit Memory.add_get0; try exact FADD. i. des. *)
(*         unfold map_add. ii. des; subst. *)
(*         - esplits; eauto. unguard. auto. *)
(*         - esplits; eauto. unguard. auto. *)
(*         - exploit COMPLETE1; try exact MAP. i. des. *)
(*           exploit Memory.add_get1; try exact GET3; eauto. i. *)
(*           exploit Memory.add_get1; try exact FGET1; eauto. i. *)
(*           esplits; try exact x1; try exact x2; eauto. *)
(*       } *)

(*       { (* memory_map *) *)
(*         econs; i. *)
(*         { revert GET. erewrite Memory.add_o; eauto. *)
(*           condtac; ss; i. *)
(*           - des. inv GET. right. *)
(*             exploit Memory.add_get0; try exact FADD. i. des. *)
(*             esplits; try exact GET0; eauto 6. *)
(*           - guardH o. *)
(*             exploit SOUND; eauto. i. des; eauto. *)
(*             exploit Memory.add_get1; try exact FGET; eauto. i. *)
(*             right. esplits; eauto. *)
(*             do 2 (eapply message_map_incr; try eapply map_add_incr). ss. *)
(*         } *)
(*         { revert FGET. erewrite Memory.add_o; eauto. *)
(*           condtac; ss; i. *)
(*           - des. symmetry in FGET. inv FGET. *)
(*             exploit Memory.add_get0; try exact ADD. i. des. *)
(*             esplits; try exact GET0; try refl. *)
(*             + destruct (Memory.get loc to rsv) as [[]|] eqn:RSV; ss. *)
(*               exploit LE; eauto. i. congr. *)
(*             + auto 6. *)
(*             + auto 6. *)
(*           - guardH o. *)
(*             exploit COMPLETE; eauto. i. des. *)
(*             exploit Memory.add_get1; try exact GET; eauto. i. *)
(*             esplits; try exact x0; eauto. *)
(*         } *)
(*       } *)
(*     } *)

(*     { (* source non-latest *) *)
(*       rename from_min into fnfrom, to_min into fnto, msg_min into fnmsg. *)
(*       rename GET into FNGET, SAT into NFROM_MAP, *)
(*         SAT0 into NFROM_LE, SAT1 into FNTO_LE, MIN into NFROM_MIN. *)

(*       destruct (TimeFacts.le_lt_dec fts0 fnfrom); cycle 1. *)
(*       { exfalso. *)
(*         exploit COMPLETE1; try exact NFROM_MAP. i. des. *)
(*         exploit Memory.get_ts; try exact FNGET. i. des; subst; timetac. *)
(*         exploit Memory.get_ts; try exact FGET. i. des. *)
(*         { subst. unguard. des; subst; timetac. } *)
(*         unguardH x0. des; subst. *)
(*         - exploit Memory.get_disjoint; [exact FNGET|exact FGET|]. i. des; subst; timetac. *)
(*           destruct (TimeFacts.le_lt_dec fto fnto). *)
(*           + apply (x0 fto); econs; ss; try refl. *)
(*             etrans; try exact l. ss. *)
(*           + apply (x0 fnto); econs; ss; try refl. econs. ss. *)
(*         - exploit Memory.get_disjoint; [exact FNGET|exact FGET|]. i. des; subst; timetac. *)
(*           apply (x0 fto); econs; ss; try refl. econs. ss. *)
(*       } *)
(*       rename l into FNFROM_LE. *)

(*       assert (FEMPTY: Memory.empty fmem1 loc fpto fnto). *)
(*       { ii. rename ts1 into fto. *)
(*         destruct (Memory.get loc fto fmem1) as [[ffrom fmsg]|] eqn:FGET; ss. *)
(*         exfalso. *)
(*         exploit Memory.lt_get; try exact TS1; try eassumption. i. *)
(*         exploit Memory.lt_get; try exact TS2; try eassumption. i. *)
(*         exploit COMPLETE; try exact FGET. i. des. *)
(*         destruct (TimeFacts.le_lt_dec to0 pto). *)
(*         { exploit PTO_MAX; try exact FGET; i; timetac. *)
(*           esplits; try exact TO; ss. *)
(*         } *)
(*         destruct (TimeFacts.le_lt_dec to0 nfrom). *)
(*         { exploit EMPTY; try exact l; timetac. congr. } *)
(*         exploit Memory.lt_from_get; try exact l0; try eassumption. i. des. *)
(*         { subst. exploit NFROM_MIN; try exact FGET; i; timetac. *)
(*           esplits; try exact FROM. *)
(*           right. split; try refl. *)
(*           eapply TimeFacts.le_lt_lt; [eassumption|]. *)
(*           exploit Memory.get_ts; try exact FGET. i. des; ss. *)
(*           subst. timetac. *)
(*         } *)
(*         exploit NFROM_MIN; try exact FGET; i; timetac. *)
(*         esplits; try exact FROM. *)
(*         - etrans; try exact x2. econs. ss. *)
(*         - eapply TimeFacts.le_lt_lt; [eassumption|]. *)
(*           exploit Memory.get_ts; try exact FGET. i. des; timetac. *)
(*       } *)

(*       assert (FMAP_EMPTY: forall ts fts *)
(*                             (LT1: Time.lt fpto fts) *)
(*                             (LT2: Time.lt fts fnfrom) *)
(*                             (MAP: f1 loc ts fts), *)
(*                  False). *)
(*       { i. exploit COMPLETE1; try exact MAP. i. des. *)
(*         exploit Memory.get_ts; try exact FNGET. i. des; subst; timetac. *)
(*         assert (FPTO_FTO: Time.lt fpto fto). *)
(*         { unguardH x0. des; subst; ss. *)
(*           exploit Memory.get_ts; try exact FGET. *)
(*           i. des; subst; timetac. etrans; eauto. *)
(*         } *)
(*         assert (FTO_FNTO: Time.lt fto fnto). *)
(*         { unguardH x0. des; subst; cycle 1. *)
(*           { eapply TimeFacts.lt_le_lt; try exact LT2. timetac. } *)
(*           destruct (TimeFacts.le_lt_dec fnto fto); ss. *)
(*           inv l. *)
(*           { exploit Memory.lt_get; try exact H0; try eassumption. i. *)
(*             rewrite x1 in LT2. *)
(*             exploit TimeFacts.le_lt_lt; try exact x0; try eassumption. i. timetac. *)
(*           } *)
(*           inv H0. rewrite FGET in *. inv FNGET. timetac. *)
(*         } *)
(*         exploit FEMPTY; try exact FPTO_FTO; try eassumption. congr. *)
(*       } *)
(*       inv FPTO_LE. *)
(*       { exploit FMAP_EMPTY; try exact H0; try eassumption; ss. *)
(*         eapply TimeFacts.lt_le_lt; try exact FNFROM_LE. *)
(*         eapply MAP_LT; try exact PTO_MAP; try exact NFROM_MAP. *)
(*         eapply TimeFacts.le_lt_lt; try exact PTO_LE. *)
(*         eapply TimeFacts.lt_le_lt; try exact H. ss. *)
(*       } *)
(*       symmetry in H0. inv H0. *)
(*       inv FNFROM_LE. *)
(*       { exploit FMAP_EMPTY; try exact H0; try eassumption; ss. *)
(*         eapply MAP_LT; try exact PTO_MAP; try exact NFROM_MAP. *)
(*         eapply TimeFacts.le_lt_lt; try exact PTO_LE. *)
(*         eapply TimeFacts.lt_le_lt; try exact H. ss. *)
(*       } *)
(*       inv H0. *)

(*       exploit MAP_LT; [|exact PTO_MAP|exact NFROM_MAP|]. *)
(*       { eapply TimeFacts.le_lt_lt; [eassumption|]. *)
(*         eapply TimeFacts.lt_le_lt; eassumption. *)
(*       } *)
(*       intro FSPACE. *)

(*       (* find ffrom and fto *) *)
(*       assert (exists fto, *)
(*                  (<<FTO_PREV: Time.lt fpto fto>>) /\ *)
(*                  (<<FTO_NEXT: Time.le fto fnfrom>>) /\ *)
(*                  (<<FTO_EQ: __guard__ (ts0 = to <-> fnfrom = fto)>>)). *)
(*       { destruct (Time.eq_dec ts0 to). *)
(*         { subst. inv NEXT; timetac. inv H0. *)
(*           exists fnfrom. splits; ss; try refl. *)
(*         } *)
(*         exists (Time.middle fpto fnfrom). *)
(*         exploit Time.middle_spec; try exact FSPACE. i. des. *)
(*         splits; ss; timetac. split; ss; i. *)
(*         rewrite H0 in x1 at 2. timetac. *)
(*       } *)
(*       des. *)

(*       assert (exists ffrom, *)
(*                  (<<FPREV: Time.le fpto ffrom>>) /\ *)
(*                  (<<FPREV_EQ: __guard__ (ts = from <-> fpto = ffrom)>>) /\ *)
(*                  (<<FTS: Time.lt ffrom fto>>)). *)
(*       { destruct (Time.eq_dec ts from). *)
(*         { subst. inv PREV; timetac. inv H0. *)
(*           exists fpto. splits; ss; try refl. *)
(*         } *)
(*         exists (Time.middle fpto fto). *)
(*         exploit Time.middle_spec; try exact FTO_PREV. i. des. *)
(*         splits; ss; timetac. split; ss. i. *)
(*         rewrite H0 in x0 at 1. timetac. *)
(*       } *)
(*       des. *)

(*       exists ffrom, fto. esplits; [refl|..]. *)

(*       { (* map_wf *) *)
(*         econs. *)
(*         - (* map_inhabited *) *)
(*           repeat apply add_map_inhabited. ss. *)
(*         - (* map_eq *) *)
(*           apply add_map_eq. *)
(*           { apply add_map_eq; ss. i. *)
(*             rewrite NFROM_LE in NEXT. inv NEXT; cycle 1. *)
(*             { inv H0. inv FTO_EQ. exploit H0; ss. i. subst. *)
(*               exploit MAP_EQ; [|exact NFROM_MAP|exact MAP|]; ss. *)
(*             } *)
(*             exploit FMAP_EMPTY; try exact MAP; ss. *)
(*             - eapply MAP_LT; try exact PTO_MAP; try exact MAP. *)
(*               eapply TimeFacts.le_lt_lt; [eassumption|]. *)
(*               eapply TimeFacts.le_lt_lt; eassumption. *)
(*             - eapply MAP_LT; try exact NFROM_MAP; try exact MAP. ss. *)
(*           } *)
(*           unfold map_add. i. des; subst; timetac. *)
(*           rewrite PREV in PTO_LE. inv PTO_LE. *)
(*           { exfalso. *)
(*             eapply FMAP_EMPTY; try exact MAP. *)
(*             - eapply MAP_LT; try exact H0; eauto. *)
(*             - eapply MAP_LT; try exact MAP; try exact NFROM_MAP. *)
(*               eapply TimeFacts.lt_le_lt; [eassumption|]. etrans; eauto. *)
(*           } *)
(*           inv H0. inv FPREV_EQ. *)
(*           exploit H0; try refl. i. subst. *)
(*           eapply MAP_EQ; eauto. *)

(*         - (* map_eq_inv *) *)
(*           apply add_map_eq_inv. *)
(*           { apply add_map_eq_inv; ss. i. *)
(*             inv FTO_NEXT. *)
(*             { exploit FMAP_EMPTY; try exact MAP; ss. } *)
(*             inv H0. inv FTO_EQ. exploit H1; ss. i. subst. *)
(*             exploit MAP_EQ_INV; [|exact NFROM_MAP|exact MAP|]; ss. *)
(*           } *)
(*           unfold map_add. i. des; subst; timetac. *)
(*           inv FPREV. *)
(*           { exfalso. *)
(*             eapply FMAP_EMPTY; try exact MAP; ss. *)
(*             eapply TimeFacts.lt_le_lt; [eassumption|]. ss. *)
(*           } *)
(*           inv H0. inv FPREV_EQ. *)
(*           exploit H1; try refl. i. subst. *)
(*           exploit MAP_EQ_INV; [|exact PTO_MAP|exact MAP|]; ss. *)

(*         - (* map_lt *) *)
(*           apply add_map_lt. *)
(*           { apply add_map_lt; ss. i. *)
(*             destruct (TimeFacts.le_lt_dec ts' ts). *)
(*             { left. split. *)
(*               - eapply TimeFacts.le_lt_lt; try exact l. *)
(*                 eapply TimeFacts.le_lt_lt; try exact PTO_LE. *)
(*                 eapply TimeFacts.le_lt_lt; eauto. *)
(*               - exploit map_le; try exact l; try eassumption. i. *)
(*                 eapply TimeFacts.le_lt_lt; try exact x0. *)
(*                 eapply TimeFacts.le_lt_lt; eauto. *)
(*             } *)
(*             destruct (TimeFacts.le_lt_dec ts0 ts'); cycle 1. *)
(*             { exploit FMAP_EMPTY; try exact MAP; ss. *)
(*               - eapply MAP_LT; try exact l; eassumption. *)
(*               - eapply MAP_LT; try exact l0; eassumption. *)
(*             } *)
(*             inv l0. *)
(*             { right. right. split. *)
(*               - eapply TimeFacts.le_lt_lt; try exact H0. *)
(*                 etrans; eassumption. *)
(*               - exploit MAP_LT; try exact H0; try eassumption. i. *)
(*                 eapply TimeFacts.le_lt_lt; try exact x0. ss. *)
(*             } *)
(*             inv H0. *)
(*             exploit MAP_EQ; [|exact NFROM_MAP|exact MAP|]; ss. i. subst. *)
(*             rewrite NFROM_LE in NEXT. inv NEXT. *)
(*             { right. right. split; ss. *)
(*               inv FTO_NEXT; ss. inv H1. *)
(*               inv FTO_EQ. exploit H2; ss. i. subst. timetac. *)
(*             } *)
(*             inv H0. right. left. split; ss. *)
(*             inv FTO_EQ. apply H0. ss. *)
(*           } *)
(*           unfold map_add. i. des; subst; timetac. *)
(*           destruct (TimeFacts.le_lt_dec ts ts'); cycle 1. *)
(*           { left. split. *)
(*             - eapply TimeFacts.lt_le_lt; try exact l. *)
(*               etrans; eauto. *)
(*             - exploit MAP_LT; try exact l; try eassumption. i. *)
(*               eapply TimeFacts.lt_le_lt; eauto. *)
(*           } *)
(*           inv l; cycle 1. *)
(*           { symmetry in H0. inv H0. *)
(*             exploit MAP_EQ; [|exact PTO_MAP|exact MAP|]; ss. i. subst. *)
(*             rewrite PREV in PTO_LE. inv PTO_LE; inv FPREV; eauto. *)
(*             - inv H1. inv FPREV_EQ. exploit H2; ss. i. subst. timetac. *)
(*             - inv H0. inv FPREV_EQ. exploit H0; ss. i. subst. timetac. *)
(*           } *)
(*           destruct (TimeFacts.le_lt_dec ts0 ts'). *)
(*           { right. right. split. *)
(*             - eapply TimeFacts.lt_le_lt; try exact l. *)
(*               eapply TimeFacts.lt_le_lt; try exact TS. *)
(*               etrans; eassumption. *)
(*             - eapply TimeFacts.lt_le_lt; try exact FTS. *)
(*               etrans; try exact FTO_NEXT. *)
(*               eapply map_le; try exact l; eauto. *)
(*           } *)
(*           { exploit FMAP_EMPTY; try exact MAP; ss. *)
(*             - eapply MAP_LT; try exact H0; eassumption. *)
(*             - eapply MAP_LT; try exact l; eauto. *)
(*           } *)

(*         - (* map_lt_inv *) *)
(*           apply add_map_lt_inv. *)
(*           { apply add_map_lt_inv; ss. i. *)
(*             destruct (TimeFacts.le_lt_dec ts' ts). *)
(*             { left. split. *)
(*               - eapply TimeFacts.le_lt_lt; try exact l. *)
(*                 eapply TimeFacts.le_lt_lt; try exact PTO_LE. *)
(*                 eapply TimeFacts.le_lt_lt; eauto. *)
(*               - exploit map_le; try exact l; try eassumption. i. *)
(*                 eapply TimeFacts.le_lt_lt; try exact x0. *)
(*                 eapply TimeFacts.le_lt_lt; eauto. *)
(*             } *)
(*             destruct (TimeFacts.le_lt_dec ts0 ts'); cycle 1. *)
(*             { exploit FMAP_EMPTY; try exact MAP; ss. *)
(*               - eapply MAP_LT; try exact l; eassumption. *)
(*               - eapply MAP_LT; try exact l0; eassumption. *)
(*             } *)
(*             inv l0. *)
(*             { right. right. split. *)
(*               - eapply TimeFacts.le_lt_lt; try exact H0. *)
(*                 etrans; eassumption. *)
(*               - exploit MAP_LT; try exact H0; try eassumption. i. *)
(*                 eapply TimeFacts.le_lt_lt; try exact x0. ss. *)
(*             } *)
(*             inv H0. *)
(*             exploit MAP_EQ; [|exact NFROM_MAP|exact MAP|]; ss. i. subst. *)
(*             rewrite NFROM_LE in NEXT. inv NEXT. *)
(*             { right. right. split; ss. *)
(*               inv FTO_NEXT; ss. inv H1. *)
(*               inv FTO_EQ. exploit H2; ss. i. subst. timetac. *)
(*             } *)
(*             inv H0. right. left. split; ss. *)
(*             inv FTO_EQ. apply H0. ss. *)
(*           } *)
(*           unfold map_add. i. des; subst; timetac. *)
(*           destruct (TimeFacts.le_lt_dec ts ts'); cycle 1. *)
(*           { left. split. *)
(*             - eapply TimeFacts.lt_le_lt; try exact l. *)
(*               etrans; eauto. *)
(*             - exploit MAP_LT; try exact l; try eassumption. i. *)
(*               eapply TimeFacts.lt_le_lt; eauto. *)
(*           } *)
(*           inv l; cycle 1. *)
(*           { symmetry in H0. inv H0. *)
(*             exploit MAP_EQ; [|exact PTO_MAP|exact MAP|]; ss. i. subst. *)
(*             rewrite PREV in PTO_LE. inv PTO_LE; inv FPREV; eauto. *)
(*             - inv H1. inv FPREV_EQ. exploit H2; ss. i. subst. timetac. *)
(*             - inv H0. inv FPREV_EQ. exploit H0; ss. i. subst. timetac. *)
(*           } *)
(*           destruct (TimeFacts.le_lt_dec ts0 ts'). *)
(*           { right. right. split. *)
(*             - eapply TimeFacts.lt_le_lt; try exact l. *)
(*               eapply TimeFacts.lt_le_lt; try exact TS. *)
(*               etrans; eassumption. *)
(*             - eapply TimeFacts.lt_le_lt; try exact FTS. *)
(*               etrans; try exact FTO_NEXT. *)
(*               eapply map_le; try exact l; eauto. *)
(*           } *)
(*           { exploit FMAP_EMPTY; try exact MAP; ss. *)
(*             - eapply MAP_LT; try exact H0; eassumption. *)
(*             - eapply MAP_LT; try exact l; eauto. *)
(*           } *)
(*       } *)

(*       i. exploit (@Memory.add_exists fmem1 loc); try exact FTS; try exact FMSG_WF. *)
(*       { ii. inv LHS. inv RHS. ss. *)
(*         exploit TimeFacts.lt_le_lt; [exact FROM|exact TO0|]. i. *)
(*         exploit TimeFacts.lt_le_lt; [exact FROM0|exact TO|]. i. *)
(*         rewrite FEMPTY in GET2; ss. *)
(*         - eapply TimeFacts.le_lt_lt; try exact x1. ss. *)
(*         - destruct (TimeFacts.le_lt_dec fnto to2); ss. *)
(*           exfalso. *)
(*           exploit Memory.get_disjoint; [exact FNGET|exact GET2|]. i. des. *)
(*           { subst. clear - FTO_NEXT x2. timetac. } *)
(*           apply (x3 fnto); econs; ss; try refl. *)
(*           eapply TimeFacts.lt_le_lt; try exact x2. *)
(*           etrans; eauto. econs. ss. *)
(*       } *)
(*       i. des. rename x0 into FADD. *)
(*       esplits; try exact FADD. *)

(*       { (* map_complete *) *)
(*         exploit Memory.add_get0; try exact ADD. i. des. *)
(*         exploit Memory.add_get0; try exact FADD. i. des. *)
(*         unfold map_add. ii. des; subst. *)
(*         - esplits; eauto. unguard. auto. *)
(*         - esplits; eauto. unguard. auto. *)
(*         - exploit COMPLETE1; try exact MAP. i. des. *)
(*           exploit Memory.add_get1; try exact GET3; eauto. i. *)
(*           exploit Memory.add_get1; try exact FGET; eauto. i. *)
(*           esplits; try exact x1; try exact x2; eauto. *)
(*       } *)

(*       { (* memory_map *) *)
(*         econs; i. *)
(*         { revert GET. erewrite Memory.add_o; eauto. *)
(*           condtac; ss; i. *)
(*           - des. inv GET. right. *)
(*             exploit Memory.add_get0; try exact FADD. i. des. *)
(*             esplits; try exact GET0; eauto 6. *)
(*           - guardH o. *)
(*             exploit SOUND; eauto. i. des; eauto. *)
(*             exploit Memory.add_get1; try exact FGET; eauto. i. *)
(*             right. esplits; eauto. *)
(*             do 2 (eapply message_map_incr; try eapply map_add_incr). ss. *)
(*         } *)
(*         { revert FGET. erewrite Memory.add_o; eauto. *)
(*           condtac; ss; i. *)
(*           - des. symmetry in FGET. inv FGET. *)
(*             exploit Memory.add_get0; try exact ADD. i. des. *)
(*             esplits; try exact GET0; try refl. *)
(*             + destruct (Memory.get loc to rsv) as [[]|] eqn:RSV; ss. *)
(*               exploit LE; eauto. i. congr. *)
(*             + auto 6. *)
(*             + auto 6. *)
(*           - guardH o. *)
(*             exploit COMPLETE; eauto. i. des. *)
(*             exploit Memory.add_get1; try exact GET; eauto. i. *)
(*             esplits; try exact x0; eauto. *)
(*         } *)
(*       } *)
(*     } *)
(*   } *)

(*   { (* target latest *) *)
(*     assert (EMPTY: forall to (TO: Time.lt pto to), *)
(*                Memory.get loc to mem1 = None). *)
(*     { i. destruct (TimeFacts.le_lt_dec to to0); eauto. *)
(*       inv l; eauto. inv H. *)
(*       exploit Memory.add_get0; eauto. i. des. congr. *)
(*     } *)

(*     assert (MAP_EMPTY: forall ts fts *)
(*                          (LT1: Time.lt pto ts) *)
(*                          (MAP: f1 loc ts fts), *)
(*                False). *)
(*     { i. exploit COMPLETE1; try exact MAP. i. des. *)
(*       rewrite EMPTY in GET; ss. unguardH x0. des; subst; ss. *)
(*       eapply TimeFacts.lt_le_lt; try exact LT1. *)
(*       exploit Memory.get_ts; try exact GET. i. des; timetac. *)
(*     } *)

(*     specialize (Memory.max_exists *)
(*                   (fun fpto => exists ts fts, f1 loc ts fts /\ Time.le ts pto /\ Time.le fpto fts) *)
(*                   loc fmem1). *)
(*     i. des. *)
(*     { exploit SOUND; try eapply INHABITED1. i. des; ss. *)
(*       exploit MAP_EQ; [|exact TO|eapply MAP_INHABITED|]; ss. i. subst. *)
(*       exploit NONE; try exact FGET; ss. *)
(*       esplits; eauto; timetac. *)
(*     } *)
(*     rename from_max into fpfrom, to_max into fpto, msg_max into fpmsg. *)
(*     rename SAT into PTO_MAP, SAT0 into PTO_LE, SAT1 into FPTO_LE, MAX into PTO_MAX. *)

(*     assert (FEMPTY: forall fto (FTO: Time.lt fpto fto), *)
(*                Memory.get loc fto fmem1 = None). *)
(*     { i. destruct (Memory.get loc fto fmem1) as [[ffrom fmsg]|] eqn:FGET; ss. *)
(*       exfalso. *)
(*       exploit COMPLETE; try exact FGET. i. des. *)
(*       destruct (TimeFacts.le_lt_dec to0 pto). *)
(*       { exploit PTO_MAX; try exact FGET; i; timetac. *)
(*         esplits; try exact TO; ss. *)
(*       } *)
(*       erewrite EMPTY in GET0; ss. *)
(*     } *)

(*     assert (FMAP_EMPTY: forall ts fts *)
(*                                (LT: Time.lt fpto fts) *)
(*                                (MAP: f1 loc ts fts), *)
(*                False). *)
(*     { i. exploit COMPLETE1; try exact MAP. i. des. *)
(*       assert (FPTO_FTO: Time.lt fpto fto). *)
(*       { unguard. des; subst; ss. *)
(*         exploit Memory.get_ts; try exact FGET. *)
(*         i. des; subst; timetac. etrans; eauto. *)
(*       } *)
(*       erewrite FEMPTY in FGET; ss. *)
(*     } *)

(*     inv FPTO_LE. *)
(*     { exploit FMAP_EMPTY; try exact H; eauto. ss. } *)
(*     symmetry in H. inv H. *)

(*     (* find ffrom and fto *) *)
(*     assert (exists ffrom fto, *)
(*                (<<FPREV: Time.le fpto ffrom>>) /\ *)
(*                (<<FPREV_EQ: __guard__ (ts = from <-> fpto = ffrom)>>) /\ *)
(*                (<<FTS: Time.lt ffrom fto>>)). *)
(*     { destruct (Time.eq_dec ts from). *)
(*       { subst. inv PREV; timetac. inv H. *)
(*         exists fpto, (Time.incr fpto). *)
(*         splits; ss; try refl. apply Time.incr_spec. *)
(*       } *)
(*       exists (Time.incr fpto), (Time.incr (Time.incr fpto)). *)
(*       splits. *)
(*       - econs. apply Time.incr_spec. *)
(*       - unguard. split; ss. i. *)
(*         specialize (Time.incr_spec fpto). *)
(*         rewrite H at 1. i. timetac. *)
(*       - apply Time.incr_spec. *)
(*     } *)
(*     des. *)
(*     exists ffrom, fto. esplits; [refl|..]. *)

(*     { (* map_wf *) *)
(*       econs. *)
(*       - (* map_inhabited *) *)
(*         repeat apply add_map_inhabited. ss. *)
(*       - (* map_eq *) *)
(*         apply add_map_eq. *)
(*         { apply add_map_eq; ss. i. *)
(*           exploit FMAP_EMPTY; try exact MAP; ss. *)
(*           eapply MAP_LT; try exact PTO_MAP; try exact MAP. *)
(*           eapply TimeFacts.le_lt_lt; [eassumption|]. *)
(*           eapply TimeFacts.le_lt_lt; eassumption. *)
(*         } *)
(*         unfold map_add. i. des; subst; timetac. *)
(*         rewrite PREV in PTO_LE. inv PTO_LE. *)
(*         { exfalso. eauto. } *)
(*         inv H. unguard. des. *)
(*         exploit FPREV_EQ; try refl. i. subst. *)
(*         exploit MAP_EQ; [|exact PTO_MAP|exact MAP|]; ss. *)
(*       - (* map_eq_inv *) *)
(*         apply add_map_eq_inv. *)
(*         { apply add_map_eq_inv; ss. i. *)
(*           exploit FMAP_EMPTY; try exact MAP; ss. *)
(*           eapply TimeFacts.le_lt_lt; eassumption. *)
(*         } *)
(*         unfold map_add. i. des; subst; timetac. *)
(*         inv FPREV. *)
(*         { exfalso. eauto. } *)
(*         inv H. unguard. des. *)
(*         exploit FPREV_EQ0; try refl. i. subst. *)
(*         exploit MAP_EQ_INV; [|exact PTO_MAP|exact MAP|]; ss. *)
(*       - (* map_lt *) *)
(*         apply add_map_lt. *)
(*         { apply add_map_lt; ss. i. *)
(*           destruct (TimeFacts.le_lt_dec ts' ts). *)
(*           { left. split. *)
(*             - eapply TimeFacts.le_lt_lt; try exact l. *)
(*               eapply TimeFacts.le_lt_lt; try exact PTO_LE. *)
(*               eapply TimeFacts.le_lt_lt; eauto. *)
(*             - exploit map_le; try exact l; try eassumption. i. *)
(*               eapply TimeFacts.le_lt_lt; try exact x0. *)
(*               eapply TimeFacts.le_lt_lt; eauto. *)
(*           } *)
(*           exploit FMAP_EMPTY; try exact MAP; ss. *)
(*           eapply MAP_LT; try exact l; eassumption. *)
(*         } *)
(*         unfold map_add. i. des; subst; timetac. *)
(*         destruct (TimeFacts.le_lt_dec ts ts'); cycle 1. *)
(*         { left. split. *)
(*           - eapply TimeFacts.lt_le_lt; try exact l. *)
(*             etrans; eauto. *)
(*           - exploit MAP_LT; try exact l; try eassumption. i. *)
(*             eapply TimeFacts.lt_le_lt; eauto. *)
(*         } *)
(*         inv l. *)
(*         { exploit FMAP_EMPTY; try exact MAP; ss. *)
(*           eapply MAP_LT; try exact H0; eassumption. *)
(*         } *)
(*         symmetry in H. inv H. *)
(*         exploit MAP_EQ; [|exact PTO_MAP|exact MAP|]; ss. i. subst. *)
(*         rewrite PREV in PTO_LE. inv PTO_LE; inv FPREV; eauto. *)
(*         { inv H0. inv FPREV_EQ. exploit H1; ss. i. subst. timetac. } *)
(*         { inv H. inv FPREV_EQ. exploit H; ss. i. subst. timetac. } *)
(*       - (* map_lt_inv *) *)
(*         apply add_map_lt_inv. *)
(*         { apply add_map_lt_inv; ss. i. *)
(*           destruct (TimeFacts.le_lt_dec ts' ts). *)
(*           { left. split. *)
(*             - eapply TimeFacts.le_lt_lt; try exact l. *)
(*               eapply TimeFacts.le_lt_lt; try exact PTO_LE. *)
(*               eapply TimeFacts.le_lt_lt; eauto. *)
(*             - exploit map_le; try exact l; try eassumption. i. *)
(*               eapply TimeFacts.le_lt_lt; try exact x0. *)
(*               eapply TimeFacts.le_lt_lt; eauto. *)
(*           } *)
(*           exploit FMAP_EMPTY; try exact MAP; ss. *)
(*           eapply MAP_LT; try exact l; eassumption. *)
(*         } *)
(*         unfold map_add. i. des; subst; timetac. *)
(*         destruct (TimeFacts.le_lt_dec ts ts'); cycle 1. *)
(*         { left. split. *)
(*           - eapply TimeFacts.lt_le_lt; try exact l. *)
(*             etrans; eauto. *)
(*           - exploit MAP_LT; try exact l; try eassumption. i. *)
(*             eapply TimeFacts.lt_le_lt; eauto. *)
(*         } *)
(*         inv l. *)
(*         { exploit FMAP_EMPTY; try exact MAP; ss. *)
(*           eapply MAP_LT; try exact H0; eassumption. *)
(*         } *)
(*         symmetry in H. inv H. *)
(*         exploit MAP_EQ; [|exact PTO_MAP|exact MAP|]; ss. i. subst. *)
(*         rewrite PREV in PTO_LE. inv PTO_LE; inv FPREV; eauto. *)
(*         { inv H0. inv FPREV_EQ. exploit H1; ss. i. subst. timetac. } *)
(*         { inv H. inv FPREV_EQ. exploit H; ss. i. subst. timetac. } *)
(*     } *)

(*     i. exploit (@Memory.add_exists fmem1 loc); try exact FTS; try exact FMSG_WF. *)
(*     { ii. inv LHS. inv RHS. ss. *)
(*       exploit TimeFacts.lt_le_lt; [exact FROM|exact TO0|]. i. *)
(*       rewrite FEMPTY in GET2; ss. *)
(*       eapply TimeFacts.le_lt_lt; try exact x1. ss. *)
(*     } *)
(*     i. des. rename x0 into FADD. *)
(*     esplits; try exact FADD. *)

(*     { (* map_complete *) *)
(*       exploit Memory.add_get0; try exact ADD. i. des. *)
(*       exploit Memory.add_get0; try exact FADD. i. des. *)
(*       unfold map_add. ii. des; subst. *)
(*       - esplits; eauto. unguard. auto. *)
(*       - esplits; eauto. unguard. auto. *)
(*       - exploit COMPLETE1; try exact MAP. i. des. *)
(*         exploit Memory.add_get1; try exact GET4; eauto. i. *)
(*         exploit Memory.add_get1; try exact FGET1; eauto. i. *)
(*         esplits; try exact x1; try exact x2; eauto. *)
(*     } *)

(*     { (* memory_map *) *)
(*       econs; i. *)
(*       { revert GET0. erewrite Memory.add_o; eauto. *)
(*         condtac; ss; i. *)
(*         - des. inv GET0. right. *)
(*           exploit Memory.add_get0; try exact FADD. i. des. *)
(*           esplits; try exact GET1; eauto 6. *)
(*         - guardH o. *)
(*           exploit SOUND; eauto. i. des; eauto. *)
(*           exploit Memory.add_get1; try exact FGET; eauto. i. *)
(*           right. esplits; eauto. *)
(*           do 2 (eapply message_map_incr; try eapply map_add_incr). ss. *)
(*       } *)
(*       { revert FGET. erewrite Memory.add_o; eauto. *)
(*         condtac; ss; i. *)
(*         - des. symmetry in FGET. inv FGET. *)
(*           exploit Memory.add_get0; try exact ADD. i. des. *)
(*           esplits; try exact GET1; try refl. *)
(*           + destruct (Memory.get loc to rsv) as [[]|] eqn:RSV; ss. *)
(*             exploit LE; eauto. i. congr. *)
(*           + auto 6. *)
(*           + auto 6. *)
(*         - guardH o. *)
(*           exploit COMPLETE; eauto. i. des. *)
(*           exploit Memory.add_get1; try exact GET0; eauto. i. *)
(*           esplits; try exact x0; eauto. *)
(*       } *)
(*     } *)
(*   } *)
(* Qed. *)

(* Lemma memory_map_reserve *)
(*       f1 rsv1 mem1 fmem1 *)
(*       loc from to rsv2 mem2 *)
(*       (COMPLETE1: map_complete f1 mem1 fmem1) *)
(*       (MAP1: memory_map f1 rsv1 mem1 fmem1) *)
(*       (RESERVE: Memory.reserve rsv1 mem1 loc from to rsv2 mem2): *)
(*   (<<COMPLETE2: map_complete f1 mem2 fmem1>>) /\ *)
(*   (<<MAP2: memory_map f1 rsv2 mem2 fmem1>>). *)
(* Proof. *)
(*   inv MAP1. inv RESERVE. splits. *)
(*   - ii. exploit COMPLETE1; eauto. i. des. *)
(*     exploit Memory.add_get1; try exact GET; eauto. i. *)
(*     esplits; eauto. *)
(*   - econs; i. *)
(*     + revert GET. erewrite Memory.add_o; eauto. *)
(*       condtac; ss; eauto. i. des. inv GET. auto. *)
(*     + exploit COMPLETE; eauto. i. des. *)
(*       exploit Memory.add_get1; try exact GET; eauto. i. *)
(*       esplits; eauto. *)
(*       erewrite Memory.add_o; eauto. condtac; ss. des. subst. *)
(*       exploit Memory.add_get0; try exact MEM. i. des. congr. *)
(* Qed. *)

(* Lemma memory_map_cancel *)
(*       f1 rsv1 mem1 fmem1 *)
(*       loc from to rsv2 mem2 *)
(*       (WF1: map_wf f1) *)
(*       (COMPLETE1: map_complete f1 mem1 fmem1) *)
(*       (MAP1: memory_map f1 rsv1 mem1 fmem1) *)
(*       (LE: Memory.le rsv1 mem1) *)
(*       (INHABITED1: Memory.inhabited mem1) *)
(*       (CANCEL: Memory.cancel rsv1 mem1 loc from to rsv2 mem2): *)
(*   (<<COMPLETE2: map_complete f1 mem2 fmem1>>) /\ *)
(*   (<<MAP2: memory_map f1 rsv2 mem2 fmem1>>). *)
(* Proof. *)
(*   inv WF1. inv MAP1. inv CANCEL. splits. *)
(*   - ii. exploit COMPLETE1; eauto. i. des. *)
(*     exploit Memory.remove_get1; try exact GET; eauto. i. des; cycle 1. *)
(*     { esplits; eauto. } *)
(*     subst. *)
(*     exploit Memory.get_ts; try exact GET. i. des. *)
(*     { subst. rewrite INHABITED1 in GET. ss. } *)
(*     exploit Memory.get_ts; try exact FGET. i. des. *)
(*     { subst. specialize (MAP_INHABITED loc). *)
(*       exploit MAP_EQ_INV; [|exact MAP_INHABITED|exact MAP|]. *)
(*       { unguard. des; ss. } *)
(*       i. subst. *)
(*       exploit MAP_EQ; [|exact MAP_INHABITED|exact MAP|]; ss. i. subst. *)
(*       specialize (INHABITED1 loc). *)
(*       exploit Memory.remove_get1; try exact INHABITED1; eauto. i. des; ss. *)
(*       esplits; try exact FGET; try exact x2. unguard. auto. *)
(*     } *)
(*     exploit COMPLETE; eauto. i. des. *)
(*     cut (to0 = to). *)
(*     { i. subst. exploit Memory.remove_get0; try exact RSV. i. des. congr. } *)
(*     exploit Memory.get_disjoint; [exact GET|exact GET0|]. i. des; ss. *)
(*     unguard. des; subst. *)
(*     + exploit map_le_inv; try exact FFROM; try eassumption. i. *)
(*       exploit MAP_LT_INV; [|exact MAP|exact TO|]. *)
(*       { eapply TimeFacts.lt_le_lt; try exact FTO. ss. } *)
(*       i. exfalso. *)
(*       destruct (TimeFacts.le_lt_dec to to0). *)
(*       * apply (x3 to); econs; ss; try refl; timetac. *)
(*       * apply (x3 to0); econs; ss; try refl; timetac. *)
(*     + exploit map_le_inv; try exact FTO; try eassumption. i. *)
(*       exploit MAP_LT_INV; [|exact FROM|exact MAP|]. *)
(*       { eapply TimeFacts.le_lt_lt; try exact x2. ss. } *)
(*       i. exfalso. *)
(*       apply (x3 to); econs; ss; try refl; timetac. *)
(*   - econs; i. *)
(*     + revert GET. erewrite Memory.remove_o; eauto. *)
(*       condtac; ss; eauto. *)
(*     + exploit COMPLETE; eauto. i. des. *)
(*       exploit Memory.remove_get1; try exact GET; eauto. i. des. *)
(*       { subst. exploit Memory.remove_get0; try exact RSV. i. des. congr. } *)
(*       esplits; eauto. *)
(*       erewrite Memory.remove_o; eauto. condtac; ss. *)
(* Qed. *)

(* Lemma map_readable *)
(*       f tview ftview *)
(*       loc to fto ord *)
(*       (MAP_WF: map_wf f) *)
(*       (TVIEW: tview_map f tview ftview) *)
(*       (TO: f loc to fto) *)
(*       (READABLE: TView.readable (TView.cur tview) loc to ord): *)
(*   TView.readable (TView.cur ftview) loc fto ord. *)
(* Proof. *)
(*   inv READABLE. econs. *)
(*   - eapply map_le; try exact PLN; try apply MAP_WF; eauto. apply TVIEW. *)
(*   - i. eapply map_le; try eapply RLX; try apply MAP_WF; eauto. apply TVIEW. *)
(* Qed. *)

(* Lemma read_tview_map *)
(*       f tview ftview *)
(*       loc to fto released freleased ord *)
(*       (MAP_WF: map_wf f) *)
(*       (TVIEW: tview_map f tview ftview) *)
(*       (TO: f loc to fto) *)
(*       (RELEASED: opt_view_map f released freleased): *)
(*   tview_map f *)
(*             (TView.read_tview tview loc to released ord) *)
(*             (TView.read_tview ftview loc fto freleased ord). *)
(* Proof. *)
(*   unfold TView.read_tview. *)
(*   econs; s; (try condtac); (repeat apply view_join_map); ss; *)
(*     try apply TVIEW; try apply bot_view_map; ss; *)
(*     try apply unwrap_map; ss; *)
(*     eauto using singleton_rw_map, singleton_ur_map, singleton_ur_if_map. *)
(* Qed. *)

(* Lemma map_read_step *)
(*       rsv *)
(*       f1 lc1 gl1 flc1 fgl1 *)
(*       loc to val released ord lc2 *)
(*       (MAP_WF1: map_wf f1) *)
(*       (MAP_COMPLETE1: map_complete f1 (Global.memory gl1) (Global.memory fgl1)) *)
(*       (LC_MAP1: local_map f1 lc1 flc1) *)
(*       (GL_MAP1: global_map f1 rsv gl1 fgl1) *)
(*       (STEP: Local.read_step lc1 gl1 loc to val released ord lc2): *)
(*   exists fto freleased flc2, *)
(*     (<<FSTEP: Local.read_step flc1 fgl1 loc fto val freleased ord flc2>>) /\ *)
(*     (<<TO_MAP: f1 loc to fto>>) /\ *)
(*     (<<RELEASED_MAP: opt_view_map f1 released freleased>>) /\ *)
(*     (<<LC_MAP2: local_map f1 lc2 flc2>>). *)
(* Proof. *)
(*   inv STEP. exploit memory_map_get; try apply GL_MAP1; eauto; ss. i. des. inv MSG. *)
(*   esplits; eauto. *)
(*   - econs; eauto. *)
(*     eapply map_readable; try apply LC_MAP1; eauto. *)
(*   - econs; s; try apply LC_MAP1. *)
(*     apply read_tview_map; ss. apply LC_MAP1. *)
(* Qed. *)

(* Lemma map_writable *)
(*       f tview ftview *)
(*       loc to fto ord *)
(*       (MAP_WF: map_wf f) *)
(*       (TVIEW: tview_map f tview ftview) *)
(*       (TO: f loc to fto) *)
(*       (WRITABLE: TView.writable (TView.cur tview) loc to ord): *)
(*   TView.writable (TView.cur ftview) loc fto ord. *)
(* Proof. *)
(*   inv MAP_WF. inv WRITABLE. econs. *)
(*   eapply MAP_LT; try exact TS; eauto. apply TVIEW. *)
(* Qed. *)

(* Lemma write_tview_map *)
(*       f tview ftview *)
(*       loc to fto ord *)
(*       (MAP_WF: map_wf f) *)
(*       (TVIEW: tview_map f tview ftview) *)
(*       (TO: f loc to fto): *)
(*   tview_map f (TView.write_tview tview loc to ord) (TView.write_tview ftview loc fto ord). *)
(* Proof. *)
(*   econs; s; i. *)
(*   - unfold LocFun.add. *)
(*     repeat condtac; try apply TVIEW. *)
(*     + apply view_join_map; ss; try apply TVIEW. *)
(*       apply singleton_ur_map; ss. *)
(*     + apply view_join_map; ss; try apply TVIEW. *)
(*       apply singleton_ur_map; ss. *)
(*   - apply view_join_map; ss; try apply TVIEW. *)
(*     apply singleton_ur_map; ss. *)
(*   - apply view_join_map; ss; try apply TVIEW. *)
(*     apply singleton_ur_map; ss. *)
(* Qed. *)

(* Lemma write_released_map *)
(*       f tview ftview *)
(*       loc to fto releasedm freleasedm ord *)
(*       (MAP_WF: map_wf f) *)
(*       (TVIEW: tview_map f tview ftview) *)
(*       (TO: f loc to fto) *)
(*       (RELEASEDM: opt_view_map f releasedm freleasedm): *)
(*   opt_view_map f *)
(*                (TView.write_released tview loc to releasedm ord) *)
(*                (TView.write_released ftview loc fto freleasedm ord). *)
(* Proof. *)
(*   unfold TView.write_released. condtac; econs. *)
(*   apply view_join_map; ss. *)
(*   - apply unwrap_map; ss. *)
(*   - unfold LocFun.add. condtac; ss. *)
(*     condtac; apply view_join_map; ss; *)
(*       try apply TVIEW; apply singleton_ur_map; ss. *)
(* Qed. *)

(* Lemma map_write_step *)
(*       f1 lc1 gl1 flc1 fgl1 *)
(*       loc from to val releasedm released ord lc2 gl2 *)
(*       freleasedm *)
(*       (MAP_WF1: map_wf f1) *)
(*       (MAP_COMPLETE1: map_complete f1 (Global.memory gl1) (Global.memory fgl1)) *)
(*       (LC_MAP1: local_map f1 lc1 flc1) *)
(*       (GL_MAP1: global_map f1 (Local.reserves lc1) gl1 fgl1) *)
(*       (LC_WF1: Local.wf lc1 gl1) *)
(*       (GL_WF1: Global.wf gl1) *)
(*       (FLC_WF1: Local.wf flc1 fgl1) *)
(*       (RELEASEDM_MAP: opt_view_map f1 releasedm freleasedm) *)
(*       (FRELEASEDM: View.opt_wf freleasedm) *)
(*       (STEP: Local.write_step lc1 gl1 loc from to val releasedm released ord lc2 gl2): *)
(*   exists f2 ffrom fto freleased flc2 fgl2, *)
(*     (<<FSTEP: Local.write_step flc1 fgl1 loc ffrom fto val freleasedm freleased ord flc2 fgl2>>) /\ *)
(*     (<<F2: f2 = map_add loc from ffrom (map_add loc to fto f1)>>) /\ *)
(*     (<<MAP_WF2: map_wf f2>>) /\ *)
(*     (<<MAP_COMPLETE2: map_complete f2 (Global.memory gl2) (Global.memory fgl2)>>) /\ *)
(*     (<<FROM_MAP: f2 loc from ffrom>>) /\ *)
(*     (<<TO_MAP: f2 loc to fto>>) /\ *)
(*     (<<RELEASED_MAP: opt_view_map f2 released freleased>>) /\ *)
(*     (<<LC_MAP2: local_map f2 lc2 flc2>>) /\ *)
(*     (<<GL_MAP2: global_map f2 (Local.reserves lc2) gl2 fgl2>>). *)
(* Proof. *)
(*   destruct lc1 as [tview1 prm1 rsv1]. *)
(*   destruct flc1 as [ftview1 fprm1 frsv1]. *)
(*   destruct gl1 as [sc1 gprm1 mem1]. *)
(*   destruct fgl1 as [fsc1 fgprm1 fmem1]. *)
(*   inv LC_MAP1. inv GL_MAP1. ss. *)
(*   inv STEP. ss. *)
(*   exploit memory_map_add; try exact MEMORY; *)
(*     try apply LC_WF1; try apply GL_WF1; eauto. i. des. *)
(*   assert (REL: opt_view_map *)
(*                  f2 *)
(*                  (TView.write_released tview1 loc to releasedm ord) *)
(*                  (TView.write_released ftview1 loc fto freleasedm ord)). *)
(*   { subst. eapply write_released_map; ss. *)
(*     - eapply tview_map_incr; try exact TVIEW. *)
(*       i. repeat apply map_add_incr. ss. *)
(*     - auto 6. *)
(*     - eapply opt_view_map_incr; try exact RELEASEDM_MAP. *)
(*       i. repeat apply map_add_incr. ss. *)
(*   } *)
(*   exploit x0; [|econs; eauto|]. *)
(*   { econs. eapply TViewFacts.write_future0; ss. apply FLC_WF1. } *)
(*   i. des. clear x0. subst. *)
(*   esplits; eauto 6. *)
(*   - econs; try exact FADD; eauto; s. *)
(*     eapply map_writable; try exact WRITABLE; try exact WF2; auto 6. *)
(*     eapply tview_map_incr; try exact TVIEW. *)
(*     i. repeat apply map_add_incr. ss. *)
(*   - ss. *)
(*   - econs; ss. *)
(*     apply write_tview_map; ss; auto 6. *)
(*     eapply tview_map_incr; try apply TVIEW. *)
(*     i. repeat apply map_add_incr. ss. *)
(*   - econs; ss. *)
(* Qed. *)

(* Lemma write_fence_tview_map *)
(*       f tview ftview sc fsc ord *)
(*       (MAP_WF: map_wf f) *)
(*       (TVIEW: tview_map f tview ftview) *)
(*       (ORD: Ordering.le ord Ordering.acqrel): *)
(*   tview_map f (TView.write_fence_tview tview sc ord) (TView.write_fence_tview ftview fsc ord). *)
(* Proof. *)
(*   econs; ss; i; repeat condtac; *)
(*     try apply view_join_map; ss; try apply TVIEW; *)
(*     try apply bot_view_map; ss; *)
(*     destruct ord; ss. *)
(* Qed. *)

(* Lemma read_fence_tview_map *)
(*       f tview ftview ord *)
(*       (MAP_WF: map_wf f) *)
(*       (TVIEW: tview_map f tview ftview): *)
(*   tview_map f (TView.read_fence_tview tview ord) (TView.read_fence_tview ftview ord). *)
(* Proof. *)
(*   econs; ss; i; repeat condtac; *)
(*     try apply view_join_map; ss; try apply TVIEW; *)
(*     try apply bot_view_map; ss. *)
(* Qed. *)

(* Lemma map_fence_step *)
(*       rsv *)
(*       f1 lc1 gl1 flc1 fgl1 *)
(*       ordr ordw lc2 gl2 *)
(*       (MAP_WF1: map_wf f1) *)
(*       (MAP_COMPLETE1: map_complete f1 (Global.memory gl1) (Global.memory fgl1)) *)
(*       (LC_MAP1: local_map f1 lc1 flc1) *)
(*       (GL_MAP1: global_map f1 rsv gl1 fgl1) *)
(*       (ORD: Ordering.le ordw Ordering.acqrel) *)
(*       (STEP: Local.fence_step lc1 gl1 ordr ordw lc2 gl2): *)
(*   exists flc2 fgl2, *)
(*     (<<FSTEP: Local.fence_step flc1 fgl1 ordr ordw flc2 fgl2>>) /\ *)
(*     (<<MAP_COMPLETE2: map_complete f1 (Global.memory gl2) (Global.memory fgl2)>>) /\ *)
(*     (<<LC_MAP2: local_map f1 lc2 flc2>>) /\ *)
(*     (<<GL_MAP2: global_map f1 rsv gl2 fgl2>>). *)
(* Proof. *)
(*   inv STEP. *)
(*   esplits. *)
(*   - econs; eauto. destruct ordw; ss. *)
(*   - ss. *)
(*   - econs; try apply LC_MAP1. s. *)
(*     apply write_fence_tview_map; ss; try apply GL_MAP1. *)
(*     apply read_fence_tview_map; ss. apply LC_MAP1. *)
(*   - econs; try apply GL_MAP1. *)
(* Qed. *)

(* Lemma map_racy_view *)
(*       f view fview loc ts fts *)
(*       (MAP_WF: map_wf f) *)
(*       (VIEW: view_map f view fview) *)
(*       (TS: f loc ts fts) *)
(*       (RACY: TView.racy_view view loc ts): *)
(*   TView.racy_view fview loc fts. *)
(* Proof. *)
(*   inv MAP_WF. unfold TView.racy_view in *. *)
(*   eapply MAP_LT; try exact RACY; eauto. *)
(*   apply VIEW. *)
(* Qed. *)

(* Lemma map_is_racy *)
(*       rsv *)
(*       f1 lc1 gl1 flc1 fgl1 *)
(*       loc to ord *)
(*       (MAP_WF1: map_wf f1) *)
(*       (LC_MAP1: local_map f1 lc1 flc1) *)
(*       (GL_MAP1: global_map f1 rsv gl1 fgl1) *)
(*       (STEP: Local.is_racy lc1 gl1 loc (Some to) ord): *)
(*   exists fto, *)
(*     (<<FSTEP: Local.is_racy flc1 fgl1 loc (Some fto) ord>>) /\ *)
(*     (<<TO: f1 loc to fto>>). *)
(* Proof. *)
(*   inv LC_MAP1. inv GL_MAP1. *)
(*   inv STEP. *)
(*   exploit memory_map_get; eauto; ss. i. des. inv MSG0. *)
(*   esplits; [econs 2|]; eauto. *)
(*   eapply map_racy_view; try apply TVIEW; eauto. *)
(* Qed. *)

(* Lemma map_racy_read_step *)
(*       rsv *)
(*       f1 lc1 gl1 flc1 fgl1 *)
(*       loc to val ord *)
(*       (MAP_WF1: map_wf f1) *)
(*       (LC_MAP1: local_map f1 lc1 flc1) *)
(*       (GL_MAP1: global_map f1 rsv gl1 fgl1) *)
(*       (STEP: Local.racy_read_step lc1 gl1 loc (Some to) val ord): *)
(*   exists fto, *)
(*     (<<FSTEP: Local.racy_read_step flc1 fgl1 loc (Some fto) val ord>>) /\ *)
(*     (<<TO: f1 loc to fto>>). *)
(* Proof. *)
(*   inv STEP. *)
(*   exploit map_is_racy; eauto. i. des. *)
(*   esplits; eauto. *)
(* Qed. *)

(* Lemma map_racy_write_step *)
(*       rsv *)
(*       f1 lc1 gl1 flc1 fgl1 *)
(*       loc to ord *)
(*       (MAP_WF1: map_wf f1) *)
(*       (LC_MAP1: local_map f1 lc1 flc1) *)
(*       (GL_MAP1: global_map f1 rsv gl1 fgl1) *)
(*       (STEP: Local.racy_write_step lc1 gl1 loc (Some to) ord): *)
(*   exists fto, *)
(*     (<<FSTEP: Local.racy_write_step flc1 fgl1 loc (Some fto) ord>>) /\ *)
(*     (<<TO: f1 loc to fto>>). *)
(* Proof. *)
(*   inv STEP. *)
(*   exploit map_is_racy; eauto. i. des. *)
(*   esplits; eauto. *)
(* Qed. *)

(* Lemma map_racy_update_step *)
(*       rsv *)
(*       f1 lc1 gl1 flc1 fgl1 *)
(*       loc to ordr ordw *)
(*       (MAP_WF1: map_wf f1) *)
(*       (LC_MAP1: local_map f1 lc1 flc1) *)
(*       (GL_MAP1: global_map f1 rsv gl1 fgl1) *)
(*       (RACE: to = None -> Ordering.le ordr Ordering.na \/ Ordering.le ordw Ordering.na) *)
(*       (STEP: Local.racy_update_step lc1 gl1 loc to ordr ordw): *)
(*   exists fto, *)
(*     (<<FSTEP: Local.racy_update_step flc1 fgl1 loc fto ordr ordw>>) /\ *)
(*     (<<TO: option_rel (f1 loc) to fto>>). *)
(* Proof. *)
(*   inv STEP. *)
(*   - esplits; eauto. ss. *)
(*   - esplits; eauto. ss. *)
(*   - destruct to. *)
(*     + exploit map_is_racy; eauto. i. des. eauto. *)
(*     + exploit RACE; eauto. *)
(*       i. des; esplits; eauto; ss. *)
(* Qed. *)

(* Lemma map_internal_step *)
(*       f1 lc1 gl1 flc1 fgl1 *)
(*       e lc2 gl2 *)
(*       (MAP_WF1: map_wf f1) *)
(*       (MAP_COMPLETE1: map_complete f1 (Global.memory gl1) (Global.memory fgl1)) *)
(*       (LC_MAP1: local_map f1 lc1 flc1) *)
(*       (GL_MAP1: global_map f1 (Local.reserves lc1) gl1 fgl1) *)
(*       (LC_WF1: Local.wf lc1 gl1) *)
(*       (GL_WF1: Global.wf gl1) *)
(*       (STEP: Local.internal_step e lc1 gl1 lc2 gl2): *)
(*   (<<MAP_COMPLETE2: map_complete f1 (Global.memory gl2) (Global.memory fgl1)>>) /\ *)
(*   (<<LC_MAP2: local_map f1 lc2 flc1>>) /\ *)
(*   (<<GL_MAP2: global_map f1 (Local.reserves lc2) gl2 fgl1>>). *)
(* Proof. *)
(*   inv LC_MAP1. inv GL_MAP1. inv STEP. *)
(*   - inv LOCAL. ss. *)
(*   - inv LOCAL. ss. *)
(*     exploit memory_map_reserve; eauto. i. des. *)
(*     esplits; ss. *)
(*   - inv LOCAL. ss. *)
(*     exploit memory_map_cancel; eauto; try apply LC_WF1; try apply GL_WF1. i. des. *)
(*     esplits; ss. *)
(* Qed. *)

(* Lemma map_program_step *)
(*       f1 lc1 gl1 flc1 fgl1 *)
(*       e lc2 gl2 *)
(*       (MAP_WF1: map_wf f1) *)
(*       (MAP_COMPLETE1: map_complete f1 (Global.memory gl1) (Global.memory fgl1)) *)
(*       (LC_MAP1: local_map f1 lc1 flc1) *)
(*       (GL_MAP1: global_map f1 (Local.reserves lc1) gl1 fgl1) *)
(*       (LC_WF1: Local.wf lc1 gl1) *)
(*       (GL_WF1: Global.wf gl1) *)
(*       (FLC_WF1: Local.wf flc1 fgl1) *)
(*       (FGL_WF1: Global.wf fgl1) *)
(*       (STEP: Local.program_step e lc1 gl1 lc2 gl2) *)
(*       (EVENT1: ~ ThreadEvent.is_racy_promise e) *)
(*       (EVENT2: ~ ThreadEvent.is_sc e): *)
(*   exists f2 fe flc2 fgl2, *)
(*     (<<FSTEP: Local.program_step fe flc1 fgl1 flc2 fgl2>>) /\ *)
(*     (<<EVENT: event_map f2 e fe>>) /\ *)
(*     (<<MAP_INCR: f1 <3= f2>>) /\ *)
(*     (<<MAP_WF2: map_wf f2>>) /\ *)
(*     (<<MAP_COMPLETE2: map_complete f2 (Global.memory gl2) (Global.memory fgl2)>>) /\ *)
(*     (<<LC_MAP2: local_map f2 lc2 flc2>>) /\ *)
(*     (<<GL_MAP2: global_map f2 (Local.reserves lc2) gl2 fgl2>>). *)
(* Proof. *)
(*   inv STEP. *)
(*   - esplits; [econs 1|..]; eauto. econs. *)
(*   - exploit map_read_step; eauto. i. des. *)
(*     esplits; [econs 2|..]; eauto. *)
(*     + econs; ss. *)
(*     + inv LOCAL. ss. *)
(*   - exploit map_write_step; eauto; try by econs. i. des. *)
(*     esplits; [econs 3|..]; try exact MAP_WF2; eauto. *)
(*     + econs; ss. *)
(*     + i. subst. repeat apply map_add_incr; ss. *)
(*   - exploit map_read_step; eauto. i. des. *)
(*     exploit Local.read_step_future; try exact LOCAL1; eauto. i. des. *)
(*     exploit Local.read_step_future; try exact FSTEP; eauto. i. des. *)
(*     exploit map_write_step; try exact LOCAL2; eauto. *)
(*     { inv LOCAL1. ss. } *)
(*     i. des. *)
(*     replace fto with ffrom in *; cycle 1. *)
(*     { inv MAP_WF2. eapply MAP_EQ; [refl|exact FROM_MAP|..]. auto. } *)
(*     esplits; [econs 4|..]; try exact MAP_WF2; eauto. *)
(*     + econs; ss. *)
(*       eapply opt_view_map_incr; try exact RELEASED_MAP. *)
(*       i. subst. repeat apply map_add_incr; ss. *)
(*     + i. subst. repeat apply map_add_incr; ss. *)
(*   - exploit map_fence_step; eauto. *)
(*     { destruct ordw; ss. } *)
(*     i. des. *)
(*     esplits; [econs 5|..]; eauto. *)
(*     + econs; ss. *)
(*     + inv LOCAL. ss. *)
(*   - exploit map_fence_step; eauto; ss. *)
(*   - esplits; [econs 7|..]; eauto. econs. *)
(*   - destruct to; ss. *)
(*     exploit map_racy_read_step; eauto. i. des. *)
(*     esplits; [econs 8|..]; eauto. econs; ss. *)
(*   - destruct to; ss. *)
(*     exploit map_racy_write_step; eauto. i. des. *)
(*     esplits; [econs 9|..]; eauto. econs; ss. *)
(*   - exploit map_racy_update_step; eauto. *)
(*     { i. subst. ss. *)
(*       apply not_and_or in EVENT1. des. *)
(*       - left. destruct ordr; ss. *)
(*       - right. destruct ordw; ss. *)
(*     } *)
(*     i. des. *)
(*     esplits; [econs 10|..]; eauto. econs; ss. *)
(* Qed. *)
