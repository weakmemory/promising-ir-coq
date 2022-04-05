Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Event.

Require Import Time.
Require Import View.
Require Import Reserves.
Require Import Cell.

Set Implicit Arguments.


Module Memory.
  Definition t := Loc.t -> Cell.t.

  Definition get (loc:Loc.t) (ts:Time.t) (mem:t): option (Time.t * Message.t) :=
    Cell.get ts (mem loc).

  Lemma get_disjoint
        l f1 f2 t1 t2 msg1 msg2 m
        (GET1: get l t1 m = Some (f1, msg1))
        (GET2: get l t2 m = Some (f2, msg2)):
    (t1 = t2 /\ f1 = f2 /\ msg1 = msg2) \/
    Interval.disjoint (f1, t1) (f2, t2).
  Proof.
    eapply Cell.get_disjoint; eauto.
  Qed.

  Lemma ext
        lhs rhs
        (EXT: forall loc ts, get loc ts lhs = get loc ts rhs):
    lhs = rhs.
  Proof.
    apply LocFun.ext. i.
    apply Cell.ext. i.
    apply EXT.
  Qed.

  Lemma get_ts
        loc to mem from msg
        (GET: get loc to mem = Some (from, msg)):
    (from = Time.bot /\ to = Time.bot) \/ Time.lt from to.
  Proof.
    unfold get in *.
    apply Cell.get_ts in GET. auto.
  Qed.

  Definition le (lhs rhs:t): Prop :=
    forall loc to from msg
      (LHS: get loc to lhs = Some (from, msg)),
      get loc to rhs = Some (from, msg).

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. ii. auto. Qed.
  Next Obligation. ii. eapply H0; eauto. Qed.

  Variant disjoint (lhs rhs:t): Prop :=
  | disjoint_intro
      (DISJOINT: forall loc to1 to2 from1 from2 msg1 msg2
                   (GET1: get loc to1 lhs = Some (from1, msg1))
                   (GET2: get loc to2 rhs = Some (from2, msg2)),
          Interval.disjoint (from1, to1) (from2, to2) /\
          (to1, to2) <> (Time.bot, Time.bot))
  .
  #[global] Hint Constructors disjoint: core.

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    inv H. econs. i. exploit DISJOINT; eauto. i. des. splits.
    - symmetry. auto.
    - ii. inv H. congr.
  Qed.

  Lemma disjoint_get
        lhs rhs
        loc froml fromr to msgl msgr
        (DISJOINT: disjoint lhs rhs)
        (LMSG: get loc to lhs = Some (froml, msgl))
        (RMSG: get loc to rhs = Some (fromr, msgr)):
    False.
  Proof.
    inv DISJOINT. exploit DISJOINT0; eauto. intros x. des.
    destruct (Time.eq_dec to Time.bot).
    - subst. congr.
    - eapply x.
      + apply Interval.mem_ub. destruct (Cell.WF (lhs loc)).
        exploit VOLUME; eauto. intros x1. des; auto. inv x1. congr.
      + apply Interval.mem_ub. destruct (Cell.WF (rhs loc)).
        exploit VOLUME; eauto. intros x1. des; auto. inv x1. congr.
  Qed.

  Lemma disjoint_get_general
        lhs rhs
        loc ts0 ts1 ts2 ts3 msgl msgr
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.le ts2 ts3)
        (DISJOINT: disjoint lhs rhs)
        (LMSG: get loc ts2 lhs = Some (ts0, msgl))
        (RMSG: get loc ts3 rhs = Some (ts1, msgr)):
    False.
  Proof.
    inv DISJOINT. exploit DISJOINT0; eauto. intros x. des.
    destruct (Time.le_lt_dec ts2 ts0).
    - destruct (Cell.WF (lhs loc)). exploit VOLUME; eauto. intros x1. des.
      + inv x1. inv TS12.
      + eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
    - eapply x.
      + eapply Interval.mem_ub. auto.
      + econs; auto.
  Qed.

  Definition bot: t := fun _ => Cell.bot.

  Lemma bot_get loc ts: get loc ts bot = None.
  Proof. unfold get. apply Cell.bot_get. Qed.

  Lemma bot_le mem: le bot mem.
  Proof. ii. rewrite bot_get in LHS. congr. Qed.

  Lemma bot_disjoint mem: disjoint bot mem.
  Proof.
    econs. i. rewrite bot_get in *. inv GET1.
  Qed.

  Definition init: t := fun _ => Cell.init.

  Variant message_to: forall (msg:Message.t) (loc:Loc.t) (to:Time.t), Prop :=
  | message_to_intro
      val released na loc to
      (TS: Time.le ((View.rlx (View.unwrap released)) loc) to):
    message_to (Message.mk val released na) loc to
  .
  #[global] Hint Constructors message_to: core.

  Definition closed_timemap (times:TimeMap.t) (mem:t): Prop :=
    forall loc, exists from val released na,
      get loc (times loc) mem = Some (from, Message.mk val released na).

  Variant closed_view (view:View.t) (mem:t): Prop :=
  | closed_view_intro
      (PLN: closed_timemap (View.pln view) mem)
      (RLX: closed_timemap (View.rlx view) mem)
  .
  #[global] Hint Constructors closed_view: core.

  Variant closed_opt_view: forall (view:option View.t) (mem:t), Prop :=
  | closed_opt_view_some
      view mem
      (CLOSED: closed_view view mem):
      closed_opt_view (Some view) mem
  | closed_opt_view_none
      mem:
      closed_opt_view None mem
  .
  #[global] Hint Constructors closed_opt_view: core.

  Variant closed_message: forall (msg:Message.t) (mem:t), Prop :=
  | closed_message_intro
      val released na mem
      (CLOSED: closed_opt_view released mem):
    closed_message (Message.mk val released na) mem
  .
  #[global] Hint Constructors closed_message: core.

  Definition closed_reserves (rsv:Reserves.t) (mem:t): Prop :=
    forall loc ts (GET: rsv loc = Some ts),
    exists from val released na,
      get loc ts mem = Some (from, Message.mk val released na).


  Definition inhabited (mem:t): Prop :=
    forall loc, get loc Time.bot mem = Some (Time.bot, Message.elt).
  #[global] Hint Unfold inhabited: core.

  Variant closed (mem:t): Prop :=
  | closed_intro
      (CLOSED: forall loc from to msg
                 (MSG: get loc to mem = Some (from, msg)),
          <<MSG_WF: Message.wf msg>> /\
          <<MSG_TS: message_to msg loc to>> /\
          <<MSG_CLOSED: closed_message msg mem>>)
      (INHABITED: inhabited mem)
  .
  #[global] Hint Constructors closed: core.

  Lemma closed_timemap_bot
        mem
        (INHABITED: inhabited mem):
    closed_timemap TimeMap.bot mem.
  Proof. ii. esplits. eapply INHABITED. Qed.

  Lemma closed_view_bot
        mem
        (INHABITED: inhabited mem):
    closed_view View.bot mem.
  Proof. econs; apply closed_timemap_bot; auto. Qed.

  Lemma unwrap_closed_opt_view
        view mem
        (CLOSED: closed_opt_view view mem)
        (INHABITED: inhabited mem):
    closed_view (View.unwrap view) mem.
  Proof.
    inv CLOSED; ss. apply closed_view_bot. ss.
  Qed.

  Lemma le_closed_timemap
        tm mem1 mem2
        (LE: le mem1 mem2)
        (CLOSED: Memory.closed_timemap tm mem1):
    Memory.closed_timemap tm mem2.
  Proof.
    ii. exploit CLOSED; eauto. i. des.
    esplits; eauto.
  Qed.

  Lemma le_closed_view
        view mem1 mem2
        (LE: le mem1 mem2)
        (CLOSED: Memory.closed_view view mem1):
    Memory.closed_view view mem2.
  Proof.
    inv CLOSED. econs; eauto using le_closed_timemap.
  Qed.

  Lemma le_closed_opt_view
        view mem1 mem2
        (LE: le mem1 mem2)
        (CLOSED: Memory.closed_opt_view view mem1):
    Memory.closed_opt_view view mem2.
  Proof.
    inv CLOSED; econs.
    eapply le_closed_view; eauto.
  Qed.

  Lemma le_closed_message
        msg mem1 mem2
        (LE: le mem1 mem2)
        (CLOSED: Memory.closed_message msg mem1):
    Memory.closed_message msg mem2.
  Proof.
    inv CLOSED; econs.
    eapply le_closed_opt_view; eauto.
  Qed.

  Lemma le_closed_reserves
        rsv mem1 mem2
        (LE: le mem1 mem2)
        (CLOSED: Memory.closed_reserves rsv mem1):
    Memory.closed_reserves rsv mem2.
  Proof.
    ii. exploit CLOSED; eauto. i. des.
    exploit LE; eauto.
  Qed.

  Lemma init_closed: closed init.
  Proof.
    econs; i; ss.
    unfold get, init, Cell.get, Cell.init in MSG. ss.
    apply DOMap.singleton_find_inv in MSG. des. inv MSG0.
    splits; ss. econs. refl.
  Qed.

  Variant add (mem1:t) (loc:Loc.t) (from to:Time.t) (msg:Message.t) (mem2:t): Prop :=
  | add_intro
      r
      (ADD: Cell.add (mem1 loc) from to msg r)
      (MEM2: mem2 = LocFun.add loc r mem1)
  .
  #[global] Hint Constructors add: core.

  Variant future_imm (mem1 mem2:t): Prop :=
  | future_imm_intro
      loc from to msg
      (ADD: add mem1 loc from to msg mem2)
      (CLOSED: closed_message msg mem2)
      (TS: message_to msg loc to)
  .
  #[global] Hint Constructors future_imm: core.

  Definition future := rtc future_imm.
  #[global] Hint Unfold future: core.


  (* Lemmas on add & future *)

  Lemma add_ts
        mem1 mem2 loc from to msg
        (ADD: add mem1 loc from to msg mem2):
    Time.lt from to.
  Proof.
    inv ADD. inv ADD0. ss.
  Qed.

  Lemma add_o
        mem2 mem1 loc from to msg
        l t
        (ADD: add mem1 loc from to msg mem2):
    get l t mem2 =
    if loc_ts_eq_dec (l, t) (loc, to)
    then Some (from, msg)
    else get l t mem1.
  Proof.
    inv ADD. unfold get, LocFun.add. condtac.
    - subst. erewrite Cell.add_o; eauto.
      repeat (condtac; subst; des; ss; try congr).
    - repeat (condtac; subst; des; ss; try congr).
  Qed.

  Lemma add_get0
        mem1 loc from1 to1 msg1 mem2
        (ADD: add mem1 loc from1 to1 msg1 mem2):
    <<GET: get loc to1 mem1 = None>> /\
    <<GET: get loc to1 mem2 = Some (from1, msg1)>>.
  Proof.
    inv ADD. eapply Cell.add_get0; eauto.
    unfold get, Cell.get, LocFun.add. condtac; ss.
  Qed.

  Lemma add_get1
        m1 loc from to msg m2
        l f t m
        (ADD: add m1 loc from to msg m2)
        (GET1: get l t m1 = Some (f, m)):
    get l t m2 = Some (f, m).
  Proof.
    erewrite add_o; eauto. condtac; ss.
    des. subst. exploit add_get0; eauto. i. des. congr.
  Qed.

  Lemma add_get_diff
        mem1 loc from to msg mem2
        loc'
        (ADD: add mem1 loc from to msg mem2)
        (LOC: loc' <> loc):
    forall to', get loc' to' mem2 = get loc' to' mem1.
  Proof.
    i. erewrite add_o; eauto. condtac; ss. des. ss.
  Qed.

  Lemma future_get1
        loc from to msg mem1 mem2
        (FUTURE: future mem1 mem2)
        (GET: get loc to mem1 = Some (from, msg)):
    <<GET: get loc to mem2 = Some (from, msg)>>.
  Proof.
    revert from msg GET.
    induction FUTURE; eauto. i.
    inv H. eauto using add_get1.
  Qed.


  (* inhabited *)

  Lemma add_inhabited
        mem1 mem2 loc from to msg
        (ADD: add mem1 loc from to msg mem2)
        (INHABITED: inhabited mem1):
    <<INHABITED: inhabited mem2>>.
  Proof.
    ii. erewrite add_o; eauto. condtac; ss.
    des. subst. inv ADD. inv ADD0. inv TO.
  Qed.

  Lemma future_inhabited
        mem1 mem2
        (FUTURE: future mem1 mem2)
        (INHABITED: inhabited mem1):
    inhabited mem2.
  Proof.
    revert INHABITED.
    induction FUTURE; eauto. i. inv H.
    apply IHFUTURE.
    eapply add_inhabited; eauto.
  Qed.


  (* le *)

  Lemma add_le
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2):
    le mem1 mem2.
  Proof.
    ii. eapply Memory.add_get1; eauto.
  Qed.

  Lemma future_le
        mem1 mem2
        (FUTURE: future mem1 mem2):
    le mem1 mem2.
  Proof.
    induction FUTURE; try refl.
    etrans; eauto.
    inv H. eapply add_le; eauto.
  Qed.


  (* Lemmas on closedness *)

  Lemma join_closed_timemap
        lhs rhs mem
        (LHS: closed_timemap lhs mem)
        (RHS: closed_timemap rhs mem):
    closed_timemap (TimeMap.join lhs rhs) mem.
  Proof.
    ii. unfold TimeMap.join.
    destruct (Time.join_cases (lhs loc) (rhs loc)) as [X|X]; rewrite X.
    - apply LHS.
    - apply RHS.
  Qed.

  Lemma join_closed_view
        lhs rhs mem
        (LHS: closed_view lhs mem)
        (RHS: closed_view rhs mem):
    closed_view (View.join lhs rhs) mem.
  Proof.
    econs.
    - apply join_closed_timemap.
      + apply LHS.
      + apply RHS.
    - apply join_closed_timemap.
      + apply LHS.
      + apply RHS.
  Qed.

  Lemma add_closed_timemap
        times
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED: closed_timemap times mem1):
    closed_timemap times mem2.
  Proof.
    ii. erewrite add_o; eauto. condtac; ss.
    des. subst. exfalso.
    specialize (CLOSED loc). des.
    exploit add_get0; eauto. i. des. congr.
  Qed.

  Lemma add_closed_view
        view
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv CLOSED. econs; eauto.
    - eapply add_closed_timemap; eauto.
    - eapply add_closed_timemap; eauto.
  Qed.

  Lemma add_closed_opt_view
        view
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED: closed_opt_view view mem1):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; econs. eapply add_closed_view; eauto.
  Qed.

  Lemma add_closed_message
        msg'
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED: closed_message msg' mem1):
    closed_message msg' mem2.
  Proof.
    destruct msg'; ss. inv CLOSED. econs.
    eapply add_closed_opt_view; eauto.
  Qed.

  Lemma add_closed_reserves
        rsv
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED: closed_reserves rsv mem1):
    closed_reserves rsv mem2.
  Proof.
    ii. exploit CLOSED; eauto. i. des.
    erewrite Memory.add_o; eauto. condtac; ss; eauto.
    des. clarify. destruct msg. esplits; eauto.
  Qed.

  Lemma add_closed
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED: closed mem1)
        (MSG_CLOSED: closed_message msg mem2)
        (MSG_TS: message_to msg loc to):
    closed mem2.
  Proof.
    inv CLOSED. econs.
    - i. revert MSG. erewrite add_o; eauto. condtac; ss.
      + des. subst. i. inv MSG. splits; auto.
        inv ADD. inv ADD0. auto.
      + guardH o. i. exploit CLOSED0; eauto. i. des. splits; auto.
        eapply add_closed_message; eauto.
    - eapply add_inhabited; eauto.
  Qed.

  Lemma future_closed_timemap
        times mem1 mem2
        (CLOSED: closed_timemap times mem1)
        (FUTURE: future mem1 mem2):
    closed_timemap times mem2.
  Proof.
    revert CLOSED. induction FUTURE; auto. i.
    apply IHFUTURE. inv H.
    eapply add_closed_timemap; eauto.
  Qed.

  Lemma future_closed_view
        view mem1 mem2
        (FUTURE: future mem1 mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    revert CLOSED. induction FUTURE; auto. i.
    apply IHFUTURE. inv H.
    eapply add_closed_view; eauto.
  Qed.

  Lemma future_closed_opt_view
        view mem1 mem2
        (FUTURE: future mem1 mem2)
        (CLOSED: closed_opt_view view mem1):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; econs. eapply future_closed_view; eauto.
  Qed.

  Lemma future_closed_message
        msg mem1 mem2
        (FUTURE: future mem1 mem2)
        (CLOSED: closed_message msg mem1):
    closed_message msg mem2.
  Proof.
    inv CLOSED; econs. eapply future_closed_opt_view; eauto.
  Qed.

  Lemma future_closed_reserves
        rsv mem1 mem2
        (FUTURE: future mem1 mem2)
        (CLOSED: closed_reserves rsv mem1):
    closed_reserves rsv mem2.
  Proof.
    revert CLOSED. induction FUTURE; auto. i.
    apply IHFUTURE. inv H.
    eapply add_closed_reserves; eauto.
  Qed.

  Lemma future_closed
        mem1 mem2
        (FUTURE: future mem1 mem2)
        (CLOSED: closed mem1):
    closed mem2.
  Proof.
    revert CLOSED. induction FUTURE; auto. i.
    apply IHFUTURE. inv H.
    eapply add_closed; eauto.
  Qed.

  Lemma singleton_closed_timemap
        loc from to val released na mem
        (GET: get loc to mem = Some (from, Message.mk val released na))
        (INHABITED: inhabited mem):
    closed_timemap (TimeMap.singleton loc to) mem.
  Proof.
    unfold TimeMap.singleton, LocFun.add, LocFun.find. ii. condtac.
    - subst. eauto.
    - apply closed_timemap_bot. auto.
  Qed.

  Lemma singleton_ur_closed_view
        loc from to val released na mem
        (GET: get loc to mem = Some (from, Message.mk val released na))
        (INHABITED: inhabited mem):
    closed_view (View.singleton_ur loc to) mem.
  Proof.
    econs; s.
    - eapply singleton_closed_timemap; eauto.
    - eapply singleton_closed_timemap; eauto.
  Qed.

  Lemma singleton_rw_closed_view
        loc from to val released na mem
        (GET: get loc to mem = Some (from, Message.mk val released na))
        (INHABITED: inhabited mem):
    closed_view (View.singleton_rw loc to) mem.
  Proof.
    econs; s.
    - apply closed_timemap_bot. auto.
    - eapply singleton_closed_timemap; eauto.
  Qed.

  Lemma singleton_ur_if_closed_view
        cond loc from to val released na mem
        (GET: get loc to mem = Some (from, Message.mk val released na))
        (INHABITED: inhabited mem):
    closed_view (View.singleton_ur_if cond loc to) mem.
  Proof.
    destruct cond; ss.
    - eapply singleton_ur_closed_view; eauto.
    - eapply singleton_rw_closed_view; eauto.
  Qed.


  (* future *)

  Lemma add_future
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED1: closed mem1)
        (MSG_CLOSED: closed_message msg mem2)
        (MSG_TS: message_to msg loc to):
    <<CLOSED2: closed mem2>> /\
    <<FUTURE: future mem1 mem2>> /\
    <<MSG_WF: Message.wf msg>>.
  Proof.
    hexploit add_inhabited; try apply CLOSED1; eauto. i. splits.
    - eapply add_closed; eauto.
    - econs 2; eauto.
    - inv ADD. inv ADD0. ss.
  Qed.


  (* Lemmas on max_timemap *)

  Definition max_ts (loc:Loc.t) (mem:t): Time.t :=
    Cell.max_ts (mem loc).

  Lemma max_ts_spec
        loc ts from msg mem
        (GET: get loc ts mem = Some (from, msg)):
    <<GET: exists from msg, get loc (max_ts loc mem) mem = Some (from, msg)>> /\
    <<MAX: Time.le ts (max_ts loc mem)>>.
  Proof. eapply Cell.max_ts_spec; eauto. Qed.

  Lemma max_ts_spec2
        tm mem loc
        (CLOSED: closed_timemap tm mem):
    Time.le (tm loc) (max_ts loc mem).
  Proof.
    exploit CLOSED. i. des.
    eapply max_ts_spec. eauto.
  Qed.

  Definition max_timemap (mem:t): TimeMap.t :=
    fun loc => max_ts loc mem.

  Lemma max_timemap_spec
        tm mem
        (TIMEMAP: closed_timemap tm mem)
        (INHABITED: inhabited mem):
    TimeMap.le tm (max_timemap mem).
  Proof.
    ii. specialize (INHABITED loc). des.
    exploit TIMEMAP. i. des.
    eapply max_ts_spec; eauto.
  Qed.

  Lemma max_timemap_closed
        mem
        (INHABITED: inhabited mem):
    closed_timemap (max_timemap mem) mem.
  Proof.
    ii. specialize (INHABITED loc).
    exploit max_ts_spec; try exact INHABITED. i. des.
    destruct msg. esplits; eauto.
  Qed.

  Definition max_reserves (mem:t): Reserves.t :=
    fun loc => Some (max_ts loc mem).

  Lemma max_reserves_spec
        rsv mem
        (RESERVES: closed_reserves rsv mem)
        (INHABITED: inhabited mem):
    Reserves.le rsv (max_reserves mem).
  Proof.
    ii. specialize (INHABITED loc).
    destruct (rsv loc) eqn:GET; ss.
    exploit RESERVES; eauto. i. des.
    exploit max_ts_spec; try exact x0. i. des.
    econs. ss.
  Qed.

  Lemma max_reserves_closed
        mem
        (INHABITED: inhabited mem):
    closed_reserves (max_reserves mem) mem.
  Proof.
    ii. inv GET.
    specialize (INHABITED loc).
    exploit max_ts_spec; try exact INHABITED. i. des.
    destruct msg. esplits; eauto.
  Qed.

  Definition max_view (mem:t): View.t :=
    View.mk (max_timemap mem) (max_timemap mem).

  Lemma max_view_wf mem: View.wf (max_view mem).
  Proof. econs. refl. Qed.

  Lemma max_view_spec tm mem
        (VIEW: closed_view tm mem)
        (INHABITED: inhabited mem):
    View.le tm (max_view mem).
  Proof.
    econs; apply max_timemap_spec; try apply VIEW; auto.
  Qed.


  (* Lemmas on existence of memory op *)

  Lemma add_exists
        mem1 loc from to msg
        (DISJOINT: forall to2 from2 msg2
                     (GET2: get loc to2 mem1 = Some (from2, msg2)),
            Interval.disjoint (from, to) (from2, to2))
        (TO1: Time.lt from to)
        (MSG_WF: Message.wf msg):
    exists mem2, add mem1 loc from to msg mem2.
  Proof.
    exploit Cell.add_exists; eauto. i. des.
    eexists. econs; eauto.
  Qed.

  Lemma add_exists_max_ts
        mem1 loc to msg
        (TS: Time.lt (max_ts loc mem1) to)
        (MSG_WF: Message.wf msg):
    exists mem2,
      add mem1 loc (max_ts loc mem1) to msg mem2.
  Proof.
    eapply add_exists; eauto.
    i. exploit max_ts_spec; eauto. i. des.
    ii. inv LHS. inv RHS. ss.
    rewrite MAX in TO0. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
  Qed.

  Lemma add_exists_le
        mem1' mem1 loc from to msg mem2
        (LE: le mem1' mem1)
        (ADD: add mem1 loc from to msg mem2):
    exists mem2', add mem1' loc from to msg mem2'.
  Proof.
    inv ADD.
    exploit Cell.add_exists_le; eauto.
    { ii. eapply LE. eauto. }
    i. des.
    eexists. econs; eauto.
  Qed.

  Lemma add_inj
        mem loc to from msg mem1 mem2
        (REMOVE1: Memory.add mem loc from to msg mem1)
        (REMOVE2: Memory.add mem loc from to msg mem2):
    mem1 = mem2.
  Proof.
    apply Memory.ext. i.
    setoid_rewrite Memory.add_o; eauto.
  Qed.
End Memory.
