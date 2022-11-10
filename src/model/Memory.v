Require Import RelationClasses.
Require Import Coq.Logic.IndefiniteDescription.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Event.

Require Import Time.
Require Import View.
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

  Lemma get_ts_le
        loc to mem from msg
        (GET: get loc to mem = Some (from, msg)):
    Time.le from to.
  Proof.
    exploit get_ts; eauto. i. des; timetac.
  Qed.

  Lemma lt_get
        loc mem
        to1 from1 msg1
        to2 from2 msg2
        (LT: Time.lt to1 to2)
        (GET1: get loc to1 mem = Some (from1, msg1))
        (GET2: get loc to2 mem = Some (from2, msg2)):
    Time.le to1 from2.
  Proof.
    exploit get_ts; try exact GET1. i. des; timetac.
    destruct (TimeFacts.le_lt_dec to1 from2); ss.
    exploit get_disjoint; [exact GET1|exact GET2|]. i. des; timetac.
    exfalso. apply (x1 to1); econs; ss; try refl.
    econs. ss.
  Qed.

  Lemma lt_from_get
        loc mem
        to1 from1 msg1
        to2 from2 msg2
        (LT: Time.lt from1 to2)
        (GET1: get loc to1 mem = Some (from1, msg1))
        (GET2: get loc to2 mem = Some (from2, msg2)):
    from1 = from2 /\ to1 = to2 /\ msg1 = msg2 \/
    Time.le to1 from2.
  Proof.
    exploit get_ts; try exact GET1. i. des.
    { subst. right. timetac. }
    exploit get_ts; try exact GET2. i. des.
    { subst. right. timetac. }
    destruct (TimeFacts.le_lt_dec to1 from2); auto.
    exploit get_disjoint; [exact GET1|exact GET2|]. i. des; auto.
    exfalso.
    destruct (TimeFacts.le_lt_dec to1 to2).
    - apply (x2 to1); econs; ss. refl.
    - apply (x2 to2); econs; ss; timetac. refl.
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

  Definition reserve_only (rsv: t): Prop :=
    forall loc from to msg
      (GET: get loc to rsv = Some (from, msg)),
      msg = Message.reserve.

  Definition bot: t := fun _ => Cell.bot.

  Lemma bot_get loc ts: get loc ts bot = None.
  Proof.
    unfold get. apply Cell.bot_get.
  Qed.

  Lemma bot_le mem: le bot mem.
  Proof.
    ii. rewrite bot_get in LHS. congr.
  Qed.

  Lemma bot_disjoint mem: disjoint bot mem.
  Proof.
    econs. i. rewrite bot_get in *. inv GET1.
  Qed.

  Lemma bot_reserve_only: reserve_only bot.
  Proof.
    ii. rewrite bot_get in *. ss.
  Qed.

  Lemma le_reserve_only
    rsv1 rsv2
    (LE: le rsv1 rsv2)
    (ONLY: reserve_only rsv2):
    reserve_only rsv1.
  Proof.
    ii. eapply ONLY. eauto.
  Qed.

  Definition init: t := fun _ => Cell.init.

  Lemma init_get
        loc from to msg
        (GET: get loc to Memory.init = Some (from, msg)):
    to = Time.bot /\ from = Time.bot /\ msg = Message.elt.
  Proof.
    unfold get, init, Cell.get, Cell.init in GET. ss.
    apply DOMap.singleton_find_inv in GET. des. inv GET0.
    auto.
  Qed.

  Variant message_to: forall (msg:Message.t) (loc:Loc.t) (to:Time.t), Prop :=
    | message_to_message
        val released na loc to
        (TS: Time.le ((View.rlx (View.unwrap released)) loc) to):
      message_to (Message.message val released na) loc to
    | message_to_reserve
      loc to:
      message_to Message.reserve loc to
  .
  #[global] Hint Constructors message_to: core.

  Definition closed_timemap (times:TimeMap.t) (mem:t): Prop :=
    forall loc, exists from val released na,
      get loc (times loc) mem = Some (from, Message.message val released na).

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
    | closed_message_message
        val released na mem
        (CLOSED: closed_opt_view released mem):
      closed_message (Message.message val released na) mem
    | closed_message_reserve
        mem:
      closed_message Message.reserve mem
  .
  #[global] Hint Constructors closed_message: core.

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
        (CLOSED: closed_timemap tm mem1):
    closed_timemap tm mem2.
  Proof.
    ii. exploit CLOSED; eauto. i. des.
    esplits; eauto.
  Qed.

  Lemma le_closed_view
        view mem1 mem2
        (LE: le mem1 mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv CLOSED. econs; eauto using le_closed_timemap.
  Qed.

  Lemma le_closed_opt_view
        view mem1 mem2
        (LE: le mem1 mem2)
        (CLOSED: closed_opt_view view mem1):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; econs.
    eapply le_closed_view; eauto.
  Qed.

  Lemma le_closed_message
        msg mem1 mem2
        (LE: le mem1 mem2)
        (CLOSED: closed_message msg mem1):
    closed_message msg mem2.
  Proof.
    inv CLOSED; econs.
    eapply le_closed_opt_view; eauto.
  Qed.

  Lemma init_closed: closed init.
  Proof.
    econs; i; ss.
    unfold get, init, Cell.get, Cell.init in MSG. ss.
    apply DOMap.singleton_find_inv in MSG. des. inv MSG0.
    splits; ss.
    - econs. ss.
    - econs. refl.
    - econs. ss.
  Qed.

  Variant add (mem1:t) (loc:Loc.t) (from to:Time.t) (msg:Message.t) (mem2:t): Prop :=
    | add_intro
        r
        (ADD: Cell.add (mem1 loc) from to msg r)
        (MEM2: mem2 = LocFun.add loc r mem1)
  .
  #[global] Hint Constructors add: core.

  Variant remove (mem1:t) (loc:Loc.t) (from to:Time.t) (msg:Message.t) (mem2:t): Prop :=
    | remove_intro
        r
        (REMOVE: Cell.remove (mem1 loc) from to msg r)
        (MEM2: mem2 = LocFun.add loc r mem1)
  .
  #[global] Hint Constructors remove: core.

  Variant future_imm (mem1 mem2:t): Prop :=
    | future_imm_add
        loc from to msg
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED: closed_message msg mem2)
        (TS: message_to msg loc to)
    | future_imm_remove
        loc from to
        (REMOVE: remove mem1 loc from to Message.reserve mem2)
  .
  #[global] Hint Constructors future_imm: core.

  Definition future := rtc future_imm.
  #[global] Hint Unfold future: core.

  Variant reserve (rsv1 mem1: t) (loc: Loc.t) (from to: Time.t) (rsv2 mem2: t): Prop :=
    | reserve_intro
        (RSV: add rsv1 loc from to Message.reserve rsv2)
        (MEM: add mem1 loc from to Message.reserve mem2)
  .
  #[global] Hint Constructors reserve: core.

  Variant cancel (rsv1 mem1: t) (loc: Loc.t) (from to: Time.t) (rsv2 mem2: t): Prop :=
    | cancel_intro
        (RSV: remove rsv1 loc from to Message.reserve rsv2)
        (MEM: remove mem1 loc from to Message.reserve mem2)
  .
  #[global] Hint Constructors cancel: core.


  (* Lemmas on add *)

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

  Lemma add_inj
        mem loc from to msg mem1 mem2
        (ADD1: add mem loc from to msg mem1)
        (ADD2: add mem loc from to msg mem2):
    mem1 = mem2.
  Proof.
    apply ext. i.
    setoid_rewrite add_o; eauto.
  Qed.

  Lemma add_inhabited
        mem1 mem2 loc from to msg
        (ADD: add mem1 loc from to msg mem2)
        (INHABITED: inhabited mem1):
    <<INHABITED: inhabited mem2>>.
  Proof.
    ii. erewrite add_o; eauto. condtac; ss.
    des. subst. inv ADD. inv ADD0. inv TO.
  Qed.

  Lemma add_le
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2):
    le mem1 mem2.
  Proof.
    ii. eapply add_get1; eauto.
  Qed.

  Lemma add_reserve_only
        mem1 loc from to mem2
        (ADD: add mem1 loc from to Message.reserve mem2)
        (ONLY1: reserve_only mem1):
    reserve_only mem2.
  Proof.
    ii. revert GET.
    erewrite add_o; eauto. condtac; ss; eauto.
    i. des. inv GET. ss.
  Qed.


  (* lemmas on remove *)

  Lemma remove_o
        mem2 mem1 loc from to msg
        l t
        (REMOVE: remove mem1 loc from to msg mem2):
    get l t mem2 =
    if loc_ts_eq_dec (l, t) (loc, to)
    then None
    else get l t mem1.
  Proof.
    inv REMOVE. unfold get, LocFun.add. condtac.
    - subst. erewrite Cell.remove_o; eauto.
      repeat (condtac; subst; des; ss; try congr).
    - repeat (condtac; subst; des; ss; try congr).
  Qed.

  Lemma remove_get0
        mem1 loc from to msg mem2
        (REMOVE: remove mem1 loc from to msg mem2):
    <<GET: get loc to mem1 = Some (from, msg)>> /\
    <<GET: get loc to mem2 = None>>.
  Proof.
    inv REMOVE. eapply Cell.remove_get0; eauto.
    unfold get, Cell.get, LocFun.add. condtac; ss.
  Qed.

  Lemma remove_get1
        m1 loc from to msg m2
        l f t m
        (REMOVE: remove m1 loc from to msg m2)
        (GET1: get l t m1 = Some (f, m)):
    l = loc /\ f = from /\ t = to /\ m = msg \/
    get l t m2 = Some (f, m).
  Proof.
    erewrite remove_o; eauto. condtac; ss; eauto.
    des. subst. exploit remove_get0; eauto. i. des.
    rewrite GET in *. inv GET1. eauto.
  Qed.

  Lemma remove_get_diff
        mem1 loc from to msg mem2
        loc'
        (REMOVE: remove mem1 loc from to msg mem2)
        (LOC: loc' <> loc):
    forall to', get loc' to' mem2 = get loc' to' mem1.
  Proof.
    i. erewrite remove_o; eauto. condtac; ss. des. ss.
  Qed.

  Lemma remove_inj
        mem loc from to msg mem1 mem2
        (REMOVE1: remove mem loc from to msg mem1)
        (REMOVE2: remove mem loc from to msg mem2):
    mem1 = mem2.
  Proof.
    apply ext. i.
    setoid_rewrite remove_o; eauto.
  Qed.

  Lemma remove_inhabited
        mem1 loc from to mem2
        (REMOVE: remove mem1 loc from to Message.reserve mem2)
        (INHABITED: inhabited mem1):
    <<INHABITED: inhabited mem2>>.
  Proof.
    ii. erewrite remove_o; eauto. condtac; ss.
    des. subst. exploit remove_get0; eauto. i. des.
    rewrite INHABITED in *. ss.
  Qed.

  Lemma remove_le
        mem1 loc from to msg mem2
        (REMOVE: remove mem1 loc from to msg mem2):
    le mem2 mem1.
  Proof.
    ii. revert LHS.
    erewrite remove_o; eauto. condtac; ss.
  Qed.

  Lemma remove_reserve_only
        mem1 loc from to msg mem2
        (REMOVE: remove mem1 loc from to msg mem2)
        (ONLY1: reserve_only mem1):
    reserve_only mem2.
  Proof.
    ii. revert GET.
    erewrite remove_o; eauto. condtac; ss; eauto.
  Qed.


  (* lemmas on reserve & cancel *)

  Lemma reserve_inhabited
        rsv1 mem1 loc from to rsv2 mem2
        (RESERVE: reserve rsv1 mem1 loc from to rsv2 mem2)
        (INHABITED: inhabited mem1):
    <<INHABITED: inhabited mem2>>.
  Proof.
    inv RESERVE. eauto using add_inhabited.
  Qed.

  Lemma cancel_inhabited
        rsv1 mem1 loc from to rsv2 mem2
        (CANCEL: cancel rsv1 mem1 loc from to rsv2 mem2)
        (INHABITED: inhabited mem1):
    <<INHABITED: inhabited mem2>>.
  Proof.
    inv CANCEL. eauto using remove_inhabited.
  Qed.


  (* lemmas on future *)

  Lemma future_get1
        loc from to val released na mem1 mem2
        (FUTURE: future mem1 mem2)
        (GET: get loc to mem1 = Some (from, Message.message val released na)):
    <<GET: get loc to mem2 = Some (from, Message.message val released na)>>.
  Proof.
    revert from val released na GET.
    induction FUTURE; eauto. i.
    inv H; eauto using add_get1.
    apply IHFUTURE. erewrite remove_o; eauto.
    condtac; ss. des. subst.
    exploit remove_get0; try exact REMOVE. i. des. congr.
  Qed.

  Lemma future_inhabited
        mem1 mem2
        (FUTURE: future mem1 mem2)
        (INHABITED: inhabited mem1):
    inhabited mem2.
  Proof.
    revert INHABITED.
    induction FUTURE; eauto.
    i. apply IHFUTURE. inv H.
    - eapply add_inhabited; eauto.
    - eapply remove_inhabited; eauto.
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

  Lemma remove_closed_timemap
        times
        mem1 loc from to mem2
        (REMOVE: remove mem1 loc from to Message.reserve mem2)
        (CLOSED: closed_timemap times mem1):
    closed_timemap times mem2.
  Proof.
    ii. erewrite remove_o; eauto. condtac; ss.
    des. subst. exfalso.
    specialize (CLOSED loc). des.
    exploit remove_get0; eauto. i. des. congr.
  Qed.

  Lemma remove_closed_view
        view
        mem1 loc from to mem2
        (REMOVE: remove mem1 loc from to Message.reserve mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv CLOSED. econs; eauto.
    - eapply remove_closed_timemap; eauto.
    - eapply remove_closed_timemap; eauto.
  Qed.

  Lemma remove_closed_opt_view
        view
        mem1 loc from to mem2
        (REMOVE: remove mem1 loc from to Message.reserve mem2)
        (CLOSED: closed_opt_view view mem1):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; econs. eapply remove_closed_view; eauto.
  Qed.

  Lemma remove_closed_message
        msg'
        mem1 loc from to mem2
        (REMOVE: remove mem1 loc from to Message.reserve mem2)
        (CLOSED: closed_message msg' mem1):
    closed_message msg' mem2.
  Proof.
    destruct msg'; ss. inv CLOSED. econs.
    eapply remove_closed_opt_view; eauto.
  Qed.

  Lemma remove_closed
        mem1 loc from to mem2
        (REMOVE: remove mem1 loc from to Message.reserve mem2)
        (CLOSED: closed mem1):
    closed mem2.
  Proof.
    inv CLOSED. econs.
    - i. revert MSG. erewrite remove_o; eauto. condtac; ss.
      guardH o. i. exploit CLOSED0; eauto. i. des. splits; auto.
      eapply remove_closed_message; eauto.
    - eapply remove_inhabited; eauto.
  Qed.

  Lemma future_closed_timemap
        times mem1 mem2
        (FUTURE: future mem1 mem2)
        (CLOSED: closed_timemap times mem1):
    closed_timemap times mem2.
  Proof.
    revert CLOSED. induction FUTURE; auto. i.
    apply IHFUTURE. inv H.
    - eapply add_closed_timemap; eauto.
    - eapply remove_closed_timemap; eauto.
  Qed.

  Lemma future_closed_view
        view mem1 mem2
        (FUTURE: future mem1 mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv CLOSED. econs; eauto using future_closed_timemap.
  Qed.

  Lemma future_closed_opt_view
        view mem1 mem2
        (FUTURE: future mem1 mem2)
        (CLOSED: closed_opt_view view mem1):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; eauto using future_closed_view.
  Qed.

  Lemma future_closed_message
        msg mem1 mem2
        (FUTURE: future mem1 mem2)
        (CLOSED: closed_message msg mem1):
    closed_message msg mem2.
  Proof.
    inv CLOSED; eauto using future_closed_opt_view.
  Qed.

  Lemma future_closed
        mem1 mem2
        (FUTURE: future mem1 mem2)
        (CLOSED: closed mem1):
    closed mem2.
  Proof.
    revert CLOSED. induction FUTURE; auto. i.
    apply IHFUTURE. inv H.
    - eapply add_closed; eauto.
    - eapply remove_closed; eauto.
  Qed.

  Lemma singleton_closed_timemap
        loc from to val released na mem
        (GET: get loc to mem = Some (from, Message.message val released na))
        (INHABITED: inhabited mem):
    closed_timemap (TimeMap.singleton loc to) mem.
  Proof.
    unfold TimeMap.singleton, LocFun.add, LocFun.find. ii. condtac.
    - subst. eauto.
    - apply closed_timemap_bot. auto.
  Qed.

  Lemma singleton_ur_closed_view
        loc from to val released na mem
        (GET: get loc to mem = Some (from, Message.message val released na))
        (INHABITED: inhabited mem):
    closed_view (View.singleton_ur loc to) mem.
  Proof.
    econs; s.
    - eapply singleton_closed_timemap; eauto.
    - eapply singleton_closed_timemap; eauto.
  Qed.

  Lemma singleton_rw_closed_view
        loc from to val released na mem
        (GET: get loc to mem = Some (from, Message.message val released na))
        (INHABITED: inhabited mem):
    closed_view (View.singleton_rw loc to) mem.
  Proof.
    econs; s.
    - apply closed_timemap_bot. auto.
    - eapply singleton_closed_timemap; eauto.
  Qed.

  Lemma singleton_ur_if_closed_view
        cond loc from to val released na mem
        (GET: get loc to mem = Some (from, Message.message val released na))
        (INHABITED: inhabited mem):
    closed_view (View.singleton_ur_if cond loc to) mem.
  Proof.
    destruct cond; ss.
    - eapply singleton_ur_closed_view; eauto.
    - eapply singleton_rw_closed_view; eauto.
  Qed.


  (* finite *)

  Definition finite (mem:t): Prop :=
    exists dom,
    forall loc from to msg (GET: get loc to mem = Some (from, msg)),
      List.In (loc, to) dom.

  Lemma bot_finite: finite bot.
  Proof.
    exists []. ii. rewrite bot_get in *. congr.
  Qed.

  Lemma add_finite
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (FINITE: finite mem1):
    finite mem2.
  Proof.
    unfold finite in *. des. exists ((loc, to) :: dom). i.
    revert GET. erewrite add_o; eauto. condtac; ss; eauto.
    i. des. inv GET. auto.
  Qed.

  Lemma remove_finite
        mem1 loc from to msg mem2
        (REMOVE: remove mem1 loc from to msg mem2)
        (FINITE: finite mem1):
    finite mem2.
  Proof.
    unfold finite in *. des. exists dom. i.
    revert GET. erewrite remove_o; eauto. condtac; ss; eauto.
  Qed.


  (* future *)

  Lemma add_future
        rsv
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED1: closed mem1)
        (LE: le rsv mem1)
        (MSG_CLOSED: closed_message msg mem2)
        (MSG_TS: message_to msg loc to):
    <<CLOSED2: closed mem2>> /\
    <<LE2: le rsv mem2>> /\
    <<FUTURE: future mem1 mem2>> /\
    <<MSG_WF: Message.wf msg>>.
  Proof.
    splits; eauto.
    - eapply add_closed; eauto.
    - etrans; eauto. eapply add_le; eauto.
    - inv ADD. inv ADD0. ss.
  Qed.

  Lemma reserve_future
        rsv1 mem1 loc from to rsv2 mem2
        (RESERVE: reserve rsv1 mem1 loc from to rsv2 mem2)
        (CLOSED1: closed mem1)
        (LE: le rsv1 mem1)
        (FINITE: finite rsv1)
        (ONLY: reserve_only rsv1):
    <<CLOSED2: closed mem2>> /\
    <<LE2: le rsv2 mem2>> /\
    <<FINITE2: finite rsv2>> /\
    <<ONLY2: reserve_only rsv2>> /\
    <<FUTURE: future mem1 mem2>>.
  Proof.
    inv RESERVE. splits; eauto.
    - eapply add_closed; eauto.
    - ii. erewrite add_o; eauto.
      revert LHS. erewrite add_o; try exact RSV.
      condtac; ss; eauto.
    - eapply add_finite; eauto.
    - eapply add_reserve_only; eauto.
  Qed.

  Lemma cancel_future
        rsv1 mem1 loc from to rsv2 mem2
        (CANCEL: cancel rsv1 mem1 loc from to rsv2 mem2)
        (CLOSED1: closed mem1)
        (LE: le rsv1 mem1)
        (FINITE: finite rsv1)
        (ONLY: reserve_only rsv1):
    <<CLOSED2: closed mem2>> /\
    <<LE2: le rsv2 mem2>> /\
    <<FINITE2: finite rsv2>> /\
    <<ONLY2: reserve_only rsv2>> /\
    <<FUTURE: future mem1 mem2>>.
  Proof.
    inv CANCEL. splits; eauto.
    - eapply remove_closed; eauto.
    - ii. erewrite remove_o; eauto.
      revert LHS. erewrite remove_o; try exact RSV.
      condtac; ss; eauto.
    - eapply remove_finite; eauto.
    - eapply remove_reserve_only; eauto.
  Qed.

  Lemma add_disjoint
        mem1 loc from to msg mem2 ctx
        (ADD: add mem1 loc from to msg mem2)
        (LE_CTX: le ctx mem1):
    <<LE_CTX2: le ctx mem2>>.
  Proof.
    ii. exploit LE_CTX; eauto. i.
    erewrite add_o; eauto.
    condtac; ss; eauto. des. subst.
    exploit add_get0; eauto. i. des. congr.
  Qed.

  Lemma reserve_disjoint
        rsv1 mem1 loc from to rsv2 mem2 ctx
        (RESERVE: reserve rsv1 mem1 loc from to rsv2 mem2)
        (DISJOINT: disjoint rsv1 ctx)
        (LE_CTX: le ctx mem1):
    <<DISJOINT2: disjoint rsv2 ctx>> /\
    <<LE_CTX2: le ctx mem2>>.
  Proof.
    inv RESERVE. splits.
    - inv DISJOINT. econs. i.
      revert GET1. erewrite add_o; eauto.
      condtac; ss; eauto. i. des. inv GET1. splits.
      + inv MEM. inv ADD. eauto.
      + ii. inv H. inv MEM. inv ADD. timetac.
    - ii. erewrite add_o; eauto.
      condtac; ss; eauto. des. subst.
      exploit LE_CTX; eauto. i.
      exploit add_get0; try exact MEM. i. des. congr.
  Qed.

  Lemma cancel_disjoint
        rsv1 mem1 loc from to rsv2 mem2 ctx
        (CANCEL: cancel rsv1 mem1 loc from to rsv2 mem2)
        (DISJOINT: disjoint rsv1 ctx)
        (LE_CTX: le ctx mem1):
    <<DISJOINT2: disjoint rsv2 ctx>> /\
    <<LE_CTX2: le ctx mem2>>.
  Proof.
    inv CANCEL. splits.
    - inv DISJOINT. econs. i.
      revert GET1. erewrite remove_o; eauto.
      condtac; ss; eauto.
    - ii. erewrite remove_o; eauto.
      condtac; ss; eauto. des. subst.
      exploit LE_CTX; eauto. i.
      exploit remove_get0; try exact RSV. i. des.
      exploit disjoint_get; try exact DISJOINT; eauto. ss.
  Qed.


  (* messages_le *)

  Definition messages_le (lhs rhs: t): Prop :=
    forall loc from to val released na
      (LHS: get loc to lhs = Some (from, Message.message val released na)),
      get loc to rhs = Some (from, Message.message val released na).

  Global Program Instance messages_le_PreOrder: PreOrder messages_le.
  Next Obligation. ii. auto. Qed.
  Next Obligation. ii. auto. Qed.

  Lemma le_messages_le
        mem1 mem2
        (LE: le mem1 mem2):
    messages_le mem1 mem2.
  Proof.
    ii. eauto.
  Qed.

  Lemma add_messages_le
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2):
    messages_le mem1 mem2.
  Proof.
    ii. erewrite add_o; eauto.
    condtac; ss. des. subst.
    exploit add_get0; eauto. i. des. congr.
  Qed.

  Lemma remove_messages_le
        mem1 loc from to mem2
        (REMOVE: remove mem1 loc from to Message.reserve mem2):
    messages_le mem1 mem2.
  Proof.
    ii. erewrite remove_o; eauto.
    condtac; ss. des. subst.
    exploit remove_get0; eauto. i. des. congr.
  Qed.

  Lemma reserve_messages_le
        rsv1 mem1 loc from to rsv2 mem2
        (RESERVE: reserve rsv1 mem1 loc from to rsv2 mem2):
    messages_le mem1 mem2.
  Proof.
    inv RESERVE. eauto using add_messages_le.
  Qed.

  Lemma cancel_messages_le
        rsv1 mem1 loc from to rsv2 mem2
        (CANCEL: cancel rsv1 mem1 loc from to rsv2 mem2):
    messages_le mem1 mem2.
  Proof.
    inv CANCEL. eauto using remove_messages_le.
  Qed.

  Lemma messages_le_closed_timemap
        times mem1 mem2
        (LE: messages_le mem1 mem2)
        (CLOSED: closed_timemap times mem1):
    closed_timemap times mem2.
  Proof.
    ii. specialize (CLOSED loc). des.
    exploit LE; eauto.
  Qed.

  Lemma messages_le_closed_view
        view mem1 mem2
        (LE: messages_le mem1 mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv CLOSED. econs; eauto using messages_le_closed_timemap.
  Qed.

  Lemma messages_le_closed_opt_view
        view mem1 mem2
        (LE: messages_le mem1 mem2)
        (CLOSED: closed_opt_view view mem1):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; econs. eapply messages_le_closed_view; eauto.
  Qed.

  Lemma messages_le_closed_message
        msg mem1 mem2
        (LE: messages_le mem1 mem2)
        (CLOSED: closed_message msg mem1):
    closed_message msg mem2.
  Proof.
    inv CLOSED; econs. eapply messages_le_closed_opt_view; eauto.
  Qed.

  Lemma future_messages_le
        mem1 mem2
        (FUTURE: future mem1 mem2):
    messages_le mem1 mem2.
  Proof.
    induction FUTURE; try refl.
    etrans; eauto. inv H.
    - eapply add_messages_le; eauto.
    - eapply remove_messages_le; eauto.
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

  Definition max_view (mem:t): View.t :=
    View.mk (max_timemap mem) (max_timemap mem).

  Lemma max_view_wf mem: View.wf (max_view mem).
  Proof.
    econs. refl.
  Qed.

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

  Lemma add_exists_max
        mem1 loc to msg
        (TO: Time.lt (max_ts loc mem1) to)
        (MSG_WF: Message.wf msg):
    exists from,
      (<<FROM: Time.lt (max_ts loc mem1) from>>) /\
      exists mem2,
        (<<ADD: add mem1 loc from to msg mem2>>).
  Proof.
    exploit Time.middle_spec; try exact TO. i. des.
    eexists. splits; try exact x0.
    eapply add_exists; eauto.
    ii. inv LHS. inv RHS. ss.
    exploit max_ts_spec; try exact GET2. i. des.
    rewrite MAX in TO1.
    rewrite FROM in x0.
    timetac.
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

  Lemma remove_exists
        mem1 loc from to msg
        (GET: get loc to mem1 = Some (from, msg)):
    exists mem2, remove mem1 loc from to msg mem2.
  Proof.
    exploit Cell.remove_exists; eauto. i. des.
    eexists. econs; eauto.
  Qed.


  (* maximal & minimal messages satisfying a property *)

  Lemma max_exists P loc mem:
    (<<NONE: forall from to msg
                    (GET: get loc to mem = Some (from, msg)),
        ~ P to>>) \/
    exists from_max to_max msg_max,
      (<<GET: get loc to_max mem = Some (from_max, msg_max)>>) /\
      (<<SAT: P to_max>>) /\
      (<<MAX: forall from to msg
                     (GET: get loc to mem = Some (from, msg))
                     (SAT: P to),
          Time.le to to_max>>).
  Proof.
    specialize (Cell.max_exists P (mem loc)). i. des; eauto.
    right. esplits; eauto.
  Qed.

  Lemma min_exists P loc mem:
    (<<NONE: forall from to msg
                    (GET: get loc to mem = Some (from, msg)),
        ~ P to>>) \/
    exists from_min to_min msg_min,
      (<<GET: get loc to_min mem = Some (from_min, msg_min)>>) /\
      (<<SAT: P to_min>>) /\
      (<<MIN: forall from to msg
                     (GET: get loc to mem = Some (from, msg))
                     (SAT: P to),
          Time.le to_min to>>).
  Proof.
    specialize (Cell.min_exists P (mem loc)). i. des; eauto.
    right. esplits; eauto.
  Qed.


  (* next & previous message *)

  Definition empty (mem: t) (loc: Loc.t) (ts1 ts2: Time.t): Prop :=
    forall ts (TS1: Time.lt ts1 ts) (TS2: Time.lt ts ts2),
      get loc ts mem = None.

  Lemma next_exists
        ts mem loc f t m
        (GET: get loc t mem = Some (f, m))
        (TS: Time.lt ts (max_ts loc mem)):
    exists from to msg,
      get loc to mem = Some (from, msg) /\
      Time.lt ts to /\
      empty mem loc ts to.
  Proof.
    exploit Cell.next_exists; eauto.
  Qed.

  Lemma prev_exists
        ts mem loc f t m
        (GET: get loc t mem = Some (f, m))
        (TS: Time.lt t ts):
    exists from to msg,
      get loc to mem = Some (from, msg) /\
      Time.lt to ts /\
      empty mem loc to ts.
  Proof.
    exploit Cell.prev_exists; eauto.
  Qed.


  (* adjacent *)

  Variant adjacent (loc: Loc.t) (from1 to1 from2 to2: Time.t) (mem: t): Prop :=
  | adjacent_intro
      m1 m2
      (GET1: get loc to1 mem = Some (from1, m1))
      (GET2: get loc to2 mem = Some (from2, m2))
      (TS: Time.lt to1 to2)
      (EMPTY: forall ts (TS1: Time.lt to1 ts) (TS2: Time.le ts from2),
          get loc ts mem = None)
  .

  Lemma adjacent_ts
        loc from1 to1 from2 to2 mem
        (ADJ: adjacent loc from1 to1 from2 to2 mem):
    Time.le to1 from2.
  Proof.
    destruct (Time.le_lt_dec to1 from2); auto.
    exfalso. inv ADJ.
    exploit get_ts; try exact GET1. i. des.
    { subst. inv l. }
    exploit get_ts; try exact GET2. i. des.
    { subst. inv TS. }
    exploit get_disjoint; [exact GET1|exact GET2|..]. i. des.
    { subst. timetac. }
    apply (x2 to1); econs; ss.
    - refl.
    - econs. auto.
  Qed.

  Lemma adjacent_inj
        loc to mem
        from1 from2 from3 to3 from4 to4
        (ADJ1: adjacent loc from1 to from3 to3 mem)
        (ADJ2: adjacent loc from2 to from4 to4 mem):
    from1 = from2 /\ from3 = from4 /\ to3 = to4.
  Proof.
    inv ADJ1. inv ADJ2.
    rewrite GET1 in GET0. inv GET0.
    destruct (Time.le_lt_dec to3 to4); cycle 1.
    { exfalso.
      destruct (Time.le_lt_dec to4 from3).
      - exploit EMPTY; try exact l0; eauto. i. congr.
      - exploit get_ts; try exact GET2. i. des.
        { subst. inv l. }
        exploit get_ts; try exact GET3. i. des.
        { subst. inv l0. }
        exploit get_disjoint; [exact GET2|exact GET3|..]. i. des.
        { subst. timetac. }
        apply (x2 to4); econs; ss.
        + econs. ss.
        + refl. }
    inv l.
    { exfalso.
      destruct (Time.le_lt_dec to3 from4).
      - exploit EMPTY0; try exact l; eauto. i. congr.
      - exploit get_ts; try exact GET2. i. des.
        { subst. inv l. }
        exploit get_ts; try exact GET3. i. des.
        { subst. inv H. }
        exploit get_disjoint; [exact GET2|exact GET3|..]. i. des.
        { subst. timetac. }
        apply (x2 to3); econs; ss.
        + refl.
        + econs. ss. }
    inv H. rewrite GET2 in GET3. inv GET3.
    splits; auto.
  Qed.

  Lemma adjacent_exists
        loc from1 to1 msg mem
        (GET: get loc to1 mem = Some (from1, msg))
        (TO: Time.lt to1 (max_ts loc mem)):
    exists from2 to2,
      adjacent loc from1 to1 from2 to2 mem.
  Proof.
    exploit next_exists; eauto. i. des.
    esplits. econs; try exact x0; eauto. i.
    eapply x2; eauto.
    exploit get_ts; try exact x0. i. des.
    - subst. inv x1.
    - eapply TimeFacts.le_lt_lt; eauto.
  Qed.


  (* cap *)

  Variant cap (mem1 mem2: t): Prop :=
  | cap_intro
      (SOUND: le mem1 mem2)
      (MIDDLE: forall loc from1 to1 from2 to2
                 (ADJ: adjacent loc from1 to1 from2 to2 mem1)
                 (TO: Time.lt to1 from2),
          get loc from2 mem2 = Some (to1, Message.reserve))
      (BACK: forall loc from msg
               (GET: get loc (max_ts loc mem1) mem1 = Some (from, msg)),
          get loc (Time.incr (max_ts loc mem1)) mem2 =
          Some (max_ts loc mem1, Message.reserve))
      (COMPLETE: forall loc from to msg
                   (GET1: get loc to mem1 = None)
                   (GET2: get loc to mem2 = Some (from, msg)),
          (exists f m, get loc from mem1 = Some (f, m)))
  .
  #[global] Hint Constructors cap: core.

  Lemma cap_inv
        mem1 mem2
        loc from to msg
        (CAP: cap mem1 mem2)
        (GET: get loc to mem2 = Some (from, msg)):
    get loc to mem1 = Some (from, msg) \/
    (get loc to mem1 = None /\
     exists from1 to2,
        adjacent loc from1 from to to2 mem1 /\
        Time.lt from to /\
        msg = Message.reserve) \/
    (get loc to mem1 = None /\
     from = max_ts loc mem1 /\
     to = Time.incr from /\
     msg = Message.reserve /\
     exists f m,
       get loc from mem1 = Some (f, m)).
  Proof.
    inv CAP. move GET at bottom.
    destruct (get loc to mem1) as [[]|] eqn:GET1.
    { exploit SOUND; eauto. intros x.
      rewrite GET in x. inv x. auto. }
    right. exploit COMPLETE; eauto. intros x. des.
    exploit max_ts_spec; eauto. intros x0. des. inv MAX.
    - left.
      exploit adjacent_exists; try eapply H; eauto. intros x1. des.
      assert (LT: Time.lt from from2).
      { clear MIDDLE BACK COMPLETE GET0 H.
        inv x1. rewrite GET0 in x. inv x.
        exploit get_ts; try exact GET2. i. des.
        { subst. inv TS. }
        destruct (Time.le_lt_dec from2 from); auto.
        inv l.
        - exfalso.
          exploit get_ts; try exact GET0. i. des.
          { subst. inv H. }
          exploit get_disjoint; [exact GET0|exact GET2|..]. i. des.
          { subst. timetac. }
          apply (x2 from); econs; ss.
          + refl.
          + econs. auto.
        - exfalso. inv H.
          exploit SOUND; try exact GET2. intros x.
          exploit get_ts; try exact GET. i. des.
          { subst. rewrite GET1 in GET0. inv GET0. }
          exploit get_disjoint; [exact GET|exact x|..]. i. des.
          { subst. rewrite GET1 in GET2. inv GET2. }
          destruct (Time.le_lt_dec to to2).
          + apply (x3 to); econs; ss. refl.
          + apply (x3 to2); econs; ss.
            * econs. auto.
            * refl.
      }
      exploit MIDDLE; try eapply x1; eauto. intros x0.
      destruct (Time.eq_dec to from2).
      + subst. rewrite GET in x0. inv x0. esplits; eauto.
      + exfalso. inv x1.
        exploit get_ts; try exact GET. i. des.
        { subst. rewrite GET1 in x. inv x. }
        exploit get_ts; try exact x0. i. des.
        { subst. exploit SOUND; try exact GET3. intros x1.
          exploit get_disjoint; [exact GET|exact x1|..]. i. des.
          { subst. rewrite GET1 in GET3. inv GET3. }
          destruct (Time.le_lt_dec to to2).
          - apply (x4 to); econs; ss. refl.
          - apply (x4 to2); econs; ss.
            + econs. auto.
            + refl.
        }
        exploit get_disjoint; [exact GET|exact x0|..]. i. des; try congr.
        destruct (Time.le_lt_dec to from2).
        * apply (x4 to); econs; ss. refl.
        * apply (x4 from2); econs; ss.
          { econs. auto. }
          { refl. }
    - right. inv H. do 2 (split; auto).
      rewrite GET0 in x. inv x.
      specialize (BACK loc).
      exploit get_ts; try exact GET. i. des; try congr.
      exploit BACK; eauto. i.
      exploit get_disjoint; [exact GET|exact x1|..]. i. des.
      { subst. esplits; eauto. }
      exfalso.
      destruct (Time.le_lt_dec to (Time.incr (max_ts loc mem1))).
      + apply (x2 to); econs; ss. refl.
      + apply (x2 (Time.incr (max_ts loc mem1))); econs; s;
          eauto using Time.incr_spec; try refl.
        econs. ss.
  Qed.

  Lemma cap_closed_timemap
        mem1 mem2 tm
        (CAP: cap mem1 mem2)
        (CLOSED: closed_timemap tm mem1):
    closed_timemap tm mem2.
  Proof.
    inv CAP. ii.
    specialize (CLOSED loc). des.
    exploit SOUND; eauto.
  Qed.

  Lemma cap_closed_view
        mem1 mem2 view
        (CAP: cap mem1 mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv CLOSED.
    econs; eauto using cap_closed_timemap.
  Qed.

  Lemma cap_closed_opt_view
        mem1 mem2 view
        (CAP: cap mem1 mem2)
        (CLOSED: closed_opt_view view mem1):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; eauto using cap_closed_view.
  Qed.

  Lemma cap_closed_message
        mem1 mem2 msg
        (CAP: cap mem1 mem2)
        (CLOSED: closed_message msg mem1):
    closed_message msg mem2.
  Proof.
    inv CLOSED; eauto using cap_closed_opt_view.
  Qed.

  Lemma cap_messages_le
        mem1 mem2
        (CAP: cap mem1 mem2):
    messages_le mem1 mem2.
  Proof.
    inv CAP. ii. eauto.
  Qed.

  Lemma cap_closed
        mem1 mem2
        (CAP: cap mem1 mem2)
        (CLOSED: closed mem1):
    closed mem2.
  Proof.
    inv CLOSED. econs; ii.
    - exploit cap_inv; eauto. i. des; subst; try by splits; ss.
      exploit CLOSED0; eauto. i. des.
      splits; eauto using cap_closed_message.
    - inv CAP. eapply SOUND; eauto.
  Qed.

  Lemma cap_le
        mem1 mem2
        (CAP: cap mem1 mem2):
    le mem1 mem2.
  Proof.
    inv CAP. ii. eauto.
  Qed.

  Lemma cap_max_ts
        mem1 mem2
        (INHABITED: inhabited mem1)
        (CAP: cap mem1 mem2):
    forall loc, max_ts loc mem2 = Time.incr (max_ts loc mem1).
  Proof.
    i. dup CAP. inv CAP0.
    exploit (max_ts_spec loc); try apply INHABITED. i. des.
    exploit BACK; eauto. i.
    exploit max_ts_spec; try exact x0. i. des.
    apply TimeFacts.antisym; ss.
    destruct (Time.le_lt_dec (max_ts loc mem2) (Time.incr (max_ts loc mem1))); ss.
    specialize (Time.incr_spec (max_ts loc mem1)). i.
    exploit cap_inv; try exact GET0; eauto. i. des.
    - exploit max_ts_spec; try exact x1. i. des.
      exploit TimeFacts.lt_le_lt; try exact l; try exact MAX1. i.
      rewrite x2 in H. timetac.
    - inv x2. exploit get_ts; try exact GET2. i. des.
      { rewrite x2 in *. inv l. }
      exploit max_ts_spec; try exact GET2. i. des.
      exploit TimeFacts.lt_le_lt; try exact x2; try exact MAX1. i.
      rewrite x4 in l. rewrite l in H. timetac.
    - subst. rewrite x3 in *. timetac.
  Qed.

  Lemma cap_exists mem:
    exists mem_cap, <<CAP: cap mem mem_cap>>.
  Proof.
    cut (exists mem_cap,
            forall loc,
              (fun loc cell =>
                 Cell.cap (mem loc) cell) loc (mem_cap loc)).
    { i. des.
      exists mem_cap. econs; ii.
      - destruct (H loc). eauto.
      - destruct (H loc). inv ADJ.
        eapply MIDDLE; eauto. econs; eauto.
      - destruct (H loc). eauto.
      - destruct (H loc).
        exploit COMPLETE; eauto.
    }
    apply choice. i.
    apply Cell.cap_exists.
  Qed.

  Lemma cap_inj
        mem mem1 mem2
        (CAP1: cap mem mem1)
        (CAP2: cap mem mem2):
    mem1 = mem2.
  Proof.
    apply ext. i.
    destruct (get loc ts mem1) as [[from1 msg1]|] eqn:GET1.
    - inv CAP2. exploit cap_inv; try exact GET1; eauto. i. des.
      + exploit SOUND; eauto.
      + subst. exploit MIDDLE; eauto.
      + subst. exploit BACK; eauto.
    - destruct (get loc ts mem2) as [[from2 msg2]|] eqn:GET2; ss.
      inv CAP1. exploit cap_inv; try exact GET2; eauto. i. des.
      + exploit SOUND; eauto. i. congr.
      + subst. exploit MIDDLE; eauto. i. congr.
      + subst. exploit BACK; eauto. i. congr.
  Qed.

  Definition cap_of_aux (mem: t): { mem_cap: t | cap mem mem_cap }.
  Proof.
    apply constructive_indefinite_description.
    apply cap_exists.
  Qed.

  Definition cap_of (mem: t): t :=
    match cap_of_aux mem with
    | exist _ mem_cap _ => mem_cap
    end.

  Lemma cap_of_cap mem:
    cap mem (cap_of mem).
  Proof.
    unfold cap_of.
    destruct (cap_of_aux mem).
    ss.
  Qed.

  Definition na_added_latest (loc: Loc.t) (mem1: t) (mem2: t): Prop :=
    exists from2 ts2 val2 released2,
      (<<GET: get loc ts2 mem2 = Some (from2, Message.message val2 released2 true)>>) /\
        (<<LATEST: forall from1 ts1 val1 released1 na1
                          (GET0: get loc ts1 mem1 = Some (from1, Message.message val1 released1 na1)),
            Time.le ts1 ts2>>).

  Lemma na_added_latest_le loc mem0 mem1 mem2 mem3
        (LE0: messages_le mem0 mem1)
        (ADDED: na_added_latest loc mem1 mem2)
        (LE1: messages_le mem2 mem3)
    :
    na_added_latest loc mem0 mem3.
  Proof.
    unfold na_added_latest in *. des. esplits.
    { eapply LE1. eauto. }
    i. eapply LE0 in GET0. hexploit LATEST; eauto.
  Qed.
End Memory.
