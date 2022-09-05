Require Import RelationClasses.
Require Import ZArith.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Event.

Require Import Time.
Require Import View.

Set Implicit Arguments.


Module Message.
  Variant t := mk (val: Const.t) (released: option View.t) (na: bool).

  Definition elt: t := mk 0%Z None true.

  Variant wf: t -> Prop :=
  | wf_intro
      val released na
      (RELEASED: View.opt_wf released):
    wf (mk val released na)
  .
  #[global] Hint Constructors wf: core.

  Definition elt_wf: wf elt.
  Proof. ss. Qed.

  Variant le: t -> t -> Prop :=
  | le_intro
      val1 released1 na1
      val2 released2 na2
      (VAL: Const.le val2 val1)
      (RELEASED: View.opt_le released1 released2)
      (NA: implb na2 na1):
    le (mk val1 released1 na1) (mk val2 released2 na2)
  .
  #[global] Hint Constructors le: core.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. destruct x. econs; try refl. destruct na; ss.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; try by (etrans; eauto).
    destruct na1, na2, na3; ss.
  Qed.

  Definition is_released_none (msg: t): bool :=
    match msg with
    | mk _ None _ => true
    | _ => false
    end.
End Message.
#[export] Hint Constructors Message.wf: core.


Module Cell.
  Module Raw.
    Definition t := DOMap.t (DenseOrder.t * Message.t).

    Variant wf (cell:t): Prop :=
    | wf_intro
        (VOLUME: forall from to msg
                   (GET: DOMap.find to cell = Some (from, msg)),
            (from, to) = (Time.bot, Time.bot) \/ Time.lt from to)
        (WF: forall from to msg
               (GET: DOMap.find to cell = Some (from, msg)),
            Message.wf msg)
        (DISJOINT: forall to1 to2 from1 from2 msg1 msg2
                     (GET1: DOMap.find to1 cell = Some (from1, msg1))
                     (GET2: DOMap.find to2 cell = Some (from2, msg2))
                     (NEQ: to1 <> to2),
            Interval.disjoint (from1, to1) (from2, to2))
    .
    #[global] Hint Constructors wf: core.

    Definition bot: t := DOMap.empty _.

    Lemma bot_wf: wf bot.
    Proof.
      econs; i.
      - rewrite DOMap.gempty in GET. inv GET.
      - rewrite DOMap.gempty in GET. inv GET.
      - rewrite DOMap.gempty in GET1. inv GET1.
    Qed.

    Definition singleton (from to:Time.t) (msg:Message.t): t :=
      DOMap.singleton to (from, msg).

    Lemma singleton_wf
          from to msg
          (LT: Time.lt from to)
          (WF: Message.wf msg):
      wf (singleton from to msg).
    Proof.
      unfold singleton. econs; s; i.
      - apply DOMap.singleton_find_inv in GET. des. inv GET0. auto.
      - apply DOMap.singleton_find_inv in GET. des. inv GET0. auto.
      - apply DOMap.singleton_find_inv in GET1. des. inv GET0.
        apply DOMap.singleton_find_inv in GET2. des. inv GET0.
        congr.
    Qed.

    Definition init: t :=
      DOMap.singleton Time.bot (Time.bot, Message.elt).

    Lemma init_wf: wf init.
    Proof.
      unfold init. econs; s; i.
      - apply DOMap.singleton_find_inv in GET. des. inv GET0. auto.
      - apply DOMap.singleton_find_inv in GET. des. inv GET0.
        apply Message.elt_wf.
      - apply DOMap.singleton_find_inv in GET1. des. inv GET0.
        apply DOMap.singleton_find_inv in GET2. des. inv GET0.
        congr.
    Qed.

    Lemma find_mem_ub
          from to msg cell
          (WF: wf cell)
          (FIND: DOMap.find to cell = Some (from, msg)):
      (from, to) = (Time.bot, Time.bot) \/
      Interval.mem (from, to) to.
    Proof.
      inv WF. exploit VOLUME; eauto. i. des; auto.
      right. econs; eauto. refl.
    Qed.

    Variant add (cell1:t) (from to:Time.t) (msg:Message.t) (cell2:t): Prop :=
    | add_intro
        (DISJOINT: forall to2 from2 msg2
                          (GET2: DOMap.find to2 cell1 = Some (from2, msg2)),
            Interval.disjoint (from, to) (from2, to2))
        (TO: Time.lt from to)
        (MSG_WF: Message.wf msg)
        (CELL2: cell2 = DOMap.add to (from, msg) cell1):
        add cell1 from to msg cell2.
    #[global] Hint Constructors add: core.

    Lemma add_o
          cell2 cell1 from to msg
          t
          (ADD: add cell1 from to msg cell2):
      DOMap.find t cell2 =
      if Time.eq_dec t to
      then Some (from, msg)
      else DOMap.find t cell1.
    Proof.
      inv ADD. rewrite DOMap.gsspec.
      repeat condtac; auto; congr.
    Qed.

    Lemma add_wf
          cell1 from to msg cell2
          (ADD: add cell1 from to msg cell2)
          (CELL1: wf cell1):
      wf cell2.
    Proof.
      inv CELL1. econs; i.
      - revert GET. erewrite add_o; eauto. condtac; auto.
        + i. inv GET. inv ADD. auto.
        + i. eapply VOLUME; eauto.
      - revert GET. erewrite add_o; eauto. condtac; auto.
        + i. inv GET. inv ADD. auto.
        + i. eapply WF; eauto.
      - revert GET1 GET2.
        erewrite (add_o to1); eauto.
        erewrite (add_o to2); eauto.
        repeat condtac; s; i.
        + inv GET1. congr.
        + inv GET1. inv ADD. hexploit DISJOINT0; eauto.
        + inv GET2. inv ADD. symmetry. hexploit DISJOINT0; eauto.
        + eapply DISJOINT; eauto.
    Qed.
  End Raw.

  Structure t := mk {
    raw :> Raw.t;
    WF: Raw.wf raw;
  }.

  Definition get (ts:Time.t) (cell:t): option (Time.t * Message.t) := DOMap.find ts (raw cell).

  Lemma ext
        (lhs rhs:t)
        (EXT: forall ts, get ts lhs = get ts rhs):
    lhs = rhs.
  Proof.
    destruct lhs, rhs.
    assert (raw0 = raw1).
    { apply DOMap.eq_leibniz. ii. apply EXT. }
    subst raw1. f_equal. apply proof_irrelevance.
  Qed.

  Lemma get_ts
        to cell from msg
        (GET: get to cell = Some (from, msg)):
    (from = Time.bot /\ to = Time.bot) \/ Time.lt from to.
  Proof.
    destruct cell. unfold get in *. ss.
    inv WF0. exploit VOLUME; eauto. intros x. des.
    - inv x. auto.
    - generalize (Time.le_lteq from to). i. des. auto.
  Qed.

  Lemma get_disjoint
        f1 f2 t1 t2 msg1 msg2 cell
        (GET1: get t1 cell = Some (f1, msg1))
        (GET2: get t2 cell = Some (f2, msg2)):
    (t1 = t2 /\ f1 = f2 /\ msg1 = msg2) \/
    Interval.disjoint (f1, t1) (f2, t2).
  Proof.
    destruct (Time.eq_dec t1 t2).
    { subst. rewrite GET1 in GET2. inv GET2. auto. }
    unfold get in *. unfold Cell.get in *.
    destruct cell; ss. inv WF0.
    hexploit DISJOINT; [exact GET1|exact GET2|..]; eauto.
  Qed.

  Definition le (lhs rhs:t): Prop :=
    forall to from msg
      (LHS: get to lhs = Some (from, msg)),
      get to rhs = Some (from, msg).

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. ii. auto. Qed.
  Next Obligation. ii. eapply H0; eauto. Qed.

  Definition bot: t := mk Raw.bot_wf.

  Lemma bot_get ts: get ts bot = None.
  Proof. unfold get, bot, Raw.bot. s. apply DOMap.gempty. Qed.

  Lemma bot_le cell: le bot cell.
  Proof. ii. rewrite bot_get in LHS. congr. Qed.

  Lemma finite cell:
    exists dom,
    forall from to msg (GET: get to cell = Some (from, msg)),
      List.In to dom.
  Proof.
    exists (List.map (fun e => (fst e)) (DOMap.elements (Cell.raw cell))). i.
    exploit DOMap.elements_correct; eauto. i.
    eapply in_prod; eauto.
  Qed.

  Definition singleton
             (from to:Time.t) (msg:Message.t)
             (LT: Time.lt from to)
             (WF: Message.wf msg): t :=
    mk (Raw.singleton_wf LT WF).

  Lemma singleton_get
        from to msg t
        (LT: Time.lt from to)
        (WF: Message.wf msg):
    get t (singleton LT WF) =
    if Time.eq_dec t to
    then Some (from, msg)
    else None.
  Proof.
    unfold get, singleton, Raw.singleton. ss. condtac.
    - subst. rewrite DOMap.singleton_eq. auto.
    - rewrite DOMap.singleton_neq; auto.
  Qed.

  Definition init: t := mk Raw.init_wf.

  Lemma init_get t:
    get t init =
    if Time.eq_dec t Time.bot
    then Some (Time.bot, Message.elt)
    else None.
  Proof.
    unfold get, init, Raw.init. ss. condtac.
    - subst. rewrite DOMap.singleton_eq. auto.
    - rewrite DOMap.singleton_neq; auto.
  Qed.

  Definition add (cell1:t) (from to:Time.t) (msg: Message.t) (cell2:t): Prop :=
    Raw.add cell1 from to msg cell2.

  Lemma add_o
        cell2 cell1 from to msg
        t
        (ADD: add cell1 from to msg cell2):
    get t cell2 =
    if Time.eq_dec t to
    then Some (from, msg)
    else get t cell1.
  Proof. apply Raw.add_o. auto. Qed.

  Definition max_ts (cell:t): Time.t :=
    DOMap.max_key (raw cell).

  Lemma max_ts_spec
        ts from msg cell
        (GET: get ts cell = Some (from, msg)):
    <<GET: exists from msg, get (max_ts cell) cell = Some (from, msg)>> /\
    <<MAX: Time.le ts (max_ts cell)>>.
  Proof.
    unfold get in GET.
    generalize (DOMap.max_key_spec (Cell.raw cell)). i. des. splits; eauto.
    - destruct (DOMap.find
                  (DOMap.max_key (Cell.raw cell))
                  (Cell.raw cell)) as [[]|]eqn:X.
      + esplits; eauto.
      + exfalso. eapply FIND; eauto. rewrite GET. congr.
    - apply MAX. rewrite GET. auto. congr.
  Qed.

  Lemma add_exists
        cell1 from to msg
        (DISJOINT: forall to2 from2 msg2
                     (GET2: get to2 cell1 = Some (from2, msg2)),
            Interval.disjoint (from, to) (from2, to2))
        (TO1: Time.lt from to)
        (WF: Message.wf msg):
    exists cell2, add cell1 from to msg cell2.
  Proof.
    destruct cell1. eexists (mk _). econs; s; eauto.
    Unshelve.
    eapply Raw.add_wf; eauto.
  Qed.

  Lemma add_exists_max_ts
        cell1 to msg
        (TO: Time.lt (max_ts cell1) to)
        (WF: Message.wf msg):
    exists cell2, add cell1 (max_ts cell1) to msg cell2.
  Proof.
    apply add_exists; auto. i.
    exploit max_ts_spec; eauto. i. des.
    ii. inv LHS. inv RHS. ss.
    rewrite MAX in TO1. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
  Qed.

  Lemma add_exists_le
        cell1' cell1 from to msg cell2
        (LE: le cell1' cell1)
        (ADD: add cell1 from to msg cell2):
    exists cell2', add cell1' from to msg cell2'.
  Proof.
    inv ADD. apply add_exists; auto. i.
    eapply DISJOINT. eauto.
  Qed.


  (* Lemmas on add *)

  Lemma add_get0
        cell1 from1 to1 msg1 cell2
        (ADD: add cell1 from1 to1 msg1 cell2):
    <<GET: get to1 cell1 = None>> /\
    <<GET: get to1 cell2 = Some (from1, msg1)>>.
  Proof.
    inv ADD. unfold get. splits.
    - destruct (DOMap.find to1 (raw cell1)) as [[]|] eqn:X; auto.
      exfalso. exploit DISJOINT; eauto.
      + apply Interval.mem_ub. auto.
      + apply Interval.mem_ub.
        destruct (Cell.WF cell1). exploit VOLUME; eauto. intros x. des; ss.
        inv x. inv TO.
    - rewrite CELL2, DOMap.gsspec. condtac; ss.
  Qed.

  Lemma add_get1
        cell1 from to msg cell2
        f t m
        (ADD: add cell1 from to msg cell2)
        (GET1: get t cell1 = Some (f, m)):
    get t cell2 = Some (f, m).
  Proof.
    erewrite add_o; eauto. condtac; ss.
    des. subst. exploit add_get0; eauto. i. des. congr.
  Qed.

  Lemma add_inhabited
        cell1 cell2 from to msg
        (ADD: add cell1 from to msg cell2)
        (INHABITED: get Time.bot cell1 = Some (Time.bot, Message.elt)):
    <<INHABITED: get Time.bot cell2 = Some (Time.bot, Message.elt)>>.
  Proof.
    erewrite add_o; eauto. condtac; auto. subst.
    inv ADD. inv TO.
  Qed.

  Lemma add_max_ts
        cell1 to msg cell2
        (ADD: add cell1 (max_ts cell1) to msg cell2)
        (INHABITED: get Time.bot cell1 = Some (Time.bot, Message.elt)):
    max_ts cell2 = to.
  Proof.
    hexploit add_inhabited; eauto. i. des.
    exploit max_ts_spec; eauto. i. des.
    revert GET. erewrite add_o; eauto. condtac; auto. i.
    apply TimeFacts.antisym.
    - left. eapply TimeFacts.le_lt_lt.
      + eapply max_ts_spec. eauto.
      + inv ADD. auto.
    - eapply max_ts_spec. erewrite add_o; eauto. condtac; ss.
  Qed.

  Lemma get_opt_wf
        cell from to msg
        (GET: get to cell = Some (from, msg)):
    Message.wf msg.
  Proof.
    destruct cell. destruct WF0. eauto.
  Qed.


  (* next & previous greater timestamp *)

  Fixpoint next (t: Time.t) (l: list Time.t) (res: option Time.t): option Time.t :=
    match l with
    | [] => res
    | hd :: tl =>
      if (Time.le_lt_dec hd t)
      then next t tl res
      else
        match res with
        | Some res =>
          if (Time.le_lt_dec res hd)
          then next t tl (Some res)
          else next t tl (Some hd)
        | None => next t tl (Some hd)
        end
    end.

  Lemma next_le
        t tnext init l
        (NEXT: next t l (Some init) = Some tnext):
    Time.le tnext init.
  Proof.
    revert init NEXT. induction l; ss; i.
    - inv NEXT. refl.
    - revert NEXT. repeat (condtac; ss); i.
      + exploit IHl; try exact NEXT. i. auto.
      + exploit IHl; try exact NEXT. i. auto.
      + exploit IHl; try exact NEXT. i.
        econs. eapply TimeFacts.le_lt_lt; eauto.
  Qed.

  Lemma next_spec_Some_aux
        t tnext init l
        (NEXT: next t l init = Some tnext):
    (init = Some tnext /\
     forall ts (TS1: Time.lt t ts) (TS2: Time.lt ts tnext),
       ~ List.In ts l) \/
    (List.In tnext l /\
     Time.lt t tnext /\
     forall ts (TS1: Time.lt t ts) (TS2: Time.lt ts tnext),
       ~ List.In ts l).
  Proof.
    revert t tnext init NEXT. induction l; ss; i.
    { left. ss. }
    revert NEXT. condtac; ss; i.
    - exploit IHl; eauto. intros x. des.
      + subst. left. split; auto. ii. des.
        * subst. timetac.
        * eapply x0; eauto.
      + right. splits; eauto. ii. des.
        * subst. timetac.
        * eapply x1; eauto.
    - destruct init0.
      + revert NEXT. condtac; ss; i.
        * exploit IHl; eauto. intros x. des.
          { inv x. left. split; auto. ii. des.
            - subst. timetac.
            - eapply x0; eauto. }
          { right. splits; eauto. ii. des.
            - subst. exploit next_le; eauto. i.
              rewrite l1 in x3. timetac.
            - eapply x1; eauto. }
        * exploit IHl; eauto. intros x. des.
          { inv x. right. splits; eauto. ii. des.
            - subst. timetac.
            - eapply x0; eauto. }
          { right. splits; eauto. ii. des.
            - subst. exploit next_le; eauto. i. timetac.
            - eapply x1; eauto. }
      + right. exploit IHl; eauto. intros x. des.
        * inv x. esplits; eauto. ii. des.
          { subst. timetac. }
          { eapply x0; eauto. }
        * esplits; eauto. ii. des.
          { subst. exploit next_le; eauto. i. timetac. }
          { eapply x1; eauto. }
  Qed.

  Lemma next_spec_Some
        t tnext l
        (NEXT: next t l None = Some tnext):
    List.In tnext l /\
    Time.lt t tnext /\
    forall ts (TS1: Time.lt t ts) (TS2: Time.lt ts tnext),
      ~ List.In ts l.
  Proof.
    exploit next_spec_Some_aux; eauto. i.
    des; try congr; eauto.
  Qed.

  Lemma next_spec_None_aux
        t init l:
    next t l (Some init) <> None.
  Proof.
    revert t init. induction l; ss; i.
    repeat condtac; ss; eauto.
  Qed.

  Lemma next_spec_None
        t l
        (NEXT: next t l None = None):
    forall ts (IN: List.In ts l),
      Time.le ts t.
  Proof.
    revert t NEXT. induction l; ss; i. des.
    - subst. revert NEXT. condtac; ss; i.
      specialize (next_spec_None_aux t0 ts l). congr.
    - revert NEXT. condtac; ss; i.
      + exploit IHl; eauto.
      + specialize (next_spec_None_aux t0 a l). congr.
  Qed.

  Lemma next_exists
        cell f t m ts
        (INHABITED: get t cell = Some (f, m))
        (TS: Time.lt ts (max_ts cell)):
    exists from to msg,
      get to cell = Some (from, msg) /\
      Time.lt ts to /\
      forall ts' (TS1: Time.lt ts ts') (TS2: Time.lt ts' to),
        get ts' cell = None.
  Proof.
    destruct cell. unfold get in *. ss.
    destruct (next ts (List.map (fun x => fst x) (DOMap.elements raw0)) None) eqn:NEXT.
    - exploit next_spec_Some; eauto. i. des.
      exploit in_prod_inv; eauto. i. des. destruct b.
      exploit DOMap.elements_complete; eauto. i.
      esplits; try exact x4; eauto. i.
      destruct (DOMap.find ts' raw0) as [[]|] eqn:GET; ss.
      exploit DOMap.elements_correct; try exact GET. i.
      exploit in_prod; try exact x5. i.
      exploit x2; eauto. ss.
    - exploit (@max_ts_spec t f m (Cell.mk WF0)); ss. i. des.
      unfold get in *. ss.
      exploit DOMap.elements_correct; try exact GET. i.
      exploit in_prod; try exact x0. i.
      exploit next_spec_None; eauto. i. timetac.
  Qed.

  Fixpoint prev (t: Time.t) (l: list Time.t) (res: option Time.t): option Time.t :=
    match l with
    | [] => res
    | hd :: tl =>
      if (Time.le_lt_dec t hd)
      then prev t tl res
      else
        match res with
        | Some res =>
          if (Time.le_lt_dec hd res)
          then prev t tl (Some res)
          else prev t tl (Some hd)
        | None => prev t tl (Some hd)
        end
    end.

  Lemma prev_le
        t tprev init l
        (PREV: prev t l (Some init) = Some tprev):
    Time.le init tprev.
  Proof.
    revert init PREV. induction l; ss; i.
    - inv PREV. refl.
    - revert PREV. repeat (condtac; ss); i.
      + exploit IHl; try exact PREV. i. auto.
      + exploit IHl; try exact PREV. i. auto.
      + exploit IHl; try exact PREV. i.
        econs. eapply TimeFacts.lt_le_lt; eauto.
  Qed.

  Lemma prev_spec_Some_aux
        t tprev init l
        (PREV: prev t l init = Some tprev):
    (init = Some tprev /\
     forall ts (TS1: Time.lt tprev ts) (TS2: Time.lt ts t),
       ~ List.In ts l) \/
    (List.In tprev l /\
     Time.lt tprev t /\
     forall ts (TS1: Time.lt tprev ts) (TS2: Time.lt ts t),
       ~ List.In ts l).
  Proof.
    revert t tprev init PREV. induction l; ss; i.
    { left. ss. }
    revert PREV. condtac; ss; i.
    - exploit IHl; eauto. intros x. des.
      + subst. left. split; auto. ii. des.
        * subst. timetac.
        * eapply x0; eauto.
      + right. splits; eauto. ii. des.
        * subst. timetac.
        * eapply x1; eauto.
    - destruct init0.
      + revert PREV. condtac; ss; i.
        * exploit IHl; eauto. intros x. des.
          { inv x. left. split; auto. ii. des.
            - subst. timetac.
            - eapply x0; eauto. }
          { right. splits; eauto. ii. des.
            - subst. exploit prev_le; eauto. i.
              eapply Time.lt_strorder.
              eapply TimeFacts.le_lt_lt; try exact TS1.
              etrans; eauto.
            - eapply x1; eauto. }
        * exploit IHl; eauto. intros x. des.
          { inv x. right. splits; eauto. ii. des.
            - subst. timetac.
            - eapply x0; eauto. }
          { right. splits; eauto. ii. des.
            - subst. exploit prev_le; eauto. i. timetac.
            - eapply x1; eauto. }
      + right. exploit IHl; eauto. intros x. des.
        * inv x. esplits; eauto. ii. des.
          { subst. timetac. }
          { eapply x0; eauto. }
        * esplits; eauto. ii. des.
          { subst. exploit prev_le; eauto. i. timetac. }
          { eapply x1; eauto. }
  Qed.

  Lemma prev_spec_Some
        t tprev l
        (PREV: prev t l None = Some tprev):
    List.In tprev l /\
    Time.lt tprev t /\
    forall ts (TS1: Time.lt tprev ts) (TS2: Time.lt ts t),
      ~ List.In ts l.
  Proof.
    exploit prev_spec_Some_aux; eauto. i.
    des; try congr; eauto.
  Qed.

  Lemma prev_spec_None_aux
        t init l:
    prev t l (Some init) <> None.
  Proof.
    revert t init. induction l; ss; i.
    repeat condtac; ss; eauto.
  Qed.

  Lemma prev_spec_None
        t l
        (PREV: prev t l None = None):
    forall ts (IN: List.In ts l),
      Time.le t ts.
  Proof.
    revert t PREV. induction l; ss; i. des.
    - subst. revert PREV. condtac; ss; i.
      specialize (prev_spec_None_aux t0 ts l). congr.
    - revert PREV. condtac; ss; i.
      + exploit IHl; eauto.
      + specialize (prev_spec_None_aux t0 a l). congr.
  Qed.

  Lemma prev_exists
        cell f t m ts
        (INHABITED: get t cell = Some (f, m))
        (TS: Time.lt t ts):
    exists from to msg,
      get to cell = Some (from, msg) /\
      Time.lt to ts /\
      forall ts' (TS1: Time.lt to ts') (TS2: Time.lt ts' ts),
        get ts' cell = None.
  Proof.
    destruct cell. unfold get in *. ss.
    destruct (prev ts (List.map (fun x => fst x) (DOMap.elements raw0)) None) eqn:PREV.
    - exploit prev_spec_Some; eauto. i. des.
      exploit in_prod_inv; eauto. i. des. destruct b.
      exploit DOMap.elements_complete; eauto. i.
      esplits; try exact x4; eauto. i.
      destruct (DOMap.find ts' raw0) as [[]|] eqn:GET; ss.
      exploit DOMap.elements_correct; try exact GET. i.
      exploit in_prod; try exact x5. i.
      exploit x2; eauto. ss.
    - exploit DOMap.elements_correct; try exact INHABITED. i.
      exploit in_prod; try exact x0. i.
      exploit prev_spec_None; eauto. i. timetac.
  Qed.
End Cell.
