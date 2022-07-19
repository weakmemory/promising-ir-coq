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
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import Cover.

Set Implicit Arguments.


Variant sim_memory (mem_src mem_tgt:Memory.t): Prop :=
| sim_memory_intro
    (COVER: forall loc ts, covered loc ts mem_src <-> covered loc ts mem_tgt)
    (MSG: forall loc from_tgt to msg_tgt
            (GET: Memory.get loc to mem_tgt = Some (from_tgt, msg_tgt)),
        exists from_src msg_src,
          <<GET: Memory.get loc to mem_src = Some (from_src, msg_src)>> /\
          <<MSG: Message.le msg_src msg_tgt>>)
.
#[export] Hint Constructors sim_memory: core.

Global Program Instance sim_memory_PreOrder: PreOrder sim_memory.
Next Obligation.
  econs; try refl. i. esplits; eauto. refl.
Qed.
Next Obligation.
  ii. inv H. inv H0. econs; try etrans; eauto. i.
  exploit MSG0; eauto. i. des.
  exploit MSG; eauto. i. des.
  esplits; eauto. etrans; eauto.
Qed.


Lemma sim_memory_get
      loc from_tgt to msg_tgt mem_src mem_tgt
      (SIM: sim_memory mem_src mem_tgt)
      (GET: Memory.get loc to mem_tgt = Some (from_tgt, msg_tgt)):
  exists from_src msg_src,
    <<GET: Memory.get loc to mem_src = Some (from_src, msg_src)>> /\
    <<MSG: Message.le msg_src msg_tgt>>.
Proof.
  eapply SIM. eauto.
Qed.

Lemma sim_memory_get_inv
      loc from_src to_src msg_src mem_src
      mem_tgt
      (INHABITED_SRC: Memory.inhabited mem_src)
      (INHABITED_TGT: Memory.inhabited mem_tgt)
      (SIM: sim_memory mem_src mem_tgt)
      (GET_SRC: Memory.get loc to_src mem_src = Some (from_src, msg_src)):
  exists from_tgt to_tgt msg_tgt,
    <<FROM: Time.le from_tgt from_src>> /\
    <<TO: Time.le to_src to_tgt>> /\
    <<GET_TGT: Memory.get loc to_tgt mem_tgt = Some (from_tgt, msg_tgt)>>.
Proof.
  destruct (Time.eq_dec to_src Time.bot).
  { subst. rewrite INHABITED_SRC in GET_SRC. inv GET_SRC.
    esplits; try refl. apply INHABITED_TGT.
  }
  dup SIM. inv SIM0. dup COVER. specialize (COVER0 loc to_src). des.
  exploit COVER0.
  { econs; eauto. econs; try refl.
    exploit Memory.get_ts; eauto. i. des; subst; timetac.
  }
  intros x. dup x. inv x0. esplits; eauto.
  - destruct (Time.le_lt_dec from from_src); ss.
    dup COVER. specialize (COVER2 loc from). des. exploit COVER2.
    { econs; eauto.
      exploit Memory.get_ts; try exact GET_SRC. i. des; ss.
      inv ITV. econs; eauto. econs. ss.
    }
    intros x0. inv x0.
    destruct (Time.eq_dec to0 from).
    + subst. exploit MSG; try exact GET0. i. des.
      exploit Memory.get_disjoint; [exact GET_SRC|exact GET1|..]. i. des.
      * subst. inv ITV. timetac.
      * exfalso. apply (x1 from).
        { inv ITV. econs; eauto. s. econs; eauto. }
        { econs; try refl. s.
          exploit Memory.get_ts; try exact GET1. i. des; ss.
          subst. inv ITV0. inv FROM. }
    + exploit Memory.get_disjoint; [exact GET|exact GET0|..]. i. des.
      * subst. inv ITV0. timetac.
      * exfalso. destruct (Time.le_lt_dec to to0).
        { apply (x1 to).
          - econs; try refl.
            exploit Memory.get_ts; try exact GET. i. des; ss.
            subst. inv ITV0. inv FROM.
          - econs; eauto. inv ITV0. ss.
            exploit Memory.get_ts; try exact GET. i. des; ss.
            + subst. inv l.
            + eapply TimeFacts.lt_le_lt; eauto. econs; eauto. }
        { apply (x1 to0).
          - inv ITV0. econs; ss.
            + inv TO; ss. inv H. congr.
            + econs. ss.
          - econs; try refl.
            exploit Memory.get_ts; try exact GET0. i. des; ss.
            subst. inv ITV0. ss. inv TO; inv H. inv FROM. }
  - inv ITV. ss.
Qed.

Lemma sim_memory_max_ts
      mem_src mem_tgt loc
      (SIM: sim_memory mem_src mem_tgt)
      (CLOSED_SRC: Memory.closed mem_src)
      (CLOSED_TGT: Memory.closed mem_tgt):
  Memory.max_ts loc mem_src = Memory.max_ts loc mem_tgt.
Proof.
  inv SIM. inv CLOSED_SRC. inv CLOSED_TGT.
  clear MSG CLOSED CLOSED0.
  apply TimeFacts.antisym.
  - specialize (COVER loc (Memory.max_ts loc mem_src)). des.
    exploit Memory.max_ts_spec; try eapply (INHABITED loc). i. des.
    exploit Memory.get_ts; eauto. i. des.
    { rewrite x1. apply Time.bot_spec. }
    exploit COVER.
    { econs; eauto. econs; eauto. refl. }
    intros x. inv x. exploit Memory.max_ts_spec; try exact GET0. i. des.
    inv ITV. ss. etrans; eauto.
  - specialize (COVER loc (Memory.max_ts loc mem_tgt)). des.
    exploit Memory.max_ts_spec; try eapply (INHABITED0 loc). i. des.
    exploit Memory.get_ts; eauto. i. des.
    { rewrite x1. apply Time.bot_spec. }
    exploit COVER0.
    { econs; eauto. econs; eauto. refl. }
    intros x. inv x. exploit Memory.max_ts_spec; try exact GET0. i. des.
    inv ITV. ss. etrans; eauto.
Qed.

Lemma sim_memory_max_timemap
      mem_src mem_tgt
      (SIM: sim_memory mem_src mem_tgt)
      (CLOSED_SRC: Memory.closed mem_src)
      (CLOSED_TGT: Memory.closed mem_tgt):
  Memory.max_timemap mem_src = Memory.max_timemap mem_tgt.
Proof.
  extensionality loc.
  eapply sim_memory_max_ts; eauto.
Qed.

Lemma sim_memory_add
      mem1_src mem1_tgt msg_src
      mem2_src mem2_tgt msg_tgt
      loc from to
      (MSG: Message.le msg_src msg_tgt)
      (SRC: Memory.add mem1_src loc from to msg_src mem2_src)
      (TGT: Memory.add mem1_tgt loc from to msg_tgt mem2_tgt)
      (SIM: sim_memory mem1_src mem1_tgt):
  sim_memory mem2_src mem2_tgt.
Proof.
  inv SIM. econs; i.
  - rewrite add_covered; [|eauto]. rewrite (@add_covered mem2_tgt); [|eauto].
    econs; i; des; (try by right).
    + left. eapply COVER. eauto.
    + left. eapply COVER. eauto.
  - revert GET. erewrite Memory.add_o; eauto. condtac; ss.
    + des. subst. i. inv GET. esplits; eauto.
      erewrite Memory.add_o; eauto. condtac; ss.
    + erewrite (@Memory.add_o mem2_src); eauto. condtac; ss. eauto.
Qed.

Lemma sim_memory_closed_timemap
      mem_src mem_tgt
      tm
      (SIM: sim_memory mem_src mem_tgt)
      (TGT: Memory.closed_timemap tm mem_tgt):
  Memory.closed_timemap tm mem_src.
Proof.
  ii. exploit TGT; eauto. i. des.
  exploit sim_memory_get; eauto. i. des.
  inv MSG. eauto.
Qed.

Lemma sim_memory_closed_view
      mem_src mem_tgt
      view
      (SIM: sim_memory mem_src mem_tgt)
      (TGT: Memory.closed_view view mem_tgt):
  Memory.closed_view view mem_src.
Proof.
  econs.
  - eapply sim_memory_closed_timemap; eauto. apply TGT.
  - eapply sim_memory_closed_timemap; eauto. apply TGT.
Qed.

Lemma sim_memory_closed_opt_view
      mem_src mem_tgt
      view
      (SIM: sim_memory mem_src mem_tgt)
      (TGT: Memory.closed_opt_view view mem_tgt):
  Memory.closed_opt_view view mem_src.
Proof.
  inv TGT; econs. eapply sim_memory_closed_view; eauto.
Qed.

Lemma sim_memory_closed_message
      mem_src mem_tgt
      msg
      (SIM: sim_memory mem_src mem_tgt)
      (TGT: Memory.closed_message msg mem_tgt):
  Memory.closed_message msg mem_src.
Proof.
  inv TGT; ss. econs. eapply sim_memory_closed_opt_view; eauto.
Qed.

Lemma sim_memory_max_opt_timemap
      mem_src mem_tgt
      rsv_src rsv_tgt
      (SIM: sim_memory mem_src mem_tgt)
      (RSV: rsv_src = rsv_tgt)
      (CLOSED_SRC: Memory.closed mem_src)
      (CLOSED_TGT: Memory.closed mem_tgt):
  Memory.max_opt_timemap rsv_src mem_src =
  Memory.max_opt_timemap rsv_tgt mem_tgt.
Proof.
  subst. extensionality x.
  unfold Memory.max_opt_timemap. condtac; ss. f_equal.
  apply sim_memory_max_ts; eauto.
Qed.
