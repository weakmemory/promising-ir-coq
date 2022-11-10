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
    (RSV: forall loc from to,
        Memory.get loc to mem_src = Some (from, Message.reserve) <->
        Memory.get loc to mem_tgt = Some (from, Message.reserve))
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
  - erewrite (@Memory.add_o mem2_src); try exact SRC.
    erewrite (@Memory.add_o mem2_tgt); try exact TGT.
    condtac; ss. des. subst. split; i.
    + inv H. inv MSG. ss.
    + inv H. inv MSG. ss.
Qed.

Lemma sim_memory_add_exist
      mem1_src mem1_tgt msg_src
      mem2_tgt msg_tgt
      loc from to
      (MSG: Message.le msg_src msg_tgt)
      (MWF: Message.wf msg_src)
      (TGT: Memory.add mem1_tgt loc from to msg_tgt mem2_tgt)
      (SIM: sim_memory mem1_src mem1_tgt):
  exists mem2_src,
    (<<ADD: Memory.add mem1_src loc from to msg_src mem2_src>>) /\
      (<<SIM: sim_memory mem2_src mem2_tgt>>).
Proof.
  assert (exists mem2_src, <<SRC: Memory.add mem1_src loc from to msg_src mem2_src>>).
  { apply Memory.add_exists.
    { eapply covered_disjoint.
      { inv SIM. eapply COVER. }
      { inv TGT. inv ADD. eauto. }
    }
    { inv TGT. inv ADD. eauto. }
    { eauto. }
  }
  des. hexploit sim_memory_add; eauto.
Qed.

Lemma sim_memory_remove
      mem1_src mem1_tgt
      mem2_src mem2_tgt
      loc from to
      (SRC: Memory.remove mem1_src loc from to Message.reserve mem2_src)
      (TGT: Memory.remove mem1_tgt loc from to Message.reserve mem2_tgt)
      (SIM: sim_memory mem1_src mem1_tgt):
  sim_memory mem2_src mem2_tgt.
Proof.
  inv SIM. econs; i.
  - rewrite remove_covered; [|eauto]. rewrite (@remove_covered mem2_tgt); [|eauto].
    econs; i; des; (try by right).
    { splits; auto. eapply COVER; eauto. }
    { splits; auto. eapply COVER; eauto. }
    { splits; auto. eapply COVER; eauto. }
    { splits; auto. eapply COVER; eauto. }
  - hexploit MSG; eauto.
    { erewrite Memory.remove_o in GET; eauto. des_ifs; eauto. }
    i. des. esplits; eauto.
    erewrite Memory.remove_o in GET; eauto.
    erewrite Memory.remove_o; eauto. des_ifs. eauto.
  - erewrite (@Memory.remove_o mem2_src); try exact SRC.
    erewrite (@Memory.remove_o mem2_tgt); try exact TGT.
    condtac; ss.
Qed.

Lemma sim_memory_adjacent_src
      mem_src mem_tgt
      loc from1 to1 from2 to2
      (SIM: sim_memory mem_src mem_tgt)
      (CLOSED_SRC: Memory.closed mem_src)
      (CLOSED_TGT: Memory.closed mem_tgt)
      (ADJ: Memory.adjacent loc from1 to1 from2 to2 mem_src)
      (TS: Time.lt to1 from2):
  exists from1' to2',
    Memory.adjacent loc from1' to1 from2 to2' mem_tgt.
Proof.
  dup SIM. inv SIM0. inv ADJ. clear TS0.
  assert (GET1_TGT: exists from1' m1', Memory.get loc to1 mem_tgt = Some (from1', m1')).
  { exploit Memory.get_ts; try exact GET1. i. des.
    { subst. esplits. eapply CLOSED_TGT. }
    destruct (COVER loc to1). exploit H.
    { econs; try exact GET1. econs; eauto. refl. }
    intros x. inv x. inv ITV. ss. inv TO; cycle 1.
    { inv H1. esplits; eauto. }
    exfalso.
    destruct (Time.le_lt_dec to from2).
    { exploit MSG; eauto. i. des.
      exploit (EMPTY to); eauto. i. congr. }
    destruct (COVER loc from2). exploit H3.
    { econs; eauto. econs; ss.
      - etrans; eauto.
      - econs; ss.
    }
    intros x. inv x. inv ITV. ss. inv TO.
    - exploit Memory.get_ts; try exact GET2. i. des.
      { subst. inv FROM0. }
      exploit Memory.get_ts; try exact GET0. i. des.
      { subst. inv H4. }
      exploit Memory.get_disjoint; [exact GET2|exact GET0|..]. i. des.
      { timetac. }
      destruct (Time.le_lt_dec to2 to0).
      + apply (x3 to2); econs; ss; try refl.
        etrans; try exact FROM0. ss.
      + apply (x3 to0); econs; ss; try refl.
        econs. ss.
    - inv H4. exploit (EMPTY to0); eauto; try refl. i. congr.
  }
  assert (GET2_TGT: exists to2' m2', Memory.get loc to2' mem_tgt = Some (from2, m2')).
  { exploit Memory.get_ts; try exact GET2. i. des.
    { subst. inv TS. }
    exploit Memory.max_ts_spec; try exact GET2. i. des.
    clear from msg GET.
    erewrite sim_memory_max_ts in MAX; eauto.
    exploit TimeFacts.lt_le_lt; try exact x0; try exact MAX. i.
    exploit Memory.next_exists; try exact x1; try eapply CLOSED_TGT. i. des.
    destruct (TimeFacts.le_lt_dec from from2).
    - inv l; cycle 1.
      { inv H. esplits; eauto. }
      destruct (COVER loc from2). exploit H1.
      { econs; try exact x2. econs; ss. econs; ss. }
      intros x. inv x. inv ITV. ss. inv TO; cycle 1.
      { inv H2. exploit (EMPTY to0); eauto; try refl. i. congr. }
      exploit Memory.get_disjoint; [exact GET2|exact GET|..]. i. des.
      { subst. timetac. }
      exfalso.
      destruct (TimeFacts.le_lt_dec to2 to0).
      + apply (x5 to2); econs; ss; try refl.
        etrans; try exact FROM. ss.
      + apply (x5 to0); econs; ss; try refl.
        * econs. ss.
        * etrans; eauto.
    - destruct (TimeFacts.le_lt_dec to2 from).
      + destruct (COVER loc to2). exploit H.
        { econs; eauto. econs; ss. refl. }
        intros x. inv x. inv ITV. ss.
        exploit (x4 to0); eauto; try congr.
        { eapply TimeFacts.lt_le_lt; try exact TO; ss. }
        destruct (Time.le_lt_dec to to0); ss.
        exploit Memory.get_ts; try exact x2. i. des.
        { subst. inv x3. }
        exploit Memory.get_disjoint; [exact x2|exact GET|..]. i. des.
        { subst. timetac. }
        exfalso.
        apply (x6 to); econs; ss; try refl.
        etrans; try exact FROM.
        eapply TimeFacts.le_lt_lt; try exact x5. ss.
      + destruct (COVER loc from). exploit H.
        { econs; try exact GET2. econs; ss. econs. ss. }
        intros x. inv x. inv ITV. ss.
        destruct (TimeFacts.le_lt_dec to to0).
        * exploit Memory.get_ts; try exact x2. i. des.
          { subst. inv x3. }
          exploit Memory.get_ts; try exact GET. i. des.
          { subst. timetac. }
          exploit Memory.get_disjoint; [exact x2|exact GET|..]. i. des.
          { subst. timetac. }
          exfalso.
          apply (x7 to); econs; ss; try refl.
          eapply TimeFacts.lt_le_lt; try exact FROM. econs. ss.
        * exploit (x4 to0); ss; try congr.
          eapply TimeFacts.lt_le_lt; try exact TO; ss.
  }
  des. esplits. econs; eauto; i.
  { exploit Memory.get_ts; try exact GET2_TGT. i. des.
    - subst. inv TS.
    - etrans; eauto. }
  destruct (Memory.get loc ts mem_tgt) as [[]|] eqn:GET; ss.
  exfalso.
  exploit Memory.get_ts; try exact GET. i. des.
  { subst. inv TS1. }
  destruct (COVER loc ts). exploit H0.
  { econs; eauto. econs; ss. refl. }
  intros x. inv x. inv ITV. ss.
  destruct (TimeFacts.le_lt_dec to from2).
  { exploit (EMPTY to); try congr.
    eapply TimeFacts.lt_le_lt; try exact TS1. ss. }
  exploit Memory.get_ts; try exact GET2. i. des.
  { subst. inv TS. }
  exploit Memory.get_ts; try exact GET0. i. des.
  { subst. inv l. }
  exploit Memory.get_disjoint; [exact GET2|exact GET0|..]. i. des.
  { subst. timetac. }
  destruct (TimeFacts.le_lt_dec to2 to).
  - apply (x3 to2); econs; ss; try refl.
    etrans; try exact x1.
    eapply TimeFacts.lt_le_lt; try exact TS2. ss.
  - apply (x3 to); econs; ss; try refl. econs. ss.
Qed.

Lemma sim_memory_adjacent_tgt
      mem_src mem_tgt
      loc from1 to1 from2 to2
      (SIM: sim_memory mem_src mem_tgt)
      (CLOSED_SRC: Memory.closed mem_src)
      (CLOSED_TGT: Memory.closed mem_tgt)
      (ADJ: Memory.adjacent loc from1 to1 from2 to2 mem_tgt)
      (TS: Time.lt to1 from2):
  exists from1' to2',
    Memory.adjacent loc from1' to1 from2 to2' mem_src.
Proof.
  dup SIM. inv SIM0. inv ADJ. clear TS0.
  assert (GET1_SRC: exists from1' m1', Memory.get loc to1 mem_src = Some (from1', m1')).
  { exploit MSG; try exact GET1. i. des. eauto. }
  assert (GET2_SRC: exists to2' m2', Memory.get loc to2' mem_src = Some (from2, m2')).
  { exploit Memory.get_ts; try exact GET2. i. des.
    { subst. inv TS. }
    exploit Memory.max_ts_spec; try exact GET2. i. des.
    clear from msg GET.
    erewrite <- sim_memory_max_ts in MAX; eauto.
    exploit TimeFacts.lt_le_lt; try exact x0; try exact MAX. i.
    exploit Memory.next_exists; try exact x1; try eapply CLOSED_SRC. i. des.
    destruct (TimeFacts.le_lt_dec from from2).
    - inv l; cycle 1.
      { inv H. esplits; eauto. }
      destruct (COVER loc from2). exploit H0.
      { econs; try exact x2. econs; ss. econs; ss. }
      intros x. inv x. inv ITV. ss. inv TO; cycle 1.
      { inv H2. exploit (EMPTY to0); eauto; try refl. i. congr. }
      exploit Memory.get_disjoint; [exact GET2|exact GET|..]. i. des.
      { subst. timetac. }
      exfalso.
      destruct (TimeFacts.le_lt_dec to2 to0).
      + apply (x5 to2); econs; ss; try refl.
        etrans; try exact FROM. ss.
      + apply (x5 to0); econs; ss; try refl.
        * econs. ss.
        * etrans; eauto.
    - destruct (TimeFacts.le_lt_dec to2 from).
      + destruct (COVER loc to2). exploit H0.
        { econs; eauto. econs; ss. refl. }
        intros x. inv x. inv ITV. ss.
        exploit (x4 to0); eauto; try congr.
        { eapply TimeFacts.lt_le_lt; try exact TO; ss. }
        destruct (Time.le_lt_dec to to0); ss.
        exploit Memory.get_ts; try exact x2. i. des.
        { subst. inv x3. }
        exploit Memory.get_disjoint; [exact x2|exact GET|..]. i. des.
        { subst. timetac. }
        exfalso.
        apply (x6 to); econs; ss; try refl.
        etrans; try exact FROM.
        eapply TimeFacts.le_lt_lt; try exact x5. ss.
      + destruct (COVER loc from). exploit H0.
        { econs; try exact GET2. econs; ss. econs. ss. }
        intros x. inv x. inv ITV. ss.
        destruct (TimeFacts.le_lt_dec to to0).
        * exploit Memory.get_ts; try exact x2. i. des.
          { subst. inv x3. }
          exploit Memory.get_ts; try exact GET. i. des.
          { subst. timetac. }
          exploit Memory.get_disjoint; [exact x2|exact GET|..]. i. des.
          { subst. timetac. }
          exfalso.
          apply (x7 to); econs; ss; try refl.
          eapply TimeFacts.lt_le_lt; try exact FROM. econs. ss.
        * exploit (x4 to0); ss; try congr.
          eapply TimeFacts.lt_le_lt; try exact TO; ss.
  }
  des. esplits. econs; eauto; i.
  { exploit Memory.get_ts; try exact GET2_SRC. i. des.
    - subst. inv TS.
    - etrans; eauto. }
  destruct (Memory.get loc ts mem_src) as [[]|] eqn:GET; ss.
  exfalso.
  exploit Memory.get_ts; try exact GET. i. des.
  { subst. inv TS1. }
  destruct (COVER loc ts). exploit H.
  { econs; eauto. econs; ss. refl. }
  intros x. inv x. inv ITV. ss.
  destruct (TimeFacts.le_lt_dec to from2).
  { exploit (EMPTY to); try congr.
    eapply TimeFacts.lt_le_lt; try exact TS1. ss. }
  exploit Memory.get_ts; try exact GET2. i. des.
  { subst. inv TS. }
  exploit Memory.get_ts; try exact GET0. i. des.
  { subst. inv l. }
  exploit Memory.get_disjoint; [exact GET2|exact GET0|..]. i. des.
  { subst. timetac. }
  destruct (TimeFacts.le_lt_dec to2 to).
  - apply (x3 to2); econs; ss; try refl.
    etrans; try exact x1.
    eapply TimeFacts.lt_le_lt; try exact TS2. ss.
  - apply (x3 to); econs; ss; try refl. econs. ss.
Qed.

Lemma sim_memory_cap_get_src
      mem1_src mem2_src
      mem1_tgt mem2_tgt
      loc from to msg
      (MEM1: sim_memory mem1_src mem1_tgt)
      (CAP_SRC: Memory.cap mem1_src mem2_src)
      (CAP_TGT: Memory.cap mem1_tgt mem2_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt)
      (GET1_SRC: Memory.get loc to mem1_src = None)
      (GET2_SRC: Memory.get loc to mem2_src = Some (from, msg)):
  <<MSG: msg = Message.reserve>> /\
  <<GET1_TGT: Memory.get loc to mem1_tgt = None>> /\
  <<GET2_TGT: Memory.get loc to mem2_tgt = Some (from, msg)>>.
Proof.
  exploit Memory.cap_inv; try exact CAP_SRC; eauto. i. des; try congr.
  - subst.
    exploit sim_memory_adjacent_src; try exact x1; eauto. i. des.
    inv CAP_TGT. exploit MIDDLE; eauto. i. splits; auto.
    inv x3. apply EMPTY; eauto. refl.
  - subst.
    erewrite sim_memory_max_ts; eauto.
    inv CAP_TGT. splits; auto.
    { destruct (Memory.get loc (Time.incr (Memory.max_ts loc mem1_tgt)) mem1_tgt) as [[]|] eqn:MAX; ss.
      exploit Memory.max_ts_spec; eauto. i. des.
      specialize (Time.incr_spec (Memory.max_ts loc mem1_tgt)). i. timetac.
    }
    { hexploit Memory.max_ts_spec.
      { eapply MEM1_TGT. }
      i. des. eapply BACK; eauto.
    }
Qed.

Lemma sim_memory_cap_get_tgt
      mem1_src mem2_src
      mem1_tgt mem2_tgt
      loc from to msg
      (MEM1: sim_memory mem1_src mem1_tgt)
      (CAP_SRC: Memory.cap mem1_src mem2_src)
      (CAP_TGT: Memory.cap mem1_tgt mem2_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt)
      (GET1_TGT: Memory.get loc to mem1_tgt = None)
      (GET2_TGT: Memory.get loc to mem2_tgt = Some (from, msg)):
  <<MSG: msg = Message.reserve>> /\
  <<GET1_SRC: Memory.get loc to mem1_src = None>> /\
  <<GET2_SRC: Memory.get loc to mem2_src = Some (from, msg)>>.
Proof.
  exploit Memory.cap_inv; try exact CAP_TGT; eauto. i. des; try congr.
  - subst.
    exploit sim_memory_adjacent_tgt; try exact x1; eauto. i. des.
    inv CAP_SRC. exploit MIDDLE; eauto. i. splits; auto.
    inv x3. apply EMPTY; eauto. refl.
  - subst.
    erewrite <- sim_memory_max_ts; eauto.
    inv CAP_SRC. splits; auto.
    { destruct (Memory.get loc (Time.incr (Memory.max_ts loc mem1_src)) mem1_src) as [[]|] eqn:MAX; ss.
      exploit Memory.max_ts_spec; eauto. i. des.
      specialize (Time.incr_spec (Memory.max_ts loc mem1_src)). i. timetac.
    }
    { hexploit Memory.max_ts_spec.
      { eapply MEM1_SRC. }
      i. des. eapply BACK; eauto.
    }
Qed.

Lemma sim_memory_cap
      mem1_src mem2_src
      mem1_tgt mem2_tgt
      (MEM1: sim_memory mem1_src mem1_tgt)
      (CAP_SRC: Memory.cap mem1_src mem2_src)
      (CAP_TGT: Memory.cap mem1_tgt mem2_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  <<MEM2: sim_memory mem2_src mem2_tgt>>.
Proof.
  econs; i; try split; i.
  - inv H.
    destruct (Memory.get loc to mem1_src) as [[]|] eqn:GET1.
    + inv CAP_SRC. exploit SOUND; eauto. intros x.
      rewrite x in GET. inv GET.
      eapply cap_covered; eauto.
      inv MEM1. eapply Interval.le_mem; eauto. econs; ss.
      { eapply Time.bot_spec. }
      { erewrite <- sim_memory_max_ts; eauto.
        eapply Memory.max_ts_spec in GET1. des.
        etrans; eauto. left. eapply Time.incr_spec.
      }
    + exploit sim_memory_cap_get_src; eauto. i. des.
      econs; eauto.
  - inv H.
    destruct (Memory.get loc to mem1_tgt) as [[]|] eqn:GET1.
    + inv CAP_TGT. exploit SOUND; eauto. intros x.
      rewrite x in GET. inv GET.
      eapply cap_covered; try apply CAP_SRC; eauto.
      inv MEM1. eapply Interval.le_mem; eauto. econs; ss.
      { eapply Time.bot_spec. }
      { erewrite sim_memory_max_ts; eauto.
        eapply Memory.max_ts_spec in GET1. des.
        etrans; eauto. left. eapply Time.incr_spec.
      }
    + exploit sim_memory_cap_get_tgt; eauto. i. des.
      econs; eauto.
  - destruct (Memory.get loc to mem1_tgt) as [[]|] eqn:GET1.
    + inv CAP_TGT. exploit SOUND; eauto. intros x.
      rewrite x in GET. inv GET.
      inv MEM1. exploit MSG; eauto. i. des.
      inv CAP_SRC. exploit SOUND; eauto. i.
      esplits; eauto.
    + exploit sim_memory_cap_get_tgt; eauto. i. des.
      esplits; eauto. refl.
  - destruct (Memory.get loc to mem1_src) as [[]|] eqn:GET1.
    + inv CAP_SRC. exploit SOUND; eauto. intros x.
      rewrite x in H. inv H.
      inv MEM1. rewrite RSV in GET1.
      inv CAP_TGT. exploit SOUND0; eauto.
    + exploit sim_memory_cap_get_src; eauto. i. des. auto.
  - destruct (Memory.get loc to mem1_tgt) as [[]|] eqn:GET1.
    + inv CAP_TGT. exploit SOUND; eauto. intros x.
      rewrite x in H. inv H.
      inv MEM1. rewrite <- RSV in GET1.
      inv CAP_SRC. exploit SOUND0; eauto.
    + exploit sim_memory_cap_get_tgt; eauto. i. des. auto.
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
