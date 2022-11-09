Require Import Lia.
Require Import Bool.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
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

Require Import OrdStep.
Require Import Writes.
Require Import WStep.
Require Import Stable.

Set Implicit Arguments.


Module PFtoRASim.
  Section PFtoRASim.
    Variable lang: language.
    Variable L: Loc.t -> bool.

    Inductive sim_tview (tview_src tview_tgt: TView.t): Prop :=
    | sim_tview_intro
        (REL: forall loc, if L loc
                     then View.le ((TView.rel tview_tgt) loc) ((TView.rel tview_src) loc)
                     else (TView.rel tview_src) loc = (TView.rel tview_tgt) loc)
        (CUR: (TView.cur tview_src) = (TView.cur tview_tgt))
        (ACQ: (TView.acq tview_src) = (TView.acq tview_tgt))
    .

    Inductive sim_local (lc_src lc_tgt: Local.t): Prop :=
    | sim_local_intro
        (TVIEW: sim_tview (Local.tview lc_src) (Local.tview lc_tgt))
    .

    Inductive sim_message (loc: Loc.t): forall (msg_src msg_tgt: Message.t), Prop :=
    | sim_message_concrete
        val released_src na_src released_tgt na_tgt
        (RELEASED: if L loc then View.opt_le released_tgt released_src else released_src = released_tgt)
        (NA: ~ L loc -> na_src = na_tgt):
        sim_message loc (Message.message val released_src na_src) (Message.message val released_tgt na_tgt)
    | sim_message_reserve:
        sim_message loc Message.reserve Message.reserve
    .

    Global Program Instance sim_message_PreOrder: forall loc, PreOrder (sim_message loc).
    Next Obligation.
      ii. destruct x; econs; eauto. des_ifs. refl.
    Qed.
    Next Obligation.
      ii. inv H; inv H0; ss; econs; eauto. des_ifs. etrans; eauto.
    Qed.

    Inductive sim_memory (rels: Writes.t) (mem_src mem_tgt: Memory.t): Prop :=
    | sim_memory_intro
        (SOUND: forall loc from to msg_src
                  (GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)),
            exists msg_tgt,
              <<GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)>> /\
              <<MSG: sim_message loc msg_src msg_tgt>>)
        (COMPLETE: forall loc from to msg_tgt
                     (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)),
            exists msg_src,
              <<GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)>> /\
              <<MSG: sim_message loc msg_src msg_tgt>>)
        (REL_WRITES: forall loc to ord
                       (IN: List.In (loc, to, ord) rels)
                       (ORD: Ordering.le Ordering.acqrel ord),
            exists from val released false,
              <<GET_SRC: Memory.get loc to mem_src = Some (from, Message.message val (Some released) false)>> /\
              <<GET_TGT: Memory.get loc to mem_tgt = Some (from, Message.message val (Some released) false)>>)
        (NA_WRITES: forall loc from to val released
                      (LOC: L loc)
                      (TO: to <> Time.bot)
                      (GET_TGT: Memory.get loc to mem_tgt = Some (from, Message.message val released true)),
            List.In (loc, to, Ordering.na) rels)
    .

    Inductive sim_statelocal (rels: Writes.t):
      forall (sl_src sl_tgt: {lang : language & Language.state lang} * Local.t), Prop :=
    | sim_statelocal_intro
        lang st lc_src lc_tgt
        (LOCAL: sim_local lc_src lc_tgt):
        sim_statelocal rels (existT _ lang st, lc_src) (existT _ lang st, lc_tgt)
    .
    Hint Constructors sim_statelocal: core.

    Inductive sim_thread (rels: Writes.t) (e_src e_tgt: Thread.t lang): Prop :=
    | sim_thread_intro
        (STATE: (Thread.state e_src) = (Thread.state e_tgt))
        (LOCAL: sim_local (Thread.local e_src) (Thread.local e_tgt))
        (SC: Global.sc (Thread.global e_src) = Global.sc (Thread.global e_tgt))
        (MEMORY: sim_memory rels (Global.memory (Thread.global e_src)) (Global.memory (Thread.global e_tgt)))
    .
    Hint Constructors sim_thread: core.


    Lemma sim_tview_ra_race
          rels tview_src tview_tgt e
          (SIM: sim_tview tview_src tview_tgt):
      RARaceW.ra_race L rels tview_src e <->
      RARaceW.ra_race L rels tview_tgt e.
    Proof.
      inv SIM.
      unfold RARaceW.ra_race, RARaceW.wr_race, RARaceW.ww_race.
      split; i; des;
        (try by left; esplits; eauto; congr);
        (try by right; esplits; eauto; congr).
    Qed.

    Lemma sim_local_ra_race
          rels lc_src lc_tgt e
          (SIM: sim_local lc_src lc_tgt):
      RARaceW.ra_race L rels (Local.tview lc_src) e <->
      RARaceW.ra_race L rels (Local.tview lc_tgt) e.
    Proof.
      inv SIM. eapply sim_tview_ra_race; eauto.
    Qed.

    Lemma sim_thread_ra_race
          rels e_src e_tgt e
          (SIM: sim_thread rels e_src e_tgt):
      RARaceW.ra_race L rels (Local.tview (Thread.local e_src)) e <->
      RARaceW.ra_race L rels (Local.tview (Thread.local e_tgt)) e.
    Proof.
      inv SIM. eapply sim_local_ra_race; eauto.
    Qed.

    Lemma sim_memory_ord_le
          loc to ord rels mem_src mem_tgt
          ord'
          (SIM: sim_memory ((loc, to, ord) :: rels) mem_src mem_tgt)
          (LE: Ordering.le ord' ord):
      sim_memory ((loc, to, ord') :: rels) mem_src mem_tgt.
    Proof.
      inv SIM. econs; eauto.
      - i. inv IN.
        + inv H. eapply REL_WRITES; [left; eauto|]. etrans; eauto.
        + eapply REL_WRITES; eauto. right. ss.
      - i. exploit NA_WRITES; eauto. i. inv x0; s; auto.
        inv H. left. destruct ord'; ss.
    Qed.

    Lemma sim_tview_write_released
          tview_src tview_tgt
          loc to releasedm ord
          (SIM: sim_tview tview_src tview_tgt)
          (LOC: ~ L loc):
      TView.write_released tview_src loc to releasedm ord =
      TView.write_released tview_tgt loc to releasedm ord.
    Proof.
      inv SIM. unfold TView.write_released. ss.
      condtac; ss.
      unfold LocFun.add. condtac; ss. condtac; ss.
      - rewrite CUR. ss.
      - specialize (REL loc). des_ifs. rewrite REL. ss.
    Qed.

    Lemma sim_memory_closed_timemap_src
          rels mem_src mem_tgt tm
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED: Memory.closed_timemap tm mem_src):
      Memory.closed_timemap tm mem_tgt.
    Proof.
      inv SIM. ii.
      specialize (CLOSED loc). des.
      exploit SOUND; eauto. i. des. inv MSG.
      eauto.
    Qed.

    Lemma sim_memory_closed_view_src
          rels mem_src mem_tgt view
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED: Memory.closed_view view mem_src):
      Memory.closed_view view mem_tgt.
    Proof.
      inv CLOSED. econs; eauto using sim_memory_closed_timemap_src.
    Qed.

    Lemma sim_memory_closed_opt_view_src
          rels mem_src mem_tgt view
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED: Memory.closed_opt_view view mem_src):
      Memory.closed_opt_view view mem_tgt.
    Proof.
      inv CLOSED; eauto using sim_memory_closed_view_src.
    Qed.

    Lemma sim_memory_closed_message_src
          rels mem_src mem_tgt msg
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED: Memory.closed_message msg mem_src):
      Memory.closed_message msg mem_tgt.
    Proof.
      inv CLOSED; eauto using sim_memory_closed_opt_view_src.
    Qed.

    Lemma sim_memory_closed_timemap_tgt
          rels mem_src mem_tgt tm
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED: Memory.closed_timemap tm mem_tgt):
      Memory.closed_timemap tm mem_src.
    Proof.
      inv SIM. ii.
      specialize (CLOSED loc). des.
      exploit COMPLETE; eauto. i. des. inv MSG.
      eauto.
    Qed.

    Lemma sim_memory_closed_view_tgt
          rels mem_src mem_tgt view
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED: Memory.closed_view view mem_tgt):
      Memory.closed_view view mem_src.
    Proof.
      inv CLOSED. econs; eauto using sim_memory_closed_timemap_tgt.
    Qed.

    Lemma sim_memory_closed_opt_view_tgt
          rels mem_src mem_tgt view
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED: Memory.closed_opt_view view mem_tgt):
      Memory.closed_opt_view view mem_src.
    Proof.
      inv CLOSED; eauto using sim_memory_closed_view_tgt.
    Qed.

    Lemma sim_memory_closed_message_tgt
          rels mem_src mem_tgt msg
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED: Memory.closed_message msg mem_tgt):
      Memory.closed_message msg mem_src.
    Proof.
      inv CLOSED; eauto using sim_memory_closed_opt_view_tgt.
    Qed.

    Lemma sim_memory_writes_wf
          rels mem_src mem_tgt
          (SIM: sim_memory rels mem_src mem_tgt):
      forall rels', Writes.wf L rels' mem_src <-> Writes.wf L rels' mem_tgt.
    Proof.
      inv SIM. i. split; i; inv H; econs; i.
      - exploit SOUND0; eauto. i. des. split; ss.
        exploit SOUND; eauto. i. des. inv MSG. eauto.
      - exploit COMPLETE; eauto. i. des. inv MSG. eauto.
      - exploit SOUND0; eauto.  i. des. split; ss.
        exploit COMPLETE; eauto. i. des. inv MSG. eauto.
      - exploit SOUND; eauto. i. des. inv MSG. eauto.
    Qed.

    (* Lemma sim_memory_add *)
    (*       rels mem1_src *)
    (*       mem1_tgt loc from to msg mem2_tgt *)
    (*       (SIM1: sim_memory rels mem1_src mem1_tgt) *)
    (*       (LOC: ~ L loc) *)
    (*       (RELS: forall ord, ~ List.In (loc, to, ord) rels) *)
    (*       (ADD_TGT: Memory.add mem1_tgt loc from to msg mem2_tgt): *)
    (*   exists mem2_src, *)
    (*     <<ADD_SRC: Memory.add mem1_src loc from to msg mem2_src>> /\ *)
    (*     <<SIM2: sim_memory rels mem2_src mem2_tgt>>. *)
    (* Proof. *)
    (*   inv SIM1. *)
    (*   exploit (@Memory.add_exists mem1_src loc from to msg). *)
    (*   { ii. inv LHS. inv RHS. ss. *)
    (*     exploit SOUND; eauto. i. des. *)
    (*     exploit Memory.add_get0; eauto. i. des. *)
    (*     exploit Memory.add_get1; eauto. i. *)
    (*     exploit Memory.get_ts; try exact GET0. i. des. *)
    (*     { subst. timetac. } *)
    (*     exploit Memory.get_ts; try exact x1. i. des. *)
    (*     { subst. timetac. } *)
    (*     exploit Memory.get_disjoint; [exact GET0|exact x1|..]. i. des. *)
    (*     { subst. congr. } *)
    (*     apply (x4 x); econs; eauto. } *)
    (*   { inv ADD_TGT. inv ADD. ss. } *)
    (*   { inv ADD_TGT. inv ADD. ss. } *)
    (*   i. des. *)
    (*   esplits; eauto. econs; i. *)
    (*   - revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss. *)
    (*     + i. des. inv GET_SRC. *)
    (*       erewrite Memory.add_o; eauto. condtac; ss. *)
    (*       esplits; eauto. refl. *)
    (*     + i. erewrite Memory.add_o; eauto. condtac; ss. eauto. *)
    (*   - revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss. *)
    (*     + i. des. inv GET_TGT. *)
    (*       erewrite Memory.add_o; eauto. condtac; ss. *)
    (*       esplits; eauto. refl. *)
    (*     + i. erewrite Memory.add_o; eauto. condtac; ss. eauto. *)
    (*   - exploit REL_WRITES; eauto. i. des. *)
    (*     erewrite Memory.add_o; eauto. *)
    (*     erewrite (@Memory.add_o mem2_tgt); eauto. *)
    (*     condtac; ss; eauto. *)
    (*     des. subst. exploit RELS; eauto. ss. *)
    (*   - revert GET_TGT. erewrite Memory.add_o; eauto. *)
    (*     condtac; ss; eauto. i. des. inv GET_TGT. ss. *)
    (* Qed. *)

    Lemma sim_memory_get_tgt
          rels mem_src mem_tgt
          loc from to val released_tgt na_tgt
          (SIM: sim_memory rels mem_src mem_tgt)
          (GET_TGT: Memory.get loc to mem_tgt = Some (from, Message.message val released_tgt na_tgt)):
      exists released_src na_src,
        (<<GET_SRC: Memory.get loc to mem_src = Some (from, Message.message val released_src na_src)>>) /\
        (<<RELEASED: View.opt_le released_tgt released_src>>) /\
        (<<NA: ~ L loc -> na_src = na_tgt>>).
    Proof.
      inv SIM. exploit COMPLETE; eauto. i. des. inv MSG.
      esplits; eauto. des_ifs; ss. refl.
    Qed.

    Lemma sim_memory_stable_view
          rels mem_src mem_tgt view
          (SIM: sim_memory rels mem_src mem_tgt)
          (STABLE_SRC: Stable.stable_view L mem_src view):
      Stable.stable_view L mem_tgt view.
    Proof.
      ii. exploit sim_memory_get_tgt; eauto. i. des. inv RELEASED.
      etrans; eauto.
    Qed.

    Lemma sim_memory_stable_tview
          rels tview_src tview_tgt mem_src mem_tgt
          (TVIEW: sim_tview tview_src tview_tgt)
          (MEM: sim_memory rels mem_src mem_tgt)
          (STABLE_SRC: Stable.stable_tview L mem_src tview_src):
      Stable.stable_tview L mem_tgt tview_tgt.
    Proof.
      destruct tview_src, tview_tgt. inv TVIEW. ss. subst.
      inv STABLE_SRC. econs; eauto using sim_memory_stable_view; ss. i.
      specialize (REL loc). des_ifs.
      rewrite <- REL. eapply sim_memory_stable_view; eauto.
      apply REL0. congr.
    Qed.

    Lemma sim_memory_stable_memory
          rels mem_src mem_tgt
          (SIM: sim_memory rels mem_src mem_tgt)
          (STABLE_SRC: Stable.stable_memory L rels mem_src):
      Stable.stable_memory L rels mem_tgt.
    Proof.
      dup SIM. inv SIM0. unfold Stable.stable_memory. i. des.
      - exploit COMPLETE; try exact GET. i. des. inv MSG. des_ifs.
        eapply sim_memory_stable_view; eauto.
        eapply STABLE_SRC; eauto. left. congr.
      - exploit REL_WRITES; eauto. i. des.
        rewrite GET_TGT in *. inv GET.
        eapply sim_memory_stable_view; eauto.
    Qed.

    Lemma sim_thread_stable
          rels e_src e_tgt
          (SIM: sim_thread rels e_src e_tgt)
          (STABLE_SRC: Stable.stable_thread L rels e_src):
      Stable.stable_thread L rels e_tgt.
    Proof.
      destruct e_src, e_tgt. inv SIM. inv STABLE_SRC. ss. subst.
      inv LOCAL. econs; ss; eauto.
      - eapply sim_memory_stable_tview; eauto.
      - eapply sim_memory_stable_view; eauto.
        rewrite <- SC. ss.
      - eapply sim_memory_stable_memory; eauto.
    Qed.

    (* step *)

    (* Lemma promise *)
    (*       rels mem1_src *)
    (*       promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind *)
    (*       (PROMISES1: OrdLocal.reserve_only L promises1) *)
    (*       (WRITES1: Writes.wf L rels mem1_src) *)
    (*       (MEM1: sim_memory rels mem1_src mem1_tgt) *)
    (*       (LE1_SRC: Memory.le promises1 mem1_src) *)
    (*       (STEP_TGT: Memory.promise promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind) *)
    (*       (MSG: L loc -> msg = Message.reserve): *)
    (*   exists mem2_src, *)
    (*     <<STEP_SRC: Memory.promise promises1 mem1_src loc from to msg promises2 mem2_src kind>> /\ *)
    (*     <<MEM2: sim_memory rels mem2_src mem2_tgt>>. *)
    (* Proof. *)
    (*   destruct (L loc) eqn:LOC. *)
    (*   { (* promise on L *) *)
    (*     rewrite MSG in *; ss. *)
    (*     inv MEM1. inv STEP_TGT. *)
    (*     - (* add *) *)
    (*       exploit (@Memory.add_exists mem1_src loc from to Message.reserve). *)
    (*       { ii. inv LHS. inv RHS. ss. *)
    (*         exploit SOUND; eauto. i. des. *)
    (*         exploit Memory.add_get0; try exact MEM. i. des. *)
    (*         exploit Memory.add_get1; try exact GET_TGT; eauto. i. *)
    (*         exploit Memory.get_ts; try exact GET0. i. des. *)
    (*         { subst. timetac. } *)
    (*         exploit Memory.get_ts; try exact x1. i. des. *)
    (*         { subst. timetac. } *)
    (*         exploit Memory.get_disjoint; [exact GET0|exact x1|..]. i. des. *)
    (*         { subst. congr. } *)
    (*         apply (x4 x); econs; ss. } *)
    (*       { inv MEM. inv ADD. ss. } *)
    (*       { econs. } *)
    (*       i. des. *)
    (*       exploit Memory.add_exists_le; try apply LE1_SRC; eauto. i. des. *)
    (*       esplits; eauto. econs; i. *)
    (*       + revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss. *)
    (*         { i. des. clarify. *)
    (*           exploit Memory.add_get0; try exact MEM. i. des. *)
    (*           esplits; eauto. econs. } *)
    (*         { i. erewrite Memory.add_o; eauto. condtac; ss; eauto. } *)
    (*       + revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss. *)
    (*         { i. des. inv GET_TGT. *)
    (*           exploit Memory.add_get0; try exact x0. i. des. *)
    (*           esplits; eauto. econs. } *)
    (*         { i. erewrite Memory.add_o; eauto. condtac; ss; eauto. } *)
    (*       + exploit REL_WRITES; eauto. i. des. *)
    (*         erewrite Memory.add_o; eauto. *)
    (*         erewrite (@Memory.add_o mem2_tgt); eauto. *)
    (*         condtac; ss; eauto. des. subst. *)
    (*         exploit Memory.add_get0; try exact MEM. i. des. congr. *)
    (*     - (* split *) *)
    (*       des. ss. *)
    (*     - (* lower *) *)
    (*       des. subst. inv MEM. inv LOWER. inv MSG_LE. ss. *)
    (*     - (* cancel *) *)
    (*       exploit Memory.remove_get0; try exact PROMISES. i. des. *)
    (*       exploit Memory.remove_exists_le; try apply LE1_SRC; eauto. i. des. *)
    (*       esplits; eauto. econs; i. *)
    (*       + revert GET_SRC. erewrite Memory.remove_o; eauto. condtac; ss. i. *)
    (*         erewrite Memory.remove_o; eauto. condtac; ss. eauto. *)
    (*       + revert GET_TGT. erewrite Memory.remove_o; eauto. condtac; ss. i. *)
    (*         erewrite Memory.remove_o; eauto. condtac; ss. eauto. *)
    (*       + exploit REL_WRITES; eauto. i. des. *)
    (*         erewrite Memory.remove_o; eauto. *)
    (*         erewrite (@Memory.remove_o mem2_tgt); eauto. *)
    (*         condtac; ss; eauto. des. subst. *)
    (*         exploit Memory.remove_get0; try exact x0. i. des. congr. *)
    (*   } *)

    (*   (* promises on other loc *) *)
    (*   clear MSG. inv STEP_TGT. *)
    (*   - (* add *) *)
    (*     exploit sim_memory_add; eauto. *)
    (*     { ii. inv WRITES1. exploit SOUND; eauto. i. des. *)
    (*       exploit Memory.add_get0; try exact MEM. i. des. congr. *)
    (*     } *)
    (*     i. des. esplits; eauto. econs; eauto. *)
    (*     i. subst. inv MEM1. exploit SOUND; eauto. i. des. eauto. *)
    (*   - (* split *) *)
    (*     exploit sim_memory_split; eauto; try congr. *)
    (*     { ii. inv WRITES1. exploit SOUND; eauto. i. des. *)
    (*       exploit Memory.split_get0; try exact MEM. i. des. *)
    (*       inv MEM1. exploit COMPLETE0; try exact GET0. i. des. *)
    (*       rewrite GET_SRC in *. clarify. *)
    (*     } *)
    (*     i. des. esplits; eauto. *)
    (*   - (* lower *) *)
    (*     exploit sim_memory_lower; eauto; try congr. *)
    (*     { ii. inv WRITES1. exploit SOUND; eauto. i. des. *)
    (*       exploit Memory.lower_get0; try exact MEM. i. des. *)
    (*       inv MEM1. exploit COMPLETE0; try exact GET. i. des. *)
    (*       rewrite GET_SRC in *. clarify. *)
    (*     } *)
    (*     i. des. *)
    (*     inv MEM1. esplits; eauto. *)
    (*   - (* cancel *) *)
    (*     exploit sim_memory_remove; eauto; try congr. *)
    (*     { ii. exploit Memory.remove_get0; try exact PROMISES. i. des. *)
    (*       exploit LE1_SRC; eauto. i. *)
    (*       inv WRITES1. exploit SOUND; eauto. i. des. congr. *)
    (*     } *)
    (*     i. des. esplits; eauto. *)
    (* Qed. *)

    Lemma add
          rels mem1_src
          mem1_tgt loc from to msg mem2_tgt
          (WRITES1: Writes.wf L rels mem1_src)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (STEP_TGT: Memory.add mem1_tgt loc from to msg mem2_tgt)
          (LOC: ~ L loc):
      exists mem2_src,
        <<STEP_SRC: Memory.add mem1_src loc from to msg mem2_src>> /\
        <<MEM2: sim_memory rels mem2_src mem2_tgt>>.
    Proof.
      inv MEM1.
      exploit (@Memory.add_exists mem1_src loc from to msg).
      { ii. inv LHS. inv RHS. ss.
        exploit SOUND; eauto. i. des.
        exploit Memory.add_get0; eauto. i. des.
        exploit Memory.add_get1; eauto. i.
        exploit Memory.get_ts; try exact GET0. i. des.
        { subst. timetac. }
        exploit Memory.get_ts; try exact x1. i. des.
        { subst. timetac. }
        exploit Memory.get_disjoint; [exact GET0|exact x1|..]. i. des.
        { subst. congr. }
        apply (x4 x); econs; eauto. }
      { inv STEP_TGT. inv ADD. ss. }
      { inv STEP_TGT. inv ADD. ss. }
      i. des.
      esplits; eauto. econs; i.
      - revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss.
        + i. des. inv GET_SRC.
          erewrite Memory.add_o; eauto. condtac; ss.
          esplits; eauto. refl.
        + i. erewrite Memory.add_o; eauto. condtac; ss. eauto.
      - revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss.
        + i. des. inv GET_TGT.
          erewrite Memory.add_o; eauto. condtac; ss.
          esplits; eauto. refl.
        + i. erewrite Memory.add_o; eauto. condtac; ss. eauto.
      - exploit REL_WRITES; eauto. i. des.
        erewrite Memory.add_o; eauto.
        erewrite (@Memory.add_o mem2_tgt); eauto.
        condtac; ss; eauto. des. subst.
        inv WRITES1. exploit SOUND0; eauto. i. des. ss.
      - revert GET_TGT. erewrite Memory.add_o; eauto.
        condtac; ss; eauto. i. des. inv GET_TGT. ss.
    Qed.

    Lemma read_step_loc
          rels lc1_src gl1_src
          lc1_tgt gl1_tgt loc to val released_tgt ord lc2_tgt
          (LC1: sim_local lc1_src lc1_tgt)
          (MEM1: sim_memory rels (Global.memory gl1_src) (Global.memory gl1_tgt))
          (WRITES1: Writes.wf L rels (Global.memory gl1_src))
          (NORMAL_TVIEW1_SRC: Normal.normal_tview L (Local.tview lc1_src))
          (NORMAL_TVIEW1_TGT: Normal.normal_tview L (Local.tview lc1_tgt))
          (STABLE_TVIEW1_SRC: Stable.stable_tview L (Global.memory gl1_src) (Local.tview lc1_src))
          (NORMAL_MEM1_SRC: Normal.normal_memory L (Global.memory gl1_src))
          (NORMAL_MEM1_TGT: Normal.normal_memory L (Global.memory gl1_tgt))
          (STABLE_MEM1_SRC: Stable.stable_memory L rels (Global.memory gl1_src))
          (LC_WF1_SRC: Local.wf lc1_src gl1_src)
          (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
          (GL_WF1_SRC: Global.wf gl1_src)
          (GL_WF1_TGT: Global.wf gl1_tgt)
          (LOC: L loc)
          (STEP_TGT: Local.read_step lc1_tgt gl1_tgt loc to val released_tgt ord lc2_tgt):
      exists released_src lc2_src,
        <<STEP_SRC: OrdLocal.read_step L Ordering.acqrel lc1_src gl1_src loc to val released_src ord lc2_src>> /\
        __guard__ (
            (<<LC2: sim_local lc2_src lc2_tgt>>) /\
            (<<RELEASED_SRC: View.opt_le released_src (Some (TView.cur (Local.tview lc2_src)))>>) /\
            (<<RELEASED_TGT: View.opt_le released_tgt (Some (TView.cur (Local.tview lc2_tgt)))>>) /\
            (<<NORMAL_TVIEW1_SRC: Normal.normal_tview L (Local.tview lc2_src)>>) /\
            (<<NORMAL_TVIEW1_TGT: Normal.normal_tview L (Local.tview lc2_tgt)>>) /\
            (<<STABLE_TVIEW1_SRC: Stable.stable_tview L (Global.memory gl1_src) (Local.tview lc2_src)>>)
            \/
            (<<RACE: RARaceW.wr_race L rels (Local.tview lc1_src) loc ord>>)).
    Proof.
      exploit sim_memory_stable_tview; eauto; try apply LC1. intro STABLE_TVIEW1_TGT.
      hexploit sim_memory_stable_memory; eauto. intro STABLE_MEM1_TGT.
      inv LC1. inv TVIEW. inv MEM1.
      dup STEP_TGT. inv STEP_TGT.
      exploit COMPLETE; eauto. i. des. inv MSG. clear RELEASED.
      inv READABLE. dup NORMAL_TVIEW1_SRC. inv NORMAL_TVIEW1_SRC0.
      rewrite <- CUR, <- CUR0 in *; ss. clear RLX.
      assert (exists released_src lc2_src,
                 <<STEP_SRC: OrdLocal.read_step L Ordering.acqrel lc1_src gl1_src loc to val released_src ord lc2_src>>).
      { esplits. do 3 (econs; eauto). rewrite <- CUR0; ss. }
      des. esplits; eauto.
      dup STEP_SRC. inv STEP_SRC0. inv STEP.
      rewrite GET0 in *. inv GET_SRC.

      inv PLN; cycle 1.
      { (* read from cur view *)
        inv H. left. esplits; try exact STEP_SRC.
        - econs; ss. rewrite LOC.
          erewrite Stable.stable_tview_read_tview; eauto; try apply LC_WF1_SRC.
          rewrite CUR in *.
          erewrite Stable.stable_tview_read_tview; eauto; try apply LC_WF1_TGT.
          econs; eauto.
        - destruct released_src; ss. econs.
          inv STABLE_TVIEW1_SRC. exploit CUR1; eauto. i.
          etrans; eauto.
          do 2 (etrans; [|apply View.join_l]).
          refl.
        - destruct released_tgt; ss. econs.
          inv STABLE_TVIEW1_TGT.
          rewrite <- CUR in *. exploit CUR1; eauto. i.
          etrans; eauto.
          do 2 (etrans; [|apply View.join_l]).
          refl.
        - rewrite LOC.
          erewrite Stable.stable_tview_read_tview; eauto; try apply LC_WF1_SRC.
        - rewrite CUR in *.
          erewrite Stable.stable_tview_read_tview; eauto; try apply LC_WF1_TGT.
        - rewrite LOC.
          erewrite Stable.stable_tview_read_tview; eauto; try apply LC_WF1_SRC.
      }

      inv WRITES1. exploit COMPLETE0; eauto.
      { ii. subst. inv H. }
      i. des.
      destruct (Ordering.le ord0 Ordering.strong_relaxed) eqn:ORDW.
      { (* non release write *)
        right. unfold RARaceW.wr_race. esplits; eauto.
      }
      destruct (Ordering.le ord Ordering.strong_relaxed) eqn:ORDR.
      { (* non acquire read *)
        right. unfold RARaceW.wr_race. esplits; eauto.
      }

      (* RA synchronized *)
      left. splits; ss.
      - econs; ss. rewrite LOC.
        exploit REL_WRITES; eauto; try by destruct ord0; ss. i. des.
        rewrite GET_SRC, GET_TGT in *. inv GET0. inv GET.
        econs; ss.
        + replace (Ordering.join ord Ordering.acqrel) with ord by (destruct ord; ss).
          condtac; try by (destruct ord; ss).
          rewrite CUR. refl.
        + replace (Ordering.join ord Ordering.acqrel) with ord by (destruct ord; ss).
          condtac; try by (destruct ord; ss).
          rewrite ACQ. refl.
      - repeat (condtac; ss); try by (destruct ord; ss).
        destruct released_src; ss. econs.
        etrans; [|eapply View.join_r]. refl.
      - repeat (condtac; ss); try by (destruct ord; ss).
        destruct released_tgt; ss. econs.
        etrans; [|eapply View.join_r]. refl.
      - inv STEP_SRC.
        exploit Normal.read_step; try exact STEP; eauto.
        rewrite LOC. destruct ord; ss.
      - exploit Normal.read_step; eauto.
        rewrite LOC. destruct ord; ss.
      - inv STEP_SRC.
        exploit Stable.read_step_loc_ra; try apply STEP; eauto.
        { destruct ord0; ss. }
        { rewrite LOC. destruct ord; ss. }
    Qed.

    Lemma read_step_other_aux
          rels lc1_src gl1_src
          lc1_tgt gl1_tgt loc to val released ord lc2_tgt
          (LC1: sim_local lc1_src lc1_tgt)
          (MEM1: sim_memory rels (Global.memory gl1_src) (Global.memory gl1_tgt))
          (LOC: L loc = false)
          (STEP_TGT: Local.read_step lc1_tgt gl1_tgt loc to val released ord lc2_tgt):
      exists lc2_src,
        (<<STEP_SRC: OrdLocal.read_step L Ordering.acqrel lc1_src gl1_src loc to val released ord lc2_src>>) /\
        (<<LC2: sim_local lc2_src lc2_tgt>>).
    Proof.
      inv LC1. inv TVIEW. inv MEM1. inv STEP_TGT.
      exploit COMPLETE; eauto. i. des. inv MSG.
      rewrite LOC in *. subst.
      esplits.
      - econs; eauto. econs; eauto. rewrite CUR, LOC in *. ss.
      - rewrite LOC in *. econs; eauto; ss.
        econs; eauto; ss; congr.
    Qed.

    Lemma read_step_other
          rels lc1_src gl1_src
          lc1_tgt gl1_tgt loc to val released ord lc2_tgt
          (LC1: sim_local lc1_src lc1_tgt)
          (MEM1: sim_memory rels (Global.memory gl1_src) (Global.memory gl1_tgt))
          (NORMAL_TVIEW1_SRC: Normal.normal_tview L (Local.tview lc1_src))
          (NORMAL_TVIEW1_TGT: Normal.normal_tview L (Local.tview lc1_tgt))
          (STABLE_TVIEW1_SRC: Stable.stable_tview L (Global.memory gl1_src) (Local.tview lc1_src))
          (NORMAL_MEM1_SRC: Normal.normal_memory L (Global.memory gl1_src))
          (NORMAL_MEM1_TGT: Normal.normal_memory L (Global.memory gl1_tgt))
          (STABLE_MEM1_SRC: Stable.stable_memory L rels (Global.memory gl1_src))
          (LC_WF1_SRC: Local.wf lc1_src gl1_src)
          (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
          (GL_WF1_SRC: Global.wf gl1_src)
          (GL_WF1_TGT: Global.wf gl1_tgt)
          (LOC: L loc = false)
          (STEP_TGT: Local.read_step lc1_tgt gl1_tgt loc to val released ord lc2_tgt):
      exists lc2_src,
        (<<STEP_SRC: OrdLocal.read_step L Ordering.acqrel lc1_src gl1_src loc to val released ord lc2_src>>) /\
        (<<LC2: sim_local lc2_src lc2_tgt>>) /\
        (<<NORMAL_TVIEW1_SRC: Normal.normal_tview L (Local.tview lc2_src)>>) /\
        (<<NORMAL_TVIEW1_TGT: Normal.normal_tview L (Local.tview lc2_tgt)>>) /\
        (<<STABLE_TVIEW1_SRC: Stable.stable_tview L (Global.memory gl1_src) (Local.tview lc2_src)>>).
    Proof.
      exploit sim_memory_stable_tview; try eapply LC1; eauto. intro STABLE_TVIEW1_TGT.
      hexploit sim_memory_stable_memory; eauto. intro STABLE_MEM1_TGT.
      exploit read_step_other_aux; eauto. i. des.
      dup STEP_SRC. inv STEP_SRC0.
      exploit Normal.read_step; try exact STEP; eauto; try congr. i. des.
      exploit Normal.read_step; try exact STEP_TGT; eauto; try congr. i. des.
      exploit Stable.read_step_other; try exact STEP; eauto; try congr. i. des.
      esplits; eauto.
    Qed.

    Lemma write_step_loc_aux
          rels lc1_src gl1_src releasedm_src
          lc1_tgt gl1_tgt loc from to val releasedm_tgt released_tgt ord lc2_tgt gl2_tgt
          (LC1: sim_local lc1_src lc1_tgt)
          (SC1: Global.sc gl1_src = Global.sc gl1_tgt)
          (MEM1: sim_memory rels (Global.memory gl1_src) (Global.memory gl1_tgt))
          (WF1_SRC: Local.wf lc1_src gl1_src)
          (WF1_TGT: Local.wf lc1_tgt gl1_tgt)
          (RELEASEDM: View.opt_le releasedm_tgt releasedm_src)
          (RELEASEDM_SRC: View.opt_le releasedm_src (Some (TView.cur (Local.tview lc1_src))))
          (RELEASEDM_TGT: View.opt_le releasedm_tgt (Some (TView.cur (Local.tview lc1_tgt))))
          (RELEASEDM_WF_SRC: View.opt_wf releasedm_src)
          (RELEASEDM_WF_TGT: View.opt_wf releasedm_tgt)
          (LOC: L loc)
          (STEP_TGT: Local.write_step lc1_tgt gl1_tgt loc from to val releasedm_tgt released_tgt ord
                                      lc2_tgt gl2_tgt):
      exists released_src lc2_src gl2_src,
        <<STEP_SRC: OrdLocal.write_step L Ordering.acqrel
                                        lc1_src gl1_src loc from to val releasedm_src released_src ord
                                        lc2_src gl2_src>> /\
        <<LC2: sim_local lc2_src lc2_tgt>> /\
        <<SC2: Global.sc gl2_src = Global.sc gl2_tgt>> /\
        <<MEM2: sim_memory ((loc, to, ord) :: rels) (Global.memory gl2_src) (Global.memory gl2_tgt)>>.
    Proof.
      destruct lc1_src as [tview1_src prm1_src rsv1_src],
          lc1_tgt as [tview1_tgt prm1_tgt rsv1_tgt].
      destruct gl1_src as [sc1_src gprm1_src mem1_src],
          gl1_tgt as [sc1_tgt gprm1_tgt mem1_tgt].
      inv LC1. inv STEP_TGT. ss. subst.
      exploit (@Memory.add_exists
                 mem1_src loc from to
                 (Message.message
                    val
                    (TView.write_released tview1_src loc to releasedm_src
                                          (Ordering.join ord Ordering.acqrel))
                    (Ordering.le (Ordering.join ord Ordering.acqrel) Ordering.na))).
      { ii. inv MEM1.
        exploit SOUND; eauto. i. des.
        exploit Memory.add_get1; try exact GET_TGT; eauto. i.
        exploit Memory.add_get0; try exact WRITE. i. des.
        exploit Memory.get_disjoint; [exact x1|exact GET0|..]. i. des; eauto.
        subst. congr.
      }
      { inv WRITE. inv ADD. ss. }
      { econs. eapply TViewFacts.write_future0; eauto. apply WF1_SRC. }
      i. des.

      esplits.
      - econs; eauto. condtac; ss. econs; ss.
        + inv TVIEW. rewrite CUR. inv WRITABLE. econs. ss.
        + econs; eauto.
        + eauto.
      - econs; ss.
        inv TVIEW. econs; ss; try congr. i.
        unfold LocFun.add. condtac; ss; cycle 1.
        { condtac; try congr.
          specialize (REL loc0). des_ifs.
        }
        condtac; ss; cycle 1.
        { specialize (REL loc0). des_ifs. }
        do 2 (condtac; ss); try by destruct ord; ss.
        + rewrite CUR. refl.
        +  rewrite CUR. apply View.join_spec; try apply View.join_r.
           etrans; [|apply View.join_l]. apply WF1_TGT.
      - ss.
      - inv MEM1. move WRITE at bottom. move x0 at bottom. econs; i.
        + erewrite Memory.add_o; eauto.
          revert GET_SRC. erewrite Memory.add_o; eauto.
          condtac; ss; eauto. i. des. clarify. esplits; eauto. econs; ss.
          condtac; ss; try congr.
          apply TViewFacts.write_released_mon; eauto; try refl.
          * inv TVIEW. econs; try rewrite CUR; try rewrite ACQ; try refl.
            i. specialize (REL loc0). des_ifs.
            unfold LocFun.find. rewrite REL. refl.
          * apply WF1_SRC.
          * destruct ord; ss.
        + erewrite Memory.add_o; eauto.
          revert GET_TGT. erewrite Memory.add_o; eauto.
          condtac; ss; eauto. i. des. clarify. esplits; eauto. econs; ss.
          condtac; ss; try congr.
          apply TViewFacts.write_released_mon; eauto; try refl.
          * inv TVIEW. econs; try rewrite CUR; try rewrite ACQ; try refl.
            i. specialize (REL loc0). des_ifs.
            unfold LocFun.find. rewrite REL. refl.
          * apply WF1_SRC.
          * destruct ord; ss.
        + inv IN; cycle 1.
          { exploit REL_WRITES; eauto. i. des.
            exploit Memory.add_get1; try exact GET_SRC; eauto.
            exploit Memory.add_get1; try exact GET_TGT; eauto. i.
            esplits; eauto.
          }
          inv H.
          erewrite (@Memory.add_o mem2); eauto.
          erewrite (@Memory.add_o mem0); eauto.
          condtac; des; ss.
          replace (Ordering.join ord0 Ordering.acqrel) with ord0 in * by (destruct ord0; ss).
          unfold TView.write_released. condtac; try by (destruct ord0; ss).
          esplits; eauto. do 4 f_equal. ss. condtac; ss.
          unfold LocFun.add. condtac; ss.
          rewrite View.le_join_r; cycle 1.
          { etrans; [|eapply View.join_l]. inv RELEASEDM_TGT; ss. apply View.bot_spec. }
          symmetry.
          rewrite View.le_join_r; cycle 1.
          { etrans; [|eapply View.join_l]. inv RELEASEDM_SRC; ss. apply View.bot_spec. }
          inv TVIEW. rewrite CUR. ss.
        + revert GET_TGT. erewrite Memory.add_o; eauto.
          condtac; ss; eauto. i. des. inv GET_TGT.
          left. destruct ord; ss.
    Qed.

    Lemma write_step_loc
          rels lc1_src gl1_src releasedm_src
          lc1_tgt gl1_tgt loc from to val releasedm_tgt released_tgt ord lc2_tgt gl2_tgt
          (LC1: sim_local lc1_src lc1_tgt)
          (SC1: Global.sc gl1_src = Global.sc gl1_tgt)
          (MEM1: sim_memory rels (Global.memory gl1_src) (Global.memory gl1_tgt))
          (WRITES1: Writes.wf L rels (Global.memory gl1_src))
          (NORMAL_TVIEW1_SRC: Normal.normal_tview L (Local.tview lc1_src))
          (NORMAL_TVIEW1_TGT: Normal.normal_tview L (Local.tview lc1_tgt))
          (STABLE_TVIEW1_SRC: Stable.stable_tview L (Global.memory gl1_src) (Local.tview lc1_src))
          (NORMAL_MEM1_SRC: Normal.normal_memory L (Global.memory gl1_src))
          (NORMAL_MEM1_TGT: Normal.normal_memory L (Global.memory gl1_tgt))
          (STABLE_MEM1_SRC: Stable.stable_memory L rels (Global.memory gl1_src))
          (LC_WF1_SRC: Local.wf lc1_src gl1_src)
          (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
          (GL_WF1_SRC: Global.wf gl1_src)
          (GL_WF1_TGT: Global.wf gl1_tgt)
          (RELEASEDM: View.opt_le releasedm_tgt releasedm_src)
          (RELEASEDM_SRC: View.opt_le releasedm_src (Some (TView.cur (Local.tview lc1_src))))
          (RELEASEDM_TGT: View.opt_le releasedm_tgt (Some (TView.cur (Local.tview lc1_tgt))))
          (RELEASEDM_NORMAL_SRC: Normal.normal_view L (View.unwrap releasedm_src))
          (RELEASEDM_NORMAL_TGT: Normal.normal_view L (View.unwrap releasedm_tgt))
          (RELEASEDM_WF_SRC: View.opt_wf releasedm_src)
          (RELEASEDM_WF_TGT: View.opt_wf releasedm_tgt)
          (RELEASEDM_TS_SRC: Time.le (View.rlx (View.unwrap releasedm_src) loc) to)
          (RELEASEDM_TS_TGT: Time.le (View.rlx (View.unwrap releasedm_tgt) loc) to)
          (RELEASEDM_CLOSED_SRC: Memory.closed_opt_view releasedm_src (Global.memory gl1_src))
          (RELEASEDM_CLOSED_TGT: Memory.closed_opt_view releasedm_tgt (Global.memory gl1_tgt))
          (LOC: L loc)
          (STEP_TGT: Local.write_step lc1_tgt gl1_tgt loc from to val releasedm_tgt released_tgt ord
                                      lc2_tgt gl2_tgt):
      exists released_src lc2_src gl2_src,
        (<<STEP_SRC: OrdLocal.write_step L Ordering.acqrel
                                         lc1_src gl1_src loc from to val releasedm_src released_src ord
                                         lc2_src gl2_src>>) /\
        (<<LC2: sim_local lc2_src lc2_tgt>>) /\
        (<<SC2: Global.sc gl2_src = Global.sc gl2_tgt>>) /\
        (<<MEM2: sim_memory ((loc, to, ord) :: rels) (Global.memory gl2_src) (Global.memory gl2_tgt)>>) /\
        (<<NORMAL_TVIEW2_SRC: Normal.normal_tview L (Local.tview lc2_src)>>) /\
        (<<NORMAL_TVIEW2_TGT: Normal.normal_tview L (Local.tview lc2_tgt)>>) /\
        (<<STABLE_TVIEW2_SRC: Stable.stable_tview L (Global.memory gl2_src) (Local.tview lc2_src)>>) /\
        (<<NORMAL_MEM2_SRC: Normal.normal_memory L (Global.memory gl2_src)>>) /\
        (<<NORMAL_MEM2_TGT: Normal.normal_memory L (Global.memory gl2_tgt)>>) /\
        (<<STABLE_MEM2_SRC: Stable.stable_memory L ((loc, to, ord) :: rels) (Global.memory gl2_src)>>).
    Proof.
      exploit sim_memory_stable_tview; try apply LC1; eauto. intro STABLE_TVIEW1_TGT.
      hexploit sim_memory_stable_memory; eauto. intro STABLE_MEM1_TGT.
      exploit write_step_loc_aux; try exact STEP_TGT; try exact RELEASEDM_SRC; eauto. i. des.
      exploit Normal.write_step; try exact STEP_TGT; eauto. i. des.
      exploit Stable.write_step; try exact STEP_TGT; eauto.
      { erewrite <- sim_memory_writes_wf; eauto. }
      { ss. }
      { i. inv RELEASEDM_TGT; ss. apply View.bot_spec. }
      i. des. des_ifs.
      dup STEP_SRC. inv STEP_SRC. des_ifs.
      exploit Normal.write_step; try exact STEP; eauto. i. des.
      exploit Stable.write_step; try exact STEP; eauto.
      { ss. }
      { i. inv RELEASEDM_SRC; ss. apply View.bot_spec. }
      i. des. des_ifs.
      esplits; eauto.
      ii. eapply STABLE_MEM0; eauto. des; eauto.
      right. inv LOC0.
      - inv H. esplits; [econs 1; eauto|]. destruct ord0; ss.
      - esplits; eauto. right. ss.
    Qed.

    Lemma write_step_other_aux
          rels lc1_src gl1_src
          lc1_tgt gl1_tgt loc from to val releasedm released_tgt ord lc2_tgt gl2_tgt
          (LC1: sim_local lc1_src lc1_tgt)
          (SC1: Global.sc gl1_src = Global.sc gl1_tgt)
          (MEM1: sim_memory rels (Global.memory gl1_src) (Global.memory gl1_tgt))
          (WRITES1: Writes.wf L rels (Global.memory gl1_src))
          (WF1_SRC: Local.wf lc1_src gl1_src)
          (WF1_TGT: Local.wf lc1_tgt gl1_tgt)
          (LOC: ~ L loc)
          (STEP_TGT: Local.write_step lc1_tgt gl1_tgt loc from to val releasedm released_tgt ord
                                      lc2_tgt gl2_tgt):
      exists released_src lc2_src gl2_src,
        (<<STEP_SRC: OrdLocal.write_step L Ordering.acqrel
                                         lc1_src gl1_src loc from to val releasedm released_src ord
                                         lc2_src gl2_src>>) /\
        (<<LC2: sim_local lc2_src lc2_tgt>>) /\
        (<<SC2: Global.sc gl2_src = Global.sc gl2_tgt>>) /\
        (<<MEM2: sim_memory rels (Global.memory gl2_src) (Global.memory gl2_tgt)>>).
    Proof.
      destruct (L loc) eqn:LOC'; try by congr.
      destruct lc1_src, lc1_tgt.
      inv LC1. inv STEP_TGT. ss.
      exploit add; try exact WRITE; eauto; try congr. i. des.
      esplits.
      - econs; [des_ifs|].
        econs; ss.
        { inv TVIEW. rewrite CUR. ss. }
        { eauto. }
        { erewrite sim_tview_write_released; eauto. congr. }
      - econs; ss.
        inv TVIEW. econs; ss; try congr.
        i. unfold LocFun.add.
        repeat (condtac; ss; eauto); subst; try congr.
        + specialize (REL loc0). des_ifs.
        + specialize (REL loc). des_ifs. rewrite REL. refl.
        + specialize (REL loc0). des_ifs.
      - ss.
      - ss.
    Qed.

    Lemma write_step_other
          rels lc1_src gl1_src
          lc1_tgt gl1_tgt loc from to val releasedm released_tgt ord lc2_tgt gl2_tgt
          (LC1: sim_local lc1_src lc1_tgt)
          (SC1: Global.sc gl1_src = Global.sc gl1_tgt)
          (MEM1: sim_memory rels (Global.memory gl1_src) (Global.memory gl1_tgt))
          (WRITES1: Writes.wf L rels (Global.memory gl1_src))
          (NORMAL_TVIEW1_SRC: Normal.normal_tview L (Local.tview lc1_src))
          (NORMAL_TVIEW1_TGT: Normal.normal_tview L (Local.tview lc1_tgt))
          (STABLE_TVIEW1_SRC: Stable.stable_tview L (Global.memory gl1_src) (Local.tview lc1_src))
          (NORMAL_MEM1_SRC: Normal.normal_memory L (Global.memory gl1_src))
          (NORMAL_MEM1_TGT: Normal.normal_memory L (Global.memory gl1_tgt))
          (STABLE_MEM1_SRC: Stable.stable_memory L rels (Global.memory gl1_src))
          (LC_WF1_SRC: Local.wf lc1_src gl1_src)
          (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
          (GL_WF1_SRC: Global.wf gl1_src)
          (GL_WF1_TGT: Global.wf gl1_tgt)
          (RELEASEDM_WF: View.opt_wf releasedm)
          (RELEASEDM_TS: Time.le (View.rlx (View.unwrap releasedm) loc) to)
          (RELEASEDM_CLOSED: Memory.closed_opt_view releasedm (Global.memory gl1_src))
          (RELEASEDM_NORMAL: Normal.normal_view L (View.unwrap releasedm))
          (RELEASEDM_STABLE: Stable.stable_view L (Global.memory gl1_src) (View.unwrap releasedm))
          (LOC: ~ L loc)
          (STEP_TGT: Local.write_step lc1_tgt gl1_tgt loc from to val releasedm released_tgt ord
                                      lc2_tgt gl2_tgt):
      exists released_src lc2_src gl2_src,
        (<<STEP_SRC: OrdLocal.write_step L Ordering.acqrel
                                         lc1_src gl1_src loc from to val releasedm released_src ord
                                         lc2_src gl2_src>>) /\
        (<<LC2: sim_local lc2_src lc2_tgt>>) /\
        (<<SC2: Global.sc gl2_src = Global.sc gl2_tgt>>) /\
        (<<MEM2: sim_memory rels (Global.memory gl2_src) (Global.memory gl2_tgt)>>) /\
        (<<NORMAL_TVIEW2_SRC: Normal.normal_tview L (Local.tview lc2_src)>>) /\
        (<<NORMAL_TVIEW2_TGT: Normal.normal_tview L (Local.tview lc2_tgt)>>) /\
        (<<STABLE_TVIEW2_SRC: Stable.stable_tview L (Global.memory gl2_src) (Local.tview lc2_src)>>) /\
        (<<NORMAL_MEM2_SRC: Normal.normal_memory L (Global.memory gl2_src)>>) /\
        (<<NORMAL_MEM2_TGT: Normal.normal_memory L (Global.memory gl2_tgt)>>) /\
        (<<STABLE_MEM2_SRC: Stable.stable_memory L rels (Global.memory gl2_src)>>).
    Proof.
      exploit sim_memory_stable_tview; try apply LC1; eauto. intro STABLE_TVIEW1_TGT.
      hexploit sim_memory_stable_memory; eauto. intro STABLE_MEM1_TGT.
      hexploit sim_memory_closed_opt_view_src; eauto. intro RELEASEDM_CLOSED_TGT.
      hexploit sim_memory_stable_view; eauto. intro RELEASEDM_STABLE_TGT.
      exploit write_step_other_aux; eauto. i. des.
      exploit Normal.write_step; try exact STEP_TGT; eauto. i. des.
      exploit Stable.write_step; try exact STEP_TGT; eauto.
      { erewrite <- sim_memory_writes_wf; eauto. }
      { ss. }
      i. des.
      dup STEP_SRC. inv STEP_SRC0. des_ifs.
      exploit Normal.write_step; try exact STEP; eauto. i. des.
      exploit Stable.write_step; try exact STEP; eauto; try congr. i. des.
      des_ifs. esplits; eauto.
    Qed.

    Lemma fence_step_aux
          rels
          lc1_src gl1_src
          lc1_tgt gl1_tgt ordr ordw lc2_tgt gl2_tgt
          (LC1: sim_local lc1_src lc1_tgt)
          (SC1: Global.sc gl1_src = Global.sc gl1_tgt)
          (MEM1: sim_memory rels (Global.memory gl1_src) (Global.memory gl1_tgt))
          (PROMISES1_SRC: Local.promises lc1_src = BoolMap.bot)
          (STEP_TGT: Local.fence_step lc1_tgt gl1_tgt ordr ordw lc2_tgt gl2_tgt):
      exists lc2_src gl2_src,
        (<<STEP_SRC: Local.fence_step lc1_src gl1_src ordr ordw lc2_src gl2_src>>) /\
        (<<LC2: sim_local lc2_src lc2_tgt>>) /\
        (<<SC2: Global.sc gl2_src = Global.sc gl2_tgt>>) /\
        (<<MEM2: sim_memory rels (Global.memory gl2_src) (Global.memory gl2_tgt)>>).
    Proof.
      destruct lc1_src, lc1_tgt, gl1_src, gl1_tgt. ss. subst.
      inv LC1. inv TVIEW. ss.
      inv STEP_TGT. ss.
      esplits.
      - econs; ss.
      - econs; ss. econs; ss; i.
        + repeat (condtac; ss); eauto; try rewrite ACQ; try rewrite CUR; try refl.
          * unfold TView.write_fence_sc, TView.read_fence_tview.
            rewrite ACQ, CUR. refl.
          * specialize (REL loc). rewrite COND in *. ss.
          * unfold TView.write_fence_sc, TView.read_fence_tview.
            rewrite ACQ, CUR. f_equal; refl.
          * specialize (REL loc). rewrite COND in *. ss.
        + repeat (condtac; ss); eauto.
          unfold TView.write_fence_sc.
          repeat (condtac; ss); congr.
        + repeat (condtac; ss); eauto; try congr.
          unfold TView.write_fence_sc.
          repeat (condtac; ss); congr.
      - unfold TView.write_fence_sc.
        repeat (condtac; ss); congr.
      - ss.
    Qed.

    Lemma fence_step
          rels lc1_src gl1_src
          lc1_tgt gl1_tgt ordr ordw lc2_tgt gl2_tgt
          (LC1: sim_local lc1_src lc1_tgt)
          (SC1: Global.sc gl1_src = Global.sc gl1_tgt)
          (MEM1: sim_memory rels (Global.memory gl1_src) (Global.memory gl1_tgt))
          (WRITES1: Writes.wf L rels (Global.memory gl1_src))
          (PROMISES1_SRC: Local.promises lc1_src = BoolMap.bot)
          (NORMAL_TVIEW1_SRC: Normal.normal_tview L (Local.tview lc1_src))
          (NORMAL_TVIEW1_TGT: Normal.normal_tview L (Local.tview lc1_tgt))
          (STABLE_TVIEW1_SRC: Stable.stable_tview L (Global.memory gl1_src) (Local.tview lc1_src))
          (STABLE_SC1_SRC: Stable.stable_timemap L (Global.memory gl1_src) (Global.sc gl1_src))
          (NORMAL_MEM1_SRC: Normal.normal_memory L (Global.memory gl1_src))
          (NORMAL_MEM1_TGT: Normal.normal_memory L (Global.memory gl1_tgt))
          (STABLE_MEM1_SRC: Stable.stable_memory L rels (Global.memory gl1_src))
          (LC_WF1_SRC: Local.wf lc1_src gl1_src)
          (LC_WF1_TGT: Local.wf lc1_tgt gl1_tgt)
          (STEP_TGT: Local.fence_step lc1_tgt gl1_tgt ordr ordw lc2_tgt gl2_tgt):
      exists lc2_src gl2_src,
        (<<STEP_SRC: Local.fence_step lc1_src gl1_src ordr ordw lc2_src gl2_src>>) /\
        (<<LC2: sim_local lc2_src lc2_tgt>>) /\
        (<<SC2: Global.sc gl2_src = Global.sc gl2_tgt>>) /\
        (<<MEM2: sim_memory rels (Global.memory gl2_src) (Global.memory gl2_tgt)>>) /\
        (<<NORMAL_TVIEW2_SRC: Normal.normal_tview L (Local.tview lc2_src)>>) /\
        (<<NORMAL_TVIEW2_TGT: Normal.normal_tview L (Local.tview lc2_tgt)>>) /\
        (<<STABLE_TVIEW2_SRC: Stable.stable_tview L (Global.memory gl2_src) (Local.tview lc2_src)>>) /\
        (<<STABLE_SC2_SRC: Stable.stable_timemap L (Global.memory gl2_src) (Global.sc gl2_src)>>) /\
        (<<NORMAL_MEM1_SRC: Normal.normal_memory L (Global.memory gl2_src)>>) /\
        (<<NORMAL_MEM1_TGT: Normal.normal_memory L (Global.memory gl2_tgt)>>) /\
        (<<STABLE_MEM1_SRC: Stable.stable_memory L rels (Global.memory gl2_src)>>).
    Proof.
      exploit sim_memory_stable_tview; try apply LC1; eauto. intro STABLE_TVIEW1_TGT.
      exploit fence_step_aux; eauto. i. des.
      exploit Normal.fence_step; try exact STEP_TGT; eauto. i. des.
      exploit Stable.fence_step; try exact STEP_TGT; eauto.
      { eapply sim_memory_stable_view; eauto.
        rewrite <- SC1. ss.
      }
      { erewrite <- sim_memory_writes_wf; eauto. }
      i. des.
      exploit Normal.fence_step; try exact STEP_SRC; eauto. i. des.
      exploit Stable.fence_step; try exact STEP_SRC; eauto. i. des.
      inv STEP_SRC. inv STEP_TGT. ss.
      esplits; eauto.
    Qed.

    Lemma failure_step
          lc1_src lc1_tgt
          (LC1: sim_local lc1_src lc1_tgt)
          (STEP_TGT: Local.failure_step lc1_tgt):
      <<STEP_SRC: Local.failure_step lc1_src>>.
    Proof.
      econs.
    Qed.

    Lemma is_racy
          rels lc1_src gl1_src
          lc1_tgt gl1_tgt loc to ord
          (LC1: sim_local lc1_src lc1_tgt)
          (MEM1: sim_memory rels (Global.memory gl1_src) (Global.memory gl1_tgt))
          (WRITES1: Writes.wf L rels (Global.memory gl1_src))
          (GPRM1_TGT: Global.promises gl1_tgt = BoolMap.bot)
          (NORMAL_TVIEW1_TGT: Normal.normal_tview L (Local.tview lc1_tgt))
          (STEP_TGT: Local.is_racy lc1_tgt gl1_tgt loc to ord):
      (<<LOC: ~ L loc>>) /\
      (<<STEP_SRC: Local.is_racy lc1_src gl1_src loc to ord>>) \/
      (exists to ordw,
          (<<LOC: L loc>>) /\
          (<<HIGHER: Time.lt (View.rlx (TView.cur (Local.tview lc1_src)) loc) to>>) /\
          (<<IN: List.In (loc, to, ordw) rels>>) /\
          __guard__ ((<<ORDW: Ordering.le ordw Ordering.na>>) \/
                     (<<ORD: Ordering.le ord Ordering.na>>))).
    Proof.
      unguard.
      inv LC1. inv TVIEW. inv MEM1. inv STEP_TGT.
      { rewrite GPRM1_TGT in *. ss. }
      exploit COMPLETE; eauto. i. des. inv MSG0.
      destruct (L loc) eqn:LOC.
      { right. destruct na.
        - exploit NA_WRITES; try exact GET; ss.
          { ii. subst. inv RACE. }
          i. esplits; try exact x0; eauto.
          rewrite CUR.
          inv NORMAL_TVIEW1_TGT. rewrite CUR0; ss.
        - destruct (Ordering.le Ordering.plain ord) eqn:ORD.
          { exploit MSG; ss. }
          inv WRITES1. exploit COMPLETE0; try exact GET_SRC; ss.
          { ii. subst. inv RACE. }
          i. des. esplits; eauto.
          + rewrite CUR.
            inv NORMAL_TVIEW1_TGT. rewrite CUR0; ss.
          + right. destruct ord; ss.
      }
      { left. split; ss. econs 2; eauto.
        rewrite CUR. ss.
      }
    Qed.

    Lemma racy_read_step
          rels lc1_src gl1_src
          lc1_tgt gl1_tgt loc to val ord
          (LC1: sim_local lc1_src lc1_tgt)
          (MEM1: sim_memory rels (Global.memory gl1_src) (Global.memory gl1_tgt))
          (WRITES1: Writes.wf L rels (Global.memory gl1_src))
          (GPRM1_TGT: Global.promises gl1_tgt = BoolMap.bot)
          (NORMAL_TVIEW1_TGT: Normal.normal_tview L (Local.tview lc1_tgt))
          (STEP_TGT: Local.racy_read_step lc1_tgt gl1_tgt loc to val ord):
      (<<LOC: ~ L loc>>) /\
      (<<STEP_SRC: Local.racy_read_step lc1_src gl1_src loc to val ord>>) \/
      (<<RACE: RARaceW.wr_race L rels (Local.tview lc1_src) loc ord>>).
    Proof.
      inv STEP_TGT.
      exploit is_racy; eauto. i. des.
      - left. splits; ss.
      - right. unfold RARaceW.wr_race. esplits; eauto.
        unguard. des.
        + left. destruct ordw; ss.
        + right. destruct ord; ss.
    Qed.

    Lemma racy_write_step
          rels lc1_src gl1_src
          lc1_tgt gl1_tgt loc to ord
          (LC1: sim_local lc1_src lc1_tgt)
          (MEM1: sim_memory rels (Global.memory gl1_src) (Global.memory gl1_tgt))
          (WRITES1: Writes.wf L rels (Global.memory gl1_src))
          (GPRM1_TGT: Global.promises gl1_tgt = BoolMap.bot)
          (NORMAL_TVIEW1_TGT: Normal.normal_tview L (Local.tview lc1_tgt))
          (STEP_TGT: Local.racy_write_step lc1_tgt gl1_tgt loc to ord):
      (<<LOC: ~ L loc>>) /\
      (<<STEP_SRC: Local.racy_write_step lc1_src gl1_src loc to ord>>) \/
      (<<RACE: RARaceW.ww_race L rels (Local.tview lc1_src) loc ord>>).
    Proof.
      inv STEP_TGT.
      exploit is_racy; eauto. i. des.
      - left. splits; ss.
      - right. unfold RARaceW.ww_race. esplits; eauto.
    Qed.

    Lemma racy_update_step
          rels lc1_src gl1_src
          lc1_tgt gl1_tgt loc to ordr ordw
          (LC1: sim_local lc1_src lc1_tgt)
          (MEM1: sim_memory rels (Global.memory gl1_src) (Global.memory gl1_tgt))
          (WRITES1: Writes.wf L rels (Global.memory gl1_src))
          (GPRM1_TGT: Global.promises gl1_tgt = BoolMap.bot)
          (NORMAL_TVIEW1_TGT: Normal.normal_tview L (Local.tview lc1_tgt))
          (STEP_TGT: Local.racy_update_step lc1_tgt gl1_tgt loc to ordr ordw):
      (<<LOC: ~ L loc>>) /\
      (<<STEP_SRC: Local.racy_update_step lc1_src gl1_src loc to ordr ordw>>) \/
      (<<RACE: RARaceW.wr_race L rels (Local.tview lc1_src) loc ordr>>) \/
      (<<NA_UPDATE: __guard__ (Ordering.le ordr Ordering.na \/ Ordering.le ordw Ordering.na)>>).
    Proof.
      unguard. inv STEP_TGT; eauto.
      exploit is_racy; eauto. i. des.
      - left. splits; ss. econs; eauto.
      - right. left. unfold RARaceW.wr_race. esplits; eauto.
        unguard. des.
        + left. destruct ordw0; ss.
        + right. destruct ordr; ss.
    Qed.


    Variant sim_event: forall (e_src e_tgt: ThreadEvent.t), Prop :=
    | sim_event_silent:
      sim_event ThreadEvent.silent ThreadEvent.silent
    | sim_event_read
        loc to val released_src released_tgt ord:
      sim_event (ThreadEvent.read loc to val released_src ord)
                (ThreadEvent.read loc to val released_tgt ord)
    | sim_event_write
        loc from to val released_src released_tgt ord:
      sim_event (ThreadEvent.write loc from to val released_src ord)
                (ThreadEvent.write loc from to val released_tgt ord)
    | sim_event_update
        loc from to valr valw releasedm_src releasedm_tgt released_src released_tgt ordr ordw:
      sim_event (ThreadEvent.update loc from to valr valw releasedm_src released_src ordr ordw)
                (ThreadEvent.update loc from to valr valw releasedm_tgt released_tgt ordr ordw)
    | sim_event_fence
        ordr ordw:
      sim_event (ThreadEvent.fence ordr ordw) (ThreadEvent.fence ordr ordw)
    | sim_event_syscall
        e:
      sim_event (ThreadEvent.syscall e) (ThreadEvent.syscall e)
    | sim_event_failure:
      sim_event ThreadEvent.failure ThreadEvent.failure
    | sim_event_racy_read
        loc to val ord:
      sim_event (ThreadEvent.racy_read loc to val ord)
                (ThreadEvent.racy_read loc to val ord)
    | sim_event_racy_write
        loc to val ord:
      sim_event (ThreadEvent.racy_write loc to val ord)
                (ThreadEvent.racy_write loc to val ord)
    | sim_event_racy_update
        loc to_src to_tgt valr valw ordr ordw:
      sim_event (ThreadEvent.racy_update loc to_src valr valw ordr ordw)
                (ThreadEvent.racy_update loc to_tgt valr valw ordr ordw)
    .
    Hint Constructors sim_event: core.

    Lemma sim_event_eq_program_event
          e_src e_tgt
          (SIM: sim_event e_src e_tgt):
      ThreadEvent.get_program_event e_src = ThreadEvent.get_program_event e_tgt.
    Proof.
      inv SIM; ss.
    Qed.

    Lemma thread_step
          rels e1_src e1_tgt
          e_tgt e2_tgt
          (SIM1: sim_thread rels e1_src e1_tgt)
          (WRITES1: Writes.wf L rels (Global.memory (Thread.global e1_src)))
          (PRM1_SRC: Local.promises (Thread.local e1_src) = BoolMap.bot)
          (GPRM1_TGT: Global.promises (Thread.global e1_tgt) = BoolMap.bot)
          (STABLE1_SRC: Stable.stable_thread L rels e1_src)
          (NORMAL1_SRC: Normal.normal_thread L e1_src)
          (NORMAL1_TGT: Normal.normal_thread L e1_tgt)
          (LC_WF1_SRC: Local.wf (Thread.local e1_src) (Thread.global e1_src))
          (LC_WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.global e1_tgt))
          (GL_WF1_SRC: Global.wf (Thread.global e1_src))
          (GL_WF1_TGT: Global.wf (Thread.global e1_tgt))
          (STEP_TGT: Thread.step e_tgt e1_tgt e2_tgt)
          (EVENT_TGT: ThreadEvent.is_program e_tgt):
      (exists e_src e2_src,
          (<<STEP_SRC: OrdThread.step L Ordering.acqrel Ordering.acqrel e_src e1_src e2_src>>) /\
          __guard__ (
              (<<SIM2: sim_thread (Writes.append L e_src rels) e2_src e2_tgt>>) /\
              (<<EVENT: sim_event e_src e_tgt>>) /\
              (<<STABLE2_SRC: Stable.stable_thread L (Writes.append L e_src rels) e2_src>>) /\
              (<<NORMAL2_SRC: Normal.normal_thread L e2_src>>) /\
              (<<NORMAL2_TGT: Normal.normal_thread L e2_tgt>>))) \/
      (<<RACE: RARaceW.ra_race L rels (Local.tview (Thread.local e1_src)) (ThreadEvent.get_program_event e_tgt)>>).
    Proof.
      destruct e1_src as [st1_src lc1_src gl1_src].
      destruct e1_tgt as [st1_tgt lc1_tgt gl1_tgt].
      inv SIM1. inv STABLE1_SRC. inv NORMAL1_SRC. inv NORMAL1_TGT. ss. subst.
      hexploit sim_memory_stable_tview; eauto; try apply LOCAL. intro STABLE_TVIEW1_TGT.
      hexploit sim_memory_stable_memory; eauto. intro STABLE_MEM1_TGT.
      inv STEP_TGT; inv LOCAL0; ss.

      - (* silent step *)
        left. esplits.
        + econs; [|econs 1]. eauto.
        + unguard. esplits; ss.

      - (* read step *)
        destruct (L loc) eqn:LOC.
        + exploit read_step_loc; eauto. i. unguardH x0. des.
          { left. esplits.
            - econs; [|econs 2]; eauto.
            - unguard. esplits; ss.
          }
          { right. left. esplits; ss. }
        + exploit read_step_other; eauto. i. des.
          left. esplits.
          * econs; [|econs 2]; eauto.
          * esplits; ss.

      - (* write step *)
        destruct (L loc) eqn:LOC.
        + hexploit write_step_loc; eauto; ss; try apply Time.bot_spec. i. des.
          left. esplits.
          * econs; [|econs 3]; eauto.
          * unguard. unfold Writes.append. ss. rewrite LOC.
            esplits; ss. econs; ss.
            inv STEP_SRC.
            exploit Local.write_step_future; try eapply STEP; eauto; try apply Time.bot_spec. i. des.
            inv STEP. ss.
            eapply Stable.future_stable_view; try exact STABLE_SC; eauto.
            { econs; s; apply GL_WF1_SRC. }
            { apply GL_FUTURE. }
        + hexploit write_step_other; eauto; ss; try congr.
          { apply Time.bot_spec. }
          { apply Stable.bot_stable_view. apply GL_WF1_SRC. }
          i. des. left. esplits.
          * econs; [|econs 3]; eauto.
          * unguard. unfold Writes.append. ss. rewrite LOC.
            esplits; ss. econs; ss. inv STEP_SRC.
            exploit Local.write_step_future; try exact STEP; eauto; try apply Time.bot_spec. i. des.
            inv STEP. ss.
            eapply Stable.future_stable_view; try exact STABLE_SC; eauto.
            { econs; s; apply GL_WF1_SRC. }
            { apply GL_FUTURE. }

      - (* update step *)
        destruct (L loc) eqn:LOC.
        + exploit read_step_loc; eauto. i. des.
          exploit Local.read_step_future; try exact LOCAL1; eauto. i. des.
          dup STEP_SRC. inv STEP_SRC0.
          exploit Local.read_step_future; try exact STEP; eauto. i. des.
          unguardH x1. des.
          * hexploit write_step_loc; try exact LOCAL2; try exact RELEASED_SRC; eauto.
            { inv LOCAL1. inv STEP. inv MEMORY.
              exploit SOUND; eauto. i. des.
              rewrite GET_TGT in *. inv GET. inv MSG.
              revert RELEASED. condtac; ss.
            }
            { destruct released_src; ss. inv STEP. eauto. }
            { destruct releasedr; ss. inv LOCAL1. eauto. }
            { etrans; eauto. inv LOCAL2. inv WRITE. inv ADD. timetac. }
            { etrans; eauto. inv LOCAL2. inv WRITE. inv ADD. timetac. }
            i. des. left. esplits.
            { econs; [|econs 4]; eauto. }
            { unguard. unfold Writes.append. ss. rewrite LOC in *.
              esplits; ss. econs; ss.
              inv STEP_SRC0. exploit Local.write_step_future; try exact STEP; eauto.
              { etrans; eauto. inv LOCAL2. inv WRITE. inv ADD. timetac. }
              i. des.
              inv STEP0. ss.
              eapply Stable.future_stable_view; try eapply STABLE_SC; ss.
              { econs; s; apply GL_WF1_SRC. }
              { apply GL_FUTURE. }
            }
          * right. left. esplits; ss.
        + exploit read_step_other; eauto. i. des.
          exploit Local.read_step_future; try exact LOCAL1; eauto. i. des.
          dup STEP_SRC. inv STEP_SRC0.
          exploit Local.read_step_future; try exact STEP; eauto. i. des.
          rewrite LOC in *.
          hexploit write_step_other; try exact LOCAL2; eauto; try congr.
          { etrans; eauto. inv LOCAL2. inv WRITE. inv ADD. timetac. }
          { inv STEP. destruct releasedr; ss. eauto. }
          { inv STEP. ss.
            destruct releasedr; ss.
            - eapply STABLE_MEMORY; eauto. left. congr.
            - apply Stable.bot_stable_view. apply GL_WF1_SRC.
          }
          i. des. left. esplits.
          * econs; [|econs 4]; eauto.
          * unguard. unfold Writes.append. ss. rewrite LOC.
            esplits; ss. econs; ss.
            inv STEP_SRC0.
            exploit Local.write_step_future; try exact STEP2; eauto.
            { etrans; eauto. inv LOCAL2. inv WRITE. inv ADD. timetac. }
            i. des.
            inv STEP0. ss.
            eapply Stable.future_stable_view; try eapply STABLE_SC; eauto.
            { econs; s; apply GL_WF1_SRC. }
            { apply GL_FUTURE. }

      - (* fence step *)
        exploit fence_step; try exact LOCAL1; eauto. i. des.
        left. esplits.
        + econs; [|econs 5]; eauto.
        + unguard. esplits; ss.

      - (* syscall step *)
        exploit fence_step; try exact LOCAL1; eauto. i. des.
        left. esplits.
        + econs; [|econs 6]; eauto.
        + unguard. esplits; ss.

      - (* failure step *)
        exploit failure_step; try exact LOCAL1; eauto. i. des.
        left. esplits.
        + econs; [|econs 7]; eauto.
        + unguard. esplits; ss.

      - (* racy read step *)
        exploit racy_read_step; try exact LOCAL1; eauto. i. des.
        + left. esplits.
          * econs; [|econs 8]; eauto.
          * unguard. esplits; ss.
        + right. left. esplits; eauto. ss.

      - (* racy write step *)
        exploit racy_write_step; try exact LOCAL1; eauto. i. des.
        + left. esplits.
          * econs; [|econs 9]; eauto.
          * unguard. esplits; ss.
        + right. right. esplits; eauto. ss.

      - (* racy update step *)
        exploit racy_update_step; try exact LOCAL1; eauto. i. des.
        + left. esplits.
          * econs; [|econs 10]; eauto.
          * unguard. esplits; ss.
        + right. left. esplits; eauto. ss.
        + left. esplits.
          * econs; [|econs 11]; eauto.
          * unguard. esplits; ss.
    Qed.
  End PFtoRASim.
End PFtoRASim.
