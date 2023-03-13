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

Require Import MaxView.
(* Require Import Delayed. *)

Require Import Lia.

Require Import SeqLift.
Require Import Sequential.

(* Require Import Pred. *)

Require Import SeqLiftStep.


Variant sim_thread_sol
        (c: bool)
        (vs: Loc.t -> Const.t)
        (P: Loc.t -> bool)
        (D: Loc.t -> bool)
        (mem: Global.t) (lc: Local.t): Prop :=
  | sim_thread_intro
      (DEBT: forall loc
                    (GET: lc.(Local.promises) loc = true),
          (<<DEBT: c = true -> D loc>>))
      (VALS: forall loc,
        exists from released na,
          (<<GET: Memory.get loc (lc.(Local.tview).(TView.cur).(View.rlx) loc) mem.(Global.memory) = Some (from, Message.message (vs loc) released na)>>))
      (PERM: forall loc val released (MAX: max_readable mem lc.(Local.promises) loc (lc.(Local.tview).(TView.cur).(View.pln) loc) val released),
          P loc)
.

(* Definition lowered_content (b: bool) (cnt0 cnt1: option (Time.t * Message.t)): Prop := *)
(*   (cnt0 = cnt1 /\ b = false) \/ *)
(*     cnt1 = match cnt0 with *)
(*            | Some (_, Message.reserve) | None => None *)
(*            | Some (from, Message.concrete val released) => Some (from, Message.concrete val None) *)
(*            end. *)

(* Lemma lowered_content_trans b0 b1 b2 cnt0 cnt1 cnt2 *)
(*       (LOWER0: lowered_content b0 cnt0 cnt1) *)
(*       (LOWER1: lowered_content b1 cnt1 cnt2) *)
(*       (BOOL: b0 = false -> b1 = false -> b2 =false) *)
(*   : *)
(*   lowered_content b2 cnt0 cnt2. *)
(* Proof. *)
(*   unfold lowered_content in *. des; subst; auto. *)
(*   right. des_ifs. *)
(* Qed. *)

(* Definition lowered_memory mem0 mem1: Prop := *)
(*   forall loc to, lowered_content false (Memory.get loc to mem0) (Memory.get loc to mem1). *)

(* Global Program Instance lowered_memory_PreOrder: PreOrder lowered_memory. *)
(* Next Obligation. *)
(* Proof. *)
(*   ii. left. auto. *)
(* Qed. *)
(* Next Obligation. *)
(* Proof. *)
(*   ii. specialize (H loc to). specialize (H0 loc to). *)
(*   eapply lowered_content_trans; eauto. *)
(* Qed. *)

(* Lemma lower_none_lowered_memory mem0 loc from to val released mem1 *)
(*       (LOWER: Memory.lower mem0 loc from to (Message.concrete val released) (Message.concrete val None) mem1) *)
(*   : *)
(*   lowered_memory mem0 mem1. *)
(* Proof. *)
(*   ii. erewrite (@Memory.lower_o mem1); eauto. des_ifs. *)
(*   { ss. des; clarify. right. *)
(*     eapply Memory.lower_get0 in LOWER. des. rewrite GET. ss. *)
(*   } *)
(*   { left. auto. } *)
(* Qed. *)

(* Lemma cancel_lowered_memory mem0 loc from to  mem1 *)
(*       (CANCEL: Memory.remove mem0 loc from to Message.reserve mem1) *)
(*   : *)
(*   lowered_memory mem0 mem1. *)
(* Proof. *)
(*   ii. erewrite (@Memory.remove_o mem1); eauto. des_ifs. *)
(*   { ss. des; clarify. right. *)
(*     eapply Memory.remove_get0 in CANCEL. des. rewrite GET. ss. *)
(*   } *)
(*   { left. auto. } *)
(* Qed. *)

(* Lemma nonsynch_all *)
(*       lang st *)
(*       tvw prom0 mem0 sc *)
(*       (LOCAL: Local.wf (Local.mk tvw prom0) mem0) *)
(*   : *)
(*   exists prom1 mem1, *)
(*     (<<STEPS: rtc (@Thread.tau_step lang) (Thread.mk _ st (Local.mk tvw prom0) sc mem0) (Thread.mk _ st (Local.mk tvw prom1) sc mem1)>>) /\ *)
(*       (<<NONE: forall loc to, *)
(*           Memory.get loc to prom1 = match Memory.get loc to prom0 with *)
(*                                     | Some (_, Message.reserve) | None => None *)
(*                                     | Some (from, Message.undef) => Some (from, Message.undef) *)
(*                                     | Some (from, Message.concrete val released) => Some (from, Message.concrete val None) *)
(*                                     end>>) /\ *)
(*       (<<MAX: forall loc val released, *)
(*           max_readable mem0 prom0 loc (tvw.(TView.cur).(View.pln) loc) val released *)
(*           <-> *)
(*             max_readable mem1 prom1 loc (tvw.(TView.cur).(View.pln) loc) val released>>) /\ *)
(*       (<<PRESERVE: forall loc to val released from *)
(*                           (GET: Memory.get loc to mem0 = Some (from, Message.concrete val released)), *)
(*         exists released', (<<GET: Memory.get loc to mem1 = Some (from, Message.concrete val released')>>)>>) *)
(* . *)
(* Proof. *)
(*   inv LOCAL. clear TVIEW_WF TVIEW_CLOSED. rename PROMISES into MLE. *)
(*   red in FINITE. des. *)
(*   cut (exists prom1 mem1, *)
(*              (<<STEPS: rtc (@Thread.tau_step lang) (Thread.mk _ st (Local.mk tvw prom0) sc mem0) (Thread.mk _ st (Local.mk tvw prom1) sc mem1)>>) /\ *)
(*                (<<NONE: forall loc to (IN: List.In (loc, to) dom), *)
(*                    lowered_content true (Memory.get loc to prom0) (Memory.get loc to prom1)>>) /\ *)
(*                (<<MAX: forall loc val released, *)
(*                    max_readable mem0 prom0 loc (tvw.(TView.cur).(View.pln) loc) val released *)
(*                    <-> *)
(*                      max_readable mem1 prom1 loc (tvw.(TView.cur).(View.pln) loc) val released>>) /\ *)
(*                (<<LOWERPROM: lowered_memory prom0 prom1>>) /\ *)
(*                (<<LOWERMEM: lowered_memory mem0 mem1>>)). *)
(*   { i. des. esplits; eauto. *)
(*     { i. specialize (NONE loc to). unfold lowered_content in *. *)
(*       destruct (Memory.get loc to prom0) as [[from msg]|] eqn:PROM. *)
(*       { hexploit NONE; eauto. i; des; ss. } *)
(*       { specialize (LOWERPROM loc to). rewrite PROM in LOWERPROM. *)
(*         red in LOWERPROM. des; auto. *)
(*       } *)
(*     } *)
(*     { i. specialize (LOWERMEM loc to). rewrite GET in LOWERMEM. des; eauto. *)
(*       red in LOWERMEM. des; eauto. *)
(*     } *)
(*   } *)
(*   clear FINITE. revert prom0 mem0 MLE BOT. induction dom. *)
(*   { i. esplits. *)
(*     { refl. } *)
(*     { i. ss. } *)
(*     { auto. } *)
(*     { refl. } *)
(*     { refl. } *)
(*   } *)
(*   i. destruct a as [loc to]. *)
(*   destruct (Memory.get loc to prom0) as [[from msg]|] eqn:GET. *)
(*   { destruct msg. *)
(*     { hexploit Memory.lower_exists. *)
(*       { eapply GET. } *)
(*       { hexploit memory_get_ts_strong; eauto. i. des; clarify. *)
(*         rewrite BOT in GET. ss. *)
(*       } *)
(*       { instantiate (1:=Message.concrete val None). econs; ss. } *)
(*       { econs; ss. refl. } *)
(*       i. des. *)
(*       hexploit Memory.lower_exists_le; eauto. i. des. *)
(*       assert (PROMISE: Memory.promise prom0 mem0 loc from to (Message.concrete val None) mem2 mem1 (Memory.op_kind_lower (Message.concrete val released))). *)
(*       { econs; eauto; ss. econs. eapply Time.bot_spec. } *)
(*       hexploit (IHdom mem2 mem1); eauto. *)
(*       { eapply promise_memory_le; eauto. } *)
(*       { eapply Memory.promise_bot_none; eauto. } *)
(*       i. des. esplits. *)
(*       { econs 2. *)
(*         { econs. *)
(*           { econs. econs 1. econs; eauto. } *)
(*           { ss. } *)
(*         } *)
(*         { eauto. } *)
(*       } *)
(*       { i. ss. des; clarify. *)
(*         { eapply lowered_content_trans. *)
(*           2:{ eapply LOWERPROM. } *)
(*           2:{ instantiate (1:=true). ss. } *)
(*           des; clarify. *)
(*           { rewrite GET. erewrite (@Memory.lower_o mem2); eauto. *)
(*             des_ifs; ss; des; clarify. right. auto. *)
(*           } *)
(*         } *)
(*         { eapply lowered_content_trans. *)
(*           2:{ eapply NONE; eauto. } *)
(*           2:{ instantiate (1:=false). ss. } *)
(*           eapply lower_none_lowered_memory; eauto. *)
(*         } *)
(*       } *)
(*       { i. etrans; [|eapply MAX]. destruct (Loc.eq_dec loc0 loc); subst. *)
(*         { eapply promise_max_readable; eauto. } *)
(*         { eapply promise_unchanged_loc in PROMISE; eauto. des. *)
(*           eapply unchanged_loc_max_readable; eauto. *)
(*         } *)
(*       } *)
(*       { etrans; eauto. eapply lower_none_lowered_memory; eauto. } *)
(*       { etrans; eauto. eapply lower_none_lowered_memory; eauto. } *)
(*     } *)
(*     { hexploit (IHdom prom0 mem0); eauto. i. des. esplits; eauto. *)
(*       i. ss. des; clarify. *)
(*       { eapply lowered_content_trans. *)
(*         2:{ eapply LOWERPROM. } *)
(*         2:{ instantiate (1:=true). ss. } *)
(*         rewrite GET. right. auto. *)
(*       } *)
(*       { eapply NONE; auto. } *)
(*     } *)
(*     { hexploit Memory.remove_exists. *)
(*       { eapply GET. } *)
(*       i. des. *)
(*       hexploit Memory.remove_exists_le; eauto. i. des. *)
(*       assert (PROMISE: Memory.promise prom0 mem0 loc from to Message.reserve mem2 mem1 (Memory.op_kind_cancel)). *)
(*       { econs; eauto; ss. } *)
(*       hexploit (IHdom mem2 mem1); eauto. *)
(*       { eapply promise_memory_le; eauto. } *)
(*       { eapply Memory.promise_bot_none; eauto. } *)
(*       i. des. esplits. *)
(*       { econs 2. *)
(*         { econs. *)
(*           { econs. econs 1. econs; eauto. } *)
(*           { ss. } *)
(*         } *)
(*         { eauto. } *)
(*       } *)
(*       { i. ss. des; clarify. *)
(*         { eapply lowered_content_trans. *)
(*           2:{ eapply LOWERPROM. } *)
(*           2:{ instantiate (1:=true). ss. } *)
(*           des; clarify. *)
(*           { rewrite GET. erewrite (@Memory.remove_o mem2); eauto. *)
(*             des_ifs; ss; des; clarify. right. auto. *)
(*           } *)
(*         } *)
(*         { eapply lowered_content_trans. *)
(*           2:{ eapply NONE; eauto. } *)
(*           2:{ instantiate (1:=false). ss. } *)
(*           eapply cancel_lowered_memory; eauto. *)
(*         } *)
(*       } *)
(*       { i. etrans; [|eapply MAX]. destruct (Loc.eq_dec loc0 loc); subst. *)
(*         { eapply promise_max_readable; eauto. } *)
(*         { eapply promise_unchanged_loc in PROMISE; eauto. des. *)
(*           eapply unchanged_loc_max_readable; eauto. *)
(*         } *)
(*       } *)
(*       { etrans; eauto. eapply cancel_lowered_memory; eauto. } *)
(*       { etrans; eauto. eapply cancel_lowered_memory; eauto. } *)
(*     } *)
(*   } *)
(*   { hexploit (IHdom prom0 mem0); eauto. i. des. esplits; eauto. *)
(*     i. ss. des; clarify. *)
(*     { eapply lowered_content_trans. *)
(*       2:{ eapply LOWERPROM. } *)
(*       2:{ instantiate (1:=true). ss. } *)
(*       rewrite GET. right. auto. *)
(*     } *)
(*     { eapply NONE; auto. } *)
(*   } *)
(* Qed. *)

Lemma sim_thread_sim_thread_sol
      c D f flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt lc_src0 lc_tgt
      (SIM: sim_thread
              f flag_src flag_tgt vs_src vs_tgt
              mem_src0 mem_tgt lc_src0 lc_tgt)
      (BOT: c = true -> lc_tgt.(Local.promises) = BoolMap.bot)
      (DEBT: forall loc (TGT: flag_src loc = false) (DEBT: D loc = false), flag_tgt loc = false)
      (WF: Mapping.wfs f)
      (LOCAL: Local.wf lc_src0 mem_src0)
  :
  exists vs,
    (<<SIM: sim_thread_sol c vs (fun loc => vs_src loc) D mem_src0 lc_src0>>) /\
      (<<VALS: forall loc val (VAL: vs_src loc = Some val), vs loc = val>>)
.
Proof.
  hexploit (choice (fun loc val =>
                      exists from released na,
                        (<<GET: Memory.get loc (lc_src0.(Local.tview).(TView.cur).(View.rlx) loc) mem_src0.(Global.memory) = Some (from, Message.message val released na)>>))).
  { inv LOCAL. inv TVIEW_CLOSED. inv CUR.
    intros loc. hexploit (RLX loc). i. des. eauto.
  }
  intros [vs VALS]. inv SIM.
  destruct lc_src0 as [tvw_src prom_src0 rsv_src].
  exists vs. esplits.
  { econs; eauto.
    { inv LOCAL0. ii. ss. subst. inv PROMISES.
      destruct (flag_src loc) eqn:EQS.
      { erewrite FLAGSRC0 in GET; ss. }
      destruct (D loc) eqn:EQD; ss.
      hexploit NOFLAG; eauto.
      rewrite BOT; auto. rewrite GET. ss.
    }
    { i. ss. ss. hexploit (MAXSRC loc). i. inv H.
      destruct (vs_src loc) eqn:VAL; ss.
      exfalso. eapply NONMAX; eauto.
    }
  }
  { i. hexploit (MAXSRC loc). i. inv H.
    hexploit (VALS loc). i.
    hexploit MAX; eauto. i. des. ss. inv MAX0.
    assert (TS: View.pln (TView.cur tvw_src) loc = View.rlx (TView.cur tvw_src) loc).
    { eapply TimeFacts.antisym.
      { eapply LOCAL. }
      destruct (Time.le_lt_dec (View.rlx (TView.cur tvw_src) loc) (View.pln (TView.cur tvw_src) loc)); auto.
      exfalso. eapply MAX1 in l; eauto; ss.
    }
    rewrite TS in *. clarify.
  }
Qed.

Lemma sim_thread_none
      vs P D mem lc
      (SIM: sim_thread_sol true vs P D mem lc)
      (DEBT: forall loc, D loc = false)
  :
  lc.(Local.promises) = BoolMap.bot.
Proof.
  extensionality loc.
  inv SIM. destruct (lc.(Local.promises) loc) eqn:GET; auto.
  exploit DEBT0; eauto.
Qed.

Lemma sim_thread_sol_failure
      c vs P D mem lc
      (SIM: sim_thread_sol c vs P D mem lc)
  :
  Local.failure_step lc.
Proof.
  inv SIM. econs.
Qed.

Lemma sim_thread_sol_fence
      c vs P D mem0 lc0 ordr ordw
      (SIM: sim_thread_sol c vs P D mem0 lc0)
      (ORDR: ~ Ordering.le Ordering.acqrel ordr)
      (ORDW: ~ Ordering.le Ordering.seqcst ordw)
  :
  exists lc1 mem1,
    (<<FENCE: Local.fence_step lc0 mem0 ordr ordw lc1 mem1>>) /\
    (<<SIM: sim_thread_sol c vs P D mem1 lc1>>)
.
Proof.
  inv SIM. esplits.
  { econs; eauto.
    { i. destruct ordw; ss. }
  }
  econs; eauto; ss.
  { ii. des_ifs. }
  { ii. des_ifs. eapply PERM; eauto. inv MAX. econs; eauto. }
Qed.

Lemma sim_thread_sol_racy
      c vs P D mem lc loc
      (SIM: sim_thread_sol c vs P D mem lc)
      (LOCAL: Local.wf lc mem)
      (ORD: ~ P loc)
  :
  exists to, Local.is_racy lc mem loc to Ordering.na.
Proof.
  inv SIM. destruct lc.
  hexploit non_max_readable_race; eauto.
Qed.

Lemma sim_thread_sol_read_na_racy
      c vs P D mem lc loc
      (SIM: sim_thread_sol c vs P D mem lc)
      (LOCAL: Local.wf lc mem)
      (ORD: ~ P loc)
      val
  :
  exists to, Local.racy_read_step lc mem loc to val Ordering.na.
Proof.
  exploit sim_thread_sol_racy; eauto. i. des.
  esplits. eauto.
Qed.

Lemma sim_thread_sol_write_na_racy
      c vs P D mem lc loc
      (SIM: sim_thread_sol c vs P D mem lc)
      (LOCAL: Local.wf lc mem)
      (ORD: ~ P loc)
  :
  exists to, Local.racy_write_step lc mem loc to Ordering.na.
Proof.
  exploit sim_thread_sol_racy; eauto. i. des.
  esplits. econs; eauto.
Qed.

Lemma sim_thread_sol_read_na
      c vs P D mem lc loc val
      (SIM: sim_thread_sol c vs P D mem lc)
      (LOCAL: Local.wf lc mem)
      (VAL: Const.le val (vs loc))
  :
  exists ts released,
    (<<READ: Local.read_step lc mem loc ts val released Ordering.na lc>>)
.
Proof.
  inv SIM. hexploit (VALS loc); eauto. i. des.
  esplits. econs; eauto.
  { econs; ss. eapply LOCAL. }
  destruct lc. f_equal. ss. unfold TView.read_tview. des_ifs.
  ss. rewrite ! View.join_bot_r. rewrite ! View.le_join_l.
  { destruct tview; auto. }
  { eapply View.singleton_rw_spec.
    { eapply LOCAL. }
    { eapply LOCAL. }
  }
  { eapply View.singleton_rw_spec.
    { eapply LOCAL. }
    { refl. }
  }
Qed.

Lemma sim_thread_sol_read
      c vs P D mem lc0 loc ord val
      (SIM: sim_thread_sol c vs P D mem lc0)
      (LOCAL: Local.wf lc0 mem)
      (ORD: ~ Ordering.le Ordering.acqrel ord)
      (VAL: Const.le val (vs loc))
  :
  exists ts released lc1,
    (<<READ: Local.read_step lc0 mem loc ts val released ord lc1>>) /\
    (<<SIM: sim_thread_sol c vs (fun loc0 => if (Loc.eq_dec loc0 loc) then true else P loc0) D mem lc1>>)
.
Proof.
  inv SIM. hexploit (VALS loc); eauto. i. des.
  esplits. econs; eauto.
  { econs; ss.
    { eapply LOCAL. }
    { i. refl. }
  }
  destruct lc0 as [tvw0 prom]. ss.
  set (tvw1 := (TView.read_tview
                  tvw0 loc
                  (View.rlx (TView.cur tvw0) loc) released ord)).
  assert (OTHERPLN: forall loc0 (NEQ: loc0 <> loc),
             tvw1.(TView.cur).(View.pln) loc0 = tvw0.(TView.cur).(View.pln) loc0).
  { i. ss. des_ifs. ss. rewrite timemap_bot_join_r.
    unfold TimeMap.join. eapply TimeFacts.le_join_l.
    unfold View.singleton_ur_if. des_ifs; ss.
    { rewrite timemap_singleton_neq; auto. eapply Time.bot_spec. }
    { eapply Time.bot_spec. }
  }
  assert (RLX: forall loc0, tvw1.(TView.cur).(View.rlx) loc0 = tvw0.(TView.cur).(View.rlx) loc0).
  { i. ss. des_ifs. ss. rewrite timemap_bot_join_r.
    unfold TimeMap.join. eapply TimeFacts.le_join_l.
    unfold View.singleton_ur_if. des_ifs; ss.
    { eapply TimeMap.singleton_spec. refl. }
    { eapply TimeMap.singleton_spec. refl. }
  }
  remember tvw1. clear tvw1 Heqt.
  econs; eauto; ss.
  { i. rewrite RLX. eauto. }
  { i. destruct (Loc.eq_dec loc0 loc); auto.
    rewrite OTHERPLN in MAX; eauto.
  }
Qed.

Lemma sim_thread_sol_write_na
      c vs P D mem0 lc0 loc val
      (SIM: sim_thread_sol c vs P D mem0 lc0)
      (LOCAL: Local.wf lc0 mem0)
      (MEM: Global.wf mem0)
  :
  (exists to, Local.racy_write_step lc0 mem0 loc to Ordering.na)
  \/
  exists lc1 mem1 from to,
    (<<WRITE: Local.write_step lc0 mem0 loc from to val None None Ordering.na lc1 mem1>>) /\
    (<<SIM: sim_thread_sol c (fun loc0 => if Loc.eq_dec loc0 loc then val else vs loc0) (fun loc0 => if (Loc.eq_dec loc0 loc) then true else P loc0) (fun loc0 => if (Loc.eq_dec loc0 loc) then false else D loc0) mem1 lc1>>)
.
Proof.
  destruct lc0 as [tvw0 prom0 rsv0].
  destruct (classic (exists val released, <<MAX: max_readable mem0 prom0 loc (tvw0.(TView.cur).(View.pln) loc) val released>>)).
  2:{ left. inv SIM.
      exploit non_max_readable_race; eauto. i. des. eauto. }
  right. des.
  inv SIM.
  assert (FULFILL: Promises.fulfill prom0 mem0.(Global.promises) loc Ordering.na (LocFun.add loc false prom0) (LocFun.add loc false mem0.(Global.promises))).
  { destruct (prom0 loc) eqn:EQ.
    { econs 2; eauto. econs; eauto. eapply LOCAL in EQ. auto. }
    { replace (LocFun.add loc false prom0) with prom0.
      2:{ extensionality loc0. rewrite loc_fun_add_spec. des_ifs. }
      replace (LocFun.add loc false mem0.(Global.promises)) with mem0.(Global.promises); auto.
      { extensionality loc0. rewrite loc_fun_add_spec. des_ifs.
        destruct (mem0.(Global.promises) loc) eqn:EQP; ss.
        inv MAX. rewrite EQP in *. rewrite EQ in *. ss.
      }
    }
  }
  hexploit max_readable_write; eauto.
  { refl. }
  { eapply Time.incr_spec. }
  i. des. esplits.
  { inv MAX. unfold implb in NONE. des_ifs. }
  i. des. esplits; eauto.
  assert (OTHERPLN: forall loc0 (NEQ: loc0 <> loc),
             tvw1.(TView.cur).(View.pln) loc0 = tvw0.(TView.cur).(View.pln) loc0).
  { inv WRITE. i. ss. des_ifs. ss.
    unfold TimeMap.join. eapply TimeFacts.le_join_l.
    rewrite timemap_singleton_neq; auto. eapply Time.bot_spec.
  }
  assert (OTHERRLX: forall loc0 (NEQ: loc0 <> loc),
             tvw1.(TView.cur).(View.rlx) loc0 = tvw0.(TView.cur).(View.rlx) loc0).
  { inv WRITE. i. ss. des_ifs. ss.
    unfold TimeMap.join. eapply TimeFacts.le_join_l.
    rewrite timemap_singleton_neq; auto. eapply Time.bot_spec.
  }
  assert (SAMERLX: tvw1.(TView.cur).(View.rlx) loc = tvw1.(TView.cur).(View.pln) loc).
  { rewrite VIEWPLN. rewrite VIEWRLX. auto. }
  econs.
  { ii. ss. rewrite loc_fun_add_spec in GET. des_ifs. eapply DEBT; eauto. }
  { ii. ss. des_ifs.
    { rewrite SAMERLX. rewrite VIEWPLN. inv MAX0. eauto. }
    { erewrite Memory.add_o; eauto. des_ifs.
      { ss. des; clarify. }
      clear o. rewrite OTHERRLX; auto.
    }
  }
  { i. ss. des_ifs.
    inv WRITE. clarify. eapply add_unchanged_loc in WRITE0; eauto.
    eapply promises_fulfill_unchanged_loc in FULFILL; eauto. des.
    rewrite OTHERPLN in MAX1; auto.
    eapply PERM. eapply unchanged_loc_max_readable; [..|eauto].
    { econs; eauto. }
    { eauto. }
  }
Qed.

Lemma write_tview_other_rlx
      tvw loc ts ord loc0
      (NEQ: loc0 <> loc)
  :
  (TView.write_tview tvw loc ts ord).(TView.cur).(View.rlx) loc0 = tvw.(TView.cur).(View.rlx) loc0.
Proof.
  ss. des_ifs. ss.
  unfold TimeMap.join. eapply TimeFacts.le_join_l.
  rewrite timemap_singleton_neq; auto. eapply Time.bot_spec.
Qed.

Lemma write_tview_other_pln
      tvw loc ts ord loc0
      (NEQ: loc0 <> loc)
  :
  (TView.write_tview tvw loc ts ord).(TView.cur).(View.pln) loc0 = tvw.(TView.cur).(View.pln) loc0.
Proof.
  ss. des_ifs. ss.
  unfold TimeMap.join. eapply TimeFacts.le_join_l.
  rewrite timemap_singleton_neq; auto. eapply Time.bot_spec.
Qed.

Lemma write_tview_same_pln
      tvw loc ts ord
      (WRITABLE: TView.writable tvw.(TView.cur) loc ts ord)
      (TVIEW: TView.wf tvw)
  :
  (TView.write_tview tvw loc ts ord).(TView.cur).(View.pln) loc = ts.
Proof.
  ss. unfold TimeMap.join.
  rewrite timemap_singleton_eq; auto. eapply TimeFacts.le_join_r.
  transitivity (View.rlx (TView.cur tvw) loc).
  { eapply TVIEW. }
  { left. eapply WRITABLE. }
Qed.

Lemma write_tview_same_rlx
      tvw loc ts ord
      (WRITABLE: TView.writable tvw.(TView.cur) loc ts ord)
  :
  (TView.write_tview tvw loc ts ord).(TView.cur).(View.rlx) loc = ts.
Proof.
  ss. unfold TimeMap.join.
  rewrite timemap_singleton_eq; auto. eapply TimeFacts.le_join_r.
  left. eapply WRITABLE.
Qed.

Lemma sim_thread_sol_write
      c vs P D mem0 lc0 loc ord val
      (SIM: sim_thread_sol c vs P D mem0 lc0)
      (LOCAL: Local.wf lc0 mem0)
      (MEM: Global.wf mem0)
  :
  (<<RACE: Local.racy_write_step lc0 mem0 loc None ord>>) \/
  exists lc1 mem1 from to released,
    (<<WRITE: Local.write_step lc0 mem0 loc from to val None released ord lc1 mem1>>) /\
    (<<SIM: sim_thread_sol c (fun loc0 => if Loc.eq_dec loc0 loc then val else vs loc0) (fun loc0 => if (Loc.eq_dec loc0 loc) then true else P loc0) D mem1 lc1>>)
.
Proof.
  destruct (classic (Local.racy_write_step lc0 mem0 loc None ord)); auto. right.
  destruct lc0 as [tvw0 prom0 rsv0].
  inv SIM. hexploit max_readable_write; eauto.
  { refl. }
  { eapply Time.incr_spec. }
  { instantiate (1:=loc). i. destruct (prom0 loc) eqn:EQ; eauto. }
  i. des. esplits.
  { eauto. }
  assert (OTHERPLN: forall loc0 (NEQ: loc0 <> loc),
             tvw1.(TView.cur).(View.pln) loc0 = tvw0.(TView.cur).(View.pln) loc0).
  { inv WRITE. i. ss. des_ifs. ss.
    unfold TimeMap.join. eapply TimeFacts.le_join_l.
    rewrite timemap_singleton_neq; auto. eapply Time.bot_spec.
  }
  assert (OTHERRLX: forall loc0 (NEQ: loc0 <> loc),
             tvw1.(TView.cur).(View.rlx) loc0 = tvw0.(TView.cur).(View.rlx) loc0).
  { inv WRITE. i. ss. des_ifs. ss.
    unfold TimeMap.join. eapply TimeFacts.le_join_l.
    rewrite timemap_singleton_neq; auto. eapply Time.bot_spec.
  }
  assert (SAMERLX: tvw1.(TView.cur).(View.rlx) loc = tvw1.(TView.cur).(View.pln) loc).
  { rewrite VIEWPLN. rewrite VIEWRLX. auto. }
  econs.
  { ii. ss. eapply DEBT; eauto. }
  { ii. ss. des_ifs.
    { rewrite SAMERLX. rewrite VIEWPLN. inv MAX. eauto. }
    { erewrite Memory.add_o; eauto. des_ifs.
      { ss. des; clarify. }
      clear o. rewrite OTHERRLX; auto.
    }
  }
  { i. ss. des_ifs.
    inv WRITE. clarify. eapply add_unchanged_loc in WRITE0; eauto.
    eapply promises_fulfill_unchanged_loc in FULFILL; eauto. des.
    rewrite OTHERPLN in MAX0; auto.
    eapply PERM. eapply unchanged_loc_max_readable; [..|eauto].
    { econs; eauto. }
    { eauto. }
  }
Qed.
