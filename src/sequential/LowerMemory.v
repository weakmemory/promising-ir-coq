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
Require Import Thread.
Require Import Configuration.
Require Import BoolMap.
Require Import Promises.
Require Import Global.

Require Import Cover.
(* Require Import MemorySplit. *)
(* Require Import MemoryMerge. *)
(* Require Import FulfillStep. *)
Require Import MemoryProps.

Set Implicit Arguments.

Definition is_promise (e: ThreadEvent.t): Prop :=
  match e with
  | ThreadEvent.promise _ => True
  | ThreadEvent.reserve _ _ _ => True
  | ThreadEvent.cancel _ _ _ => True
  | _ => False
  end.

Variant lower_event: forall (e_src e_tgt: ThreadEvent.t), Prop :=
| lower_event_promise
    loc
  :
  lower_event
    (ThreadEvent.promise loc)
    (ThreadEvent.promise loc)
| lower_event_reserve
    loc from to
  :
  lower_event
    (ThreadEvent.reserve loc from to)
    (ThreadEvent.reserve loc from to)
| lower_event_cancel
    loc from to
  :
  lower_event
    (ThreadEvent.cancel loc from to)
    (ThreadEvent.cancel loc from to)
| lower_event_silent
  :
  lower_event
    ThreadEvent.silent
    ThreadEvent.silent
| lower_event_read
    loc ts val released_src released_tgt ord
    (RELEASED: View.opt_le released_src released_tgt)
  :
  lower_event
    (ThreadEvent.read loc ts val released_src ord)
    (ThreadEvent.read loc ts val released_tgt ord)
| lower_event_write
    loc from to val released_src released_tgt ord
    (RELEASED: View.opt_le released_src released_tgt)
  :
  lower_event
    (ThreadEvent.write loc from to val released_src ord)
    (ThreadEvent.write loc from to val released_tgt ord)
| lower_event_update
    loc tsr tsw valr valw releasedr_src releasedr_tgt releasedw_src releasedw_tgt ordr ordw
    (RELEASEDR: View.opt_le releasedr_src releasedr_tgt)
    (RELEASEDW: View.opt_le releasedw_src releasedw_tgt)
  :
  lower_event
    (ThreadEvent.update loc tsr tsw valr valw releasedr_src releasedw_src ordr ordw)
    (ThreadEvent.update loc tsr tsw valr valw releasedr_tgt releasedw_tgt ordr ordw)
| lower_event_fence
    ordr ordw
  :
  lower_event
    (ThreadEvent.fence ordr ordw)
    (ThreadEvent.fence ordr ordw)
| lower_event_syscall
    e
  :
  lower_event
    (ThreadEvent.syscall e)
    (ThreadEvent.syscall e)
| lower_event_failure
  :
  lower_event
    ThreadEvent.failure
    ThreadEvent.failure
| lower_event_racy_read
    loc to_src to_tgt val ord
  :
  lower_event
    (ThreadEvent.racy_read loc to_src val ord)
    (ThreadEvent.racy_read loc to_tgt val ord)
| lower_event_racy_write
    loc to_src to_tgt val ord
  :
  lower_event
    (ThreadEvent.racy_write loc to_src val ord)
    (ThreadEvent.racy_write loc to_tgt val ord)
| lower_event_racy_update
    loc to_src to_tgt valr valw ordr ordw
  :
  lower_event
    (ThreadEvent.racy_update loc to_src valr valw ordr ordw)
    (ThreadEvent.racy_update loc to_tgt valr valw ordr ordw)
.
#[export] Hint Constructors lower_event: core.


Global Program Instance lower_event_PreOrder: PreOrder lower_event.
Next Obligation. ii. destruct x; try (econs; eauto); refl. Qed.
Next Obligation. ii. inv H; inv H0; econs; eauto; etrans; eauto. Qed.

Lemma lower_event_program_event
      e_src e_tgt
      (EVENT: lower_event e_src e_tgt):
  ThreadEvent.get_program_event e_src = ThreadEvent.get_program_event e_tgt.
Proof.
  inv EVENT; ss.
Qed.

Lemma lower_event_machine_event
      e_src e_tgt
      (EVENT: lower_event e_src e_tgt):
  ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt.
Proof.
  inv EVENT; ss.
Qed.

Variant lower_memory_content: forall (cnt_src cnt_tgt: option (Loc.t * Message.t)), Prop :=
| lower_memory_content_none
  :
    lower_memory_content None None
| lower_memory_content_some
    from msg_src msg_tgt
    (MESSAGE: Message.le msg_src msg_tgt \/ msg_tgt = Message.reserve)
  :
    lower_memory_content (Some (from, msg_src)) (Some (from, msg_tgt))
.

Global Program Instance lower_memory_content_PreOrder: PreOrder lower_memory_content.
Next Obligation.
Proof.
  ii. destruct x as [[]|]; econs. left. refl.
Qed.
Next Obligation.
Proof.
  ii. inv H; inv H0; econs. des; auto.
  { left. etrans; eauto. }
  { subst. inv MESSAGE0; auto. }
Qed.


Variant lower_memory (mem_src mem_tgt: Memory.t): Prop :=
| lower_memory_intro
    (LOWER: forall loc to, lower_memory_content (Memory.get loc to mem_src) (Memory.get loc to mem_tgt))
.

Global Program Instance lower_memory_PreOrder: PreOrder lower_memory.
Next Obligation.
Proof.
  ii. econs. i. refl.
Qed.
Next Obligation.
Proof.
  ii. inv H. inv H0. econs. i. etrans; eauto.
Qed.

Variant lower_global (gl_src gl_tgt: Global.t): Prop :=
| lower_global_intro
    (ADDNA: Global.na_added_latest gl_tgt gl_src)
    (SC: TimeMap.le gl_src.(Global.sc) gl_tgt.(Global.sc))
    (MEM: lower_memory gl_src.(Global.memory) gl_tgt.(Global.memory))
.

Global Program Instance lower_global_PreOrder: PreOrder lower_global.
Next Obligation.
Proof.
  ii. econs; try refl. econs. i. left. rewrite Bool.implb_same. auto.
Qed.
Next Obligation.
Proof.
  ii. inv H. inv H0. econs.
  2:{ etrans; eauto. }
  2:{ etrans; eauto. }
  { destruct x, y, z. ss.
    econs. i. ss. destruct (promises1 loc) eqn:PRM2.
    { destruct (promises loc) eqn:PRM0.
      { left. ss. }
      right. destruct (promises0 loc) eqn:PRM1; auto.
      { inv ADDNA. ss. hexploit ADDNA1; eauto.
        rewrite PRM1. rewrite PRM0. i.
        des; ss. rr in LATEST. des. rr. esplits; eauto.
        i. inv MEM0. hexploit (LOWER loc ts1). i.
        rewrite GET0 in H. inv H. des; ss. inv MESSAGE. eapply LATEST0; eauto.
      }
      { inv ADDNA0. ss. hexploit ADDNA1; eauto.
        rewrite PRM2. rewrite PRM1. i.
        des; ss. rr in LATEST. des. rr.
        inv MEM. hexploit (LOWER loc ts2). i.
        rewrite GET in H. inv H. des; ss. inv MESSAGE. destruct na1; ss. esplits; eauto.
      }
    }
    econs; etrans; eauto.
  }
Qed.

Variant lower_local: forall (lc_src lc_tgt: Local.t), Prop :=
| lower_local_intro
    tvw_src tvw_tgt prom_src prom_tgt rsv
    (TVIEW: TView.le tvw_src tvw_tgt)
    (PROMISES: BoolMap.le prom_src prom_tgt)
  :
    lower_local (Local.mk tvw_src prom_src rsv) (Local.mk tvw_tgt prom_tgt rsv)
.

Global Program Instance lower_local_PreOrder: PreOrder lower_local.
Next Obligation.
Proof.
  ii. destruct x. econs; eauto. refl.
Qed.
Next Obligation.
Proof.
  ii. inv H; inv H0. econs; eauto. etrans; eauto.
Qed.

Variant lower_thread {lang: language} (e_src e_tgt: Thread.t lang): Prop :=
| lower_thread_intro
    (STATE: Thread.state e_src = Thread.state e_tgt)
    (LOCAL: lower_local (Thread.local e_src) (Thread.local e_tgt))
    (GLOBAL: lower_global (Thread.global e_src) (Thread.global e_tgt))
.

Global Program Instance lower_thread_PreOrder {lang: language}: PreOrder (@lower_thread lang).
Next Obligation.
Proof.
  ii. destruct x. econs; ss; refl.
Qed.
Next Obligation.
Proof.
  ii. destruct x, y, z. inv H. inv H0. ss. subst.
  econs; ss; eauto; etrans; eauto.
Qed.

Lemma lower_memory_get mem_src mem_tgt
      (MEM: lower_memory mem_src mem_tgt)
      loc from to msg_tgt
      (GETTGT: Memory.get loc to mem_tgt = Some (from, msg_tgt))
  :
    exists msg_src,
      (<<GETSRC: Memory.get loc to mem_src = Some (from, msg_src)>>) /\
      (<<MESSAGE: Message.le msg_src msg_tgt \/ msg_tgt = Message.reserve>>).
Proof.
  inv MEM. specialize (LOWER loc to). rewrite GETTGT in *.
  inv LOWER. eauto.
Qed.

Lemma lower_memory_get_inv mem_src mem_tgt
      (MEM: lower_memory mem_src mem_tgt)
      loc from to msg_src
      (GETSRC: Memory.get loc to mem_src = Some (from, msg_src))
  :
    exists msg_tgt,
      (<<GETTGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)>>) /\
      (<<MESSAGE: Message.le msg_src msg_tgt \/ msg_tgt = Message.reserve>>).
Proof.
  inv MEM. specialize (LOWER loc to). rewrite GETSRC in *.
  inv LOWER. eauto.
Qed.

Lemma lower_memory_closed_timemap mem_src mem_tgt
      (MEM: lower_memory mem_src mem_tgt)
      tm
      (CLOSED: Memory.closed_timemap tm mem_tgt)
  :
    Memory.closed_timemap tm mem_src.
Proof.
  ii. specialize (CLOSED loc). des.
  hexploit lower_memory_get; eauto. i. des; ss. inv MESSAGE. esplits; eauto.
Qed.

Lemma lower_memory_closed_view mem_src mem_tgt
      (MEM: lower_memory mem_src mem_tgt)
      vw
      (CLOSED: Memory.closed_view vw mem_tgt)
  :
    Memory.closed_view vw mem_src.
Proof.
  inv CLOSED. econs.
  { eapply lower_memory_closed_timemap; eauto. }
  { eapply lower_memory_closed_timemap; eauto. }
Qed.

Lemma lower_memory_closed_opt_view mem_src mem_tgt
      (MEM: lower_memory mem_src mem_tgt)
      vw
      (CLOSED: Memory.closed_opt_view vw mem_tgt)
  :
    Memory.closed_opt_view vw mem_src.
Proof.
  inv CLOSED; econs.
  eapply lower_memory_closed_view; eauto.
Qed.

Lemma lower_memory_closed_message mem_src mem_tgt
      (MEM: lower_memory mem_src mem_tgt)
      msg
      (CLOSED: Memory.closed_message msg mem_tgt)
  :
    Memory.closed_message msg mem_src.
Proof.
  inv CLOSED; econs.
  eapply lower_memory_closed_opt_view; eauto.
Qed.

Lemma lower_memory_add mem_src0 mem_tgt0
      (MEM: lower_memory mem_src0 mem_tgt0)
      loc from to msg_src msg_tgt mem_tgt1
      (ADD: Memory.add mem_tgt0 loc from to msg_tgt mem_tgt1)
      (MSG: Message.le msg_src msg_tgt)
      (WF: Message.wf msg_tgt -> Message.wf msg_src)
  :
    exists mem_src1,
      (<<ADD: Memory.add mem_src0 loc from to msg_src mem_src1>>) /\
      (<<MEM: lower_memory mem_src1 mem_tgt1>>).
Proof.
  hexploit add_succeed_wf; eauto. i. des.
  hexploit (@Memory.add_exists mem_src0 loc from to msg_src); eauto.
  { i. hexploit lower_memory_get_inv; eauto. i. des; eauto. }
  i. des. esplits; eauto. econs. i.
  erewrite (@Memory.add_o mem2); eauto. erewrite (@Memory.add_o mem_tgt1); eauto. des_ifs.
  { des; clarify. econs; eauto. }
  { eapply MEM. }
Qed.

Lemma lower_memory_remove mem_src0 mem_tgt0
      (MEM: lower_memory mem_src0 mem_tgt0)
      loc from to msg_src msg_tgt mem_tgt1 mem_src1
      (REMOVETGT: Memory.remove mem_tgt0 loc from to msg_tgt mem_tgt1)
      (REMOVESRC: Memory.remove mem_src0 loc from to msg_src mem_src1)
  :
    lower_memory mem_src1 mem_tgt1.
Proof.
  econs. i.
  erewrite (@Memory.remove_o mem_src1); eauto. erewrite (@Memory.remove_o mem_tgt1); eauto. des_ifs.
  { econs. }
  { eapply MEM. }
Qed.

Lemma lower_memory_promise_step gl_src0 gl_tgt0 loc
      (MEM: lower_global gl_src0 gl_tgt0)
      lc_src0 lc_tgt0 lc_tgt1 gl_tgt1
      (STEP: Local.promise_step lc_tgt0 gl_tgt0 loc lc_tgt1 gl_tgt1)
      (LOCAL: lower_local lc_src0 lc_tgt0)
      (WF: Local.wf lc_src0 gl_src0)
  :
    exists gl_src1 lc_src1,
      ((<<STEP: Local.promise_step lc_src0 gl_src0 loc lc_src1 gl_src1>>) \/ (<<EQ: lc_src1 = lc_src0 /\ gl_src1 = gl_src0>>))/\
      (<<LOCAL: lower_local lc_src1 lc_tgt1>>) /\
      (<<MEM: lower_global gl_src1 gl_tgt1>>).
Proof.
  inv LOCAL. inv STEP.
  { inv MEM. ss. inv PROMISE.
    destruct (gl_src0.(Global.promises) loc) eqn:SRC.
    { esplits.
      { right. eauto. }
      { econs; eauto. etrans; eauto. eapply BoolMap.add_le; eauto. }
      { econs; eauto.
        econs. i; ss. inv ADDNA.
        hexploit ADDNA0; eauto. i. des; eauto.
        left. erewrite BoolMap.add_o; eauto. des_ifs.
      }
    }
    { hexploit BoolMap.add_exists; eauto. i. des.
      hexploit bool_map_le_exists.
      { eauto. }
      { eapply WF. }
      i. des. esplits.
      { left. econs; eauto. }
      { ss. econs; eauto. eapply BoolMap.le_add; eauto. }
      { econs; eauto. econs. i. ss.
        inv ADDNA. hexploit ADDNA0; eauto. i. des; eauto.
        left. erewrite (@BoolMap.add_o gprm2); eauto.
        erewrite (@BoolMap.add_o bm2); eauto. des_ifs.
      }
    }
  }
Qed.

Lemma lower_memory_reserve_step gl_src0 gl_tgt0 loc from to
      (MEM: lower_global gl_src0 gl_tgt0)
      lc_src0 lc_tgt0 lc_tgt1 gl_tgt1
      (STEP: Local.reserve_step lc_tgt0 gl_tgt0 loc from to lc_tgt1 gl_tgt1)
      (LOCAL: lower_local lc_src0 lc_tgt0)
      (WF: Local.wf lc_src0 gl_src0)
  :
    exists gl_src1 lc_src1,
      (<<STEP: Local.reserve_step lc_src0 gl_src0 loc from to lc_src1 gl_src1>>) /\
      (<<LOCAL: lower_local lc_src1 lc_tgt1>>) /\
      (<<MEM: lower_global gl_src1 gl_tgt1>>).
Proof.
  inv LOCAL. inv STEP.
  { inv RESERVE. ss. inv MEM.
    hexploit lower_memory_add; eauto. i. des. esplits.
    { econs; eauto. }
    { econs; eauto. }
    { econs; eauto. econs. i; ss.
      inv ADDNA. exploit ADDNA0; eauto. i. des; eauto.
      right. rr in LATEST. des. rr. esplits.
      { eapply Memory.add_get1; eauto. }
      { i. erewrite Memory.add_o in GET0; eauto. des_ifs. eauto. }
    }
  }
Qed.

Lemma lower_memory_cancel_step gl_src0 gl_tgt0 loc from to
      (MEM: lower_global gl_src0 gl_tgt0)
      lc_src0 lc_tgt0 lc_tgt1 gl_tgt1
      (STEP: Local.cancel_step lc_tgt0 gl_tgt0 loc from to lc_tgt1 gl_tgt1)
      (LOCAL: lower_local lc_src0 lc_tgt0)
      (WF: Local.wf lc_src0 gl_src0)
  :
    exists gl_src1 lc_src1,
      (<<STEP: Local.cancel_step lc_src0 gl_src0 loc from to lc_src1 gl_src1>>) /\
      (<<LOCAL: lower_local lc_src1 lc_tgt1>>) /\
      (<<MEM: lower_global gl_src1 gl_tgt1>>).
Proof.
  inv LOCAL. inv STEP.
  { inv CANCEL. ss. inv MEM.
    hexploit Memory.remove_exists; eauto.
    { eapply WF. eapply Memory.remove_get0 in RSV. des; eauto. }
    i. des. esplits.
    { econs; eauto. }
    { econs; eauto. }
    { econs; eauto.
      { econs. i; ss.
        inv ADDNA. exploit ADDNA0; eauto. i. des; eauto.
        right. rr in LATEST. des.
        eapply Memory.remove_get1 in GET; eauto. des; clarify.
        rr. esplits; eauto. i.
        erewrite Memory.remove_o in GET0; eauto. des_ifs. eauto.
      }
      { eapply lower_memory_remove; eauto. }
    }
  }
Qed.

Lemma lower_memory_internal_step gl_src0 gl_tgt0 e
      (MEM: lower_global gl_src0 gl_tgt0)
      lc_src0 lc_tgt0 lc_tgt1 gl_tgt1
      (STEP: Local.internal_step e lc_tgt0 gl_tgt0 lc_tgt1 gl_tgt1)
      (LOCAL: lower_local lc_src0 lc_tgt0)
      (WF: Local.wf lc_src0 gl_src0)
  :
    exists gl_src1 lc_src1,
      ((<<STEP: Local.internal_step e lc_src0 gl_src0 lc_src1 gl_src1>>) \/ (<<EQ: lc_src1 = lc_src0 /\ gl_src1 = gl_src0>>))/\
      (<<LOCAL: lower_local lc_src1 lc_tgt1>>) /\
      (<<MEM: lower_global gl_src1 gl_tgt1>>).
Proof.
  inv STEP.
  { hexploit lower_memory_promise_step; eauto. i. des; eauto.
    { esplits; try eassumption. left. eauto. }
    { esplits; try eassumption. right. eauto. }
  }
  { hexploit lower_memory_reserve_step; eauto. i. des; eauto.
    esplits; try eassumption. left. eauto.
  }
  { hexploit lower_memory_cancel_step; eauto. i. des; eauto.
    esplits; try eassumption. left. eauto.
  }
Qed.

Lemma lower_memory_read_step gl_src0 gl_tgt0
      (MEM: lower_global gl_src0 gl_tgt0)
      lc_src0 lc_tgt0 loc to val released_tgt ord lc_tgt1
      (STEP: Local.read_step lc_tgt0 gl_tgt0 loc to val released_tgt ord lc_tgt1)
      (LOCAL: lower_local lc_src0 lc_tgt0)
      (CLOSED: Global.wf gl_src0)
  :
    exists lc_src1 released_src,
      (<<STEP: Local.read_step lc_src0 gl_src0 loc to val released_src ord lc_src1>>) /\
      (<<LOCAL: lower_local lc_src1 lc_tgt1>>) /\
      (<<RELEASED: View.opt_le released_src released_tgt>>) /\
      (<<RELWF: View.opt_wf released_src>>)
.
Proof.
  inv LOCAL. inv MEM. inv STEP. hexploit lower_memory_get; eauto.
  i. des; ss. inv MESSAGE.
  hexploit TViewFacts.readable_mon; eauto.
  { eapply TVIEW. }
  { refl. }
  i. esplits; eauto.
  { econs; eauto. etrans; eauto. }
  { econs; eauto. ss. eapply read_tview_mon; eauto. refl. }
  { eapply CLOSED in GETSRC. des. inv MSG_WF. auto. }
Qed.

Lemma lower_memory_fence_step
      lc_src0 lc_tgt0 ordr ordw lc_tgt1 gl_tgt0 gl_tgt1 gl_src0
      (STEP: Local.fence_step lc_tgt0 gl_tgt0 ordr ordw lc_tgt1 gl_tgt1)
      (LOCAL: lower_local lc_src0 lc_tgt0)
      (SC: lower_global gl_src0 gl_tgt0)
  :
    exists lc_src1 gl_src1,
      (<<STEP: Local.fence_step lc_src0 gl_src0 ordr ordw lc_src1 gl_src1>>) /\
      (<<LOCAL: lower_local lc_src1 lc_tgt1>>) /\
      (<<SC: lower_global gl_src1 gl_tgt1>>)
.
Proof.
  inv LOCAL. inv STEP. esplits.
  { econs; ss. i. hexploit PROMISES0; eauto. i. subst.
    eapply BoolMap.antisym; auto.
    eapply BoolMap.bot_spec.
  }
  { econs; ss. eapply write_fence_tview_mon_same_ord; eauto.
    { eapply SC. }
    eapply read_fence_tview_mon_same_ord; eauto. }
  { inv SC. econs; ss.
    { inv ADDNA. econs; eauto. }
    { eapply write_fence_fc_mon_same_ord; eauto.
      eapply read_fence_tview_mon_same_ord; eauto. }
  }
Qed.

Lemma lower_memory_write_step gl_src0 gl_tgt0
      (MEM: lower_global gl_src0 gl_tgt0)
      lc_src0 lc_tgt0 loc from to val releasedr_tgt releasedw_tgt ord lc_tgt1 gl_tgt1
      releasedr_src
      (STEP: Local.write_step lc_tgt0 gl_tgt0 loc from to val releasedr_tgt releasedw_tgt ord lc_tgt1 gl_tgt1)
      (LOCAL: lower_local lc_src0 lc_tgt0)
      (WFSRC: Local.wf lc_src0 gl_src0)
      (WFTGT: Local.wf lc_tgt0 gl_tgt0)
      (RELSRC: View.opt_wf releasedr_src)
      (RELTGT: View.opt_wf releasedr_tgt)
      (RELEASEDR: View.opt_le releasedr_src releasedr_tgt)
  :
    (exists lc_src1 gl_src1 releasedw_src,
      (<<STEP: Local.write_step lc_src0 gl_src0 loc from to val releasedr_src releasedw_src ord lc_src1 gl_src1>>) /\
      (<<MEM: lower_global gl_src1 gl_tgt1>>) /\
      (<<LOCAL: lower_local lc_src1 lc_tgt1>>) /\
      (<<RELEASEDW: View.opt_le releasedw_src releasedw_tgt>>))
    \/
    (exists ts, <<RACE: Local.is_racy lc_src0 gl_src0 loc ts ord>>)
.
Proof.
  destruct (classic (exists ts, <<RACE: Local.is_racy lc_src0 gl_src0 loc ts ord>>)) as [RACE|NRACE]; auto.
  inv LOCAL. inv STEP.
  hexploit TViewFacts.writable_mon; eauto.
  { eapply TVIEW. }
  { refl. }
  i. ss. hexploit lower_memory_add; try eassumption.
  { eapply MEM. }
  { econs; [refl| |eapply Bool.implb_same].
    eapply TViewFacts.write_released_mon; eauto.
    { eapply WFTGT. }
    { refl. }
  }
  { i. ss. econs. eapply TViewFacts.write_future0; eauto. eapply WFSRC. }
  i. des. inv FULFILL.
  { left. esplits.
    { econs; eauto. }
    { inv MEM. econs; eauto.
      econs. i; ss.
      inv ADDNA. hexploit (ADDNA0 loc0); eauto. i. des; eauto.
      right. rr in LATEST. rr. des. esplits.
      { eapply Memory.add_get1; eauto. }
      { i. erewrite Memory.add_o in GET0; eauto. des_ifs; eauto.
        ss. des; clarify. exfalso. eapply NRACE. esplits. econs 2.
        { eauto. }
        2:{ auto. }
        ss. r. eapply TimeFacts.le_lt_lt.
        { eapply TVIEW. }
        inv WFTGT. inv TVIEW_CLOSED. inv CUR. exploit PLN; eauto. i. des; ss.
        eapply LATEST0; eauto.
      }
    }
    { econs; eauto. eapply TViewFacts.write_tview_mon; eauto.
      { eapply WFTGT. }
      { refl. }
    }
    { eapply TViewFacts.write_released_mon; eauto.
      { eapply WFTGT. }
      { refl. }
    }
  }
  destruct (prom_src loc) eqn:EQ.
  { hexploit BoolMap.remove_exists; eauto. i. des.
    hexploit BoolMap.remove_exists.
    { eapply WFSRC. eapply EQ. }
    i. des. left. esplits.
    { econs; [| |econs 2|..]; eauto. }
    { inv MEM. econs; eauto. econs. i; ss.
      erewrite (@BoolMap.remove_o gprm2); eauto.
      erewrite (@BoolMap.remove_o bm0); eauto. condtac; auto.
      inv ADDNA. hexploit ADDNA0; eauto. i. des; eauto.
      right. rr in LATEST. rr. des. esplits.
      { eapply Memory.add_get1; eauto. }
      { i. erewrite Memory.add_o in GET0; eauto. revert GET0. condtac.
        { ss. des; ss. }
        i. eauto.
      }
    }
    { econs; eauto. eapply TViewFacts.write_tview_mon; eauto.
      { eapply WFTGT. }
      { eapply BoolMap.le_remove; eauto. }
    }
    { eapply TViewFacts.write_released_mon; eauto.
      { eapply WFTGT. }
    }
  }
  { left. esplits.
    { econs; eauto. }
    { inv MEM. econs; eauto.
      econs. i; ss. erewrite (@BoolMap.remove_o gprm2); eauto. condtac; auto.
      inv ADDNA. hexploit (ADDNA0 loc0); eauto. i. des; eauto.
      right. rr in LATEST. rr. des. esplits.
      { eapply Memory.add_get1; eauto. }
      { i. erewrite Memory.add_o in GET0; eauto. revert GET0. condtac.
        { des; ss. }
        eauto.
      }
    }
    { econs; eauto. eapply TViewFacts.write_tview_mon; eauto.
      { eapply WFTGT. }
      { ii. ss. erewrite (@BoolMap.remove_o prm2); [|eauto].
        condtac; auto. subst. rewrite EQ in LHS. ss.
      }
    }
    { eapply TViewFacts.write_released_mon; eauto.
      { eapply WFTGT. }
    }
  }
Qed.

Lemma lower_memory_is_racy gl_src0 gl_tgt0
      (MEM: lower_global gl_src0 gl_tgt0)
      lc_src0 lc_tgt0
      loc to_tgt ord
      (RACE: Local.is_racy lc_tgt0 gl_tgt0 loc to_tgt ord)
      (LOCAL: lower_local lc_src0 lc_tgt0)
      (WFTGT: Local.wf lc_tgt0 gl_tgt0)
  :
    exists to_src, <<RACY: Local.is_racy lc_src0 gl_src0 loc to_src ord>>.
Proof.
  inv LOCAL. inv MEM. inv RACE.
  { inv ADDNA. hexploit ADDNA0; eauto. i. des.
    { exists None. econs 1.
      { rewrite GET in PROMISES0. destruct (gl_src0.(Global.promises) loc); ss. }
      { ss. specialize (PROMISES loc). destruct (prom_src loc) eqn:EQ; auto.
        rewrite PROMISES in GETP; auto.
      }
    }
    rr in LATEST. des. esplits. econs 2; eauto.
    ss. r. eapply TimeFacts.le_lt_lt.
    { eapply TVIEW. }
    inv WFTGT. inv TVIEW_CLOSED. inv CUR. exploit PLN; eauto. i. des; ss.
    eapply LATEST0; eauto.
  }
  { hexploit lower_memory_get; eauto. i. des; ss. inv MESSAGE.
    hexploit TViewFacts.racy_view_mon; eauto.
    { eapply TVIEW. }
    i. exists (Some to). econs; eauto.
    i. hexploit MSG; auto. i. subst. destruct na1; auto.
  }
Qed.

Lemma lower_memory_program_step gl_src0 gl_tgt0
      (MEM: lower_global gl_src0 gl_tgt0)
      lc_src0 lc_tgt0 lc_tgt1 gl_tgt1
      e_tgt
      (STEP: Local.program_step e_tgt lc_tgt0 gl_tgt0 lc_tgt1 gl_tgt1)
      (LOCAL: lower_local lc_src0 lc_tgt0)
      (WFSRC: Local.wf lc_src0 gl_src0)
      (WFTGT: Local.wf lc_tgt0 gl_tgt0)
      (CLOSEDSRC: Global.wf gl_src0)
      (CLOSEDTGT: Global.wf gl_tgt0)
  :
    (exists e_src lc_src1 gl_src1,
      (<<STEP: Local.program_step e_src lc_src0 gl_src0 lc_src1 gl_src1>>) /\
      (<<MEM: lower_global gl_src1 gl_tgt1>>) /\
      (<<LOCAL: lower_local lc_src1 lc_tgt1>>) /\
      (<<EVENT: lower_event e_src e_tgt>>)) \/
    (exists e_race,
      <<STEP: Local.program_step e_race lc_src0 gl_src0 lc_src0 gl_src0>> /\
      <<EVENT: ThreadEvent.get_program_event e_race = ThreadEvent.get_program_event e_tgt>> /\
      <<RACE: ThreadEvent.get_machine_event e_race = MachineEvent.failure>>)
.
Proof.
  inv STEP.
  { left. esplits; eauto. }
  { left. hexploit lower_memory_read_step; eauto. i. des.
     eexists (ThreadEvent.read _ _ _ _ _). esplits; eauto. }
  { hexploit lower_memory_write_step; eauto. i. des.
    { left. eexists (ThreadEvent.write _ _ _ _ _ _). esplits; eauto. }
    { right. eexists (ThreadEvent.racy_write _ _ _ _). esplits; eauto. ss. }
  }
  { hexploit lower_memory_read_step; eauto. i. des.
    hexploit Local.read_step_future; try apply LOCAL1; eauto. i. des.
    hexploit Local.read_step_future; try apply STEP; eauto. i. des.
    hexploit lower_memory_write_step; eauto. i. des.
    { left. eexists (ThreadEvent.update _ _ _ _ _ _ _ _ _). esplits; eauto. }
    { right. destruct (Ordering.le ordw Ordering.na) eqn:ORD.
      { eexists (ThreadEvent.racy_update _ _ _ _ _ _). esplits; eauto; ss. }
      eexists (ThreadEvent.racy_update _ _ _ _ _ _). esplits; eauto; ss.
      econs. inv LOCAL1. inv STEP. inv RACE.
      { instantiate (1:=ts). econs 3; eauto. }
      { econs 3; eauto. econs.
        { eauto. }
        { eapply TViewFacts.racy_view_mon; eauto. eapply TVIEW_FUTURE0. }
        { i. eapply MSG. destruct ordw; ss. }
      }
    }
  }
  { hexploit lower_memory_fence_step; eauto. i. des.
    left. eexists (ThreadEvent.fence _ _). esplits; eauto. }
  { hexploit lower_memory_fence_step; eauto. i. des.
    left. eexists (ThreadEvent.syscall _). esplits; eauto. }
  { inv LOCAL0.
    left. eexists (ThreadEvent.failure). esplits; eauto. }
  { inv LOCAL0. hexploit lower_memory_is_racy; eauto. i. des.
    left. eexists (ThreadEvent.racy_read _ _ _ _). esplits; eauto. }
  { inv LOCAL0. hexploit lower_memory_is_racy; eauto. i. des.
    left. eexists (ThreadEvent.racy_write _ _ _ _). esplits; eauto. }
  { inv LOCAL0.
    { left. eexists (ThreadEvent.racy_update _ _ _ _ ordr ordw). esplits; eauto. }
    { left. eexists (ThreadEvent.racy_update _ _ _ _ ordr ordw). esplits; eauto. }
    { hexploit lower_memory_is_racy; eauto. i. des.
      right. eexists (ThreadEvent.racy_update _ _ _ _ ordr ordw). esplits; eauto. ss. }
  }
Qed.

Lemma lower_thread_step
      lang e1_src
      e_tgt e1_tgt e2_tgt
      (LOWER: @lower_thread lang e1_src e1_tgt)
      (STEP: Thread.step e_tgt e1_tgt e2_tgt)
      (WFSRC: Local.wf (Thread.local e1_src) (Thread.global e1_src))
      (WFTGT: Local.wf (Thread.local e1_tgt) (Thread.global e1_tgt))
      (CLOSEDSRC: Global.wf (Thread.global e1_src))
      (CLOSEDTGT: Global.wf (Thread.global e1_tgt))
  :
  (exists e_src e2_src,
      ((<<STEP: Thread.step e_src e1_src e2_src>>) \/ ((<<EQ: e2_src = e1_src>>) /\ (<<SILENT: ThreadEvent.get_machine_event e_tgt = MachineEvent.silent>>) /\ (<<PROMISE: is_promise e_tgt>>))) /\
        (<<EVENT: lower_event e_src e_tgt>>) /\
        (<<LOWER: lower_thread e2_src e2_tgt>>)) \/
    (exists e_race e2_src,
        (<<STEP: Thread.step e_race e1_src e2_src>>) /\
          (<<EVENT: ThreadEvent.get_program_event e_race = ThreadEvent.get_program_event e_tgt>>) /\
          (<<RACE: ThreadEvent.get_machine_event e_race = MachineEvent.failure>>))
.
Proof.
  destruct e1_src, e1_tgt, e2_tgt. inv LOWER. ss. subst.
  inv STEP.
  { hexploit lower_memory_internal_step; eauto. i. des.
    { left. esplits.
      { left. econs 1; eauto. }
      { refl. }
      { econs; eauto. }
    }
    { subst. left. esplits.
      { right. splits; eauto.
        { inv LOCAL0; ss. }
        { inv LOCAL0; ss. }
      }
      { refl. }
      { econs; eauto. }
    }
  }
  i.
  exploit lower_memory_program_step;
    try exact LOCAL; try exact SC; try exact MEMORY; eauto. i. des.
  { left. esplits.
    { left. econs 2; [|eauto]. erewrite lower_event_program_event; eauto. }
    { auto. }
    { econs; eauto. }
  }
  { right. esplits.
    { econs 2; [|eauto]. rewrite EVENT. eauto. }
    { eauto. }
    { eauto. }
  }
Qed.

Lemma lower_memory_max_ts
      mem_src mem_tgt
      (LOWER: lower_memory mem_src mem_tgt)
      (MEM_SRC: Memory.inhabited mem_src)
      (MEM_TGT: Memory.inhabited mem_tgt):
  forall loc, Memory.max_ts loc mem_src = Memory.max_ts loc mem_tgt.
Proof.
  i.
  exploit Memory.max_ts_spec; try eapply MEM_SRC.
  instantiate (1:=loc). i. des.
  exploit Memory.max_ts_spec; try eapply MEM_TGT.
  instantiate (1:=loc). i. des.
  inv LOWER.
  generalize (LOWER0 loc (Memory.max_ts loc mem_src)).
  rewrite GET. i. inv H. clear MESSAGE. symmetry in H3.
  exploit Memory.max_ts_spec; try eapply H3. i. des.
  generalize (LOWER0 loc (Memory.max_ts loc mem_tgt)).
  rewrite GET0. i. inv H. clear MESSAGE. symmetry in H1.
  exploit Memory.max_ts_spec; try eapply H1. i. des.
  apply TimeFacts.antisym; eauto.
Qed.

Lemma lower_memory_cap
      mem_src mem_tgt
      cap_src cap_tgt
      (LOWER: lower_memory mem_src mem_tgt)
      (MEM_SRC: Memory.closed mem_src)
      (MEM_TGT: Memory.closed mem_tgt)
      (CAP_SRC: Memory.cap mem_src cap_src)
      (CAP_TGT: Memory.cap mem_tgt cap_tgt):
  lower_memory cap_src cap_tgt.
Proof.
  dup LOWER. inv LOWER. rename LOWER1 into LOWER. econs. i.
  destruct (Memory.get loc to cap_src) as [[from msg]|] eqn:GET_SRC.
  { inv CAP_TGT.
    exploit Memory.cap_inv; try exact CAP_SRC; eauto. i. des.
    - generalize (LOWER loc to). rewrite x0. i. inv H.
      exploit SOUND; eauto. intros x. rewrite x. econs. ss.
    - subst. inv x1.
      exploit (MIDDLE loc from1 from to to2); eauto; cycle 1.
      { i. rewrite x1. econs. auto. }
      generalize (LOWER loc from). rewrite GET1. i. inv H.
      generalize (LOWER loc to2). rewrite GET2. i. inv H.
      econs; eauto. i.
      exploit EMPTY; eauto. intros x.
      generalize (LOWER loc ts). rewrite x. i. inv H. ss.
    - subst.
      erewrite lower_memory_max_ts; eauto; try apply MEM_SRC; try apply MEM_TGT.
      inv MEM_TGT. specialize (INHABITED loc). eapply Memory.max_ts_spec in INHABITED. des.
      erewrite BACK; eauto. econs. auto.
  }
  { destruct (Memory.get loc to cap_tgt) as [[from msg]|] eqn:GET_TGT; try by econs.
    exfalso. inv CAP_SRC.
    exploit Memory.cap_inv; try exact CAP_TGT; eauto. i. des.
    - generalize (LOWER loc to). rewrite x0. i. inv H.
      exploit SOUND; eauto. intros x. rewrite x in *. ss.
    - subst. inv x1.
      exploit (MIDDLE loc from1 from to to2); eauto; cycle 1.
      { i. rewrite x1 in *. ss. }
      generalize (LOWER loc from). rewrite GET1. i. inv H.
      generalize (LOWER loc to2). rewrite GET2. i. inv H.
      econs; eauto. i.
      exploit EMPTY; eauto. intros x.
      generalize (LOWER loc ts). rewrite x. i. inv H. ss.
    - subst.
      erewrite <- lower_memory_max_ts in GET_SRC; eauto;
        try apply MEM_SRC; try apply MEM_TGT.
      inv MEM_SRC. specialize (INHABITED loc). eapply Memory.max_ts_spec in INHABITED. des.
      erewrite BACK in GET_SRC; ss. eauto.
  }
Qed.

Lemma lower_global_cap
      gl_src gl_tgt
      (LOWER: lower_global gl_src gl_tgt)
      (MEM_SRC: Global.wf gl_src)
      (MEM_TGT: Global.wf gl_tgt):
  lower_global (Global.cap_of gl_src) (Global.cap_of gl_tgt).
Proof.
  hexploit (@Global.cap_of_cap gl_src); eauto. i. des.
  hexploit (@Global.cap_of_cap gl_tgt); eauto. i. des.
  inv LOWER. econs; ss.
  { econs. inv ADDNA. i. hexploit (ADDNA0 loc). i. ss. des.
    { left. auto. }
    { right. rr in LATEST. des. rr. esplits.
      { eapply Memory.cap_le; eauto. }
      { i. hexploit Memory.cap_inv; eauto. i. des; ss.
        eapply LATEST0; eauto.
      }
    }
  }
  { eapply lower_memory_cap; eauto.
    { eapply MEM_SRC. }
    { eapply MEM_TGT. }
  }
Qed.
