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
Require Import Global.
Require Import TView.
Require Import Local.
Require Import Thread.

Require Import ITreeLang.

Set Implicit Arguments.


Lemma progress_read_step
      lc1 gl1
      loc ord
      (LC_WF1: Local.wf lc1 gl1):
  exists val released lc2,
    <<READ: Local.read_step lc1 gl1 loc ((TView.cur (Local.tview lc1)).(View.rlx) loc) val released ord lc2>>.
Proof.
  dup LC_WF1. inv LC_WF0. inv TVIEW_CLOSED. inv CUR.
  specialize (RLX loc). des.
  esplits. econs; eauto; try refl.
  econs; try apply TVIEW_WF; try refl.
Qed.

Lemma progress_read_step_plain
      lc1 gl1
      loc ord
      (LC_WF1: Local.wf lc1 gl1)
      (ORD: Ordering.le ord Ordering.plain):
  exists val released,
    <<READ: Local.read_step lc1 gl1 loc ((TView.cur (Local.tview lc1)).(View.pln) loc) val released ord lc1>>.
Proof.
  dup LC_WF1. inv LC_WF0. inv TVIEW_CLOSED. inv CUR.
  specialize (PLN loc). des.
  esplits. econs; eauto; try refl.
  - econs; try refl. i. destruct ord; ss.
  - destruct lc1. ss. f_equal.
    apply TView.antisym.
    + apply TViewFacts.read_tview_incr.
    + unfold TView.read_tview.
      econs; repeat (condtac; aggrtac; try apply LC_WF1).
      etrans; apply LC_WF1.
Qed.

Lemma progress_write_step
      lc1 gl1
      loc to val releasedm ord
      (LT: Time.lt (Memory.max_ts loc (Global.memory gl1)) to)
      (LC_WF1: Local.wf lc1 gl1)
      (GL_WF1: Global.wf gl1)
      (REL_WF: View.opt_wf releasedm)
      (REL_CLOSED: Memory.closed_opt_view releasedm (Global.memory gl1)):
  exists released lc2 gl2,
    Local.write_step lc1 gl1 loc (Memory.max_ts loc (Global.memory gl1)) to val releasedm released ord lc2 gl2.
Proof.
  exploit TViewFacts.write_future0; try exact REL_WF; try apply LC_WF1. i. des.
  exploit Memory.add_exists_max_ts; try exact LT; try by (econs 1; eassumption). i. des.
  esplits. econs; try exact x0; eauto.
  econs; i; (try eapply TimeFacts.le_lt_lt; [|eauto]).
  apply Memory.max_ts_spec2. apply LC_WF1.
Qed.

Lemma progress_fence_step
      lc1 sc1
      ordr ordw
      (PROMISES: Ordering.le Ordering.seqcst ordw -> (Local.promises lc1) = BoolMap.bot):
  exists lc2 sc2,
    Local.fence_step lc1 sc1 ordr ordw lc2 sc2.
Proof.
  esplits. econs; eauto.
Qed.


(* progress of an itree program *)

Lemma progress_program_step_non_update
      R0 R1
      (pe: MemE.t R0) (k: ktree MemE.t R0 R1)
      lc1 gl1
      (LC_WF1: Local.wf lc1 gl1)
      (GL_WF1: Global.wf gl1)
      (PROMISES1: Local.promises lc1 = BoolMap.bot)
      (UPDATE: match pe with | MemE.update _ _ _ _ => False | _ => True end):
  exists e th2,
    (<<STEP: Thread.step e (Thread.mk (lang R1) (Vis pe k) lc1 gl1) th2>>) /\
    (<<EVENT: ThreadEvent.is_program e>>).
Proof.
  destruct pe; ss.
  - hexploit progress_read_step; eauto. i. des.
    esplits.
    + econs 2; [|econs 2]; eauto. econs. refl.
    + ss.
  - hexploit progress_write_step; eauto.
    { apply Time.incr_spec. }
    i. des. esplits.
    + econs 2; [|econs 3]; eauto. econs. refl.
    + ss.
  - hexploit progress_fence_step; eauto. i. des.
    esplits.
    + econs 2; [|econs 5]; eauto. econs. refl.
    + ss.
  - hexploit progress_fence_step; eauto. i. des.
    esplits.
    + econs 2; [|econs 6]; eauto. econs. refl.
    + ss.
  - esplits.
    + econs 2; [|econs 7]; eauto. econs.
    + ss.
  - esplits.
    + econs; [|econs 1]; eauto. econs. econs.
    + ss.
  Unshelve.
  all: try exact 0.
Qed.
