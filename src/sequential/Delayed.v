Require Import RelationClasses.
Require Import Program.

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
Require Import Promises.
Require Import Global.
Require Import Thread.
Require Import Configuration.
Require Import BoolMap.

Require Import Cover.
Require Import PFConsistent.
Require Import Certify.
Require Import CurrentCertify.

Require Import SimLocal.

Require Import MemoryProps.
Require Import LowerMemory.

Require Import Owned.

Set Implicit Arguments.


Section DELAYEDREL.

  Variant delayed_content_private:
    forall (gp lp: bool),
      option (Time.t * Message.t) -> option (Time.t * Message.t) ->
      option (Time.t * Message.t) -> option (Time.t * Message.t) -> Prop :=
    | delayed_content_private_other
        from val released na
      :
      delayed_content_private
        true false
        None None
        (Some (from, Message.reserve)) (Some (from, Message.message val released na))
    | delayed_content_private_self
        from val released na
      :
      delayed_content_private
        true true
        (Some (from, Message.reserve)) None
        (Some (from, Message.reserve)) (Some (from, Message.message val released na))
    | delayed_content_private_normal
        gp lp rsv from msg_src msg_tgt
        (MESSAGE: Message.le msg_src msg_tgt)
      :
      delayed_content_private
        gp lp rsv rsv
        (Some (from, msg_src)) (Some (from, msg_tgt))
    | delayed_content_private_none
        gp lp
      :
      delayed_content_private
        gp lp None None
        None None
  .

  Definition delayed_memory_private (gprm lprm: BoolMap.t)
             (rsv_src rsv_tgt: Memory.t)
             (mem_src mem_tgt: Memory.t): Prop :=
    forall loc to,
      delayed_content_private
        (gprm loc) (lprm loc)
        (Memory.get loc to rsv_src) (Memory.get loc to rsv_tgt)
        (Memory.get loc to mem_src) (Memory.get loc to mem_tgt)
  .

  Variant delayed_global_private:
    Local.t -> Local.t -> Global.t -> Global.t -> Prop :=
    | delayed_global_private_intro
        lprm_src lprm_tgt rsv_src rsv_tgt tvw_src tvw_tgt
        sc_src sc_tgt gprm_src gprm_tgt mem_src mem_tgt
        (SC: TimeMap.le sc_src sc_tgt)
        (PROMISES: BoolMap.le gprm_tgt gprm_src)
        (MEM: delayed_memory_private gprm_src lprm_src rsv_src rsv_tgt mem_src mem_tgt)
      :
      delayed_global_private (Local.mk tvw_src lprm_src rsv_src) (Local.mk tvw_tgt lprm_tgt rsv_tgt) (Global.mk sc_src gprm_src mem_src) (Global.mk sc_tgt gprm_tgt mem_tgt)
  .



  Variant delayed_content_public:
    forall (gp: bool),
      option (Time.t * Message.t) -> option (Time.t * Message.t) -> Prop :=
    | delayed_content_public_delayed
        from val released na
      :
      delayed_content_public
        true
        (Some (from, Message.reserve)) (Some (from, Message.message val released na))
    | delayed_content_public_normal
        gp from msg_src msg_tgt
        (MESSAGE: Message.le msg_src msg_tgt)
      :
      delayed_content_public
        gp
        (Some (from, msg_src)) (Some (from, msg_tgt))
    | delayed_content_public_none
        gp
      :
      delayed_content_public
        gp
        None None
  .

  Definition delayed_memory_public (gprm: BoolMap.t)
             (mem_src mem_tgt: Memory.t): Prop :=
    forall loc to,
      delayed_content_public
        (gprm loc)
        (Memory.get loc to mem_src) (Memory.get loc to mem_tgt)
  .

  Lemma delayed_memory_public_get_space gprm mem_src mem_tgt
        loc to from msg_src
        (SIM: delayed_memory_public gprm mem_src mem_tgt)
        (GET: Memory.get loc to mem_src = Some (from, msg_src))
    :
    exists msg_tgt, (<<GET: Memory.get loc to mem_tgt = Some (from, msg_tgt)>>).
  Proof.
    specialize (SIM loc to). rewrite GET in SIM. inv SIM; eauto.
  Qed.

  Lemma delayed_memory_public_get_space_inv gprm mem_src mem_tgt
        loc to from msg_tgt
        (SIM: delayed_memory_public gprm mem_src mem_tgt)
        (GET: Memory.get loc to mem_tgt = Some (from, msg_tgt))
    :
    exists msg_src, (<<GET: Memory.get loc to mem_src = Some (from, msg_src)>>).
  Proof.
    specialize (SIM loc to). rewrite GET in SIM. inv SIM; eauto.
  Qed.

  Lemma delayed_memory_public_adjacent gprm mem_src mem_tgt
        loc ts0 ts1 ts2 ts3
        (SIM: delayed_memory_public gprm mem_src mem_tgt)
        (ADJ: Memory.adjacent loc ts0 ts1 ts2 ts3 mem_tgt)
    :
    Memory.adjacent loc ts0 ts1 ts2 ts3 mem_src.
  Proof.
    inv ADJ. eapply delayed_memory_public_get_space_inv in GET1; eauto.
    eapply delayed_memory_public_get_space_inv in GET2; eauto. des.
    econs; eauto. i. destruct (Memory.get loc ts mem_src) eqn:EQ; ss.
    destruct p. hexploit delayed_memory_public_get_space; eauto.
    i. des. erewrite EMPTY in GET1; eauto. ss.
  Qed.

  Lemma delayed_memory_public_adjacent_inv gprm mem_src mem_tgt
        loc ts0 ts1 ts2 ts3
        (SIM: delayed_memory_public gprm mem_src mem_tgt)
        (ADJ: Memory.adjacent loc ts0 ts1 ts2 ts3 mem_src)
    :
    Memory.adjacent loc ts0 ts1 ts2 ts3 mem_tgt.
  Proof.
    inv ADJ. eapply delayed_memory_public_get_space in GET1; eauto.
    eapply delayed_memory_public_get_space in GET2; eauto. des.
    econs; eauto. i. destruct (Memory.get loc ts mem_tgt) eqn:EQ; ss.
    destruct p. hexploit delayed_memory_public_get_space_inv; eauto.
    i. des. erewrite EMPTY in GET1; eauto. ss.
  Qed.

  Lemma delayed_memory_public_max_ts gprm mem_src mem_tgt loc
        (SIM: delayed_memory_public gprm mem_src mem_tgt)
        (GET: (exists from to msg, Memory.get loc to mem_src = Some (from, msg))
              \/
                (exists from to msg, Memory.get loc to mem_tgt = Some (from, msg)))
    :
    Memory.max_ts loc mem_src = Memory.max_ts loc mem_tgt.
  Proof.
    assert (exists from to msg, (<<GET: Memory.get loc to mem_src = Some (from, msg)>>)).
    { des; eauto. hexploit delayed_memory_public_get_space_inv; eauto. }
    clear GET. des. des. eapply Memory.max_ts_spec in GET. des.
    hexploit delayed_memory_public_get_space; eauto. i. des.
    eapply Memory.max_ts_spec in GET. des.
    hexploit delayed_memory_public_get_space_inv; eauto. i. des.
    eapply Memory.max_ts_spec in GET. des; auto.
    eapply TimeFacts.antisym; auto.
  Qed.

  Lemma delayed_memory_public_cap gprm mem_src mem_tgt
        (SIM: delayed_memory_public gprm mem_src mem_tgt)
    :
    delayed_memory_public gprm (Memory.cap_of mem_src) (Memory.cap_of mem_tgt).
  Proof.
    dup SIM.
    pose proof (@Memory.cap_of_cap mem_src) as CAPSRC.
    pose proof (@Memory.cap_of_cap mem_tgt) as CAPTGT.
    ii. specialize (SIM loc to). inv SIM.
    { rename H into GETSRC. rename H2 into GETTGT.
      symmetry in GETSRC. symmetry in GETTGT.
      eapply Memory.cap_le in GETSRC; eauto. eapply Memory.cap_le in GETTGT; eauto.
      rewrite GETSRC. rewrite GETTGT. econs 1; auto.
    }
    { rename H1 into GETSRC. rename H2 into GETTGT.
      symmetry in GETSRC. symmetry in GETTGT.
      eapply Memory.cap_le in GETSRC; eauto. eapply Memory.cap_le in GETTGT; eauto.
      rewrite GETSRC. rewrite GETTGT. econs 2; auto.
    }
    { rename H1 into GETSRC. rename H2 into GETTGT.
      symmetry in GETSRC. symmetry in GETTGT.
      destruct (Memory.get loc to (Memory.cap_of mem_src)) eqn:GETSRC1.
      { destruct p. inv CAPTGT.
        hexploit Memory.cap_inv; eauto. i. des; subst.
        { rewrite GETSRC in *. ss. }
        { hexploit MIDDLE; eauto.
          { eapply delayed_memory_public_adjacent_inv; eauto. }
          { i. rewrite H2. econs; auto. }
        }
        { hexploit delayed_memory_public_get_space; eauto. i. des.
          erewrite delayed_memory_public_max_ts in GET; eauto.
          hexploit BACK; eauto. i.
          erewrite <- delayed_memory_public_max_ts in H0; eauto. rewrite H0.
          econs; auto.
        }
      }
      { destruct (Memory.get loc to (Memory.cap_of mem_tgt)) eqn:GETTGT1.
        { destruct p. inv CAPSRC.
          hexploit Memory.cap_inv; eauto. i. des; subst.
          { rewrite GETTGT in *. ss. }
          { hexploit MIDDLE; eauto.
            { eapply delayed_memory_public_adjacent; eauto. }
            { i. rewrite GETSRC1 in *. ss. }
          }
          { hexploit delayed_memory_public_get_space_inv; eauto. i. des.
            erewrite <- delayed_memory_public_max_ts in GET; eauto.
            hexploit BACK; eauto. i.
            erewrite <- delayed_memory_public_max_ts in GETSRC1; eauto.
            rewrite GETSRC1 in *. ss.
          }
        }
        { econs. }
      }
    }
  Qed.

  Variant delayed_global_public: Global.t -> Global.t -> Prop :=
    | delayed_global_public_intro
        sc_src sc_tgt gprm_src gprm_tgt mem_src mem_tgt
        (SC: TimeMap.le sc_src sc_tgt)
        (PROMISES: BoolMap.le gprm_tgt gprm_src)
        (MEM: delayed_memory_public gprm_src mem_src mem_tgt)
      :
      delayed_global_public (Global.mk sc_src gprm_src mem_src) (Global.mk sc_tgt gprm_tgt mem_tgt)
  .

  Lemma delayed_global_public_cap gl_src gl_tgt
        (SIM: delayed_global_public gl_src gl_tgt)
    :
    delayed_global_public (Global.cap_of gl_src) (Global.cap_of gl_tgt).
  Proof.
    inv SIM. econs; ss.
    eapply delayed_memory_public_cap; eauto.
  Qed.

  Lemma delayed_memory_private_to_public
        gprm lprm rsv_src rsv_tgt mem_src mem_tgt
        (MEM: delayed_memory_private gprm lprm rsv_src rsv_tgt mem_src mem_tgt)
    :
    delayed_memory_public gprm mem_src mem_tgt.
  Proof.
    ii. specialize (MEM loc to). inv MEM; try by (econs; eauto).
  Qed.

  Lemma delayed_global_private_to_public
        lc_src lc_tgt gl_src gl_tgt
        (GLOBAL: delayed_global_private lc_src lc_tgt gl_src gl_tgt)
    :
    delayed_global_public gl_src gl_tgt.
  Proof.
    inv GLOBAL. econs; eauto. eapply delayed_memory_private_to_public; eauto.
  Qed.

  Lemma delayed_global_public_to_private
        lc_src gl_src0 gl_src1
        lc_tgt gl_tgt0 gl_tgt1
        (PRIVATE: delayed_global_private lc_src lc_tgt gl_src0 gl_tgt0)
        (PUBLIC0: delayed_global_public gl_src0 gl_tgt0)
        (PUBLIC1: delayed_global_public gl_src1 gl_tgt1)

        (LOCALSRC0: Local.wf lc_src gl_src0)
        (LOCALTGT0: Local.wf lc_tgt gl_tgt0)
        (GLOBALSRC0: Global.wf gl_src0)
        (GLOBALTGT0: Global.wf gl_tgt0)

        (LOCALSRC1: Local.wf lc_src gl_src1)
        (LOCALTGT1: Local.wf lc_tgt gl_tgt1)
        (GLOBALSRC1: Global.wf gl_src1)
        (GLOBALTGT1: Global.wf gl_tgt1)

        (OWNEDSRC: owned_future_global_promises lc_src.(Local.promises) gl_src0 gl_src1)
        (OWNEDTGT: owned_future_global_promises lc_src.(Local.promises) gl_tgt0 gl_tgt1)

        (FUTURESRC: Global.le gl_src0 gl_src1)
        (FUTURETGT: Global.le gl_tgt0 gl_tgt1)
    :
    delayed_global_private lc_src lc_tgt gl_src1 gl_tgt1.
  Proof.
    inv PUBLIC1. inv PRIVATE. econs; eauto.
    ii. specialize (MEM0 loc to). specialize (MEM loc to).
    inv MEM.
    { rename H into SRCMEM1. symmetry in SRCMEM1.
      rename H2 into TGTMEM1. symmetry in TGTMEM1.
      destruct (lprm_src loc) eqn:PROMISED.
      { exploit OWNEDTGT; eauto. intros UNCHTGT.
        exploit OWNEDSRC; eauto. intros UNCHSRC.
        rr in UNCHTGT. rr in UNCHSRC. des; ss.
        eapply MEM1 in TGTMEM1. rewrite TGTMEM1 in MEM0. inv MEM0.
        { econs. }
        { rename H5 into SRCMEM0. symmetry in SRCMEM0.
          inv MESSAGE. eapply FUTURESRC in SRCMEM0. ss. clarify.
        }
      }
      { inv MEM0.
        { econs 1. }
        { rename H4 into TGTRSV. symmetry in TGTRSV.
          rename H5 into SRCMEM0. symmetry in SRCMEM0.
          rename H6 into TGTMEM0. symmetry in TGTMEM0.
          destruct (Memory.get loc to rsv_src) eqn:SRCRSV.
          { destruct p.
            inv LOCALSRC1. inv LOCALTGT1. ss.
            eapply RESERVES in SRCRSV. eapply RESERVES0 in TGTRSV.
            rewrite TGTMEM1 in TGTRSV. rewrite SRCMEM1 in SRCRSV. clarify.
          }
          { econs. }
        }
        { econs. }
      }
    }
    { rename H1 into SRCMEM1. symmetry in SRCMEM1.
      rename H2 into TGTMEM1. symmetry in TGTMEM1. inv MEM0.
      { econs; eauto. }
      { rename H2 into SRCRSV. symmetry in SRCRSV.
        rename H3 into TGTRSV. symmetry in TGTRSV.
        rename H4 into SRCMEM0. symmetry in SRCMEM0.
        rename H5 into TGTMEM0. symmetry in TGTMEM0.
        eapply FUTURETGT in TGTMEM0. ss. clarify.
        inv MESSAGE. ss.
        exploit OWNEDSRC; eauto. intros UNCHSRC.
        rr in UNCHSRC. des; ss. eapply MEM in SRCMEM1. clarify.
      }
      { econs; eauto. }
      { econs; eauto. }
    }
    { rename H1 into SRCMEM1. symmetry in SRCMEM1.
      rename H2 into TGTMEM1. symmetry in TGTMEM1.
      destruct (Memory.get loc to rsv_src) eqn:SRCRSV.
      { destruct p. inv LOCALSRC1. ss.
        eapply RESERVES in SRCRSV. clarify. }
      destruct (Memory.get loc to rsv_tgt) eqn:TGTRSV.
      { destruct p. inv LOCALTGT1. ss.
        eapply RESERVES in TGTRSV. clarify. }
      econs.
    }
  Qed.

End DELAYEDREL.


Require Import LowerStep.

Section DELAYEDLOWER.

  Lemma lower_step_delayed_preserve lang
        st0 lc0 gl0 st1 lc1 gl1 e
        lc_tgt gl_tgt
        (STEP: lower_step e (Thread.mk lang st0 lc0 gl0) (Thread.mk _ st1 lc1 gl1))
        (LC_WF: Local.wf lc0 gl0)
        (GL_WF: Global.wf gl0)
        (LC_WF_TGT: Local.wf lc_tgt gl_tgt)
        (GL_WF_TGT: Global.wf gl_tgt)
        (DELAYED: delayed_global_private lc1 lc_tgt gl1 gl_tgt):
    delayed_global_private lc0 lc_tgt gl0 gl_tgt.
  Proof.
    destruct lc0 as [tview0 prm0 rsv0], lc1 as [tview1 prm1 rsv1].
    destruct gl0 as [sc0 gprm0 mem0], gl1 as [sc1 gprm1 mem1].
    exploit lower_step_future; eauto. s. i. des.
    inv DELAYED. econs.
    { etrans; eauto. apply GL_FUTURE. }
    { etrans; eauto. inv STEP. des; ss.
      { inv STEP0. clarify. inv LOCAL; ss.
        { destruct ord; ss. }
        { inv LOCAL0; ss. clarify. }
      }
      { inv STEP; [|inv LOCAL]. inv LOCAL. inv LOCAL0. ss.
        inv STEP0. inv LOCAL; ss. inv LOCAL0; ss. clarify.
        inv FULFILL; ss. inv GREMOVE. ii.
        rewrite loc_fun_add_spec in LHS. des_ifs.
      }
    }
    clear PROMISES.
    inv STEP. inv STEP0. inv LOCAL; ss.
    { (* silent *)
      des; ss. clarify.
    }
    { (* read *)
      des; ss. clarify.
      inv LOCAL0; ss. clarify.
    }
    { (* write *)
      des; ss; clarify.
      { destruct ord; ss. }
      inv STEP; inv LOCAL. inv LOCAL1. inv CANCEL. ss.
      inv LOCAL0. ss. clarify.
      ii. specialize (MEM loc to). revert MEM.
      erewrite (@Memory.remove_o rsv2); eauto.
      erewrite (@Memory.add_o mem3); eauto.
      erewrite (@Memory.remove_o mem2); eauto.
      condtac; ss; cycle 1.
      { inv FULFILL; ss.
        erewrite (@BoolMap.remove_o prm2); eauto.
        erewrite (@BoolMap.remove_o gprm2); eauto.
        condtac; ss. subst. ss.
        i. inv MEM; ss; econs; ss.
      }
      des. subst. i.
      exploit Memory.remove_get0; try exact RSV. i. des.
      exploit Memory.remove_get0; try exact MEM0. i. des.
      inv LC_WF. exploit PROMISES; eauto. ss. i.
      rewrite GET, GET1, PROMISED, x0.
      inv FULFILL.
      { inv MEM. inv MESSAGE. econs. }
      { exploit BoolMap.remove_get0; try exact REMOVE. i. des.
        exploit BoolMap.remove_get0; try exact GREMOVE. i. des.
        rewrite GET4, GET6 in *.
        inv MEM. inv MESSAGE. econs.
      }
    }
    { (* fence *)
      des; ss. clarify.
      inv LOCAL0. ss. clarify.
    }
    { (* racy read *)
      des; ss. clarify.
    }
  Qed.

  Lemma lower_steps_delayed_preserve lang
        st0 lc0 gl0 st1 lc1 gl1
        lc_tgt gl_tgt
        (STEPS: rtc (tau lower_step) (Thread.mk lang st0 lc0 gl0) (Thread.mk _ st1 lc1 gl1))
        (LC_WF: Local.wf lc0 gl0)
        (GL_WF: Global.wf gl0)
        (LC_WF_TGT: Local.wf lc_tgt gl_tgt)
        (GL_WF_TGT: Global.wf gl_tgt)
        (DELAYED: delayed_global_private lc1 lc_tgt gl1 gl_tgt):
    delayed_global_private lc0 lc_tgt gl0 gl_tgt.
  Proof.
    remember (Thread.mk _ st0 lc0 gl0). remember (Thread.mk _ st1 lc1 gl1).
    revert st0 lc0 gl0 st1 lc1 gl1 lc_tgt gl_tgt
           DELAYED LC_WF GL_WF LC_WF_TGT GL_WF_TGT Heqt Heqt0.
    induction STEPS; i; clarify.
    inv H. destruct y.
    hexploit lower_step_delayed_preserve; eauto.
    hexploit lower_step_future; eauto. i. des; ss.
    hexploit IHSTEPS; eauto.
  Qed.
End DELAYEDLOWER.


Section DELAYEDSTEP.
  Lemma undelayed_memory_get
        lprm gprm rsv_src rsv_tgt
        mem_src mem_tgt
        loc to from msg_tgt
        (RSV: rsv_src = rsv_tgt)
        (MEM: delayed_memory_private gprm lprm rsv_src rsv_tgt mem_src mem_tgt)
        (GET: Memory.get loc to mem_tgt = Some (from, msg_tgt))
        (RESERVE: msg_tgt <> Message.reserve):
    (exists msg_src,
        (<<GET: Memory.get loc to mem_src = Some (from, msg_src)>>) /\
        (<<LE: Message.le msg_src msg_tgt>>)) \/
    ((<<LPRM: lprm loc = false>>) /\ (<<GPRM: gprm loc = true>>)).
  Proof.
    subst. specialize (MEM loc to).
    rewrite GET in MEM. inv MEM; eauto.
  Qed.

  Lemma undelayed_memory_covered
        lprm gprm rsv0 rsv1
        mem_src mem_tgt
        loc to from msg_src
        (GET: Memory.get loc to mem_src = Some (from, msg_src))
        (SIMGLOBAL: delayed_memory_private gprm lprm rsv0 rsv1 mem_src mem_tgt)
    :
    exists msg_tgt,
      (<<GET: Memory.get loc to mem_tgt = Some (from, msg_tgt)>>).
  Proof.
    specialize (SIMGLOBAL loc to). rewrite GET in SIMGLOBAL. inv SIMGLOBAL; eauto.
  Qed.

  Lemma undelayed_memory_reserve
        lprm gprm
        rsv0_src rsv0_tgt
        mem0_src mem0_tgt
        loc to from rsv1_tgt mem1_tgt
        (RSV: rsv0_src = rsv0_tgt)
        (MEM: delayed_memory_private gprm lprm rsv0_src rsv0_tgt mem0_src mem0_tgt)
        (LE: Memory.le rsv0_src mem0_src)
        (RESERVE: Memory.reserve rsv0_tgt mem0_tgt loc from to rsv1_tgt mem1_tgt):
    exists mem1_src,
      (<<RESERVE: Memory.reserve rsv0_src mem0_src loc from to rsv1_tgt mem1_src>>) /\
      (<<SIM: delayed_memory_private gprm lprm rsv1_tgt rsv1_tgt mem1_src mem1_tgt>>).
  Proof.
    inv RESERVE. hexploit add_succeed_wf; eauto. i. des.
    hexploit (@Memory.add_exists mem0_src loc from to); eauto.
    { i. hexploit undelayed_memory_covered; eauto. i. des. eauto. }
    i. des.
    hexploit Memory.add_exists_le; eauto.
    i. des. esplits.
    { econs; eauto. }
    { ii. erewrite (@Memory.add_o rsv1_tgt); eauto.
      erewrite (@Memory.add_o mem2); eauto.
      erewrite (@Memory.add_o mem1_tgt); eauto.
      des_ifs. econs. ss.
    }
  Qed.

  Lemma undelayed_memory_cancel
        lprm gprm
        rsv0_src rsv0_tgt
        mem0_src mem0_tgt
        loc to from rsv1_tgt mem1_tgt
        (RSV: rsv0_src = rsv0_tgt)
        (MEM: delayed_memory_private gprm lprm rsv0_src rsv0_tgt mem0_src mem0_tgt)
        (LE: Memory.le rsv0_src mem0_src)
        (CANCEL: Memory.cancel rsv0_tgt mem0_tgt loc from to rsv1_tgt mem1_tgt):
    exists mem1_src,
      (<<CANCEL: Memory.cancel rsv0_src mem0_src loc from to rsv1_tgt mem1_src>>) /\
      (<<SIM: delayed_memory_private gprm lprm rsv1_tgt rsv1_tgt mem1_src mem1_tgt>>).
  Proof.
    inv CANCEL. hexploit Memory.remove_exists_le; eauto.
    i. des. esplits.
    { econs; eauto. }
    { ii. erewrite (@Memory.remove_o rsv1_tgt); eauto.
      erewrite (@Memory.remove_o mem2'); eauto.
      erewrite (@Memory.remove_o mem1_tgt); eauto.
      des_ifs. econs.
    }
  Qed.

  Lemma undelayed_memory_add
        lprm gprm
        rsv_src rsv_tgt
        mem0_src mem0_tgt
        loc to from msg_tgt mem1_tgt
        msg_src
        (RSV: rsv_src = rsv_tgt)
        (MEM: delayed_memory_private gprm lprm rsv_src rsv_tgt mem0_src mem0_tgt)
        (MSG_WF: Message.wf msg_src)
        (MSG_LE: Message.le msg_src msg_tgt)
        (ADD: Memory.add mem0_tgt loc from to msg_tgt mem1_tgt):
    exists mem1_src,
      (<<ADD: Memory.add mem0_src loc from to msg_src mem1_src>>) /\
      (<<SIM: delayed_memory_private gprm lprm rsv_src rsv_tgt mem1_src mem1_tgt>>).
  Proof.
    hexploit add_succeed_wf; eauto. i. des.
    hexploit (@Memory.add_exists mem0_src loc from to msg_src); eauto.
    { i. hexploit undelayed_memory_covered; eauto. i. des. eauto. }
    i. des. esplits; eauto.
    ii. erewrite (@Memory.add_o mem1_tgt); eauto.
    erewrite (@Memory.add_o mem2); eauto.
    des_ifs. econs. ss.
  Qed.

  Lemma undelayed_read
        lc1_src lc1_tgt
        gl_src gl_tgt
        loc to val released_tgt ord lc2_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (GLOBAL1: delayed_global_private lc1_src lc1_tgt gl_src gl_tgt)
        (LC_WF_TGT: Local.wf lc1_tgt gl_tgt)
        (GL_WF_TGT: Global.wf gl_tgt)
        (STEP: Local.read_step lc1_tgt gl_tgt loc to val released_tgt ord lc2_tgt):
    (exists released_src lc2_src,
        (<<RELEASED: View.opt_le released_src released_tgt>>) /\
        (<<STEP: Local.read_step lc1_src gl_src loc to val released_src ord lc2_src>>) /\
        (<<LOCAL2: sim_local lc2_src lc2_tgt>>) /\
        (<<GLOBAL2: delayed_global_private lc2_src lc2_tgt gl_src gl_tgt>>)) \/
    ((<<STEP: Local.racy_read_step lc1_src gl_src loc None val ord>>) /\
     (<<LOCAL2: sim_local lc1_src lc2_tgt>>) /\
     (<<GLOBAL2: delayed_global_private lc1_src lc2_tgt gl_src gl_tgt>>)).
  Proof.
    inv LOCAL1. inv GLOBAL1. inv STEP.
    exploit undelayed_memory_get; try apply GET; eauto; ss. i. des.
    { left. inv LE. esplits; eauto.
      - econs; eauto; (try by etrans; eauto).
        eapply TViewFacts.readable_mon; eauto; try apply TVIEW. refl.
      - econs; eauto. s. apply TViewFacts.read_tview_mon; auto; try refl.
        + apply LC_WF_TGT.
        + inv GL_WF_TGT. inv MEM_CLOSED.
          exploit CLOSED; eauto. i. des. inv MSG_WF. auto.
      - ss.
    }
    { right. esplits; eauto.
      - econs; eauto. s.
        etrans; [apply TVIEW|].
        apply TViewFacts.read_tview_incr.
      - ss.
    }
  Qed.

  Lemma undelayed_fulfill
        rsv_src lprm0_src gprm0_src mem_src
        rsv_tgt lprm0_tgt gprm0_tgt mem_tgt
        loc ord lprm1_tgt gprm1_tgt
        (RSV: rsv_src = rsv_tgt)
        (PRM: lprm0_src = lprm0_tgt)
        (GPRM: BoolMap.le gprm0_tgt gprm0_src)
        (MEM: delayed_memory_private gprm0_src lprm0_src rsv_src rsv_tgt mem_src mem_tgt)
        (FULFILL: Promises.fulfill lprm0_tgt gprm0_tgt loc ord lprm1_tgt gprm1_tgt):
    exists lprm1_src gprm1_src,
      (<<FULFILL: Promises.fulfill lprm0_src gprm0_src loc ord lprm1_src gprm1_src>>) /\
      (<<PRM: lprm1_src = lprm1_tgt>>) /\
      (<<GPRM: BoolMap.le gprm1_tgt gprm1_src>>) /\
      (<<MEM: delayed_memory_private gprm1_src lprm1_src rsv_src rsv_tgt mem_src mem_tgt>>).
  Proof.
    inv FULFILL.
    { esplits; eauto. }
    { inv GREMOVE. esplits.
      { econs 2; eauto. }
      { ss. }
      { ii. rewrite loc_fun_add_spec in *. condtac; ss. eauto. }
      { inv REMOVE. ii. specialize (MEM loc0 to).
        rewrite ! loc_fun_add_spec. condtac; ss. subst.
        inv MEM.
        { congr. }
        { econs. ss. }
        { econs. }
      }
    }
  Qed.

  Lemma undelayed_write
        lc1_src lc1_tgt
        gl1_src gl1_tgt
        loc from to val releasedm_tgt released_tgt ord lc2_tgt gl2_tgt
        releasedm_src
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (GLOBAL1: delayed_global_private lc1_src lc1_tgt gl1_src gl1_tgt)
        (LC_WF_SRC: Local.wf lc1_src gl1_src)
        (GL_WF_SRC: Global.wf gl1_src)
        (LC_WF_TGT: Local.wf lc1_tgt gl1_tgt)
        (GL_WF_TGT: Global.wf gl1_tgt)
        (RELM: View.opt_le releasedm_src releasedm_tgt)
        (RELM_WF_SRC: View.opt_wf releasedm_src)
        (RELM_WF_TGT: View.opt_wf releasedm_tgt)
        (STEP: Local.write_step lc1_tgt gl1_tgt loc from to val releasedm_tgt released_tgt ord lc2_tgt gl2_tgt):
    (BoolMap.minus gl1_src.(Global.promises) lc1_src.(Local.promises) loc = false /\
     exists released_src lc2_src gl2_src,
        (<<STEP: Local.write_step lc1_src gl1_src loc from to val releasedm_src released_src ord lc2_src gl2_src>>) /\
        (<<RELEASED: View.opt_le released_src released_tgt>>) /\
        (<<LOCAL2: sim_local lc2_src lc2_tgt>>) /\
        (<<GLOBAL2: delayed_global_private lc2_src lc2_tgt gl2_src gl2_tgt>>)) \/
    (<<STEP: Local.racy_write_step lc1_src gl1_src loc None ord>>).
  Proof.
    inv LOCAL1. inv GLOBAL1. ss.
    destruct (BoolMap.minus gprm_src lprm_src loc) eqn:PROMISED.
    { right. unfold BoolMap.minus in *.
      destruct (gprm_src loc) eqn:GPRM, (lprm_src loc) eqn:PRM; ss.
      esplits; eauto.
    }
    left. split; ss. inv STEP. ss.
    assert (RELT_LE:
             View.opt_le
               (TView.write_released tvw_src loc to releasedm_src ord)
               (TView.write_released tvw_tgt loc to releasedm_tgt ord)).
    { apply TViewFacts.write_released_mon; ss.
      - apply LC_WF_TGT.
      - refl.
    }
    assert (RELT_WF:
             View.opt_wf (TView.write_released tvw_src loc to releasedm_src ord)).
    { unfold TView.write_released. condtac; econs.
      repeat (try condtac; viewtac; try apply LC_WF_SRC).
    }
    exploit undelayed_fulfill; try exact FULFILL; try exact MEM; eauto. i. des. subst.
    exploit undelayed_memory_add; try exact MEM0; try exact WRITE.
    { refl. }
    { econs 1. exact RELT_WF. }
    { econs 1; try exact RELT_LE; try refl.
      eapply ord_implb. refl.
    }
    i. des. esplits.
    - econs; eauto.
      eapply TViewFacts.writable_mon; try exact WRITABLE; eauto; try refl. apply TVIEW.
    - ss.
    - econs; eauto; s; try apply TVIEW.
      apply TViewFacts.write_tview_mon; ss; try refl.
      apply LC_WF_TGT.
    - ss.
  Qed.

  Lemma undelayed_update
        lc1_src lc1_tgt
        gl1_src gl1_tgt
        loc ts1 val1 released1_tgt ordr lc2_tgt
        from2 to2 val2 released2_tgt ordw lc3_tgt gl3_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (GLOBAL1: delayed_global_private lc1_src lc1_tgt gl1_src gl1_tgt)
        (LC_WF_SRC: Local.wf lc1_src gl1_src)
        (GL_WF_SRC: Global.wf gl1_src)
        (LC_WF_TGT: Local.wf lc1_tgt gl1_tgt)
        (GL_WF_TGT: Global.wf gl1_tgt)
        (STEP1: Local.read_step lc1_tgt gl1_tgt loc ts1 val1 released1_tgt ordr lc2_tgt)
        (STEP2: Local.write_step lc2_tgt gl1_tgt loc from2 to2 val2 released1_tgt released2_tgt ordw lc3_tgt gl3_tgt):
    (BoolMap.minus gl1_src.(Global.promises) lc1_src.(Local.promises) loc = false /\
     exists released1_src released2_src lc2_src lc3_src gl3_src,
        (<<STEP1: Local.read_step lc1_src gl1_src loc ts1 val1 released1_src ordr lc2_src>>) /\
        (<<STEP2: Local.write_step lc2_src gl1_src loc from2 to2 val2 released1_src released2_src ordw lc3_src gl3_src>>) /\
        (<<RELEASED1: View.opt_le released1_src released1_tgt>>) /\
        (<<RELEASED2: View.opt_le released2_src released2_tgt>>) /\
        (<<LOCAL3: sim_local lc3_src lc3_tgt>>) /\
        (<<GLOBAL3: delayed_global_private lc3_src lc3_tgt gl3_src gl3_tgt>>)) \/
    (<<STEP: Local.racy_update_step lc1_src gl1_src loc None ordr ordw>>).
  Proof.
    destruct (BoolMap.minus gl1_src.(Global.promises) lc1_src.(Local.promises) loc) eqn:PROMISED.
    { right. inv LOCAL1. inv GLOBAL1. ss.
      unfold BoolMap.minus in *.
      destruct (gprm_src loc) eqn:GPRM, (lprm_src loc) eqn:PRM; ss.
      esplits; eauto.
    }
    exploit undelayed_read; try exact LOCAL1; try exact GLOBAL1; eauto. i. des; cycle 1.
    { right. inv STEP. econs 3. ss. }
    exploit Local.read_step_future; try exact STEP1; eauto. i. des.
    exploit Local.read_step_future; try exact STEP; eauto. i. des.
    exploit undelayed_write; try exact STEP2; eauto. i. des; cycle 1.
    { right. inv STEP0. inv RACE. econs 3. econs; ss. inv STEP. ss. }
    left. split; ss. esplits; eauto.
  Qed.

  Lemma undelayed_fence
        lc1_src lc1_tgt
        gl1_src gl1_tgt
        ordr ordw lc2_tgt gl2_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (GLOBAL1: delayed_global_private lc1_src lc1_tgt gl1_src gl1_tgt)
        (LC_WF_SRC: Local.wf lc1_src gl1_src)
        (LC_WF_TGT: Local.wf lc1_tgt gl1_tgt)
        (STEP: Local.fence_step lc1_tgt gl1_tgt ordr ordw lc2_tgt gl2_tgt):
    exists lc2_src gl2_src,
      (<<STEP: Local.fence_step lc1_src gl1_src ordr ordw lc2_src gl2_src>>) /\
      (<<LOCAL2: sim_local lc2_src lc2_tgt>>) /\
      (<<GLOBAL2: delayed_global_private lc2_src lc2_tgt gl2_src gl2_tgt>>).
  Proof.
    inv GLOBAL1. inv STEP.
    esplits.
    - econs; eauto. i.
      erewrite sim_local_promises_bot; eauto.
    - econs; try apply LOCAL1. s.
      apply TViewFacts.write_fence_tview_mon; auto; try refl; cycle 1.
      { eapply TViewFacts.read_fence_future; apply LC_WF_SRC. }
      apply TViewFacts.read_fence_tview_mon; auto; try refl.
      + apply LOCAL1.
      + apply LC_WF_TGT.
    - econs; ss.
      apply TViewFacts.write_fence_sc_mon; auto; try refl.
      apply TViewFacts.read_fence_tview_mon; auto; try refl.
      + apply LOCAL1.
      + apply LC_WF_TGT.
  Qed.

  Lemma undelayed_is_racy
        lc_src lc_tgt gl_src gl_tgt loc to_tgt ord
        (LOCAL: sim_local lc_src lc_tgt)
        (GLOBAL: delayed_global_private lc_src lc_tgt gl_src gl_tgt)
        (RACE: Local.is_racy lc_tgt gl_tgt loc to_tgt ord):
    exists to_src,
      (<<RACE: Local.is_racy lc_src gl_src loc to_src ord>>).
  Proof.
    inv LOCAL. inv GLOBAL. inv RACE; ss.
    { esplits. econs 1; auto. s. congr. }
    { specialize (MEM loc to). rewrite GET in MEM. inv MEM.
      { esplits. econs 1; eauto. }
      { congr. }
      { inv MESSAGE. esplits. econs 2; eauto; s.
        { eapply TViewFacts.racy_view_mon; eauto. apply TVIEW. }
        { i. exploit MSG; eauto. i. subst. destruct na1; ss. }
      }
    }
  Qed.

  Lemma undelayed_racy_read
        lc_src lc_tgt gl_src gl_tgt loc to_tgt val ord
        (LOCAL: sim_local lc_src lc_tgt)
        (GLOBAL: delayed_global_private lc_src lc_tgt gl_src gl_tgt)
        (STEP: Local.racy_read_step lc_tgt gl_tgt loc to_tgt val ord):
    exists to_src,
      (<<RACE: Local.racy_read_step lc_src gl_src loc to_src val ord>>).
  Proof.
    inv STEP.
    exploit undelayed_is_racy; eauto. i. des.
    esplits; eauto.
  Qed.

  Lemma undelayed_racy_write
        lc_src lc_tgt gl_src gl_tgt loc to_tgt ord
        (LOCAL: sim_local lc_src lc_tgt)
        (GLOBAL: delayed_global_private lc_src lc_tgt gl_src gl_tgt)
        (STEP: Local.racy_write_step lc_tgt gl_tgt loc to_tgt ord):
    exists to_src,
      (<<RACE: Local.racy_write_step lc_src gl_src loc to_src ord>>).
  Proof.
    inv STEP.
    exploit undelayed_is_racy; eauto. i. des.
    esplits; eauto.
  Qed.

  Lemma undelayed_racy_update
        lc_src lc_tgt gl_src gl_tgt loc to_tgt ordr ordw
        (LOCAL: sim_local lc_src lc_tgt)
        (GLOBAL: delayed_global_private lc_src lc_tgt gl_src gl_tgt)
        (STEP: Local.racy_update_step lc_tgt gl_tgt loc to_tgt ordr ordw):
    exists to_src,
      (<<RACE: Local.racy_update_step lc_src gl_src loc to_src ordr ordw>>).
  Proof.
    inv STEP; eauto.
    exploit undelayed_is_racy; eauto. i. des.
    esplits; eauto.
  Qed.

  Lemma write_owned_future
        own
        lc1 gl1 loc from to val releasedm released ord lc2 gl2
        (WRITE: Local.write_step lc1 gl1 loc from to val releasedm released ord lc2 gl2)
        (OWN: own loc = false):
    owned_future_global_promises own gl1 gl2.
  Proof.
    ii. inv WRITE. econs; ss; ii.
    { revert GET. erewrite Memory.add_o; eauto. condtac; ss.
      des. subst. congr.
    }
    { inv FULFILL; ss.
      erewrite BoolMap.remove_o; eauto. condtac; ss. congr.
    }
  Qed.

  Lemma undelayed_program_step
        lc1_src lc1_tgt
        gl1_src gl1_tgt
        e_tgt lc2_tgt gl2_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (GLOBAL1: delayed_global_private lc1_src lc1_tgt gl1_src gl1_tgt)
        (LC_WF_SRC: Local.wf lc1_src gl1_src)
        (GL_WF_SRC: Global.wf gl1_src)
        (LC_WF_TGT: Local.wf lc1_tgt gl1_tgt)
        (GL_WF_TGT: Global.wf gl1_tgt)
        (STEP: Local.program_step e_tgt lc1_tgt gl1_tgt lc2_tgt gl2_tgt):
    (exists e_src lc2_src gl2_src,
        (<<STEP: Local.program_step e_src lc1_src gl1_src lc2_src gl2_src>>) /\
        (<<LOCAL2: sim_local lc2_src lc2_tgt>>) /\
        (<<GLOBAL2: delayed_global_private lc2_src lc2_tgt gl2_src gl2_tgt>>) /\
        (<<EVENT1: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>>) /\
        (<<EVENT2: release_event e_src <-> release_event e_tgt>>) /\
        (<<EVENT3: ThreadEvent.get_program_event e_src = ThreadEvent.get_program_event e_tgt>>) /\
        (<<OWNEDSRC: owned_future_global_promises
                    (BoolMap.minus gl1_src.(Global.promises) lc1_src.(Local.promises))
                    gl1_src gl2_src>>) /\
        (<<OWNED: owned_future_global_promises
                    (BoolMap.minus gl1_src.(Global.promises) lc1_src.(Local.promises))
                    gl1_tgt gl2_tgt>>)) \/
    exists e_src lc2_src gl2_src,
      (<<STEP: Local.program_step e_src lc1_src gl1_src lc2_src gl2_src>>) /\
      (<<EVENT: ThreadEvent.get_program_event e_src = ThreadEvent.get_program_event e_tgt>>) /\
      (<<EVENT_FAILURE: ThreadEvent.get_machine_event e_src = MachineEvent.failure>>).
  Proof.
    inv STEP.
    { (* silent *)
      left. esplits; eauto; try by refl.
    }
    { (* read *)
      exploit undelayed_read; eauto. i. des.
      - left. esplits; [econs 2|..]; eauto; try by refl.
      - left. esplits; [econs 8|..]; eauto; try by refl.
    }
    { (* write *)
      exploit undelayed_write; eauto. i. des.
      - left. esplits; [econs 3|..]; eauto.
        { eapply write_owned_future; eauto. }
        { eapply write_owned_future; eauto. }
      - right. esplits; [econs 9|..]; eauto; ss.
    }
    { (* update *)
      exploit undelayed_update; eauto. i. des.
      - left. esplits; [econs 4|..]; eauto.
        { eapply write_owned_future; eauto. }
        { eapply write_owned_future; eauto. }
      - right. esplits; [econs 10|..]; eauto; ss.
    }
    { (* fence *)
      exploit undelayed_fence; eauto. i. des.
      left. esplits; [econs 5|..]; eauto.
      { inv STEP. ii. econs; ss. }
      { inv LOCAL. ii. econs; ss. }
    }
    { (* syscall *)
      exploit undelayed_fence; eauto. i. des.
      left. esplits; [econs 6|..]; eauto.
      { inv STEP. ii. econs; ss. }
      { inv LOCAL. ii. econs; ss. }
    }
    { (* failure *)
      left. esplits; [econs 7|..]; eauto; try by refl.
    }
    { (* racy read *)
      exploit undelayed_racy_read; eauto. i. des.
      left. esplits; [econs 8|..]; eauto; try by refl.
    }
    { (* racy write *)
      exploit undelayed_racy_write; eauto. i. des.
      left. esplits; [econs 9|..]; eauto; ss; try by refl.
    }
    { (* racy update *)
      exploit undelayed_racy_update; eauto. i. des.
      left. esplits; [econs 10|..]; eauto; ss; try by refl.
    }
    Unshelve.
    all: ss.
  Qed.

  Lemma undelayed_reserve
        lc1_src lc1_tgt
        gl1_src gl1_tgt
        loc from to lc2_tgt gl2_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (GLOBAL1: delayed_global_private lc1_src lc1_tgt gl1_src gl1_tgt)
        (LC_WF_SRC: Local.wf lc1_src gl1_src)
        (GL_WF_SRC: Global.wf gl1_src)
        (LC_WF_TGT: Local.wf lc1_tgt gl1_tgt)
        (GL_WF_TGT: Global.wf gl1_tgt)
        (STEP: Local.reserve_step lc1_tgt gl1_tgt loc from to lc2_tgt gl2_tgt):
    exists lc2_src gl2_src,
      (<<STEP: Local.reserve_step lc1_src gl1_src loc from to lc2_src gl2_src>>) /\
      (<<LOCAL2: sim_local lc2_src lc2_tgt>>) /\
      (<<GLOBAL2: delayed_global_private lc2_src lc2_tgt gl2_src gl2_tgt>>) /\
      (<<OWNEDSRC: owned_future_global_promises
                  (BoolMap.minus gl1_src.(Global.promises) lc1_src.(Local.promises))
                  gl1_src gl2_src>>) /\
      (<<OWNED: owned_future_global_promises
                  (BoolMap.minus gl1_src.(Global.promises) lc1_src.(Local.promises))
                  gl1_tgt gl2_tgt>>).
  Proof.
    hexploit local_reserve_step_owned_future; eauto.
    instantiate (1:=BoolMap.minus gl1_src.(Global.promises) lc1_src.(Local.promises)).
    inv LOCAL1. inv GLOBAL1. inv STEP. ss. subst.
    exploit undelayed_memory_reserve; try exact MEM; eauto; try apply LC_WF_SRC. i. des.
    esplits; eauto; ss.
    hexploit local_reserve_step_owned_future; eauto.
    { econs; eauto. instantiate (5:=Local.mk _ _ _). eauto. }
    Unshelve. all: ss.
  Qed.

  Lemma undelayed_cancel
        lc1_src lc1_tgt
        gl1_src gl1_tgt
        loc from to lc2_tgt gl2_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (GLOBAL1: delayed_global_private lc1_src lc1_tgt gl1_src gl1_tgt)
        (LC_WF_SRC: Local.wf lc1_src gl1_src)
        (GL_WF_SRC: Global.wf gl1_src)
        (LC_WF_TGT: Local.wf lc1_tgt gl1_tgt)
        (GL_WF_TGT: Global.wf gl1_tgt)
        (STEP: Local.cancel_step lc1_tgt gl1_tgt loc from to lc2_tgt gl2_tgt):
    exists lc2_src gl2_src,
      (<<STEP: Local.cancel_step lc1_src gl1_src loc from to lc2_src gl2_src>>) /\
      (<<LOCAL2: sim_local lc2_src lc2_tgt>>) /\
      (<<GLOBAL2: delayed_global_private lc2_src lc2_tgt gl2_src gl2_tgt>>) /\
      (<<OWNEDSRC: owned_future_global_promises
                  (BoolMap.minus gl1_src.(Global.promises) lc1_src.(Local.promises))
                  gl1_src gl2_src>>) /\
      (<<OWNED: owned_future_global_promises
                  (BoolMap.minus gl1_src.(Global.promises) lc1_src.(Local.promises))
                  gl1_tgt gl2_tgt>>).
  Proof.
    hexploit local_cancel_step_owned_future; eauto.
    instantiate (1:=BoolMap.minus gl1_src.(Global.promises) lc1_src.(Local.promises)).
    inv LOCAL1. inv GLOBAL1. inv STEP. ss. subst.
    exploit undelayed_memory_cancel; try exact MEM; eauto; try apply LC_WF_SRC. i. des.
    esplits; eauto; ss.
    hexploit local_cancel_step_owned_future; eauto.
    { econs; eauto. instantiate (5:=Local.mk _ _ _). eauto. }
    Unshelve. all: ss.
  Qed.

  Variant undelayed_thread {lang: language} (th_src th_tgt: Thread.t lang): Prop :=
    | undelayed_thread_intro
        (STATE: th_src.(Thread.state) = th_tgt.(Thread.state))
        (LOCAL: sim_local th_src.(Thread.local) th_tgt.(Thread.local))
        (GLOBAL: delayed_global_private th_src.(Thread.local) th_tgt.(Thread.local)
                                        th_src.(Thread.global) th_tgt.(Thread.global))
  .
  #[local] Hint Constructors undelayed_thread: core.

  Variant undelayed_event: forall (e_src e_tgt: ThreadEvent.t), Prop :=
    | undelayed_event_promise
        loc:
      undelayed_event (ThreadEvent.promise loc) (ThreadEvent.promise loc)
    | undelayed_event_reserve
        loc from to:
      undelayed_event (ThreadEvent.reserve loc from to) (ThreadEvent.reserve loc from to)
    | undelayed_event_cancel
        loc from to:
      undelayed_event (ThreadEvent.cancel loc from to) (ThreadEvent.cancel loc from to)
    | undelayed_event_program
        e_src e_tgt
        (EVENT_SRC: ThreadEvent.is_program e_src)
        (EVENT_TGT: ThreadEvent.is_program e_tgt)
        (EVENT_EQ: ThreadEvent.get_program_event e_src = ThreadEvent.get_program_event e_tgt):
      undelayed_event e_src e_tgt
  .
  #[local] Hint Constructors undelayed_event: core.

  Lemma undelayed_event_program_event
        e_src e_tgt
        (EVENT: undelayed_event e_src e_tgt):
    ThreadEvent.get_program_event e_src = ThreadEvent.get_program_event e_tgt.
  Proof.
    inv EVENT; ss.
  Qed.

  Lemma undelayed_event_is_pf
        e_src e_tgt
        (EVENT: undelayed_event e_src e_tgt):
    ThreadEvent.is_pf e_src <-> ThreadEvent.is_pf e_tgt.
  Proof.
    inv EVENT; ss.
    destruct e_src, e_tgt; clarify.
  Qed.

  Lemma undelayed_event_is_internal
        e_src e_tgt
        (EVENT: undelayed_event e_src e_tgt):
    ThreadEvent.is_internal e_src <-> ThreadEvent.is_internal e_tgt.
  Proof.
    inv EVENT; ss.
    destruct e_src, e_tgt; clarify.
  Qed.

  Lemma undelayed_event_is_program
        e_src e_tgt
        (EVENT: undelayed_event e_src e_tgt):
    ThreadEvent.is_program e_src <-> ThreadEvent.is_program e_tgt.
  Proof.
    inv EVENT; ss.
  Qed.

  Lemma undelayed_event_non_sc
        e_src e_tgt
        (EVENT: undelayed_event e_src e_tgt)
        (MACHINE_EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt):
    non_sc e_src <-> non_sc e_tgt.
  Proof.
    inv EVENT; ss.
    destruct e_src, e_tgt; clarify; ss.
  Qed.

  Lemma undelayed_thread_non_promise_step
        lang
        th0_src
        th0_tgt
        e_tgt th1_tgt
        (SIM: undelayed_thread th0_src th0_tgt)
        (LC_WF_SRC: Local.wf th0_src.(Thread.local) th0_src.(Thread.global))
        (GL_WF_SRC: Global.wf th0_src.(Thread.global))
        (LC_WF_TGT: Local.wf th0_tgt.(Thread.local) th0_tgt.(Thread.global))
        (GL_WF_TGT: Global.wf th0_tgt.(Thread.global))
        (STEP: @Thread.step lang e_tgt th0_tgt th1_tgt)
        (EVENT: match e_tgt with ThreadEvent.promise _ => False | _ => True end):
    (exists e_src th1_src,
        (<<STEP: Thread.step e_src th0_src th1_src>>) /\
        (<<SIM: undelayed_thread th1_src th1_tgt>>) /\
        (<<EVENT1: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>>) /\
        (<<EVENT2: release_event e_src <-> release_event e_tgt>>) /\
          (<<EVENT3: undelayed_event e_src e_tgt>>) /\
          (<<OWNEDSRC: owned_future_global_promises
                         (BoolMap.minus th0_src.(Thread.global).(Global.promises) th0_src.(Thread.local).(Local.promises))
                         (th0_src.(Thread.global)) (th1_src.(Thread.global))>>) /\
        (<<OWNED: owned_future_global_promises
                    (BoolMap.minus th0_src.(Thread.global).(Global.promises) th0_src.(Thread.local).(Local.promises))
                    (th0_tgt.(Thread.global)) (th1_tgt.(Thread.global))>>)) \/
    (exists e_src th1_src,
        (<<STEP_FAILURE: Thread.step e_src th0_src th1_src>>) /\
        (<<EVENT_FAILURE: ThreadEvent.get_machine_event e_src = MachineEvent.failure>>)).
  Proof.
    destruct th0_src as [st0_src lc0_src gl0_src], th0_tgt as [st0_tgt lc0_tgt gl0_tgt].
    inv SIM. ss. subst. inv STEP.
    { left. inv LOCAL0; ss.
      - exploit undelayed_reserve; try exact LOCAL; try exact GLOBAL; eauto. i. des.
        esplits; eauto.
      - exploit undelayed_cancel; try exact LOCAL; try exact GLOBAL; eauto. i. des.
        esplits; eauto.
    }
    exploit undelayed_program_step; try exact LOCAL; try exact GLOBAL; eauto. i. des.
    { left. esplits.
      - econs 2; try exact STEP. rewrite EVENT3. eauto.
      - ss.
      - ss.
      - ss.
      - econs 4; ss.
        + inv STEP; ss.
        + inv LOCAL0; ss.
      - ss.
      - ss.
    }
    { right. esplits.
      - econs 2; try exact STEP. rewrite EVENT0. eauto.
      - ss.
    }
  Qed.

  Lemma undelayed_thread_rtc_pf_step
        lang
        th0_src
        th0_tgt th1_tgt
        (SIM: undelayed_thread th0_src th0_tgt)
        (LC_WF_SRC: Local.wf th0_src.(Thread.local) th0_src.(Thread.global))
        (GL_WF_SRC: Global.wf th0_src.(Thread.global))
        (LC_WF_TGT: Local.wf th0_tgt.(Thread.local) th0_tgt.(Thread.global))
        (GL_WF_TGT: Global.wf th0_tgt.(Thread.global))
        (STEPS: rtc (pstep (@Thread.step lang) (ThreadEvent.is_pf /1\ non_sc)) th0_tgt th1_tgt):
    (exists th1_src,
        (<<STEPS: rtc (pstep (@Thread.step lang) (ThreadEvent.is_pf /1\ non_sc)) th0_src th1_src>>) /\
        (<<SIM: undelayed_thread th1_src th1_tgt>>)) \/
    (exists th1_src e_src th2_src,
        (<<STEPS: rtc (pstep (@Thread.step lang) (ThreadEvent.is_pf /1\ non_sc)) th0_src th1_src>>) /\
        (<<STEP_FAILURE: Thread.step e_src th1_src th2_src>>) /\
        (<<EVENT_FAILURE: ThreadEvent.get_machine_event e_src = MachineEvent.failure>>)).
  Proof.
    revert th0_src SIM LC_WF_SRC GL_WF_SRC.
    induction STEPS; i; eauto.
    inv H. des.
    exploit undelayed_thread_non_promise_step; try exact SIM; eauto.
    { destruct e; ss. }
    i. des.
    { exploit Thread.step_future; try exact STEP; eauto. i. des.
      exploit Thread.step_future; try exact STEP0; eauto. i. des.
      exploit IHSTEPS; try exact SIM0; eauto. i. des.
      { left. esplits.
        - econs 2; [|eauto]. econs; eauto.
          exploit undelayed_event_is_pf; eauto. i.
          exploit undelayed_event_non_sc; eauto. i.
          rewrite x1, x2. ss.
        - ss.
      }
      { right. esplits.
        - econs 2; [|eauto]. econs; eauto.
          exploit undelayed_event_is_pf; eauto. i.
          exploit undelayed_event_non_sc; eauto. i.
          rewrite x1, x2. ss.
        - eauto.
        - eauto.
      }
    }
    { right. esplits; eauto. }
  Qed.

  Lemma undelayed_thread_promise_step
        lang
        th0_src
        th0_tgt
        loc th1_tgt
        (SIM: undelayed_thread th0_src th0_tgt)
        (LC_WF_SRC: Local.wf th0_src.(Thread.local) th0_src.(Thread.global))
        (GL_WF_SRC: Global.wf th0_src.(Thread.global))
        (LC_WF_TGT: Local.wf th0_tgt.(Thread.local) th0_tgt.(Thread.global))
        (GL_WF_TGT: Global.wf th0_tgt.(Thread.global))
        (STEP: @Thread.step lang (ThreadEvent.promise loc) th0_tgt th1_tgt)
        (STEPS: rtc_consistent th1_tgt):
    (exists th1_src,
        (<<STEP: Thread.step (ThreadEvent.promise loc) th0_src th1_src>>) /\
        (<<SIM: undelayed_thread th1_src th1_tgt>>) /\
        (<<OWNEDSRC: owned_future_global_promises
                    (BoolMap.minus th0_src.(Thread.global).(Global.promises) th0_src.(Thread.local).(Local.promises))
                    (th0_src.(Thread.global)) (th1_src.(Thread.global))>>) /\
        (<<OWNED: owned_future_global_promises
                    (BoolMap.minus th0_src.(Thread.global).(Global.promises) th0_src.(Thread.local).(Local.promises))
                    (th0_tgt.(Thread.global)) (th1_tgt.(Thread.global))>>)) \/
    (exists e_src th1_src th2_src,
        (<<STEPS: rtc (pstep (@Thread.step _) (ThreadEvent.is_pf /1\ non_sc)) th0_src th1_src>>) /\
        (<<STEP_FAILURE: Thread.step e_src th1_src th2_src>>) /\
        (<<EVENT_FAILURE: ThreadEvent.get_machine_event e_src = MachineEvent.failure>>)).
  Proof.
    destruct (th0_src.(Thread.global).(Global.promises) loc) eqn:GPRM_SRC; cycle 1.
    { left.
      destruct th0_src as [st0_src [tview0_src prm0_src rsv0_src] [sc0_src gprm0_src mem0_src]],
          th0_tgt as [st0_tgt [tview0_tgt prm0_tgt rsv0_tgt] [sc0_tgt gprm0_tgt mem0_tgt]].
      inv SIM. inv LOCAL. ss. subst.
      inv STEP; inv LOCAL. inv LOCAL0. inv PROMISE. ss.
      esplits.
      { econs. econs. econs; eauto. }
      { econs; ss.
        { inv GLOBAL. econs; ss.
          { eapply BoolMap.le_add; eauto. }
          ii.
          specialize (MEM loc0 to).
          erewrite (@BoolMap.add_o prm2); eauto.
          erewrite loc_fun_add_spec. condtac; ss. subst.
          inv MEM; try congr; econs; ss.
        }
      }
      { ii. econs; ss.
        erewrite BoolMap.add_o; eauto. condtac; ss. subst.
        unfold BoolMap.minus in OWNED.
        rewrite GPRM_SRC in *. ss.
      }
      { ii. econs; ss.
        erewrite BoolMap.add_o; eauto. condtac; ss. subst.
        unfold BoolMap.minus in OWNED.
        rewrite GPRM_SRC in *. ss.
      }
    }

    { right. inv STEPS. des.
      exploit CurrentCertify.rtc_step_consistent_ceritfy_racy_promise; eauto. i. inv x1.
      { exploit undelayed_thread_rtc_pf_step; eauto. i. des.
        { exploit Thread.rtc_all_step_future;
            try eapply rtc_implies; try exact STEPS0; eauto.
          { i. inv H. econs. eauto. }
          i. des.
          exploit Thread.rtc_all_step_future;
            try eapply rtc_implies; try exact STEPS1; eauto.
          { i. inv H. econs. eauto. }
          i. des.
          exploit undelayed_thread_non_promise_step; try exact STEP_FAILURE; eauto.
          { destruct e; ss. }
          i. des.
          { esplits; eauto. congr. }
          { esplits; eauto. }
        }
        { esplits; eauto. }
      }
      { exploit undelayed_thread_rtc_pf_step; eauto. i. des.
        { exploit Thread.rtc_all_step_future;
            try eapply rtc_implies; try exact STEPS0; eauto.
          { i. inv H. econs. eauto. }
          i. des.
          exploit Thread.rtc_all_step_future;
            try eapply rtc_implies; try exact STEPS1; eauto.
          { i. inv H. econs. eauto. }
          i. des.
          exploit undelayed_thread_non_promise_step; try exact STEP_FAILURE; eauto; ss. i. des.
          { cut (exists th, Thread.step (ThreadEvent.racy_write loc None val ord) th1_src th).
            { i. des. esplits; try exact H; eauto. }
            exploit Thread.rtc_all_step_promises_minus;
              try eapply rtc_implies; try exact STEPS1.
            { i. inv H. econs. eauto. }
            i. inv EVENT3. destruct e_src; ss. inv EVENT_EQ.
            inv STEP0; inv LOCAL. ss.
            esplits. econs 2; eauto. econs. econs.
            inv STEP; inv LOCAL. inv LOCAL1. inv PROMISE. inv ADD.
            inv SIM. inv LOCAL. ss.
            rewrite PROMISES in x1.
            eapply equal_f in x1. unfold BoolMap.minus in x1.
            rewrite GPRM_SRC, GET in x1. ss.
            destruct (lc1.(Local.promises) loc) eqn:X, (gl1.(Global.promises) loc) eqn:Y; ss.
            econs; eauto.
          }
          { esplits; eauto. }
        }
        { esplits; eauto. }
      }
    }
  Qed.

  Lemma undelayed_thread_step
        lang
        th0_src
        th0_tgt
        e_tgt th1_tgt
        (SIM: undelayed_thread th0_src th0_tgt)
        (LC_WF_SRC: Local.wf th0_src.(Thread.local) th0_src.(Thread.global))
        (GL_WF_SRC: Global.wf th0_src.(Thread.global))
        (LC_WF_TGT: Local.wf th0_tgt.(Thread.local) th0_tgt.(Thread.global))
        (GL_WF_TGT: Global.wf th0_tgt.(Thread.global))
        (STEP: @Thread.step lang e_tgt th0_tgt th1_tgt)
        (STEPS: ThreadEvent.get_machine_event e_tgt <> MachineEvent.failure -> rtc_consistent th1_tgt):
    (exists e_src th1_src,
        (<<STEP: Thread.step e_src th0_src th1_src>>) /\
        (<<SIM: undelayed_thread th1_src th1_tgt>>) /\
        (<<EVENT1: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>>) /\
        (<<EVENT2: release_event e_src <-> release_event e_tgt>>) /\
        (<<EVENT3: ThreadEvent.get_program_event e_src = ThreadEvent.get_program_event e_tgt>>) /\
        (<<OWNEDSRC: owned_future_global_promises
                       (BoolMap.minus th0_src.(Thread.global).(Global.promises) th0_src.(Thread.local).(Local.promises))
                       (th0_src.(Thread.global)) (th1_src.(Thread.global))>>) /\
        (<<OWNED: owned_future_global_promises
                    (BoolMap.minus th0_src.(Thread.global).(Global.promises) th0_src.(Thread.local).(Local.promises))
                    (th0_tgt.(Thread.global)) (th1_tgt.(Thread.global))>>)) \/
    (exists e_src th1_src th2_src,
        (<<STEPS: rtc (pstep (@Thread.step _) (ThreadEvent.is_pf /1\ non_sc)) th0_src th1_src>>) /\
        (<<STEP_FAILURE: Thread.step e_src th1_src th2_src>>) /\
        (<<EVENT_FAILURE: ThreadEvent.get_machine_event e_src = MachineEvent.failure>>)).
  Proof.
    destruct (match e_tgt with ThreadEvent.promise _ => true | _ => false end) eqn:EVENT.
    { destruct e_tgt; ss.
      exploit undelayed_thread_promise_step; eauto.
      { eapply STEPS; ss. }
      i. des.
      - left. esplits; eauto.
      - right. esplits; eauto.
    }
    { exploit undelayed_thread_non_promise_step; eauto.
      { destruct e_tgt; ss. }
      i. des.
      - left. esplits; eauto.
        apply undelayed_event_program_event; ss.
      - right. esplits; eauto.
    }
  Qed.
End DELAYEDSTEP.

Section DELAYED.
  Variable lang: language.

  Definition delayed st0 st1 lc0 lc1 gl0 gl1: Prop :=
      exists lc1' gl1',
        (<<STEPS: rtc (tau lower_step) (Thread.mk lang st0 lc0 gl0) (Thread.mk _ st1 lc1' gl1')>>) /\
          (<<SIMLC: sim_local lc1' lc1>>) /\
          (<<SIMGLOBAL: delayed_global_private lc1' lc1 gl1' gl1>>)
  .

  Lemma lower_step_owned_future_global_promises
        (th1 th2: Thread.t lang) e
        (STEP: lower_step e th1 th2)
        (LC_WF1: Local.wf (Thread.local th1) (Thread.global th1))
        (GL_WF1: Global.wf (Thread.global th1))
    :
    owned_future_global_promises
      (BoolMap.minus th1.(Thread.global).(Global.promises) th1.(Thread.local).(Local.promises))
      (th1.(Thread.global)) (th2.(Thread.global)).
  Proof.
    inv STEP. des; subst.
    { inv STEP0. ss.
      hexploit local_program_step_owned_future; eauto. i. des; eauto.
      destruct e; ss. clarify. destruct ord; ss.
    }
    { hexploit Thread.step_promises_minus; eauto. i.
      inv STEP; [|inv LOCAL]. inv LOCAL.
      hexploit local_cancel_step_owned_future; eauto. i. ss.
      inv STEP0. ss.
      hexploit local_program_step_owned_future; eauto. i. des.
      { r. etrans; eauto. }
      rewrite H in RACE.
      unfold BoolMap.minus, andb, negb in RACE. des_ifs.
      inv LOCAL0. ss. clarify.
    }
  Qed.

  Lemma lower_steps_owned_future_global_promises
        (th1 th2: Thread.t lang)
        (STEPS: rtc (tau lower_step) th1 th2)
        (LC_WF1: Local.wf (Thread.local th1) (Thread.global th1))
        (GL_WF1: Global.wf (Thread.global th1))
    :
    owned_future_global_promises
      (BoolMap.minus th1.(Thread.global).(Global.promises) th1.(Thread.local).(Local.promises))
      (th1.(Thread.global)) (th2.(Thread.global)).
  Proof.
    revert LC_WF1 GL_WF1. induction STEPS; i.
    { refl. }
    { inv H. hexploit lower_step_future; eauto. i. des.
      hexploit lower_step_owned_future_global_promises; eauto.
      i. des. etrans; eauto.
      eapply lower_step_step in TSTEP.
      eapply Thread.rtc_all_step_promises_minus in TSTEP.
      rewrite TSTEP. auto.
    }
  Qed.

  Lemma delayed_sync st0 st1 lc0 lc1 gl0 gl1
        (DELAYED: delayed st0 st1 lc0 lc1 gl0 gl1)
        (GL0: Global.wf gl0)
        (GL1: Global.wf gl1)
        (LC0: Local.wf lc0 gl0)
        (LC1: Local.wf lc1 gl1)
    :
    exists lc1' gl1',
      (<<STEPS: rtc (tau lower_step) (Thread.mk lang st0 lc0 gl0) (Thread.mk _ st1 lc1' gl1')>>) /\
        (<<SIMLC: sim_local lc1' lc1>>) /\
        (<<SIMGL: delayed_global_private lc1' lc1 gl1' gl1>>) /\
        (<<WF: delayed st1 st1 lc1' lc1 gl1' gl1>>) /\
        (<<OWNED: owned_future_global_promises
                    (BoolMap.minus gl0.(Global.promises) lc0.(Local.promises))
                    gl0 gl1'>>)
  .
  Proof.
    unfold delayed in *. des.
    hexploit lower_steps_future; eauto. i. des; ss.
    esplits; eauto.
    eapply lower_steps_owned_future_global_promises in STEPS; eauto.
  Qed.

  Lemma delayed_step_non_release st0 st1 lc0 lc1 gl0 gl1
        e st2 lc2 gl2
        (STEP: Thread.step e (Thread.mk _ st1 lc1 gl1) (Thread.mk _ st2 lc2 gl2))
        (DELAYED: delayed st0 st1 lc0 lc1 gl0 gl1)
        (NRELEASE: ~ release_event e)
        (GL0: Global.wf gl0)
        (GL1: Global.wf gl1)
        (LC0: Local.wf lc0 gl0)
        (LC1: Local.wf lc1 gl1)
        (CONSISTENT: ThreadEvent.get_machine_event e <> MachineEvent.failure -> rtc_consistent (Thread.mk _ st2 lc2 gl2))
    :
    (exists lc0' gl0',
        (<<PROMISES: rtc (@Thread.internal_step _) (Thread.mk _ st0 lc0 gl0) (Thread.mk _ st0 lc0' gl0')>>) /\
          (<<DELAYED: delayed st0 st2 lc0' lc2 gl0' gl2>>) /\
          (<<SIMGL: delayed_global_private lc0' lc2 gl0' gl2>>) /\
          (<<FUTURESRC: owned_future_global_promises
                          (BoolMap.minus gl0.(Global.promises) lc0.(Local.promises))
                          gl0 gl0'>>) /\
          (<<FUTURETGT: owned_future_global_promises
                          (BoolMap.minus gl0.(Global.promises) lc0.(Local.promises))
                          gl1 gl2>>) /\
          (<<SILENT: ThreadEvent.get_machine_event e = MachineEvent.silent>>)) \/
      (<<FAILURE: Thread.steps_failure (Thread.mk lang st0 lc0 gl0)>>).
  Proof.
    hexploit Thread.step_future; eauto. i. des; ss.
    hexploit delayed_sync; eauto. i. des.
    hexploit lower_steps_future; eauto. i. des; ss.
    hexploit undelayed_thread_step.
    { instantiate (2:=Thread.mk _ _ _ _). instantiate (1:=Thread.mk _ _ _ _).
      econs.
      { simpl. eauto. }
      { simpl. eapply SIMLC. }
      { simpl. eapply SIMGL. }
    }
    all: eauto.
    i. des; cycle 1.
    { right. econs.
      { etrans.
        { eapply tau_lower_steps_tau_steps. eapply STEPS. }
        { eapply rtc_implies; [|eapply STEPS0].
          i. inv H. des. inv EVENT0. econs; eauto.
        }
      }
      { eauto. }
      { eauto. }
    }
    inv SIM. ss. destruct th1_src. ss. subst.
    hexploit Thread.step_future; eauto. i. des; ss.
    destruct (ThreadEvent.get_machine_event e) eqn:EVT; cycle 1.
    { destruct e; ss. }
    { right. econs.
      { eapply tau_lower_steps_tau_steps. eapply STEPS. }
      { eauto. }
      { eauto. }
    }
    hexploit split_step; eauto.
    i. des; cycle 1.
    { right. econs.
      { eapply tau_lower_steps_tau_steps. eapply STEPS. }
      { eauto. }
      { eauto. }
    }
    hexploit reorder_lower_steps_internal_steps; [| |eapply STEPS|eapply INTERNALS|..]; eauto.
    i. des; ss.
    destruct th1', th1.
    hexploit Thread.rtc_internal_step_future; eauto. i. des; ss; subst.
    left. esplits.
    { eapply STEPS1. }
    { unfold delayed. esplits.
      { etrans; [eapply STEPS2|eapply LOWER]. }
      { eauto. }
      { auto. }
    }
    { eapply lower_steps_delayed_preserve; [..|eauto]; eauto.
      etrans; eauto.
    }
    { eapply rtc_internal_step_owned_future in STEPS1; eauto. }
    { eapply tau_lower_steps_tau_steps in STEPS.
      eapply Thread.rtc_tau_step_promises_minus in STEPS. ss.
      rewrite STEPS. auto.
    }
    { auto. }
  Qed.

  Lemma delayed_step_release st0 st1 lc0 lc1 gl0 gl1
        e_tgt st2 lc2 gl2
        (STEP: Thread.step e_tgt (Thread.mk _ st1 lc1 gl1) (Thread.mk _ st2 lc2 gl2))
        (DELAYED: delayed st0 st1 lc0 lc1 gl0 gl1)
        (RELEASE: release_event e_tgt)
        (GL0: Global.wf gl0)
        (GL1: Global.wf gl1)
        (LC0: Local.wf lc0 gl0)
        (LC1: Local.wf lc1 gl1)
        (CONSISTENT: ThreadEvent.get_machine_event e_tgt <> MachineEvent.failure -> rtc_consistent (Thread.mk _ st2 lc2 gl2))
    :
    (exists lc2' gl2' e_src th,
          (<<LOWERS: rtc (tau lower_step) (Thread.mk _ st0 lc0 gl0) th>>) /\
          (<<STEP: Thread.step e_src th (Thread.mk _ st2 lc2' gl2')>>) /\
          (<<SIMGL: delayed_global_private lc2' lc2 gl2' gl2>>) /\
          (<<DELAYED: delayed st2 st2 lc2' lc2 gl2' gl2>>) /\
          (<<FUTURESRC: owned_future_global_promises
                          (BoolMap.minus gl0.(Global.promises) lc0.(Local.promises))
                          gl0 gl2'>>) /\
          (<<FUTURETGT: owned_future_global_promises
                          (BoolMap.minus gl0.(Global.promises) lc0.(Local.promises))
                          gl1 gl2>>) /\
          (<<RELEASE: release_event e_src>>) /\
          (<<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>>)) \/
      (<<FAILURE: Thread.steps_failure (Thread.mk lang st0 lc0 gl0)>>).
  Proof.
    hexploit Thread.step_future; eauto. i. des; ss.
    hexploit delayed_sync; eauto. i. des.
    hexploit lower_steps_future; eauto. i. des; ss.
    hexploit undelayed_thread_step.
    { instantiate (2:=Thread.mk _ _ _ _). instantiate (1:=Thread.mk _ _ _ _).
      econs.
      { simpl. eauto. }
      { simpl. eapply SIMLC. }
      { simpl. eapply SIMGL. }
    }
    all: eauto.
    i. des; cycle 1.
    { right. econs.
      { etrans.
        { eapply tau_lower_steps_tau_steps. eapply STEPS. }
        { eapply rtc_implies; [|eapply STEPS0].
          i. inv H. des. inv EVENT0. econs; eauto.
        }
      }
      { eauto. }
      { eauto. }
    }
    inv SIM. ss. destruct th1_src. ss. subst.
    hexploit Thread.rtc_tau_step_promises_minus.
    { eapply tau_lower_steps_tau_steps; eauto. }
    s. i. left. esplits.
    { eauto. }
    { eauto. }
    { auto. }
    { r. esplits; eauto. }
    { etrans.
      { eauto. }
      { rewrite H. auto. }
    }
    { rewrite H. auto. }
    { auto. }
    { auto. }
  Qed.

  Lemma cherrypicked_global_delayed_global gl_tgt gl_src lc
        lc0 lc1 gl_src0 gl_src1 gl_tgt0 gl_tgt1
        (AFTER: delayed_global_private lc1 lc gl_tgt1 gl_tgt)
        (BEFORE: delayed_global_private lc0 lc gl_src0 gl_src)
        (CHERRY: cherrypicked_global
                   ((gl_src0, lc0), (gl_tgt0, lc0))
                   ((gl_src1, lc1), (gl_tgt1, lc1)))
        (SIMLOCAL: sim_local lc1 lc)
        (OTHERSRC: BoolMap.minus gl_src1.(Global.promises) lc1.(Local.promises)
                   =
                     BoolMap.minus gl_src0.(Global.promises) lc0.(Local.promises))
        (OTHERTGT: BoolMap.minus gl_tgt1.(Global.promises) lc1.(Local.promises)
                   =
                     BoolMap.minus gl_tgt0.(Global.promises) lc0.(Local.promises))
        (OWNEDSRC: owned_future_global_promises lc0.(Local.promises) gl_tgt gl_src)
    :
    delayed_global_private lc1 lc gl_src1 gl_src.
  Proof.
    inv AFTER; ss. inv BEFORE; ss. des_ifs. des; subst.
    inv SIMLOCAL. ss. subst.
    econs; ss.
    { intros loc. specialize (PRM loc). dup PRM. inv PRM.
      { eapply PROMISES0. }
      { ii. exfalso. exploit (OWNEDSRC loc); auto. i. r in x0. des; ss.
        rewrite PROMISES in H6; eauto.
      }
    }
    { ii. eapply equal_f with (x:=loc) in OTHERSRC.
      eapply equal_f with (x:=loc) in OTHERTGT.
      specialize (MEM loc to). specialize (MEM0 loc to).
      rename MEM into AFTER. rename MEM0 into BEFORE.
      specialize (PRM loc). specialize (MEM1 loc to). inv MEM1.
      { inv PRM.
        { rewrite <- H5 in BEFORE. eapply BEFORE. }
        { inv BEFORE; try by (econs; eauto).
          { clarify. unfold BoolMap.minus, andb, negb in OTHERSRC.
            rewrite <- H2 in OTHERSRC. rewrite <- H8 in OTHERSRC.
            des_ifs. rewrite <- H2 in *. clarify.
          }
          { rewrite H5 in *. rewrite <- H14 in *. ss. }
        }
      }
      { inv PRM.
        { rewrite <- H13 in AFTER. rewrite <- H14 in AFTER.
          rewrite <- H5 in AFTER. rewrite <- H6 in AFTER.
          inv AFTER. rewrite <- H5 in BEFORE. rewrite <- H1 in BEFORE. inv BEFORE.
          econs. exploit (OWNEDSRC loc).
          { eauto. }
          i. r in x0. des; ss. exploit MEM; eauto. i.
          rewrite x0 in H17. clarify.
        }
        { rewrite <- H13 in AFTER. rewrite <- H14 in AFTER.
          rewrite <- H5 in AFTER. rewrite <- H6 in AFTER. inv AFTER.
          rewrite <- H5 in BEFORE. rewrite <- H1 in BEFORE. inv BEFORE.
          exploit (OWNEDSRC loc).
          { eauto. }
          i. r in x0. des; ss. exploit MEM; eauto. i.
          rewrite x0 in H21. clarify. econs; eauto.
        }
      }
    }
  Qed.

  Lemma delayed_future st0 st1 lc0 lc1 gl0 gl1 gl0' gl1'
        (DELAYED: delayed st0 st1 lc0 lc1 gl0 gl1)
        (FUTURESRC: Global.strong_le gl0 gl0')
        (FUTURETGT: Global.le gl1 gl1')
        (OWNEDSRC: owned_future_global_promises lc0.(Local.promises) gl0 gl0')
        (OWNEDTGT: owned_future_global_promises lc0.(Local.promises) gl1 gl1')
        (PRIVATE: delayed_global_private lc0 lc1 gl0 gl1)
        (PUBLIC: delayed_global_public gl0' gl1')
        (GL0: Global.wf gl0)
        (GL1: Global.wf gl1)
        (LC0: Local.wf lc0 gl0)
        (LC1: Local.wf lc1 gl1)
        (GLNEW0: Global.wf gl0')
        (GLNEW1: Global.wf gl1')
        (LCNEW0: Local.wf lc0 gl0')
        (LCNEW1: Local.wf lc1 gl1')
    :
    (<<DELAYED: delayed st0 st1 lc0 lc1 gl0' gl1'>>) \/
      (<<FAILURE: Thread.steps_failure (Thread.mk lang st0 lc0 gl0')>>).
  Proof.
    hexploit delayed_sync; eauto. i. des.
    exploit delayed_global_public_to_private.
    { eapply PRIVATE. }
    { eapply delayed_global_private_to_public; eauto. }
    { eapply PUBLIC. }
    all: eauto.
    { eapply FUTURESRC. }
    intros PRIVATE0.
    hexploit lower_steps_strong_future; eauto. i. des; cycle 1.
    { right. econs.
      { eapply tau_lower_steps_tau_steps; eauto. }
      { eauto. }
      { eauto. }
    }
    left. unfold delayed. esplits.
    { eapply STEPS0. }
    { eauto. }
    { exploit cherrypicked_global_delayed_global; [| |eapply CHERRY|..]; eauto.
      { eapply tau_lower_steps_tau_steps in STEPS0.
        eapply Thread.rtc_tau_step_promises_minus in STEPS0. ss.
      }
      { eapply tau_lower_steps_tau_steps in STEPS.
        eapply Thread.rtc_tau_step_promises_minus in STEPS. ss.
      }
    }
  Qed.

  Lemma cap_owned_future_mem_loc loc mem
    :
    owned_future_mem_loc loc mem (Memory.cap_of mem).
  Proof.
    r. i. hexploit Memory.cap_inv; eauto.
    { eapply Memory.cap_of_cap; eauto. }
    i. des; clarify.
  Qed.

  Lemma cap_owned_future_global_promises prom gl
    :
    owned_future_global_promises prom gl (Global.cap_of gl).
  Proof.
    ii. r. splits.
    { eapply cap_owned_future_mem_loc. }
    { ss. }
  Qed.
End DELAYED.
