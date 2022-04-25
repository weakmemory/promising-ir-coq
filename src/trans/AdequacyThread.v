From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Language.
From PromisingLib Require Import Event.

Require Import Time.
Require Import View.
Require Import BoolMap.
Require Import Promises.
Require Import Reserves.
Require Import Cell.
Require Import Memory.
Require Import Global.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import Simulation.

Require Import SimMemory.
Require Import SimLocal.
Require Import SimGlobal.
Require Import SimThread.

Set Implicit Arguments.


Lemma tids_find
      tids ths_src ths_tgt
      tid
      (TIDS_SRC: tids = Threads.tids ths_src)
      (TIDS_TGT: tids = Threads.tids ths_tgt):
  (exists lang_src st_src lc_src,
      IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src)) <->
  (exists lang_tgt st_tgt lc_tgt, 
      IdentMap.find tid ths_tgt = Some (existT _ lang_tgt st_tgt, lc_tgt)).
Proof.
  split; i; des.
  - destruct (IdentSet.mem tid tids) eqn:MEM.
    + rewrite TIDS_TGT in MEM.
      rewrite Threads.tids_o in MEM.
      destruct (IdentMap.find tid ths_tgt); ss.
      destruct p. destruct s. esplits; eauto.
    + rewrite TIDS_SRC in MEM.
      rewrite Threads.tids_o in MEM.
      destruct (IdentMap.find tid ths_src); ss.
  - destruct (IdentSet.mem tid tids) eqn:MEM.
    + rewrite TIDS_SRC in MEM.
      rewrite Threads.tids_o in MEM.
      destruct (IdentMap.find tid ths_src); ss.
      destruct p. destruct s. esplits; eauto.
    + rewrite TIDS_TGT in MEM.
      rewrite Threads.tids_o in MEM.
      destruct (IdentMap.find tid ths_tgt); ss.
Qed.

Lemma thread_rtc_step_rtc_step
      ths1 tid lang st1 lc1 gl1 st2 lc2 gl2
      (WF: Configuration.wf (Configuration.mk ths1 gl1))
      (FIND: IdentMap.find tid ths1 = Some (existT _ lang st1, lc1))
      (STEPS: rtc (@Thread.tau_step lang (Global.max_reserved gl1))
                  (Thread.mk lang st1 lc1 gl1)
                  (Thread.mk lang st2 lc2 gl2))
      (CONS: Thread.consistent (Thread.mk lang st2 lc2 gl2)):
  rtc Configuration.tau_step
      (Configuration.mk ths1 gl1)
      (Configuration.mk (IdentMap.add tid (existT _ lang st2, lc2) ths1) gl2).
Proof.
  inv WF. inv WF0. ss. exploit THREADS; eauto. i.
  exploit Thread.rtc_tau_step_future; eauto. s. i. des.
  generalize (rtc_tail STEPS). i. des.
  - inv H0. inv TSTEP. econs; eauto.
    econs. rewrite <- EVENT. econs; ss; eauto.
  - inv H.
    replace (IdentMap.add tid (existT _ lang st2, lc2) ths1) with ths1; auto.
    apply IdentMap.eq_leibniz. ii.
    rewrite -> IdentMap.gsident; auto.
Qed.

Lemma sim_thread_sim
      ths_src gl0_src
      ths_tgt gl0_tgt
      (TIDS: Threads.tids ths_src = Threads.tids ths_tgt)
      (GLOBAL: sim_global gl0_src gl0_tgt)
      (SIM: forall tid lang_src st_src lc_src lang_tgt st_tgt lc_tgt,
          IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src) ->
          IdentMap.find tid ths_tgt = Some (existT _ lang_tgt st_tgt, lc_tgt) ->
          exists sim_terminal,
            @sim_thread lang_src lang_tgt sim_terminal st_src lc_src gl0_src st_tgt lc_tgt gl0_tgt)
  :
    sim (Configuration.mk ths_src gl0_src) (Configuration.mk ths_tgt gl0_tgt).
Proof.
  remember (Threads.tids ths_src) as tids eqn:TIDS_SRC.
  rename TIDS into TIDS_TGT.
  revert ths_src gl0_src ths_tgt gl0_tgt tids TIDS_SRC TIDS_TGT GLOBAL SIM.
  pcofix CIH. i. pfold. ii. splits.
  { (* TERMINAL CASE *)
    assert (NOTIN: forall tid lang_src st_src lc_src
                     (FIND: IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src))
                     (TID: ~ List.In tid (IdentSet.elements tids)),
               Language.is_terminal _ st_src /\ Local.is_terminal lc_src).
    { i. destruct (IdentSet.mem tid tids) eqn:MEM.
      - exfalso. apply TID. rewrite IdentSet.mem_spec in MEM.
        rewrite <- IdentSet.elements_spec1 in MEM.
        clear - MEM. induction MEM; [econs 1|econs 2]; auto.
      - rewrite TIDS_SRC in MEM. rewrite Threads.tids_o in MEM.
        destruct (IdentMap.find tid ths_src) eqn:IFIND; [inv MEM|]. ss.
    }
    assert (IN: forall tid lang_src st_src lc_src lang_tgt st_tgt lc_tgt
                  (TID: List.In tid (IdentSet.elements tids)),
               IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src) ->
               IdentMap.find tid ths_tgt = Some (existT _ lang_tgt st_tgt, lc_tgt) ->
               exists sim_terminal,
                 @sim_thread lang_src lang_tgt sim_terminal st_src lc_src gl0_src st_tgt lc_tgt gl0_tgt)
      by eauto.
    assert (TIDS_MEM: forall tid, List.In tid (IdentSet.elements tids) -> IdentSet.mem tid tids = true).
    { i. rewrite IdentSet.mem_spec.
      rewrite <- IdentSet.elements_spec1.
      eapply SetoidList.In_InA; auto.
    }
    assert (NODUP: List.NoDup (IdentSet.elements tids)).
    { specialize (IdentSet.elements_spec2w tids). i.
      clear - H. induction H; econs; eauto.
    }

    revert NOTIN IN TIDS_MEM NODUP.
    move tids at top. clear SIM. revert_until CIH.
    induction (IdentSet.elements tids); i.
    { right. esplits; eauto. ii. exploit NOTIN; eauto. }
    destruct (IdentMap.find a ths_src) as [[[lang_src st_src] lc_src]|] eqn:ASRC;
      destruct (IdentMap.find a ths_tgt) as [[[lang_tgt st_tgt] lc_tgt]|] eqn:ATGT; cycle 1.
    { exploit tids_find; [apply TIDS_SRC|apply TIDS_TGT|..]. i. des.
      exploit x0; eauto. intros x. des. rewrite ATGT in x. inv x.
    }
    { exploit tids_find; [apply TIDS_SRC|apply TIDS_TGT|..]. i. des.
      exploit x1; eauto. intros x. des. rewrite ASRC in x. inv x.
    }
    { exploit IHl; [exact TIDS_SRC|exact TIDS_TGT|..]; eauto; i.
      - eapply NOTIN; eauto. ii. inv H; ss. congr.
      - eapply IN; eauto. econs 2; eauto.
      - eapply TIDS_MEM; eauto. econs 2; eauto.
      - inv NODUP. ss.
    }
    generalize WF_SRC. intro X. inv X. ss. inv WF. exploit THREADS; eauto. intros x.
    generalize WF_TGT. intro X. inv X. ss. inv WF. exploit THREADS0; eauto. intros x0.
    exploit (IN a); eauto. i. des.
    exploit TERMINAL_TGT; eauto. i. des.
    exploit sim_global_max_reserved; try exact GLOBAL; eauto. i.
    punfold x2.
    exploit x2; try exact x; try exact x0; try refl; eauto. i. des.
    exploit TERMINAL; eauto. i. des.
    - (* failure *)
      left. inv FAILURE. destruct e3.
      econs; [refl|]. rewrite <- EVENT_FAILURE. econs; eauto. destruct e; ss.
    - (* non-failure *)
      exploit thread_rtc_step_rtc_step; try exact STEPS; eauto.
      { econs 2; try refl. s.
        inv THREAD. eapply sim_local_promises_bot; eauto.
      }
      s. i.
      exploit Configuration.rtc_step_future; try eapply x4; eauto. s. i. des.
      exploit IHl; try exact GLOBAL0; try exact WF2; try exact WF_TGT; eauto.
      { rewrite Threads.tids_add. rewrite IdentSet.add_mem; eauto. }
      { i. rewrite IdentMap.gsspec in FIND. revert FIND. condtac; ss; i.
        - subst. Configuration.simplify. split; auto.
          inv THREAD. econs. eapply sim_local_promises_bot; eauto.
        - eapply NOTIN; eauto. ii. des; ss. subst. ss.
      }
      { i. rewrite IdentMap.gsspec in H. revert H. condtac; ss; i.
        - subst. inv NODUP. congr.
        - exploit IN; eauto. i. des.
          exploit sim_thread_future; try exact x5; try exact GL_FUTURE; try refl. i. eauto.
      }
      { inv NODUP. ss. }
      intros x1. des.
      + left. inv x1.
        rewrite STEPS0 in x4. esplits; try exact x4; eauto.
      + right.
        rewrite x1 in x4. esplits; try exact x4; eauto.
  }

  { (* STEP CASE *)
    i. inv STEP_TGT. destruct e2. ss.
    destruct (IdentMap.find tid_tgt ths_src) as [[[lang_src st_src] lc_src]|] eqn:FIND_SRC; cycle 1.
    { remember (Threads.tids ths_src) as tids eqn:TIDS_SRC.
      exploit tids_find; [exact TIDS_SRC|exact TIDS_TGT|..]. i. des.
      exploit x1; eauto. intros x. des. rewrite FIND_SRC in x. inv x.
    }
    dup WF_SRC. inv WF_SRC0. inv WF. ss.
    dup WF_TGT. inv WF_TGT0. inv WF. ss.
    exploit SIM; eauto. i. des.
    exploit sim_global_max_reserved; eauto. i.
    exploit sim_thread_plus_step; try exact STEPS; try exact x0; eauto.
    { rewrite <- x1. refl. }
    s. i. des.
    { left. inv FAILURE. destruct e3.
      econs; try refl. rewrite <- EVENT_FAILURE. econs; eauto. destruct e; ss.
    }
    right. inv STEP0.
    { exploit thread_rtc_step_rtc_step; try exact STEPS0; eauto.
      { eapply sim_thread_consistent; eauto.
        apply CONSISTENT. destruct e0; ss.
      }
      i. rewrite <- EVENT. ss.
      esplits; eauto; ss.
      right. eapply CIH.
      - rewrite Threads.tids_add. rewrite IdentSet.add_mem; ss.
        rewrite Threads.tids_o. rewrite FIND_SRC. ss.
      - rewrite TIDS_TGT.
        rewrite Threads.tids_add. rewrite IdentSet.add_mem; ss.
        rewrite Threads.tids_o. rewrite TID. ss.
      - ss.
      - i. Configuration.simplify; eauto.
        exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
        exploit Thread.step_future; try exact STEP; eauto. s. i. des.
        exploit Thread.rtc_tau_step_future; try exact x2; eauto. s. i. des.
        exploit SIM; try eapply H; eauto. i. des.
        esplits.
        eapply sim_thread_future; try exact x3; eauto. etrans; eauto.
    }
    { esplits; eauto.
      - rewrite <- EVENT. econs 2. econs; eauto. i.
        eapply sim_thread_consistent; eauto.
        apply CONSISTENT. destruct e0, e_src; ss.
      - ss. right. eapply CIH.
        + rewrite Threads.tids_add. rewrite IdentSet.add_mem; ss.
          rewrite Threads.tids_o. rewrite FIND_SRC. ss.
        + rewrite TIDS_TGT.
          rewrite Threads.tids_add. rewrite IdentSet.add_mem; ss.
          rewrite Threads.tids_o. rewrite TID. ss.
        + ss.
        + i. Configuration.simplify; eauto.
          exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
          exploit Thread.step_future; try exact STEP; eauto. s. i. des.
          exploit Thread.rtc_tau_step_future; try exact STEPS0; eauto. s. i. des.
          exploit Thread.step_future; try exact STEP1; eauto. s. i. des.
          exploit SIM; try eapply H; eauto. i. des.
          esplits.
          eapply sim_thread_future; try exact x2; try by (etrans; eauto).
    }
  }
Unshelve.
{ auto. }
Qed.
