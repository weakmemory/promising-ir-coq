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
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Behavior.
Require Import Global.

Require Import OrdStep.
Require Import RARace.
Require Import SCStep.
Require Import Stable.
Require Import PFConfiguration.

Require Import LocalDRFRA.

Section SIM.

  Variable L: Loc.t -> bool.

  Lemma ra_thread_step_sc_thread_step_or_race lang
        (th0 th1: Thread.t lang) e
        (STEP: OrdThread.step L Ordering.acqrel Ordering.acqrel e th0 th1)
    :
      (<<STEP: SCThread.step L e th0 th1>>) \/
      (<<RACE: SCRace.race L th0>>).
  Proof.
    destruct (classic (SCRace.race L th0)) as [RACE|RACE]; auto.
    left. inv STEP. econs; eauto. inv LOCAL; ss.
    - econs; eauto.
    - inv LOCAL0. econs; eauto. econs; eauto.
      i. destruct (Time.le_lt_dec to' ts); auto. exfalso. eapply RACE.
      unfold SCRace.race, SCLocal.non_maximal. esplits; eauto; ss.
      inv STEP. inv READABLE. eapply TimeFacts.le_lt_lt; eauto.
      eapply RLX. des_ifs. etrans; [|eapply Ordering.join_r]. auto.
    - inv LOCAL0. econs; eauto. econs; eauto.
      i. destruct (Time.le_lt_dec to to'); auto. exfalso. eapply RACE.
      unfold SCRace.race, SCLocal.non_maximal. esplits; eauto; ss.
      inv STEP. inv WRITABLE. eapply TimeFacts.lt_le_lt; eauto.
    - inv LOCAL1. inv LOCAL2. econs; eauto.
      + econs; eauto.
        i. destruct (Time.le_lt_dec to' tsr); auto. exfalso. eapply RACE.
        unfold SCRace.race, SCLocal.non_maximal. esplits; eauto; ss.
        inv STEP. inv READABLE. eapply TimeFacts.le_lt_lt; eauto.
        eapply RLX. des_ifs. etrans; [|eapply Ordering.join_r]. auto.
      + econs; eauto.
        i. destruct (Time.le_lt_dec tsw to'); auto. exfalso. eapply RACE.
        unfold SCRace.race, SCLocal.non_maximal. esplits; eauto; ss.
        inv STEP0. inv WRITABLE. eapply TimeFacts.lt_le_lt; eauto.
        eapply TimeFacts.le_lt_lt; eauto. inv STEP. ss.
        etrans; [|eapply Time.join_l]. eapply Time.join_l.
    - econs; eauto.
    - econs; eauto.
    - econs; eauto.
    - inv LOCAL0.
      { econs. econs; eauto. }
    - econs; eauto.
    - econs; eauto.
    - econs; eauto. des.
      { econs 1; eauto. }
      { econs 2; eauto. }
  Qed.

  Lemma ra_thread_all_steps_sc_thread_all_steps_or_race lang
        (th0 th1: Thread.t lang)
        (STEPS: rtc (OrdThread.all_step L Ordering.acqrel Ordering.acqrel) th0 th1)
    :
      (<<STEPS: rtc (SCThread.all_step L) th0 th1>>) \/
      (exists th',
          (<<STEPS0: rtc (SCThread.all_step L) th0 th'>>) /\
          (<<STEPS1: rtc (OrdThread.all_step L Ordering.acqrel Ordering.acqrel) th' th1>>) /\
          (<<RACE: SCRace.race L th'>>)).
  Proof.
    induction STEPS; eauto. dup H. inv H.
    eapply ra_thread_step_sc_thread_step_or_race in USTEP; eauto. des.
    - left. econs; eauto. econs; eauto.
    - right. exists th'. esplits; eauto. econs; eauto. econs; eauto.
    - right. exists x. esplits; eauto.
    - right. exists x. esplits; eauto.
  Qed.

  Lemma ra_configuration_step_sc_configuration_step_or_race e tid c0 c1
        (STEP: OrdConfiguration.estep L Ordering.acqrel Ordering.acqrel e tid c0 c1)
        (WF: Configuration.wf c0)
    :
      (<<STEP: SCConfiguration.estep L e tid c0 c1>>) \/
      (<<RACE: SCRace.race_steps L c0 tid>>).
  Proof.
    destruct (classic (SCRace.race_steps L c0 tid)) as [RACE|RACE]; auto. left.
    inv STEP.

    exploit ra_thread_step_sc_thread_step_or_race; try apply STEP0.
    i. des; cycle 1.
    { exfalso. eapply RACE. unfold SCRace.race_steps. esplits; eauto. }

    econs; eauto.
  Qed.

  Lemma ra_configuration_steps_sc_configuration_steps_or_race c0 c1
        (STEPS: rtc (OrdConfiguration.all_step L Ordering.acqrel Ordering.acqrel) c0 c1)
        (WF: Configuration.wf c0)
    :
      (<<STEPS: rtc (SCConfiguration.all_step L) c0 c1>>) \/
      (exists c' tid,
          (<<STEPS: rtc (SCConfiguration.all_step L) c0 c'>>) /\
          (<<RACE: SCRace.race_steps L c' tid>>)).
  Proof.
    ginduction STEPS; eauto. i. inv H.
    eapply ra_configuration_step_sc_configuration_step_or_race in STEP; eauto. des.
    { exploit SCConfiguration.estep_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      { left. econs; eauto. econs; eauto. }
      { right. esplits; [|eapply RACE]. econs; eauto. econs; eauto. }
    }
    { right. esplits; eauto. }
  Qed.

  Lemma ra_behavior_sc_behavior_or_race c
        (RACEFREE: SCRace.racefree L c)
        (WF: Configuration.wf c)
    :
      behaviors (@OrdConfiguration.step L Ordering.acqrel Ordering.acqrel) c <2=
      behaviors (@SCConfiguration.step L) c.
  Proof.
    i. ginduction PR; eauto; i.
    - econs 1; eauto.
    - inv STEP.
      eapply ra_configuration_step_sc_configuration_step_or_race in STEP0; eauto. des.
      + econs 2; eauto.
        * rewrite <- H0. econs; eauto.
        * eapply IHPR; eauto.
          { eapply SCRace.step_racefree; eauto. econs; eauto. }
          { eapply SCConfiguration.step_future; eauto. econs; eauto. }
      + exfalso. eapply RACEFREE; eauto.
    - inv STEP.
      eapply ra_configuration_step_sc_configuration_step_or_race in STEP0; eauto. des.
      + econs 3; eauto.
        * rewrite <- H0. econs; eauto.
      + exfalso. eapply RACEFREE; eauto.
    - inv STEP.
      eapply ra_configuration_step_sc_configuration_step_or_race in STEP0; eauto. des.
      + econs 4; eauto.
        * rewrite <- H0. econs; eauto.
        * eapply IHPR; eauto.
          { eapply SCRace.step_racefree; eauto. econs; eauto. }
          { eapply SCConfiguration.step_future; eauto. econs; eauto. }
      + exfalso. eapply RACEFREE; eauto.
    - econs 5.
  Qed.

  Lemma sc_racefree_ra_racefree c
        (RACEFREE: SCRace.racefree L c)
        (WF: Configuration.wf c)
    :
      RARace.racefree L c.
  Proof.
    ii. unfold RARace.race in *. des.
    exploit ra_configuration_steps_sc_configuration_steps_or_race.
    { etrans.
      { eapply STEPS1. } econs 2.
      { econs; eauto. }
      { eapply STEPS2. }
    }
    { eauto. }
    i. des.
    2:{ eapply RACEFREE; eauto. }
    inv RACE.
    { des. eapply RACEFREE; [eauto|]. unfold SCRace.race_steps. esplits; eauto.
      assert (exists from msg, (<<GET: Memory.get loc to c3.(Configuration.global).(Global.memory) = Some (from, msg)>>) /\ (<<NRESERVE: msg <> Message.reserve>>)).
      { hexploit OrdConfiguration.rtc_all_step_future; [eapply STEPS1|..]; eauto.
        i. des.
        hexploit OrdConfiguration.estep_future; eauto. i. des.
        hexploit OrdConfiguration.rtc_all_step_future; [eapply STEPS2|..]; eauto. i. des.
        inv WRITE_STEP. ss.
        hexploit OrdThread.step_future; eauto.
        { eapply WF2; eauto. }
        { eapply WF2. }
        i. ss. des.
        assert (exists from msg, (<<GET: Memory.get loc to gl2.(Global.memory) = Some (from, msg)>>) /\ (<<NRESERVE: msg <> Message.reserve>>)).
        { inv STEP0. inv LOCAL; ss.
          { clarify. inv LOCAL0. inv STEP0. esplits.
            { eapply Memory.add_get0; eauto. }
            { ss. }
          }
          { clarify. inv LOCAL2. inv STEP0. esplits.
            { eapply Memory.add_get0; eauto. }
            { ss. }
          }
        }
        des. eapply Global.future_le in GL_FUTURE1. inv GL_FUTURE1.
        destruct msg; ss. eapply MEMORY in GET. eauto.
      }
      des. unfold RARace.wr_race, SCRace.race in *. esplits; eauto.
      { instantiate (1:=loc). destruct e; ss; clarify. }
      { des; auto. }
      econs. esplits; eauto. ss. des; auto.
    }
    { des. eapply RACEFREE; [eauto|]. unfold SCRace.race_steps. esplits; eauto.
      assert (exists from msg, (<<GET: Memory.get loc to c3.(Configuration.global).(Global.memory) = Some (from, msg)>>) /\ (<<NRESERVE: msg <> Message.reserve>>)).
      { hexploit OrdConfiguration.rtc_all_step_future; [eapply STEPS1|..]; eauto.
        i. des.
        hexploit OrdConfiguration.estep_future; eauto. i. des.
        hexploit OrdConfiguration.rtc_all_step_future; [eapply STEPS2|..]; eauto. i. des.
        inv WRITE_STEP. ss.
        hexploit OrdThread.step_future; eauto.
        { eapply WF2; eauto. }
        { eapply WF2. }
        i. ss. des.
        assert (exists from msg, (<<GET: Memory.get loc to gl2.(Global.memory) = Some (from, msg)>>) /\ (<<NRESERVE: msg <> Message.reserve>>)).
        { inv STEP0. inv LOCAL; ss.
          { clarify. inv LOCAL0. inv STEP0. esplits.
            { eapply Memory.add_get0; eauto. }
            { ss. }
          }
          { clarify. inv LOCAL2. inv STEP0. esplits.
            { eapply Memory.add_get0; eauto. }
            { ss. }
          }
        }
        des. eapply Global.future_le in GL_FUTURE1. inv GL_FUTURE1.
        destruct msg; ss. eapply MEMORY in GET. eauto.
      }
      des. unfold RARace.ww_race, SCRace.race in *. esplits; eauto.
      { instantiate (1:=loc). destruct e; ss; clarify. }
      { des; auto. }
      econs. esplits; eauto. ss. des; auto.
    }
  Qed.

End SIM.


(* LDRF-SC theorem *)
Theorem local_drf_sc L
        s
        (RACEFREE: SCRace.racefree_syn L s):
  behaviors (PFConfiguration.step ThreadEvent.get_machine_event_pf) (Configuration.init s) <2=
  behaviors (@SCConfiguration.step L) (Configuration.init s).
Proof.
  i. eapply local_drf_ra in PR; eauto.
  - eapply ra_behavior_sc_behavior_or_race; eauto.
    eapply Configuration.init_wf; eauto.
  - eapply sc_racefree_ra_racefree; eauto.
    eapply Configuration.init_wf; eauto.
Qed.
