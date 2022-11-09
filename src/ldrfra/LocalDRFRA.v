Require Import Lia.
Require Import Bool.
Require Import RelationClasses.
Require Import Program.

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
Require Import Configuration.
Require Import PFConfiguration.
Require Import Behavior.

Require Import OrdStep.
Require Import Stable.
Require Import WStep.
Require Import PFtoRA.
Require Import RARace.

Set Implicit Arguments.


(* LDRF-RA theorem *)

Theorem local_drf_ra L
        s
        (RACEFREE: RARace.racefree_syn L s):
  behaviors (PFConfiguration.step ThreadEvent.get_machine_event_pf) (Configuration.init s) <2=
  behaviors (@OrdConfiguration.step L Ordering.acqrel Ordering.acqrel) (Configuration.init s).
Proof.
  hexploit RARace.racefree_implies; eauto. i.
  specialize (PFtoRA.init_sim_conf L s). intro SIM.
  specialize (PFtoRA.init_wf_pf s). intro WF_PF.
  specialize (PFtoRA.init_wf_ra L s). intro WF_RA.
  ii. eapply PFtoRA.sim_conf_behavior; eauto.
Qed.
