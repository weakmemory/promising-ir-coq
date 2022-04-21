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

Set Implicit Arguments.


Variant sim_local (lc_src lc_tgt: Local.t): Prop :=
| sim_local_intro
    (TVIEW: TView.le (Local.tview lc_src) (Local.tview lc_tgt))
    (PROMISES: Local.promises lc_src = Local.promises lc_tgt)
    (RESERVES: Local.reserves lc_src = Local.reserves lc_tgt)
.
#[export] Hint Constructors sim_local: core.

Global Program Instance sim_local_PreOrder: PreOrder sim_local.
Next Obligation.
  ii. destruct x. econs; refl.
Qed.
Next Obligation.
  ii. destruct x, y, z. inv H. inv H0. ss. subst.
  econs; ss. etrans; eauto.
Qed.

Lemma sim_local_is_terminal
      lc_src lc_tgt
      (SIM: sim_local lc_src lc_tgt):
  Local.is_terminal lc_src <-> Local.is_terminal lc_tgt.
Proof.
  destruct lc_src, lc_tgt. inv SIM. ss.
  split; i; inv H; ss.
Qed.
