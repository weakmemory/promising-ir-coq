From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
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
Require Import TView.
Require Import Global.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import PFConfiguration.
Require Import Behavior.

Set Implicit Arguments.


Variant pf_race (c0: Configuration.t): Prop :=
| pf_race_intro
    e tid c1 c2
    (STEPS: PFConfiguration.all_step c0 c1)
    (STEP: PFConfiguration.estep e tid c1 c2)
    (RACE: ThreadEvent.is_race e)
.

Definition pf_racefree (c: Configuration.t): Prop :=
  ~ pf_race c.

Definition pf_racefree_syn (syn: Threads.syntax): Prop :=
  pf_racefree (Configuration.init syn).
