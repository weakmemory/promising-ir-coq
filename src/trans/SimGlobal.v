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
Require Import Cell.
Require Import Memory.
Require Import Global.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import SimMemory.

Set Implicit Arguments.


Variant sim_global (gl_src gl_tgt: Global.t): Prop :=
| sim_global_intro
    (SC: TimeMap.le (Global.sc gl_src) (Global.sc gl_tgt))
    (PROMISES: Global.promises gl_src = Global.promises gl_tgt)
    (MEMORY: sim_memory (Global.memory gl_src) (Global.memory gl_tgt))
.
#[export] Hint Constructors sim_global: core.

Global Program Instance sim_global_PreOrder: PreOrder sim_global.
Next Obligation.
  ii. destruct x. econs; refl.
Qed.
Next Obligation.
  ii. destruct x, y, z. inv H. inv H0. ss. subst.
  econs; ss; etrans; eauto.
Qed.

Lemma init_sim_global: sim_global Global.init Global.init.
Proof. refl. Qed.

Lemma sim_global_cap gl_src gl_tgt
      (GL: sim_global gl_src gl_tgt)
      (GL_WF_SRC: Global.wf gl_src)
      (GL_WF_TGT: Global.wf gl_tgt)
  :
  sim_global (Global.cap_of gl_src) (Global.cap_of gl_tgt).
Proof.
  inv GL. econs; eauto. ss.
  eapply sim_memory_cap; eauto.
  { eapply Memory.cap_of_cap. }
  { eapply Memory.cap_of_cap. }
  { eapply GL_WF_SRC. }
  { eapply GL_WF_TGT. }
Qed.
