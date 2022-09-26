Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Event.

Require Import Time.
Require Import View.
Require Import BoolMap.
Require Import Promises.
Require Import Cell.
Require Import Memory.

Set Implicit Arguments.


Module Global.
  Structure t := mk {
    sc: TimeMap.t;
    promises: BoolMap.t;
    memory: Memory.t;
  }.

  Definition init := mk TimeMap.bot BoolMap.bot Memory.init.

  Variant wf (gl: t): Prop :=
  | wf_intro
      (SC_CLOSED: Memory.closed_timemap (sc gl) (memory gl))
      (MEM_CLOSED: Memory.closed (memory gl))
  .
  #[global] Hint Constructors wf: core.

  Lemma init_wf: wf init.
  Proof.
    econs; ss.
    - apply Memory.closed_timemap_bot.
      apply Memory.init_closed.
    - apply Memory.init_closed.
  Qed.

  Variant cap (gl gl_cap: t): Prop :=
    | cap_intro
        (SC: sc gl = sc gl_cap)
        (PROMISES: promises gl = promises gl_cap)
        (MEMORY: Memory.cap (memory gl) (memory gl_cap))
  .
  #[global] Hint Constructors cap: core.

  Lemma cap_exists
        gl
        (WF: wf gl):
    exists gl_cap, cap gl gl_cap.
  Proof.
    destruct gl.
    exploit Memory.cap_exists; try apply WF. s. i. des.
    eexists (mk _ _ _). econs; s; eauto.
  Qed.

  Variant future (gl1 gl2: t): Prop :=
  | future_intro
      (SC: TimeMap.le (sc gl1) (sc gl2))
      (MEMORY: Memory.future (memory gl1) (memory gl2))
  .
  #[global] Hint Constructors future: core.

  Global Program Instance future_PreOrder: PreOrder future.
  Next Obligation.
    ii. destruct x. econs; refl.
  Qed.
  Next Obligation.
    ii. destruct x, y, z. inv H. inv H0. ss.
    econs; etrans; eauto.
  Qed.

  Variant le (gl1 gl2: t): Prop :=
    | le_intro
        (SC: TimeMap.le (sc gl1) (sc gl2))
        (MEMORY: Memory.messages_le (memory gl1) (memory gl2))
  .
  #[global] Hint Constructors le: core.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. econs; refl.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; etrans; eauto.
  Qed.

  Lemma future_le
    gl1 gl2
    (FUTURE: future gl1 gl2):
    le gl1 gl2.
  Proof.
    inv FUTURE. econs; ss.
    eauto using Memory.future_messages_le.
  Qed.

  Lemma cap_le
    gl gl_cap
    (CAP: cap gl gl_cap):
    le gl gl_cap.
  Proof.
    destruct gl, gl_cap. inv CAP. ss. subst.
    econs; s; try refl.
    eauto using Memory.cap_messages_le.
  Qed.
End Global.
