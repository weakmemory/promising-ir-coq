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

Set Implicit Arguments.


Variant covered (loc:Loc.t) (ts:Time.t) (mem:Memory.t): Prop :=
| covered_intro
    from to msg
    (GET: Memory.get loc to mem = Some (from, msg))
    (ITV: Interval.mem (from, to) ts)
.

Lemma covered_disjoint
      mem1 mem2 loc from to
      (COVER: forall loc ts, covered loc ts mem1 -> covered loc ts mem2)
      (DISJOINT: forall to2 from2 msg2
                   (GET2: Memory.get loc to2 mem2 = Some (from2, msg2)),
          Interval.disjoint (from, to) (from2, to2)):
  forall to2 from2 msg2
    (GET2: Memory.get loc to2 mem1 = Some (from2, msg2)),
    Interval.disjoint (from, to) (from2, to2).
Proof.
  ii. exploit COVER; eauto.
  { econs; eauto. }
  intros x0. inv x0. eapply DISJOINT; eauto.
Qed.

Lemma get_disjoint_covered_disjoint
      mem loc from to:
  (forall t f m, Memory.get loc t mem = Some (f, m) -> Interval.disjoint (from, to) (f, t)) ->
  (forall ts, covered loc ts mem -> ~ Interval.mem (from, to) ts).
Proof.
  ii. inv H0. eapply H; eauto.
Qed.

Lemma covered_disjoint_get_disjoint
      mem loc from to:
  (forall ts, covered loc ts mem -> ~ Interval.mem (from, to) ts) ->
  (forall t f m, Memory.get loc t mem = Some (f, m) -> Interval.disjoint (from, to) (f, t)).
Proof.
  ii. eapply H; eauto. econs; eauto.
Qed.

Lemma add_covered
      mem2 mem1 loc from to msg
      l t
      (ADD: Memory.add mem1 loc from to msg mem2):
  covered l t mem2 <->
  covered l t mem1 \/ (l = loc /\ Interval.mem (from, to) t).
Proof.
  econs; i.
  - inv H. revert GET. erewrite Memory.add_o; eauto. condtac; ss.
    + des. subst. i. inv GET. auto.
    + left. econs; eauto.
  - des.
    + inv H. econs; eauto.
      erewrite Memory.add_o; eauto. condtac; ss; eauto.
      des. subst. exploit Memory.add_get0; eauto. i. des. congr.
    + subst. econs; eauto. erewrite Memory.add_o; eauto. condtac; ss.
      des; congr.
Qed.

Lemma cap_covered
      mem cap
      loc ts
      (CLOSED: Memory.closed mem)
      (CAP: Memory.cap mem cap)
      (ITV: Interval.mem (Time.bot, Time.incr (Memory.max_ts loc mem)) ts):
  covered loc ts cap.
Proof.
  specialize (Memory.max_exists (fun to => Time.le to ts) loc mem). i. des.
  { exfalso. eapply NONE; try apply CLOSED. apply Time.bot_spec. }
  inv SAT; cycle 1.
  { inv H. inv CAP. exploit SOUND; eauto. i.
    econs; eauto. econs; s; try refl.
    exploit Memory.get_ts; try exact GET. i. des; ss.
    subst. inv ITV. timetac.
  }
  specialize (Memory.min_exists (Time.le ts) loc mem). i. des.
  { exploit Memory.max_ts_spec; try apply CLOSED. i. des. clear MAX0.
    hexploit NONE; try exact GET0. i.
    inv CAP. exploit BACK; try exact GET0. i.
    econs; try exact x0.
    inv ITV. ss. econs; ss.
    destruct (TimeFacts.le_lt_dec ts (Memory.max_ts loc mem)); ss.
  }
  destruct (TimeFacts.le_lt_dec ts from_min); cycle 1.
  { inv CAP. exploit SOUND; try exact GET0. i.
    econs; try exact x0. econs; ss.
  }
  inv CAP. exploit MIDDLE.
  { econs; [exact GET|exact GET0|..].
    - eapply TimeFacts.lt_le_lt; try exact H. etrans; eauto.
      exploit Memory.get_ts; try exact GET0. i. des; timetac.
    - i. destruct (Memory.get loc ts0 mem) as [[]|] eqn:GET'; ss.
      destruct (TimeFacts.le_lt_dec ts0 ts).
      + exploit MAX; try exact GET'; ss. i. timetac.
      + exploit MIN; try exact GET'; timetac. i.
        rewrite TS2 in x0.
        exploit Memory.get_ts; try exact GET0. i. des; timetac.
        exploit TimeFacts.lt_le_lt; try exact TS1; try exact TS2. i. timetac.
  }
  { timetac. }
  i. econs; try exact x0. econs; ss.
Qed.
