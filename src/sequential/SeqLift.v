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
Require Import Cell.
Require Import Memory.
(* Require Import MemoryFacts. *)
Require Import TView.
Require Import Local.
Require Import Promises.
Require Import BoolMap.
Require Import Global.
Require Import Thread.
Require Import Configuration.

Require Import Cover.
(* Require Import MemorySplit. *)
(* Require Import MemoryMerge. *)
(* Require Import FulfillStep. *)
Require Import MemoryProps.

Require Import LowerMemory.
(* Require Import JoinedView. *)

Require Import MaxView.
Require Export Owned.

Require Import Lia.

Set Implicit Arguments.

Definition version := Loc.t -> nat.
Definition version_le (v0 v1: version): Prop := forall loc, le (v0 loc) (v1 loc).

Definition opt_version_le (v0 v1: option version): Prop :=
  match v0, v1 with
  | None, _ => True
  | Some v0, Some v1 => version_le v0 v1
  | _, _ => False
  end.

Global Program Instance version_le_PreOrder: PreOrder version_le.
Next Obligation.
Proof.
  ii. refl.
Qed.
Next Obligation.
Proof.
  ii. etrans; eauto.
Qed.

Global Program Instance opt_version_le_PreOrder: PreOrder opt_version_le.
Next Obligation.
Proof.
  ii. destruct x; ss.
Qed.
Next Obligation.
Proof.
  ii. destruct x, y, z; ss. etrans; eauto.
Qed.

Definition version_join (v0 v1: version): version :=
  fun loc => Nat.max (v0 loc) (v1 loc).

Lemma version_join_l v0 v1
  :
    version_le v0 (version_join v0 v1).
Proof.
  ii. unfold version_join. lia.
Qed.

Lemma version_join_r v0 v1
  :
    version_le v1 (version_join v0 v1).
Proof.
  ii. unfold version_join. lia.
Qed.

Lemma version_join_spec v0 v1 v
      (LE0: version_le v0 v)
      (LE1: version_le v1 v)
  :
    version_le (version_join v0 v1) v.
Proof.
  ii. specialize (LE0 loc). specialize (LE1 loc).
  unfold version_join. lia.
Qed.

Definition opt_version_join (v0 v1: option version): option version :=
  match v0, v1 with
  | None, _ => v1
  | _, None => v0
  | Some v0, Some v1 => Some (version_join v0 v1)
  end.

Lemma opt_version_join_l v0 v1
  :
    opt_version_le v0 (opt_version_join v0 v1).
Proof.
  destruct v0, v1; ss. eapply version_join_l; eauto.
Qed.

Lemma opt_version_join_r v0 v1
  :
    opt_version_le v1 (opt_version_join v0 v1).
Proof.
  destruct v0, v1; ss. eapply version_join_r; eauto.
Qed.

Lemma opt_version_join_spec v0 v1 v
      (LE0: opt_version_le v0 v)
      (LE1: opt_version_le v1 v)
  :
    opt_version_le (opt_version_join v0 v1) v.
Proof.
  destruct v0, v1, v; ss. eapply version_join_spec; eauto.
Qed.

Definition versions := Loc.t -> Time.t -> option version.
Definition reserve_versions := Loc.t -> Time.t -> option nat.

Definition versions_le (vers0 vers1: versions): Prop :=
  forall loc ts v (VER: vers0 loc ts = Some v),
    vers1 loc ts = Some v.

Global Program Instance versions_le_PreOrder: PreOrder versions_le.
Next Obligation.
Proof.
  ii. auto.
Qed.
Next Obligation.
Proof.
  ii. eapply H0; eauto.
Qed.

Definition opt_time_lt (ts0 ts1: option Time.t): Prop :=
  match ts0, ts1 with
  | Some _, None => True
  | Some ts0, Some ts1 => Time.lt ts0 ts1
  | None, _ => False
  end.

Definition opt_time_le (ts0 ts1: option Time.t): Prop :=
  match ts0, ts1 with
  | _, None => True
  | Some ts0, Some ts1 => Time.le ts0 ts1
  | None, Some _ => False
  end.

Lemma opt_time_lt_some ts0 ts1
      (LT: opt_time_lt (Some ts0) (Some ts1))
  :
  Time.lt ts0 ts1.
Proof.
  auto.
Qed.

Lemma opt_time_le_some ts0 ts1
      (LT: opt_time_le (Some ts0) (Some ts1))
  :
  Time.le ts0 ts1.
Proof.
  auto.
Qed.

Global Program Instance opt_time_le_PreOrder: PreOrder opt_time_le.
Next Obligation.
Proof.
  ii. destruct x; ss. refl.
Qed.
Next Obligation.
Proof.
  ii. destruct x, y, z; ss. etrans; eauto.
Qed.

Global Program Instance opt_time_lt_StrOrder: StrictOrder opt_time_lt.
Next Obligation.
Proof.
  ii. destruct x; ss. eapply Time.lt_strorder; eauto.
Qed.
Next Obligation.
Proof.
  ii. destruct x, y, z; ss. etrans; eauto.
Qed.

Lemma opt_time_le_lt_dec ts0 ts1
  :
  {opt_time_le ts0 ts1} + {opt_time_lt ts1 ts0}.
Proof.
  destruct ts0, ts1; ss; auto. apply Time.le_lt_dec.
Defined.

Lemma opt_time_eq_dec (ts0 ts1: option Time.t)
  :
  {ts0 = ts1} + {ts0 <> ts1}.
Proof.
  destruct ts0, ts1; ss.
  { destruct (Time.eq_dec t t0); ss.
    { left. f_equal. auto. }
    { right. ii. clarify. }
  }
  { right. ii; clarify. }
  { right. ii; clarify. }
  { left. auto. }
Defined.

Lemma opt_time_lt_le ts0 ts1
      (LT: opt_time_lt ts0 ts1)
  :
  opt_time_le ts0 ts1.
Proof.
  destruct ts0, ts1; ss. left. auto.
Qed.

Lemma opt_time_le_inv ts0 ts1
      (LE: opt_time_le ts0 ts1)
  :
  opt_time_lt ts0 ts1 \/ ts0 = ts1.
Proof.
  destruct ts0, ts1; ss; auto. inv LE; auto. inv H. auto.
Qed.

Lemma opt_time_le_antisym ts0 ts1
      (LE0: opt_time_le ts0 ts1)
      (LE1: opt_time_le ts1 ts0)
  :
  ts0 = ts1.
Proof.
  destruct ts0, ts1; ss. f_equal. eapply TimeFacts.antisym; eauto.
Qed.

Lemma opt_time_le_lt_lt ts0 ts1 ts2
      (LE: opt_time_le ts0 ts1)
      (LT: opt_time_lt ts1 ts2)
  :
  opt_time_lt ts0 ts2.
Proof.
  destruct ts0, ts1, ts2; ss. eapply TimeFacts.le_lt_lt; eauto.
Qed.

Lemma opt_time_lt_le_lt ts0 ts1 ts2
      (LT: opt_time_lt ts0 ts1)
      (LE: opt_time_le ts1 ts2)
  :
  opt_time_lt ts0 ts2.
Proof.
  destruct ts0, ts1, ts2; ss. eapply TimeFacts.lt_le_lt; eauto.
Qed.

Lemma opt_time_le_lt_bot ts0 ts1
      (LE: opt_time_le ts0 ts1)
      (LT: opt_time_lt ts1 ts0)
  :
  False.
Proof.
  eapply opt_time_lt_StrOrder. eapply opt_time_le_lt_lt; eauto.
Qed.

Lemma opt_time_bot_spec ts
  :
  opt_time_le (Some Time.bot) ts.
Proof.
  destruct ts; ss. eapply Time.bot_spec.
Qed.

Definition opt_time_join (ts0 ts1: option Time.t): option Time.t :=
  match ts0, ts1 with
  | Some ts0, Some ts1 => Some (Time.join ts0 ts1)
  | _, _ => None
  end.

Lemma opt_time_join_l ts0 ts1
  :
  opt_time_le ts0 (opt_time_join ts0 ts1).
Proof.
  destruct ts0, ts1; ss. eapply Time.join_l.
Qed.

Lemma opt_time_join_r ts0 ts1
  :
  opt_time_le ts1 (opt_time_join ts0 ts1).
Proof.
  destruct ts0, ts1; ss. eapply Time.join_r.
Qed.

Lemma opt_time_join_spec ts0 ts1 ts
      (LE0: opt_time_le ts0 ts)
      (LE1: opt_time_le ts1 ts)
  :
  opt_time_le (opt_time_join ts0 ts1) ts.
Proof.
  destruct ts0, ts1, ts; ss. eapply Time.join_spec; auto.
Qed.

Lemma opt_time_join_unfold ts0 ts1
  :
  opt_time_join ts0 ts1 = if opt_time_le_lt_dec ts0 ts1 then ts1 else ts0.
Proof.
  eapply opt_time_le_antisym.
  { des_ifs.
    { eapply opt_time_join_spec; auto. refl. }
    { eapply opt_time_join_spec; auto.
      { refl. }
      { apply opt_time_lt_le. auto. }
    }
  }
  { des_ifs.
    { apply opt_time_join_r. }
    { apply opt_time_join_l. }
  }
Qed.

Lemma opt_time_join_some ts0 ts1
  :
  Some (Time.join ts0 ts1) = opt_time_join (Some ts0) (Some ts1).
Proof.
  auto.
Qed.

Definition opt_time_meet (ts0 ts1: option Time.t): option Time.t :=
  match ts0, ts1 with
  | Some ts0, Some ts1 => Some (Time.meet ts0 ts1)
  | None, ts1 => ts1
  | ts0, None => ts0
  end.

Lemma opt_time_meet_l ts0 ts1
  :
  opt_time_le (opt_time_meet ts0 ts1) ts0.
Proof.
  destruct ts0, ts1; ss.
  { eapply Time.meet_l. }
  { refl. }
Qed.

Lemma opt_time_meet_r ts0 ts1
  :
  opt_time_le (opt_time_meet ts0 ts1) ts1.
Proof.
  destruct ts0, ts1; ss.
  { eapply Time.meet_r. }
  { refl. }
Qed.

Lemma opt_time_meet_spec ts0 ts1 ts
      (LE0: opt_time_le ts ts0)
      (LE1: opt_time_le ts ts1)
  :
  opt_time_le ts (opt_time_meet ts0 ts1).
Proof.
  destruct ts0, ts1, ts; ss. eapply Time.meet_spec; auto.
Qed.

Lemma opt_time_meet_unfold ts0 ts1
  :
  opt_time_meet ts0 ts1 = if opt_time_le_lt_dec ts0 ts1 then ts0 else ts1.
Proof.
  eapply opt_time_le_antisym.
  { des_ifs.
    { apply opt_time_meet_l. }
    { apply opt_time_meet_r. }
  }
  { des_ifs.
    { eapply opt_time_meet_spec; auto. refl. }
    { eapply opt_time_meet_spec; auto.
      { apply opt_time_lt_le. auto. }
      { refl. }
    }
  }
Qed.

Lemma opt_time_meet_some ts0 ts1
  :
  Some (Time.meet ts0 ts1) = opt_time_meet (Some ts0) (Some ts1).
Proof.
  auto.
Qed.

Lemma finite_greatest_opt P (l: list (option Time.t))
  :
  (exists to,
      (<<SAT: P to>>) /\
        (<<IN: List.In to l>>) /\
        (<<GREATEST: forall to'
                            (IN: List.In to' l)
                            (SAT: P to'),
            opt_time_le to' to>>)) \/
    (<<EMPTY: forall to (IN: List.In to l), ~ P to>>).
Proof.
  induction l.
  - right. ii. inv IN.
  - destruct (classic (P a)).
    + des.
      * destruct (opt_time_le_lt_dec to a).
        { left. exists a. esplits; ss; eauto.
          i. des; clarify; eauto; try refl. etrans; eauto.
        }
        { left. exists to. esplits; ss; eauto.
          i. des; clarify; eauto. eapply opt_time_lt_le. eauto. }
      * left. exists a. esplits; ss; eauto.
        i. des; clarify.
        { refl. }
        { exfalso. eapply EMPTY; eauto. }
    + des.
      * left. esplits; ss; eauto.
        i. des; clarify. eapply GREATEST; eauto.
      * right. ii. ss. des; clarify.
        eapply EMPTY; eauto.
Qed.

Lemma finite_least_opt P (l: list (option Time.t))
  :
  (exists to,
      (<<SAT: P to>>) /\
        (<<IN: List.In to l>>) /\
        (<<LEAST: forall to'
                         (IN: List.In to' l)
                         (SAT: P to'),
            opt_time_le to to'>>)) \/
    (<<EMPTY: forall to (IN: List.In to l), ~ P to>>).
Proof.
  induction l.
  - right. ii. inv IN.
  - destruct (classic (P a)).
    + des.
      * destruct (opt_time_le_lt_dec a to).
        { left. exists a. esplits; ss; eauto.
          i. des; clarify; eauto; try refl. etrans; eauto. }
        { left. exists to. esplits; ss; eauto.
          i. des; clarify; eauto. eapply opt_time_lt_le. eauto. }
      * left. exists a. esplits; ss; eauto.
        i. des; clarify.
        { refl. }
        { exfalso. eapply EMPTY; eauto. }
    + des.
      * left. esplits; ss; eauto.
        i. des; clarify. eapply LEAST; eauto.
      * right. ii. ss. des; clarify.
        eapply EMPTY; eauto.
Qed.

Inductive times_sorted_opt: list (option Time.t) -> Prop :=
| times_sorted_opt_nil
  :
  times_sorted_opt []
| times_sorted_opt_cons
    hd tl
    (HD: List.Forall (opt_time_lt hd) tl)
    (TL: times_sorted_opt tl)
  :
  times_sorted_opt (hd :: tl)
.

Fixpoint insert_opt (to: option Time.t) (l: list (option Time.t)): list (option Time.t) :=
  match l with
  | [] => [to]
  | hd :: tl =>
      match (opt_time_le_lt_dec to hd) with
      | left LE => match (opt_time_eq_dec to hd) with
                   | left EQ => hd :: tl
                   | right LT => to :: hd :: tl
                   end
      | right LT => hd :: (insert_opt to tl)
      end
  end.

Fixpoint sorting_opt (l: list (option Time.t)): list (option Time.t) :=
  match l with
  | [] => []
  | hd :: tl => insert_opt hd (sorting_opt tl)
  end.

Lemma insert_opt_complete a l
  :
  forall b, List.In b (insert_opt a l) <-> (a = b \/ List.In b l).
Proof.
  ginduction l; ss. i. des_ifs; ss.
  - split; i; des; eauto.
  - split; i; des; eauto.
    + eapply IHl in H. des; eauto.
    + clarify. right. eapply IHl; eauto.
    + right. eapply IHl; eauto.
Qed.

Lemma insert_opt_sorted a l
      (SORTED: times_sorted_opt l)
  :
  times_sorted_opt (insert_opt a l).
Proof.
  ginduction l; ss.
  - i. econs; ss.
  - i. des_ifs.
    + econs; eauto. inv SORTED. econs.
      * apply opt_time_le_inv in o. des; ss.
      * eapply List.Forall_impl; cycle 1; eauto.
        i. eapply opt_time_le_lt_lt; eauto.
    + econs.
      * inv SORTED.
        eapply List.Forall_forall. i.
        eapply insert_opt_complete in H. des; clarify.
        eapply List.Forall_forall in HD; eauto.
      * inv SORTED. eapply IHl; eauto.
Qed.

Lemma sorting_opt_sorted l
  :
  (<<COMPLETE: forall a, List.In a l <-> List.In a (sorting_opt l)>>) /\
    (<<SORTED: times_sorted_opt (sorting_opt l)>>).
Proof.
  induction l; ss.
  - split; i; ss. econs.
  - i. des. splits.
    + i. erewrite insert_opt_complete.
      split; i; des; eauto.
      * right. eapply COMPLETE; eauto.
      * right. eapply COMPLETE; eauto.
    + eapply insert_opt_sorted; eauto.
Qed.


Module Mapping.
  Record t: Type :=
    mk
      { map:> nat -> option Time.t -> option Time.t;
        ver: nat;
      }.

  Record wf (f: t): Prop :=
    { map_finite: forall v, exists l, forall ts fts (MAP: f v ts = Some fts),
            List.In (ts, fts) l;
      mapping_map_lt_iff: forall v ts0 ts1 fts0 fts1
                             (MAP0: f.(map) v ts0 = Some fts0) (MAP0: f.(map) v ts1 = Some fts1),
          opt_time_lt ts0 ts1 <-> Time.lt fts0 fts1;
      mapping_incr: forall v0 v1 ts fts0
                           (VER0: v0 <= v1)
                           (VER1: v1 <= f.(ver))
                           (MAP0: f.(map) v0 ts = Some fts0),
          exists fts1,
            (<<MAP: f.(map) v1 ts = Some fts1>>) /\
            (<<TS: Time.le fts0 fts1>>);
      mapping_empty: forall v (VER: f.(ver) < v) ts, f v ts = None;
      mapping_bot: f.(map) 0 (Some Time.bot) = Some Time.bot;
      mapping_max: f.(map) 0 None <> None;
    }.

  Definition le (f0 f1: t): Prop :=
    (<<VER: f0.(ver) <= f1.(ver)>>) /\
    (<<MAP: forall v (VER: v <= f0.(ver)),
        f1.(map) v = f0.(map) v>>)
  .

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. unfold le. splits; i; refl.
  Qed.
  Next Obligation.
  Proof.
    ii. unfold le in *. des. splits; i.
    { etrans; eauto. }
    { transitivity (y.(map) v); eauto. eapply MAP; eauto. lia. }
  Qed.

  Definition le_strong (f0 f1: t): Prop :=
    (<<VER: f0.(ver) <= f1.(ver)>>) /\
    (<<MAP: forall v (VER: v <= f0.(ver)),
        f1.(map) v = f0.(map) v>>) /\
    (<<PRESERVE: forall v ts fts
                        (VER0: f0.(ver) < v) (VER1: v <= f1.(ver))
                        (MAP: f0.(map) f0.(ver) ts = Some fts),
        f1.(map) v ts = Some fts>>)
  .

  Global Program Instance le_strong_PreOrder: PreOrder le_strong.
  Next Obligation.
  Proof.
    ii. unfold le_strong. splits; i; auto. exfalso. lia.
  Qed.
  Next Obligation.
  Proof.
    ii. unfold le_strong in *. des. splits; i.
    { etrans; eauto. }
    { transitivity (y.(map) v); eauto. eapply MAP; eauto. lia. }
    { assert (v <= y.(ver) \/ y.(ver) < v) by lia. des.
      { rewrite MAP; eauto. }
      { eapply PRESERVE; eauto.
        assert (x.(ver) < y.(ver) \/ x.(ver) = y.(ver)) by lia. des.
        { eapply PRESERVE0; eauto. }
        { rewrite H0 in *. rewrite MAP0; eauto. }
      }
    }
  Qed.

  Lemma le_strong_le f0 f1
        (LE: le_strong f0 f1)
    :
      le f0 f1.
  Proof.
    unfold le_strong, le in*. des. splits; auto.
  Qed.

  Definition le_update (f0 f1: t): Prop :=
    (<<LE: le f0 f1>>) /\
    (<<WF: wf f0 -> wf f1>>) /\
    (<<UPDATE: forall (WF0: wf f0)
                      ts0 ts1 fts0 fts1 fts2
                      (MAP0: f0.(map) f0.(ver) ts0 = Some fts0)
                      (MAP2: f0.(map) f0.(ver) ts1 = Some fts1)
                      (MAP1: f1.(map) f1.(ver) ts0 = Some fts2),
        (<<EQ: fts0 = fts2>>) \/ (<<LT: Time.lt fts1 fts2>>)>>)
  .

  Global Program Instance le_update_PreOrder: PreOrder le_update.
  Next Obligation.
  Proof.
    ii. unfold le_update. splits.
    { refl. }
    { auto. }
    { i. clarify. left. auto. }
  Qed.
  Next Obligation.
  Proof.
    ii. unfold le_update in *. des. splits.
    { etrans; eauto. }
    { auto. }
    i. hexploit WF0; eauto. i.
    hexploit WF; eauto. i.
    hexploit mapping_incr.
    { eapply H. }
    { eapply LE0. }
    { refl. }
    { red in LE0. des. rewrite MAP; [|refl]. eapply MAP0. }
    i. des.
    hexploit mapping_incr.
    { eapply H. }
    { eapply LE0. }
    { refl. }
    { red in LE0. des. rewrite MAP3; [|refl]. eapply MAP2. }
    i. des. hexploit UPDATE.
    { eauto. }
    { eapply MAP. }
    { eapply MAP3. }
    { eauto. }
    hexploit UPDATE0.
    { eauto. }
    { eapply MAP0. }
    { eapply MAP2. }
    { eauto. }
    i. des; clarify; auto.
    { right. eapply TimeFacts.le_lt_lt; eauto. }
    { right. eapply TimeFacts.le_lt_lt; eauto. }
  Qed.

  Lemma le_strong_le_update f0 f1
        (LE: le_strong f0 f1)
        (WF: wf f1)
    :
      le_update f0 f1.
  Proof.
    unfold le_update. splits.
    { eapply le_strong_le; eauto. }
    { auto. }
    { i. left. red in LE. des.
      assert (ver f0 < ver f1 \/ ver f0 = ver f1) by lia. des.
      { erewrite PRESERVE in MAP1; eauto. clarify. }
      { rewrite <- H in MAP1. erewrite MAP in MAP1; [|refl]. clarify. }
    }
  Qed.

  Lemma mapping_map_le (f: t) (WF: wf f):
    forall v ts0 ts1 fts0 fts1
           (MAP0: f.(map) v ts0 = Some fts0) (MAP0: f.(map) v ts1 = Some fts1),
      opt_time_le ts0 ts1 <-> Time.le fts0 fts1.
  Proof.
    i. split.
    { i. destruct (Time.le_lt_dec fts0 fts1); auto.
      erewrite <- mapping_map_lt_iff in l; eauto. exfalso. eapply opt_time_le_lt_bot; eauto. }
    { i. destruct (opt_time_le_lt_dec ts0 ts1); auto.
      erewrite mapping_map_lt_iff in o; eauto. timetac. }
  Qed.

  Lemma mapping_map_eq (f: t) (WF: wf f):
    forall v ts0 ts1 fts0 fts1
           (MAP0: f.(map) v ts0 = Some fts0) (MAP0: f.(map) v ts1 = Some fts1),
      ts0 = ts1 <-> fts0 = fts1.
  Proof.
    i. split.
    { i. subst. apply TimeFacts.antisym.
      { erewrite <- mapping_map_le; eauto. refl. }
      { erewrite <- mapping_map_le; eauto. refl. }
    }
    { i. subst. apply opt_time_le_antisym.
      { erewrite mapping_map_le; eauto. refl. }
      { erewrite mapping_map_le; eauto. refl. }
    }
  Qed.

  Definition ts := Loc.t -> Mapping.t.

  Definition vers (f: ts): version :=
    fun loc => (f loc).(ver).

  Definition wfs (f: ts): Prop := forall loc, wf (f loc).

  Definition les (f0 f1: ts): Prop :=
    forall loc, le (f0 loc) (f1 loc).

  Global Program Instance les_PreOrder: PreOrder les.
  Next Obligation.
  Proof.
    ii. refl.
  Qed.
  Next Obligation.
  Proof.
    ii. etrans; eauto.
  Qed.

  Definition les_strong (f0 f1: ts): Prop :=
    forall loc, le_strong (f0 loc) (f1 loc).

  Global Program Instance les_strong_PreOrder: PreOrder les_strong.
  Next Obligation.
  Proof.
    ii. refl.
  Qed.
  Next Obligation.
  Proof.
    ii. etrans; eauto.
  Qed.

  Lemma les_strong_les f0 f1
        (LE: les_strong f0 f1)
    :
      les f0 f1.
  Proof.
    ii. eapply le_strong_le; eauto.
  Qed.

  Definition les_update (f0 f1: ts): Prop :=
    forall loc, le_update (f0 loc) (f1 loc).

  Global Program Instance les_update_PreOrder: PreOrder les_update.
  Next Obligation.
  Proof.
    ii. refl.
  Qed.
  Next Obligation.
  Proof.
    ii. etrans; eauto.
  Qed.

  Lemma les_strong_les_update f0 f1
        (LE: les_strong f0 f1)
        (WF: wfs f1)
    :
      les_update f0 f1.
  Proof.
    ii. eapply le_strong_le_update; eauto.
  Qed.
End Mapping.


Definition reserve_versions_wf (f: Mapping.ts) (rvers: reserve_versions): Prop :=
  forall loc to ver (VER: rvers loc to = Some ver),
    le ver (Mapping.vers f loc).

Definition loc_version_wf (f: Mapping.t) (v: nat): Prop :=
  le v f.(Mapping.ver).

Definition version_wf (f: Mapping.ts) (v: version): Prop :=
  forall loc, loc_version_wf (f loc) (v loc).

Definition opt_version_wf (f: Mapping.ts) (v: option version): Prop :=
  match v with
  | Some v => version_wf f v
  | None => True
  end.

Definition versions_wf (f: Mapping.ts) (vers: versions): Prop :=
  forall loc to, opt_version_wf f (vers loc to).

Lemma version_le_version_wf f v
  :
    version_le v (Mapping.vers f) <-> version_wf f v.
Proof.
  split.
  { ii. eapply H. }
  { ii. eapply H. }
Qed.

Definition versions_messages_le (vers0 vers1: versions): Prop :=
  forall loc ts v
         (VER: vers0 loc ts = Some v),
    vers1 loc ts = Some v.

Global Program Instance versions_messages_le_PreOrder: PreOrder versions_messages_le.

Lemma mapping_latest_wf_loc f
  :
    loc_version_wf f (Mapping.ver f).
Proof.
  ii. red. refl.
Qed.

Lemma mapping_latest_wf f
  :
    version_wf f (Mapping.vers f).
Proof.
  ii. red. refl.
Qed.

Definition sim_timestamp_exact (f: Mapping.t) (v: nat) (ts_src: Time.t) (ts_tgt: option Time.t) :=
  f.(Mapping.map) v ts_tgt = Some ts_src.

Lemma mapping_map_finite_exact (f: Mapping.t) (WF: Mapping.wf f) v:
  exists l, forall ts fts,
      sim_timestamp_exact f v fts ts <-> List.In (ts, fts) l.
Proof.
  hexploit Mapping.map_finite; eauto. i. des.
  hexploit (@list_filter_exists _ (fun '(ts, fts) => f.(Mapping.map) v ts = Some fts) l).
  i. des. exists l'. i. split; i.
  { eapply COMPLETE. splits; eauto. }
  { eapply COMPLETE in H0. des; auto. }
Qed.

Fixpoint list_map_filter A B (f: A -> option B) (l: list A): list B :=
  match l with
  | [] => []
  | a::tl => match f a with
             | Some a => a::(list_map_filter f tl)
             | None => list_map_filter f tl
             end
  end.

Lemma list_map_filter_in_iff A B (f: A -> option B) l b
  :
  List.In b (list_map_filter f l) <-> exists a, f a = Some b /\ List.In a l.
Proof.
  revert b. induction l.
  { i. split; ss; i. des; ss. }
  { i. split; ss; i.
    { des_ifs.
      { ss. des; clarify.
        { esplits; eauto. }
        { eapply IHl in H; eauto. des. esplits ; eauto. }
      }
      { eapply IHl in H. des. esplits; eauto. }
    }
    { des_ifs.
      { hexploit H; eauto. i. des; clarify; ss; auto.
        right. eapply IHl. eauto.
      }
      { des; clarify.
        eapply IHl. esplits; eauto.
      }
    }
  }
Qed.

Lemma mapping_map_finite_exact_some (f: Mapping.t) (WF: Mapping.wf f) v:
  exists l, forall ts fts,
      sim_timestamp_exact f v fts (Some ts) <-> List.In (ts, fts) l.
Proof.
  hexploit mapping_map_finite_exact; eauto. i. des.
  exists (list_map_filter (fun '(ts, fts) =>
                             match ts with
                             | Some ts => Some (ts, fts)
                             | None => None
                             end) l).
  i. erewrite list_map_filter_in_iff. split; i; des.
  { eexists (Some _, _). splits; eauto. eapply H; eauto. }
  { des_ifs. eapply H; eauto. }
Qed.

Lemma sim_timestamp_exact_inject f v ts_src0 ts_src1 ts_tgt
      (SIM0: sim_timestamp_exact f v ts_src0 ts_tgt)
      (SIM1: sim_timestamp_exact f v ts_src1 ts_tgt)
  :
    ts_src0 = ts_src1.
Proof.
  unfold sim_timestamp_exact in *. clarify.
Qed.

Lemma sim_timestamp_exact_mon_ver f v0 v1 ts_src0 ts_tgt
      (SIM: sim_timestamp_exact f v0 ts_src0 ts_tgt)
      (VER: v0 <= v1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v1)
  :
    exists ts_src1, (<<TS: Time.le ts_src0 ts_src1>>) /\ (<<SIM: sim_timestamp_exact f v1 ts_src1 ts_tgt>>).
Proof.
  unfold sim_timestamp_exact in *.
  eapply Mapping.mapping_incr in SIM; eauto. des. esplits; eauto.
Qed.

Lemma sim_timestamp_exact_mon_mapping f0 f1 v ts_src ts_tgt
      (WF: Mapping.wf f0)
      (VERWF: loc_version_wf f0 v)
      (MAP: Mapping.le f0 f1)
  :
    sim_timestamp_exact f0 v ts_src ts_tgt <-> sim_timestamp_exact f1 v ts_src ts_tgt.
Proof.
  unfold sim_timestamp_exact, Mapping.le in *. des.
  rewrite MAP0; eauto.
Qed.

Lemma sim_timestamp_exact_mon_strong f0 f1 ts_src ts_tgt
      (WF: Mapping.wf f0)
      (MAP: Mapping.le_strong f0 f1)
      (SIM: sim_timestamp_exact f0 f0.(Mapping.ver) ts_src ts_tgt)
  :
    sim_timestamp_exact f1 f1.(Mapping.ver) ts_src ts_tgt.
Proof.
  unfold sim_timestamp_exact, Mapping.le_strong in *. des.
  assert (f0.(Mapping.ver) < f1.(Mapping.ver) \/ f0.(Mapping.ver) = f1.(Mapping.ver)) by lia.
  des.
  { eapply PRESERVE; eauto. }
  { rewrite H in *. rewrite MAP; eauto. }
Qed.


Definition sim_timestamp (f: Mapping.t) (v: nat) (ts_src: Time.t) (ts_tgt: option Time.t) :=
  exists ts_src' ts_tgt',
    (<<TSSRC: Time.le ts_src ts_src'>>) /\
    (<<TSTGT: opt_time_le ts_tgt' ts_tgt>>) /\
    (<<SIM: sim_timestamp_exact f v ts_src' ts_tgt'>>)
.

Lemma sim_timestamp_exact_sim f v ts_src ts_tgt
      (EXACT: sim_timestamp_exact f v ts_src ts_tgt)
  :
    sim_timestamp f v ts_src ts_tgt.
Proof.
  exists ts_src, ts_tgt. splits; auto; try refl.
Qed.

Lemma sim_timestamp_exact_sim_latest f v ts_src ts_tgt
      (EXACT: sim_timestamp_exact f v ts_src ts_tgt)
      (WF: Mapping.wf f)
  :
    sim_timestamp f f.(Mapping.ver) ts_src ts_tgt.
Proof.
  hexploit sim_timestamp_exact_mon_ver.
  { eauto. }
  { instantiate (1:=f.(Mapping.ver)).
    apply Compare_dec.not_gt. ii.
    eapply Mapping.mapping_empty in H; auto.
    rewrite EXACT in H. ss.
  }
  { auto. }
  { apply mapping_latest_wf_loc. }
  i. des. rr. esplits; [..|eauto]; auto. refl.
Qed.

Lemma sim_timestamp_mon_tgt f v ts_src ts_tgt0 ts_tgt1
      (SIM: sim_timestamp f v ts_src ts_tgt0)
      (TS: opt_time_le ts_tgt0 ts_tgt1)
  :
    sim_timestamp f v ts_src ts_tgt1.
Proof.
  unfold sim_timestamp in *. des.
  esplits; [..|eauto]; auto. etrans; eauto.
Qed.

Lemma sim_timestamp_mon_src f v ts_src0 ts_src1 ts_tgt
      (SIM: sim_timestamp f v ts_src1 ts_tgt)
      (TS: Time.le ts_src0 ts_src1)
  :
    sim_timestamp f v ts_src0 ts_tgt.
Proof.
  unfold sim_timestamp in *. des.
  esplits; [..|eauto]; auto. etrans; eauto.
Qed.

Lemma sim_timestamp_mon_ver f v0 v1 ts_src ts_tgt
      (SIM: sim_timestamp f v0 ts_src ts_tgt)
      (VER: v0 <= v1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v1)
  :
    sim_timestamp f v1 ts_src ts_tgt.
Proof.
  unfold sim_timestamp in *. des.
  eapply sim_timestamp_exact_mon_ver in SIM; eauto. des.
  esplits; [..|eauto]; eauto.
Qed.

Lemma sim_timestamp_mon_mapping f0 f1 v ts_src ts_tgt
      (WF: Mapping.wf f0)
      (VERWF: loc_version_wf f0 v)
      (MAP: Mapping.le f0 f1)
  :
    sim_timestamp f0 v ts_src ts_tgt <-> sim_timestamp f1 v ts_src ts_tgt.
Proof.
  unfold sim_timestamp in *. split.
  { i. des. esplits; eauto.
    { erewrite <- sim_timestamp_exact_mon_mapping; eauto. }
  }
  { i. des. esplits; eauto.
    { erewrite sim_timestamp_exact_mon_mapping; eauto. }
  }
Qed.

Lemma sim_timestamp_mon_mapping_latest f0 f1 ts_src ts_tgt
      (SIM: sim_timestamp f0 f0.(Mapping.ver) ts_src ts_tgt)
      (WF0: Mapping.wf f0)
      (WF1: Mapping.wf f1)
      (MAP: Mapping.le f0 f1)
  :
  sim_timestamp f1 f1.(Mapping.ver) ts_src ts_tgt.
Proof.
  erewrite sim_timestamp_mon_mapping in SIM; eauto.
  2:{ eapply mapping_latest_wf_loc. }
  eapply sim_timestamp_mon_ver; eauto.
  { eapply MAP. }
  { eapply mapping_latest_wf_loc. }
Qed.

Lemma sim_timestamp_bot f v ts
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    sim_timestamp f v Time.bot ts.
Proof.
  hexploit Mapping.mapping_bot; eauto. i.
  eapply Mapping.mapping_incr with (v1:=v) in H; eauto.
  { des. exists fts1, (Some Time.bot). esplits; ss; eauto.
    { eapply opt_time_bot_spec. }
  }
  { eapply le_0_n. }
Qed.

Lemma sim_timestamp_bot_latest f ts
      (WF: Mapping.wf f)
  :
    sim_timestamp f f.(Mapping.ver) Time.bot ts.
Proof.
  eapply sim_timestamp_bot; auto. apply mapping_latest_wf_loc.
Qed.

Lemma sim_timestamp_exact_le f v
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp_exact f v ts_src0 ts_tgt0)
      (SIM1: sim_timestamp_exact f v ts_src1 ts_tgt1)
      (TS: opt_time_le ts_tgt0 ts_tgt1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    Time.le ts_src0 ts_src1.
Proof.
  unfold sim_timestamp_exact in *.
  erewrite <- Mapping.mapping_map_le; cycle 1; eauto.
Qed.

Lemma sim_timestamp_exact_lt f v
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp_exact f v ts_src0 ts_tgt0)
      (SIM1: sim_timestamp_exact f v ts_src1 ts_tgt1)
      (TS: opt_time_lt ts_tgt0 ts_tgt1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    Time.lt ts_src0 ts_src1.
Proof.
  unfold sim_timestamp in *. des.
  erewrite <- Mapping.mapping_map_lt_iff; cycle 1; eauto.
Qed.

Lemma sim_timestamp_le f v
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp f v ts_src0 ts_tgt0)
      (SIM1: sim_timestamp_exact f v ts_src1 ts_tgt1)
      (TS: opt_time_le ts_tgt0 ts_tgt1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    Time.le ts_src0 ts_src1.
Proof.
  unfold sim_timestamp in *. des.
  transitivity ts_src'; eauto.
  erewrite <- Mapping.mapping_map_le; cycle 1; eauto. etrans; eauto.
Qed.

Lemma sim_timestamp_lt f v
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp f v ts_src0 ts_tgt0)
      (SIM1: sim_timestamp_exact f v ts_src1 ts_tgt1)
      (TS: opt_time_lt ts_tgt0 ts_tgt1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    Time.lt ts_src0 ts_src1.
Proof.
  unfold sim_timestamp in *. des.
  eapply TimeFacts.le_lt_lt; eauto.
  erewrite <- Mapping.mapping_map_lt_iff; cycle 1; eauto.
  eapply opt_time_le_lt_lt; eauto.
Qed.

Lemma sim_timestamp_exact_join f v
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp_exact f v ts_src0 ts_tgt0)
      (SIM1: sim_timestamp_exact f v ts_src1 ts_tgt1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    sim_timestamp_exact f v (Time.join ts_src0 ts_src1) (opt_time_join ts_tgt0 ts_tgt1).
Proof.
  rewrite opt_time_join_unfold in *. unfold Time.join. des_ifs.
  { erewrite <- Mapping.mapping_map_le in l; eauto. exfalso. eapply opt_time_le_lt_bot; eauto. }
  { erewrite Mapping.mapping_map_le in o; eauto. timetac. }
Qed.

Lemma sim_timestamp_join f v
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp f v ts_src0 ts_tgt0)
      (SIM1: sim_timestamp f v ts_src1 ts_tgt1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    sim_timestamp f v (Time.join ts_src0 ts_src1) (opt_time_join ts_tgt0 ts_tgt1).
Proof.
  unfold sim_timestamp in *. des.
  exists (Time.join ts_src'0 ts_src'), (opt_time_join ts_tgt'0 ts_tgt'). splits.
  { eapply time_join_mon; eauto. }
  { eapply opt_time_join_spec.
    { etrans; [|eapply opt_time_join_l]. auto. }
    { etrans; [|eapply opt_time_join_r]. auto. }
  }
  { eapply sim_timestamp_exact_join; eauto. }
Qed.

Lemma sim_timestamp_join_latest f
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp f f.(Mapping.ver) ts_src0 ts_tgt0)
      (SIM1: sim_timestamp f f.(Mapping.ver) ts_src1 ts_tgt1)
      (WF: Mapping.wf f)
  :
    sim_timestamp f f.(Mapping.ver) (Time.join ts_src0 ts_src1) (opt_time_join ts_tgt0 ts_tgt1).
Proof.
  eapply sim_timestamp_join; eauto. eapply mapping_latest_wf_loc.
Qed.

Lemma sim_timestamp_exact_meet f v
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp_exact f v ts_src0 ts_tgt0)
      (SIM1: sim_timestamp_exact f v ts_src1 ts_tgt1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    sim_timestamp_exact f v (Time.meet ts_src0 ts_src1) (opt_time_meet ts_tgt0 ts_tgt1).
Proof.
  rewrite opt_time_meet_unfold in *. unfold Time.meet in *. des_ifs.
  { erewrite <- Mapping.mapping_map_le in l; eauto. exfalso. eapply opt_time_le_lt_bot; eauto. }
  { erewrite Mapping.mapping_map_le in o; eauto. timetac. }
Qed.

Lemma sim_timestamp_exact_le_if f v
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp_exact f v ts_src0 ts_tgt0)
      (SIM1: sim_timestamp_exact f v ts_src1 ts_tgt1)
      (TS: Time.le ts_src0 ts_src1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    opt_time_le ts_tgt0 ts_tgt1.
Proof.
  unfold sim_timestamp_exact in *.
  erewrite Mapping.mapping_map_le; eauto.
Qed.

Lemma sim_timestamp_exact_lt_if f v
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp_exact f v ts_src0 ts_tgt0)
      (SIM1: sim_timestamp_exact f v ts_src1 ts_tgt1)
      (TS: Time.lt ts_src0 ts_src1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    opt_time_lt ts_tgt0 ts_tgt1.
Proof.
  unfold sim_timestamp_exact in *.
  erewrite Mapping.mapping_map_lt_iff; eauto.
Qed.

Lemma sim_timestamp_exact_unique f v ts_src ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp_exact f v ts_src ts_tgt0)
      (SIM1: sim_timestamp_exact f v ts_src ts_tgt1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    ts_tgt0 = ts_tgt1.
Proof.
  eapply opt_time_le_antisym.
  { eapply sim_timestamp_exact_le_if; eauto. refl. }
  { eapply sim_timestamp_exact_le_if; eauto. refl. }
Qed.


Lemma sim_disjoint f v
      from_tgt0 from_src0 to_tgt0 to_src0
      from_tgt1 from_src1 to_tgt1 to_src1
      (WF: Mapping.wf f)
      (VER: loc_version_wf f v)
      (FROM0: sim_timestamp_exact f v from_src0 (Some from_tgt0))
      (TO0: sim_timestamp_exact f v to_src0 (Some to_tgt0))
      (FROM1: sim_timestamp_exact f v from_src1 (Some from_tgt1))
      (TO1: sim_timestamp_exact f v to_src1 (Some to_tgt1))
      (DISJOINT: Interval.disjoint (from_tgt0, to_tgt0) (from_tgt1, to_tgt1))
  :
    Interval.disjoint (from_src0, to_src0) (from_src1, to_src1).
Proof.
  apply NNPP. ii. revert DISJOINT.
  apply disjoint_equivalent. apply disjoint_equivalent in H. des.
  splits.
  - eapply opt_time_lt_some. eapply sim_timestamp_exact_lt_if; eauto.
  - eapply opt_time_lt_some. eapply sim_timestamp_exact_lt_if; eauto.
  - eapply opt_time_lt_some. eapply sim_timestamp_exact_lt_if; eauto.
    + rewrite opt_time_join_some. eapply sim_timestamp_exact_join; eauto.
    + rewrite opt_time_meet_some. eapply sim_timestamp_exact_meet; eauto.
Qed.

Lemma sim_disjoint_if f v
      from_tgt0 from_src0 to_tgt0 to_src0
      from_tgt1 from_src1 to_tgt1 to_src1
      (WF: Mapping.wf f)
      (VER: loc_version_wf f v)
      (FROM0: sim_timestamp_exact f v from_src0 (Some from_tgt0))
      (TO0: sim_timestamp_exact f v to_src0 (Some to_tgt0))
      (FROM1: sim_timestamp_exact f v from_src1 (Some from_tgt1))
      (TO1: sim_timestamp_exact f v to_src1 (Some to_tgt1))
      (DISJOINT: Interval.disjoint (from_src0, to_src0) (from_src1, to_src1))
  :
    Interval.disjoint (from_tgt0, to_tgt0) (from_tgt1, to_tgt1).
Proof.
  apply NNPP. ii. revert DISJOINT.
  apply disjoint_equivalent. apply disjoint_equivalent in H. des.
  splits.
  - eapply sim_timestamp_exact_lt; eauto.
  - eapply sim_timestamp_exact_lt; eauto.
  - eapply sim_timestamp_exact_lt; eauto.
    + eapply sim_timestamp_exact_join; eauto.
    + eapply sim_timestamp_exact_meet; eauto.
    + eapply opt_time_lt_some. eauto.
Qed.



Definition sim_timemap (L: Loc.t -> Prop)
           (f: Mapping.ts) (v: version) (tm_src tm_tgt: TimeMap.t) :=
  forall l (LOC: L l), sim_timestamp (f l) (v l) (tm_src l) (Some (tm_tgt l)).

Lemma sim_timemap_mon_tgt L f v tm_src tm_tgt0 tm_tgt1
      (SIM: sim_timemap L f v tm_src tm_tgt0)
      (TM: TimeMap.le tm_tgt0 tm_tgt1)
  :
    sim_timemap L f v tm_src tm_tgt1.
Proof.
  ii. eapply sim_timestamp_mon_tgt; eauto. ss.
Qed.

Lemma sim_timemap_mon_ver L f v0 v1 tm_src tm_tgt
      (SIM: sim_timemap L f v0 tm_src tm_tgt)
      (VER: version_le v0 v1)
      (WF: Mapping.wfs f)
      (VERWF: version_wf f v1)
  :
    sim_timemap L f v1 tm_src tm_tgt.
Proof.
  ii. eapply sim_timestamp_mon_ver; eauto.
Qed.

Lemma sim_timemap_mon_mapping L f0 f1 v tm_src tm_tgt
      (WF: Mapping.wfs f0)
      (VERWF: version_wf f0 v)
      (MAP: Mapping.les f0 f1)
  :
    sim_timemap L f0 v tm_src tm_tgt <-> sim_timemap L f1 v tm_src tm_tgt.
Proof.
  split; ii.
  { erewrite <- sim_timestamp_mon_mapping; eauto. }
  { erewrite sim_timestamp_mon_mapping; eauto. }
Qed.

Lemma sim_timemap_mon_locs L0 L1 f v tm_src tm_tgt
      (SIM: sim_timemap L1 f v tm_src tm_tgt)
      (LOCS: L0 <1= L1)
  :
    sim_timemap L0 f v tm_src tm_tgt.
Proof.
  ii. eauto.
Qed.

Lemma sim_timemap_join L f v
      tm_src0 tm_src1 tm_tgt0 tm_tgt1
      (SIM0: sim_timemap L f v tm_src0 tm_tgt0)
      (SIM1: sim_timemap L f v tm_src1 tm_tgt1)
      (WF: Mapping.wfs f)
      (VERWF: version_wf f v)
  :
    sim_timemap L f v (TimeMap.join tm_src0 tm_src1) (TimeMap.join tm_tgt0 tm_tgt1).
Proof.
  ii. unfold TimeMap.join at 2. rewrite opt_time_join_some. eapply sim_timestamp_join; eauto.
Qed.

Lemma sim_timemap_bot l f v tm
      (WF: Mapping.wfs f)
      (VERWF: version_wf f v)
  :
    sim_timemap l f v TimeMap.bot tm.
Proof.
  ii. eapply sim_timestamp_bot; eauto.
Qed.

Lemma sim_timemap_singleton l (L: Loc.t -> Prop) f v
      ts_src ts_tgt
      (SIM: L l -> sim_timestamp (f l) (v l) ts_src (Some ts_tgt))
      (WF: Mapping.wfs f)
      (VERWF: version_wf f v)
  :
    sim_timemap L f v (TimeMap.singleton l ts_src) (TimeMap.singleton l ts_tgt).
Proof.
  ii. unfold TimeMap.singleton.
  setoid_rewrite LocFun.add_spec. des_ifs; eauto.
  rewrite LocFun.init_spec.
  eapply sim_timestamp_bot; eauto.
Qed.

Lemma sim_timemap_mon_src L f v tm_src0 tm_src1 tm_tgt
      (SIM: sim_timemap L f v tm_src1 tm_tgt)
      (TM: TimeMap.le tm_src0 tm_src1)
  :
    sim_timemap L f v tm_src0 tm_tgt.
Proof.
  ii. eapply sim_timestamp_mon_src; eauto.
Qed.

Lemma sim_timemap_mon_mapping_latest L f0 f1 tm_src tm_tgt
      (SIM: sim_timemap L f0 (Mapping.vers f0) tm_src tm_tgt)
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wfs f1)
      (MAP: Mapping.les f0 f1)
  :
  sim_timemap L f1 (Mapping.vers f1) tm_src tm_tgt.
Proof.
  ii. eapply sim_timestamp_mon_mapping_latest; eauto.
Qed.

Lemma sim_timemap_bot_latest L f tm
      (WF: Mapping.wfs f)
  :
    sim_timemap L f (Mapping.vers f) TimeMap.bot tm.
Proof.
  ii. eapply sim_timestamp_bot_latest; auto.
Qed.

Lemma sim_timemap_join_latest L f
      tm_src0 tm_src1 tm_tgt0 tm_tgt1
      (SIM0: sim_timemap L f (Mapping.vers f) tm_src0 tm_tgt0)
      (SIM1: sim_timemap L f (Mapping.vers f) tm_src1 tm_tgt1)
      (WF: Mapping.wfs f)
  :
    sim_timemap L f (Mapping.vers f) (TimeMap.join tm_src0 tm_src1) (TimeMap.join tm_tgt0 tm_tgt1).
Proof.
  ii. unfold TimeMap.join. rewrite opt_time_join_some. eapply sim_timestamp_join_latest; eauto.
Qed.

Lemma sim_timemap_singleton_latest l (L: Loc.t -> Prop) f
      ts_src ts_tgt
      (SIM: L l -> sim_timestamp (f l) (Mapping.ver (f l)) ts_src (Some ts_tgt))
      (WF: Mapping.wfs f)
  :
    sim_timemap L f (Mapping.vers f) (TimeMap.singleton l ts_src) (TimeMap.singleton l ts_tgt).
Proof.
  ii. unfold TimeMap.singleton.
  setoid_rewrite LocFun.add_spec. des_ifs; eauto.
  rewrite LocFun.init_spec.
  eapply sim_timestamp_bot_latest; eauto.
Qed.


Definition time_le_timemap (loc: Loc.t) (ts: Time.t) (tm: TimeMap.t): Prop :=
  Time.le (tm loc) ts.

Record time_le_view (loc: Loc.t) (ts: Time.t) (vw: View.t): Prop :=
  time_le_view_intro {
      time_le_view_pln: time_le_timemap loc ts vw.(View.pln);
      time_le_view_rlx: time_le_timemap loc ts vw.(View.rlx);
    }.

Variant time_le_opt_view (loc: Loc.t) (ts: Time.t):
  forall (vw: option View.t), Prop :=
| time_le_opt_view_some
    vw
    (EXACT: time_le_view loc ts vw)
  :
    time_le_opt_view loc ts (Some vw)
| time_le_opt_view_none
  :
    time_le_opt_view loc ts None
.

Definition time_exact_timemap (loc: Loc.t) (ts: Time.t) (tm: TimeMap.t): Prop :=
  tm loc = ts.

Record time_exact_view (loc: Loc.t) (ts: Time.t) (vw: View.t): Prop :=
  time_exact_view_intro {
      time_exact_view_pln: time_exact_timemap loc ts vw.(View.pln);
      time_exact_view_rlx: time_exact_timemap loc ts vw.(View.rlx);
    }.

Variant time_exact_opt_view (loc: Loc.t) (ts: Time.t):
  forall (vw: option View.t), Prop :=
| time_exact_opt_view_some
    vw
    (EXACT: time_exact_view loc ts vw)
  :
    time_exact_opt_view loc ts (Some vw)
| time_exact_opt_view_none
  :
    time_exact_opt_view loc ts None
.

Record sim_view (L: Loc.t -> Prop)
       (f: Mapping.ts) (v: version) (vw_src vw_tgt: View.t) :=
  sim_timemap_intro {
      sim_view_pln: sim_timemap L f v vw_src.(View.pln) vw_tgt.(View.pln);
      sim_view_rlx: sim_timemap L f v vw_src.(View.rlx) vw_tgt.(View.rlx);
    }.

Lemma sim_view_mon_tgt L f v vw_src vw_tgt0 vw_tgt1
      (SIM: sim_view L f v vw_src vw_tgt0)
      (VW: View.le vw_tgt0 vw_tgt1)
  :
    sim_view L f v vw_src vw_tgt1.
Proof.
  econs.
  { eapply sim_timemap_mon_tgt; eauto.
    { eapply SIM. }
    { eapply VW. }
  }
  { eapply sim_timemap_mon_tgt; eauto.
    { eapply SIM. }
    { eapply VW. }
  }
Qed.

Lemma sim_view_mon_ver L f v0 v1 vw_src vw_tgt
      (SIM: sim_view L f v0 vw_src vw_tgt)
      (VER: version_le v0 v1)
      (WF: Mapping.wfs f)
      (VERWF: version_wf f v1)
  :
    sim_view L f v1 vw_src vw_tgt.
Proof.
  econs.
  { eapply sim_timemap_mon_ver; eauto.
    eapply SIM.
  }
  { eapply sim_timemap_mon_ver; eauto.
    eapply SIM.
  }
Qed.

Lemma sim_view_mon_mapping L f0 f1 v vw_src vw_tgt
      (WF: Mapping.wfs f0)
      (VERWF: version_wf f0 v)
      (MAP: Mapping.les f0 f1)
  :
    sim_view L f0 v vw_src vw_tgt <-> sim_view L f1 v vw_src vw_tgt.
Proof.
  split; ii; econs.
  { erewrite <- sim_timemap_mon_mapping; eauto. eapply H. }
  { erewrite <- sim_timemap_mon_mapping; eauto. eapply H. }
  { erewrite sim_timemap_mon_mapping; eauto. eapply H. }
  { erewrite sim_timemap_mon_mapping; eauto. eapply H. }
Qed.

Lemma sim_view_mon_locs L0 L1 f v vw_src vw_tgt
      (SIM: sim_view L1 f v vw_src vw_tgt)
      (LOCS: L0 <1= L1)
  :
    sim_view L0 f v vw_src vw_tgt.
Proof.
  econs.
  { eapply sim_timemap_mon_locs; eauto. eapply SIM. }
  { eapply sim_timemap_mon_locs; eauto. eapply SIM. }
Qed.

Lemma sim_view_join l f v
      vw_src0 vw_src1 vw_tgt0 vw_tgt1
      (SIM0: sim_view l f v vw_src0 vw_tgt0)
      (SIM1: sim_view l f v vw_src1 vw_tgt1)
      (WF: Mapping.wfs f)
      (VERWF: version_wf f v)
  :
    sim_view l f v (View.join vw_src0 vw_src1) (View.join vw_tgt0 vw_tgt1).
Proof.
  econs.
  { eapply sim_timemap_join; eauto.
    { eapply SIM0. }
    { eapply SIM1. }
  }
  { eapply sim_timemap_join; eauto.
    { eapply SIM0. }
    { eapply SIM1. }
  }
Qed.

Lemma sim_view_bot l f v vw
      (WF: Mapping.wfs f)
      (VERWF: version_wf f v)
  :
    sim_view l f v View.bot vw.
Proof.
  econs.
  { eapply sim_timemap_bot; eauto. }
  { eapply sim_timemap_bot; eauto. }
Qed.

Lemma sim_view_singleton_ur l (L: Loc.t -> Prop) f v
      ts_src ts_tgt
      (SIM: L l -> sim_timestamp (f l) (v l) ts_src (Some ts_tgt))
      (WF: Mapping.wfs f)
      (VERWF: version_wf f v)
  :
    sim_view L f v (View.singleton_ur l ts_src) (View.singleton_ur l ts_tgt).
Proof.
  econs; ss.
  { eapply sim_timemap_singleton; eauto. }
  { eapply sim_timemap_singleton; eauto. }
Qed.

Lemma sim_view_singleton_rw l (L: Loc.t -> Prop) f v
      ts_src ts_tgt
      (SIM: L l -> sim_timestamp (f l) (v l) ts_src (Some ts_tgt))
      (WF: Mapping.wfs f)
      (VERWF: version_wf f v)
  :
    sim_view L f v (View.singleton_rw l ts_src) (View.singleton_rw l ts_tgt).
Proof.
  econs; ss.
  { eapply sim_timemap_bot; eauto. }
  { eapply sim_timemap_singleton; eauto. }
Qed.

Lemma sim_view_mon_src L f v vw_src0 vw_src1 vw_tgt
      (SIM: sim_view L f v vw_src1 vw_tgt)
      (VW: View.le vw_src0 vw_src1)
  :
    sim_view L f v vw_src0 vw_tgt.
Proof.
  inv SIM. econs.
  { eapply sim_timemap_mon_src; eauto. eapply VW. }
  { eapply sim_timemap_mon_src; eauto. eapply VW. }
Qed.

Lemma sim_view_mon_mapping_latest L f0 f1 vw_src vw_tgt
      (SIM: sim_view L f0 (Mapping.vers f0) vw_src vw_tgt)
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wfs f1)
      (MAP: Mapping.les f0 f1)
  :
  sim_view L f1 (Mapping.vers f1) vw_src vw_tgt.
Proof.
  inv SIM. econs.
  { eapply sim_timemap_mon_mapping_latest; eauto. }
  { eapply sim_timemap_mon_mapping_latest; eauto. }
Qed.

Lemma sim_view_bot_latest L f vw
      (WF: Mapping.wfs f)
  :
    sim_view L f (Mapping.vers f) View.bot vw.
Proof.
  econs.
  { eapply sim_timemap_bot_latest; eauto. }
  { eapply sim_timemap_bot_latest; eauto. }
Qed.

Lemma sim_view_join_latest L f
      vw_src0 vw_src1 vw_tgt0 vw_tgt1
      (SIM0: sim_view L f (Mapping.vers f) vw_src0 vw_tgt0)
      (SIM1: sim_view L f (Mapping.vers f) vw_src1 vw_tgt1)
      (WF: Mapping.wfs f)
  :
    sim_view L f (Mapping.vers f) (View.join vw_src0 vw_src1) (View.join vw_tgt0 vw_tgt1).
Proof.
  inv SIM0. inv SIM1. econs.
  { eapply sim_timemap_join_latest; eauto. }
  { eapply sim_timemap_join_latest; eauto. }
Qed.

Lemma sim_view_singleton_ur_latest l (L: Loc.t -> Prop) f
      ts_src ts_tgt
      (SIM: L l -> sim_timestamp (f l) (Mapping.ver (f l)) ts_src (Some ts_tgt))
      (WF: Mapping.wfs f)
  :
    sim_view L f (Mapping.vers f) (View.singleton_ur l ts_src) (View.singleton_ur l ts_tgt).
Proof.
  econs.
  { eapply sim_timemap_singleton_latest; eauto. }
  { eapply sim_timemap_singleton_latest; eauto. }
Qed.

Lemma sim_view_singleton_rw_latest l (L: Loc.t -> Prop) f
      ts_src ts_tgt
      (SIM: L l -> sim_timestamp (f l) (Mapping.ver (f l)) ts_src (Some ts_tgt))
      (WF: Mapping.wfs f)
  :
    sim_view L f (Mapping.vers f) (View.singleton_rw l ts_src) (View.singleton_rw l ts_tgt).
Proof.
  econs; ss.
  { eapply sim_timemap_bot_latest; eauto. }
  { eapply sim_timemap_singleton_latest; eauto. }
Qed.


Variant sim_opt_view (L: Loc.t -> Prop)
        (f: Mapping.ts):
  forall (v: option version) (vw_src vw_tgt: option View.t), Prop :=
| sim_opt_view_some
    v vw_src vw_tgt
    (SIM: sim_view L f v vw_src vw_tgt)
  :
    sim_opt_view L f (Some v) (Some vw_src) (Some vw_tgt)
| sim_opt_view_none
    v vw
  :
    sim_opt_view L f v None vw
.

Lemma sim_opt_view_mon_tgt L f v vw_src vw_tgt0 vw_tgt1
      (SIM: sim_opt_view L f v vw_src vw_tgt0)
      (VW: View.opt_le vw_tgt0 vw_tgt1)
  :
    sim_opt_view L f v vw_src vw_tgt1.
Proof.
  inv SIM; inv VW; econs.
  eapply sim_view_mon_tgt; eauto.
Qed.

Lemma sim_opt_view_mon_ver L f v0 v1 vw_src vw_tgt
      (SIM: sim_opt_view L f v0 vw_src vw_tgt)
      (VER: opt_version_le v0 v1)
      (WF: Mapping.wfs f)
      (VERWF: opt_version_wf f v1)
  :
    sim_opt_view L f v1 vw_src vw_tgt.
Proof.
  inv SIM.
  { destruct v1; ss. econs. eapply sim_view_mon_ver; eauto. }
  { econs. }
Qed.

Lemma sim_opt_view_mon_mapping L f0 f1 v vw_src vw_tgt
      (WF: Mapping.wfs f0)
      (VERWF: opt_version_wf f0 v)
      (MAP: Mapping.les f0 f1)
  :
    sim_opt_view L f0 v vw_src vw_tgt <-> sim_opt_view L f1 v vw_src vw_tgt.
Proof.
  split; i.
  { inv H; econs. erewrite <- sim_view_mon_mapping; eauto. }
  { inv H; econs. erewrite sim_view_mon_mapping; eauto. }
Qed.

Lemma sim_opt_view_mon_locs L0 L1 f v vw_src vw_tgt
      (SIM: sim_opt_view L1 f v vw_src vw_tgt)
      (LOCS: L0 <1= L1)
  :
    sim_opt_view L0 f v vw_src vw_tgt.
Proof.
  inv SIM; econs; eauto.
  eapply sim_view_mon_locs; eauto.
Qed.

Lemma sim_opt_view_unwrap l f v0 v1
      vw_src vw_tgt
      (SIM: sim_opt_view l f v0 vw_src vw_tgt)
      (WF: Mapping.wfs f)
      (VERWF: version_wf f v1)
      (VER: forall v (VER: v0 = Some v), version_le v v1)
  :
    sim_view l f v1 (View.unwrap vw_src) (View.unwrap vw_tgt).
Proof.
  inv SIM; ss.
  { hexploit VER; eauto. i.
    eapply sim_view_mon_ver; eauto. }
  { eapply sim_view_bot; eauto. }
Qed.

Lemma sim_opt_view_mon_src L f v vw_src0 vw_src1 vw_tgt
      (SIM: sim_opt_view L f v vw_src1 vw_tgt)
      (VW: View.opt_le vw_src0 vw_src1)
  :
    sim_opt_view L f v vw_src0 vw_tgt.
Proof.
  inv SIM; inv VW; econs.
  eapply sim_view_mon_src; eauto.
Qed.

Lemma sim_opt_view_mon_mapping_latest L f0 f1 vw_src vw_tgt
      (SIM: sim_opt_view L f0 (Some (Mapping.vers f0)) vw_src vw_tgt)
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wfs f1)
      (MAP: Mapping.les f0 f1)
  :
  sim_opt_view L f1 (Some (Mapping.vers f1)) vw_src vw_tgt.
Proof.
  inv SIM; econs.
  eapply sim_view_mon_mapping_latest; eauto.
Qed.

Lemma sim_opt_view_unwrap_latest l f
      vw_src vw_tgt
      (SIM: sim_opt_view l f (Some (Mapping.vers f)) vw_src vw_tgt)
      (WF: Mapping.wfs f)
  :
    sim_view l f (Mapping.vers f) (View.unwrap vw_src) (View.unwrap vw_tgt).
Proof.
  inv SIM; ss. econs; ss.
  { eapply sim_timemap_bot_latest; auto. }
  { eapply sim_timemap_bot_latest; auto. }
Qed.



Definition top_time (top: Time.t) (f: Mapping.t): Prop :=
  forall ts fts
         (MAP: f.(Mapping.map) f.(Mapping.ver) ts = Some fts),
    Time.lt fts top.

Lemma top_time_mon ts0 ts1 f
      (TOP: top_time ts0 f)
      (TS: Time.le ts0 ts1)
  :
    top_time ts1 f.
Proof.
  ii. eapply TimeFacts.lt_le_lt; eauto.
Qed.

Lemma top_time_mon_mapping ts f0 f1
      (TOP: top_time ts f0)
      (LE: Mapping.le_strong f0 f1)
      (WF0: Mapping.wf f0)
      (WF1: Mapping.wf f1)
  :
    top_time ts f1.
Proof.
  hexploit Mapping.mapping_max; [apply WF0|..]. i.
  destruct (Mapping.map f0 0 None) eqn:EQ; ss.
  hexploit sim_timestamp_exact_mon_ver.
  { eauto. }
  { instantiate (1:=Mapping.ver f0). lia. }
  { eauto. }
  { eapply mapping_latest_wf_loc. }
  i. des. ii.
  hexploit sim_timestamp_exact_le.
  { eapply MAP. }
  { eapply sim_timestamp_exact_mon_strong; [..|eapply SIM]; eauto. }
  { destruct ts0; ss. }
  { eauto. }
  { eapply mapping_latest_wf_loc. }
  i. exploit TOP; eauto. i.
  eapply TimeFacts.le_lt_lt; eauto.
Qed.

Definition top_times (f: Mapping.ts) (tops: Loc.t -> option Time.t): Prop :=
  (<<MAX: forall loc ts fts top
                 (TOP: tops loc = Some top)
                 (MAP: (f loc).(Mapping.map) (f loc).(Mapping.ver) ts = Some fts),
      Time.lt fts top>>) /\
  (<<FIN: exists l, forall loc top (TOP: tops loc = Some top), List.In loc l>>)
.

Lemma top_time_exists f ts
      (WF: Mapping.wf f)
  :
    exists top, (<<TOP: top_time top f>>) /\ (<<TS: Time.lt ts top>>).
Proof.
  hexploit Mapping.map_finite; eauto. i. des.
  hexploit (@finite_greatest (fun _ => True) (List.map snd l)).
  i. des.
  { exists (Time.incr (Time.join ts to)). split.
    { ii. eapply TimeFacts.le_lt_lt; [|eapply Time.incr_spec].
      etrans; [|eapply Time.join_r]. eapply GREATEST; ss.
      eapply H in MAP. eapply List.in_map with (f:=snd) in MAP; auto. }
    { eapply TimeFacts.le_lt_lt; [|eapply Time.incr_spec]. eapply Time.join_l. }
  }
  { exists (Time.incr ts). split.
    { ii. eapply H in MAP. eapply List.in_map with (f:=snd) in MAP.
      exfalso. eapply EMPTY; eauto. }
    { eapply Time.incr_spec. }
  }
Qed.

Variant sim_message
        (loc: Loc.t)
        (f: Mapping.ts):
  forall (v: option version) (msg_src msg_tgt: Message.t), Prop :=
| sim_message_concrete
    v val_src val_tgt vw_src vw_tgt na_src na_tgt
    (VAL: Const.le val_tgt val_src)
    (SIM: sim_opt_view (fun loc0 => loc0 <> loc) f (Some v) vw_src vw_tgt)
    (NA: Bool.le na_tgt na_src)
  :
    sim_message loc f (Some v) (Message.message val_src vw_src na_src) (Message.message val_tgt vw_tgt na_tgt)
| sim_message_reserve
    v
  :
    sim_message loc f v Message.reserve Message.reserve
.

Program Instance Bool_le_PreOrder: PreOrder Bool.le.
Next Obligation. Proof. ii. destruct x; ss. Qed.
Next Obligation. Proof. ii. destruct x, y, z; ss. Qed.

Lemma sim_message_mon_tgt loc f v msg_src msg_tgt0 msg_tgt1
      (SIM: sim_message loc f v msg_src msg_tgt0)
      (MSG: Message.le msg_tgt0 msg_tgt1)
  :
    sim_message loc f v msg_src msg_tgt1.
Proof.
  inv SIM; inv MSG.
  { econs; eauto.
    { etrans; eauto. }
    { eapply sim_opt_view_mon_tgt; eauto. }
    { apply Bool.le_implb in NA0. etrans; eauto. }
  }
  { econs. }
Qed.

Lemma sim_message_mon_src L f v msg_src0 msg_src1 msg_tgt
      (SIM: sim_message L f v msg_src1 msg_tgt)
      (MSG: Message.le msg_src0 msg_src1)
  :
    sim_message L f v msg_src0 msg_tgt.
Proof.
  inv SIM; inv MSG; econs; eauto.
  { etrans; eauto. }
  { eapply sim_opt_view_mon_src; eauto. }
  { etrans; eauto. apply Bool.le_implb; auto. }
Qed.

Lemma sim_message_mon_ver loc f v0 v1 msg_src msg_tgt
      (SIM: sim_message loc f v0 msg_src msg_tgt)
      (VER: option_rel version_le v0 v1)
      (WF: Mapping.wfs f)
      (VERWF: opt_version_wf f v1)
  :
    sim_message loc f v1 msg_src msg_tgt.
Proof.
  inv SIM.
  { ss. des_ifs. econs; eauto. eapply sim_opt_view_mon_ver; eauto. }
  { ss. des_ifs. econs; eauto. }
Qed.

Lemma sim_message_mon_mapping loc f0 f1 v msg_src msg_tgt
      (WF: Mapping.wfs f0)
      (VERWF: opt_version_wf f0 v)
      (MAP: Mapping.les f0 f1)
  :
    sim_message loc f0 v msg_src msg_tgt <-> sim_message loc f1 v msg_src msg_tgt.
Proof.
  split; i.
  { inv H; try by (econs; auto). econs 1; eauto.
    erewrite <- sim_opt_view_mon_mapping; eauto. }
  { inv H; try by (econs; auto). econs 1; eauto. erewrite sim_opt_view_mon_mapping; eauto. }
Qed.

Lemma sim_message_mon_mapping_latest L f0 f1 msg_src msg_tgt
      (SIM: sim_message L f0 (Some (Mapping.vers f0)) msg_src msg_tgt)
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wfs f1)
      (MAP: Mapping.les f0 f1)
  :
  sim_message L f1 (Some (Mapping.vers f1)) msg_src msg_tgt.
Proof.
  inv SIM; econs; auto.
  eapply sim_opt_view_mon_mapping_latest; eauto.
Qed.

Lemma message_to_time_le_opt_view loc to val released na
      (MSGTO: Memory.message_to (Message.message val released na) loc to)
      (MSGWF: Message.wf (Message.message val released na))
  :
    time_le_opt_view loc to released.
Proof.
  inv MSGTO. destruct released; ss; econs. econs.
  { inv MSGWF. inv RELEASED. red. etrans; eauto. eapply WF. }
  { eauto. }
Qed.

Definition mapping_update_latest (f: Mapping.t)
           (mapping: option Time.t -> option Time.t) :=
  Mapping.mk
    (fun v => if PeanoNat.Nat.eq_dec v (S f.(Mapping.ver))
              then mapping
              else
                f.(Mapping.map) v)
    (S f.(Mapping.ver))
.

Lemma mapping_update_latest_mapping f mapping
  :
    (mapping_update_latest f mapping).(Mapping.map) (mapping_update_latest f mapping).(Mapping.ver) = mapping.
Proof.
  ss. des_ifs.
Qed.

Lemma mapping_update_latest_wf f mapping
      (WF: Mapping.wf f)
      (FINMAP: exists l, forall ts fts (MAP: mapping ts = Some fts),
            List.In (ts, fts) l)
      (MAPLT: forall ts0 ts1 fts0 fts1
                     (MAP0: mapping ts0 = Some fts0) (MAP0: mapping ts1 = Some fts1),
          opt_time_lt ts0 ts1 <-> Time.lt fts0 fts1)
      (MAPINCR: forall ts fts0
                       (MAP0: f.(Mapping.map) f.(Mapping.ver) ts = Some fts0),
          exists fts1,
            (<<MAP: mapping ts = Some fts1>>) /\
            (<<TS: Time.le fts0 fts1>>))
  :
    (<<MAPWF: Mapping.wf (mapping_update_latest f mapping)>>) /\
    (<<MAPLE: Mapping.le f (mapping_update_latest f mapping)>>) /\
    (<<MAPLESTRONG: forall (PRESERVE: forall ts fts
                                             (MAP: f.(Mapping.map) f.(Mapping.ver) ts = Some fts),
                               mapping ts = Some fts),
        Mapping.le_strong f (mapping_update_latest f mapping)>>)
.
Proof.
  splits.
  { econs; ss.
    { i. des_ifs. eapply Mapping.map_finite; eauto. }
    { i. des_ifs.
      { eapply MAPLT; eauto. }
      { eapply Mapping.mapping_map_lt_iff; eauto. }
    }
    { i. des_ifs.
      { esplits; eauto. refl. }
      { hexploit Mapping.mapping_incr; [..|refl|eapply MAP0|]; eauto.
        { lia. }
        i. des. eapply MAPINCR in MAP; eauto. des.
        esplits; eauto.
      }
      { exfalso. lia. }
      { eapply Mapping.mapping_incr; eauto. lia. }
    }
    { i. des_ifs.
      { exfalso. lia. }
      { eapply Mapping.mapping_empty; eauto. lia. }
    }
    { eapply Mapping.mapping_bot; eauto. }
    { apply WF. }
  }
  { red. splits; ss; eauto.
    { i. des_ifs. exfalso. lia. }
  }
  { i. red. splits; ss; eauto.
    { i. des_ifs. exfalso. lia. }
    { i. des_ifs.
      { eapply PRESERVE; eauto. }
      { exfalso. lia. }
    }
  }
Qed.

Definition mapping_update (f: Mapping.t) ts fts: Mapping.t :=
  mapping_update_latest
    f
    (fun ts' =>
       if (opt_time_eq_dec ts ts')
       then Some fts
       else f.(Mapping.map) f.(Mapping.ver) ts')
.

Lemma mapping_update_old f ts fts ts0 fts0
      (MAP: sim_timestamp_exact f f.(Mapping.ver) fts0 ts0)
  :
    (sim_timestamp_exact (mapping_update f ts fts) (mapping_update f ts fts).(Mapping.ver) fts0 ts0) \/
    (ts = ts0).
Proof.
  unfold sim_timestamp_exact in *. ss. des_ifs; auto.
Qed.

Lemma mapping_update_new f ts fts
  :
    sim_timestamp_exact (mapping_update f ts fts) (mapping_update f ts fts).(Mapping.ver) fts ts.
Proof.
  unfold sim_timestamp_exact in *. ss. des_ifs; auto.
Qed.

Lemma mapping_update_wf f ts fts
      (WF: Mapping.wf f)
      (INCR: forall fts' (MAP: sim_timestamp_exact f f.(Mapping.ver) fts' ts),
          Time.le fts' fts)
      (LEFT: forall ts' fts'
                    (LT: opt_time_lt ts' ts)
                    (MAP: sim_timestamp_exact f f.(Mapping.ver) fts' ts'),
          Time.lt fts' fts)
      (RIGHT: forall ts' fts'
                     (LT: opt_time_lt ts ts')
                     (MAP: sim_timestamp_exact f f.(Mapping.ver) fts' ts'),
          Time.lt fts fts')
  :
    Mapping.wf (mapping_update f ts fts).
Proof.
  eapply mapping_update_latest_wf; eauto.
  { hexploit (Mapping.map_finite WF f.(Mapping.ver)); eauto. i. des.
    exists ((ts, fts)::l). i.
    unfold mapping_update in *. ss. des_ifs.
    { auto. }
    { right. eapply H; eauto. }
  }
  { i. des_ifs.
    { split; i; timetac. exfalso. eapply opt_time_lt_StrOrder; eauto. }
    { split.
      { i. hexploit LEFT; eauto. }
      { i. destruct (opt_time_le_lt_dec ts1 ts0); auto.
        apply opt_time_le_inv in o. des; ss.
        eapply RIGHT in o; eauto.
        exfalso. eapply Time.lt_strorder. etrans; eauto. }
    }
    { split.
      { i. hexploit RIGHT; eauto. }
      { i. destruct (opt_time_le_lt_dec ts1 ts0); auto.
        apply opt_time_le_inv in o. des; ss.
        2:{ exfalso. eapply n; ss. }
        eapply LEFT in o; eauto.
        exfalso. eapply Time.lt_strorder. etrans; eauto. }
    }
    { eapply Mapping.mapping_map_lt_iff; eauto. }
  }
  { i. des_ifs.
     { esplits; eauto. }
     { esplits; eauto. refl. }
  }
Qed.

Lemma mapping_update_le f ts fts
  :
    Mapping.le f (mapping_update f ts fts).
Proof.
  red. splits.
  { ss. lia. }
  { i. ss. des_ifs. exfalso. lia. }
Qed.

Lemma mapping_add f0 ts
      (WF: Mapping.wf f0)
  :
    exists f1 fts,
      (<<WF: Mapping.wf f1>>) /\
      (<<MAPLE: Mapping.le_strong f0 f1>>) /\
      (<<MAP: sim_timestamp_exact f1 f1.(Mapping.ver) fts ts>>) /\
      (<<MAPEQ: forall ts0 fts0 (MAP: sim_timestamp_exact f0 f0.(Mapping.ver) fts0 ts0),
          sim_timestamp_exact f1 f1.(Mapping.ver) fts0 ts0>>)
.
Proof.
  destruct (classic (exists fts1, sim_timestamp_exact f0 f0.(Mapping.ver) fts1 ts)).
  { des. exists f0, fts1. splits; auto. refl. }
  hexploit Mapping.map_finite; eauto. i. des.
  hexploit (@finite_greatest_opt (fun ts' => opt_time_le ts' ts /\ exists fts, Mapping.map f0 f0.(Mapping.ver) ts' = Some fts) (List.map fst l)). i. des.
  2:{
    exfalso. hexploit (Mapping.mapping_bot); eauto. i.
    eapply sim_timestamp_exact_mon_ver with (v1:=f0.(Mapping.ver)) in H1; eauto.
    { des. eapply EMPTY.
      { hexploit H; eauto. i.
        eapply List.in_map with (f:=fst) in H0; ss; eauto. }
      { split.
        { eapply opt_time_bot_spec. }
        { esplits; eauto. }
      }
    }
    { eapply le_0_n. }
    { eapply mapping_latest_wf_loc. }
  }
  apply opt_time_le_inv in SAT. des.
  2:{ inv SAT. exfalso. eapply H; eauto. }
  hexploit (@finite_least_opt (fun ts' => opt_time_le ts ts' /\ exists fts, Mapping.map f0 f0.(Mapping.ver) ts' = Some fts) (List.map fst l)). i. des.
  { apply opt_time_le_inv in SAT1. des.
    2:{ inv SAT1. exfalso. eapply H; eauto. }
    assert (LT: Time.lt fts fts0).
    { erewrite <- Mapping.mapping_map_lt_iff; cycle 2; try eassumption.
      transitivity ts; eauto. }
    exists (mapping_update f0 ts (Time.middle fts fts0)), (Time.middle fts fts0).
    splits.
    { eapply mapping_update_wf; eauto.
      { i. exfalso. eapply H; eauto. }
      { i. hexploit (GREATEST (fst (ts', fts'))).
        { eapply List.in_map; eauto. }
        { splits; eauto. ss. apply opt_time_lt_le. auto. }
        i. ss. eapply (@TimeFacts.le_lt_lt _ fts).
        { erewrite <- Mapping.mapping_map_le; cycle 2; eauto. }
        { eapply Time.middle_spec; eauto. }
      }
      { i. hexploit (LEAST (fst (ts', fts'))).
        { eapply List.in_map; eauto. }
        { splits; eauto. ss. apply opt_time_lt_le. auto. }
        i. ss. eapply (@TimeFacts.lt_le_lt _ fts0).
        { eapply Time.middle_spec; eauto. }
        { erewrite <- Mapping.mapping_map_le; cycle 2; eauto. }
      }
    }
    { red. splits.
      { ss. lia. }
      { i. ss. des_ifs. exfalso. lia. }
      { i. ss. des_ifs.
        { exfalso. eapply H; eauto. }
        { replace v with f0.(Mapping.ver) by lia. auto. }
      }
    }
    { unfold sim_timestamp_exact. ss. des_ifs. }
    { unfold sim_timestamp_exact. i. ss. des_ifs. ss. des; clarify.
      exfalso. eapply H; eauto. }
  }
  { exists (mapping_update f0 ts (Time.incr fts)), (Time.incr fts).
    splits.
    { eapply mapping_update_wf; eauto.
      { i. exfalso. eapply H; eauto. }
      { i. hexploit (GREATEST (fst (ts', fts'))).
        { eapply List.in_map; eauto. }
        { splits; eauto. ss. apply opt_time_lt_le. auto. }
        i. ss. eapply (@TimeFacts.le_lt_lt _ fts).
        { erewrite <- Mapping.mapping_map_le; cycle 2; eauto. }
        { eapply Time.incr_spec; eauto. }
      }
      { i. exfalso. eapply EMPTY.
        { eapply List.in_map. eapply H0. eapply MAP. }
        { ss. splits; eauto. apply opt_time_lt_le. auto. }
      }
    }
    { red. splits.
      { ss. lia. }
      { i. ss. des_ifs. exfalso. lia. }
      { i. ss. des_ifs.
        { exfalso. eapply H; eauto. }
        { replace v with f0.(Mapping.ver) by lia. auto. }
      }
    }
    { unfold sim_timestamp_exact. ss. des_ifs. }
    { unfold sim_timestamp_exact. i. ss. des_ifs. ss. des; clarify.
      exfalso. eapply H; eauto. }
  }
Qed.

Lemma mapping_add_list f0 tl
      (WF: Mapping.wf f0)
  :
    exists f1,
      (<<WF: Mapping.wf f1>>) /\
      (<<MAPLE: Mapping.le_strong f0 f1>>) /\
      (<<MAP: forall ts (IN: List.In ts tl), exists fts, sim_timestamp_exact f1 f1.(Mapping.ver) fts (Some ts)>>) /\
      (<<MAPEQ: forall ts0 fts0 (MAP: sim_timestamp_exact f0 f0.(Mapping.ver) fts0 ts0),
          sim_timestamp_exact f1 f1.(Mapping.ver) fts0 ts0>>)
.
Proof.
  revert f0 WF. induction tl; i.
  { exists f0. splits; auto; ss. reflexivity. }
  { hexploit mapping_add; eauto. i. des.
    hexploit IHtl; eauto. i. des. esplits; eauto.
    { etrans; eauto. }
    { i. ss. des; eauto. subst. eauto. }
  }
Qed.

Fixpoint map_shift (f: option Time.t -> option Time.t) (l: list (option Time.t))
         (ts: option Time.t) (fts: Time.t): option Time.t -> option Time.t :=
  match l with
  | [] => f
  | hd::tl =>
    if (opt_time_le_lt_dec ts hd)
    then map_shift (fun to => if opt_time_eq_dec to hd then Some fts else f to) tl ts (Time.incr fts)
    else map_shift f tl ts fts
  end.

Lemma map_shift_finite l:
  forall f ts fts
         (FIN: exists l', forall ts' fts' (MAP: f ts' = Some fts'),
               List.In (ts', fts') l'),
  exists l', forall ts' fts' (MAP: map_shift f l ts fts ts' = Some fts'),
      List.In (ts', fts') l'.
Proof.
  induction l; ss; i; des.
  des_ifs.
  { hexploit (IHl (fun to => if opt_time_eq_dec to a then Some fts else f to)).
    { exists ((a, fts)::l'). i. des_ifs; ss; auto. }
    i. des. esplits. i. eapply H; eauto.
  }
  { eapply IHl; eauto. }
Qed.

Lemma map_shift_preserved l:
  forall f ts fts to
         (FORALL: List.Forall (opt_time_lt to) l),
    map_shift f l ts fts to = f to.
Proof.
  induction l; ss. i. inv FORALL. des_ifs.
  { erewrite IHl; eauto. des_ifs. exfalso. eapply opt_time_lt_StrOrder; eauto. }
  { erewrite IHl; eauto. }
Qed.

Lemma map_shift_correct0 l:
  forall f ts fts
         (SORTED: times_sorted_opt l)
         to
         (TS: opt_time_lt to ts),
    map_shift f l ts fts to = f to.
Proof.
  induction l; i; ss.
  inv SORTED. des_ifs.
  { erewrite IHl; eauto. des_ifs.
    exfalso. eapply opt_time_le_lt_bot; eauto.
  }
  { eapply IHl; eauto. }
Qed.

Lemma map_shift_correct1 l:
  forall f ts fts
         (SORTED: times_sorted_opt l)
         (IN: List.In ts l),
    map_shift f l ts fts ts = Some fts.
Proof.
  induction l; i; ss.
  inv SORTED. des_ifs.
  { des; clarify.
    { erewrite map_shift_preserved; eauto. des_ifs. }
    { eapply List.Forall_forall in IN; eauto. exfalso. eapply opt_time_le_lt_bot; eauto. }
  }
  { des; clarify.
    { exfalso. eapply opt_time_lt_StrOrder; eauto. }
    { eapply IHl; eauto. }
  }
Qed.

Lemma map_shift_correct2 l:
  forall f ts fts
         (SORTED: times_sorted_opt l)
         to
         (TS: opt_time_le ts to)
         (IN: List.In to l),
  exists fto,
    (<<MAP: map_shift f l ts fts to = Some fto>>) /\
    (<<TS: Time.le fts fto>>) /\
    (<<LARGER: forall to' (TS: opt_time_lt to to') (IN: List.In to' l),
        exists fto',
          (<<MAP: map_shift f l ts fts to' = Some fto'>>) /\
          (<<TS: Time.lt fto fto'>>)>>)
.
Proof.
  induction l; ss; i. des; clarify.
  { inv SORTED. des_ifs.
    { exists fts. esplits.
      { erewrite map_shift_preserved; eauto. des_ifs. }
      { refl. }
      { i. des; clarify.
        { exfalso. eapply opt_time_lt_StrOrder; eauto. }
        { hexploit IHl.
          { eauto. }
          { etrans; [eapply TS|]. eapply opt_time_lt_le. eauto. }
          { eauto. }
          i. des. esplits.
          { eapply MAP. }
          { eapply TimeFacts.lt_le_lt; eauto. eapply Time.incr_spec. }
        }
      }
    }
    { exfalso. eapply opt_time_le_lt_bot; eauto. }
  }
  { inv SORTED. des_ifs.
    { hexploit IHl.
      { eauto. }
      { eapply TS. }
      { eauto. }
      i. des. esplits.
      { eapply MAP. }
      { etrans; eauto. left. eapply Time.incr_spec. }
      { i. des; clarify.
        { exfalso. eapply List.Forall_forall in HD; eauto. exfalso.
          eapply opt_time_lt_StrOrder. etrans; eauto.
        }
        { eauto. }
      }
    }
    { hexploit IHl.
      { eauto. }
      { eapply TS. }
      { eauto. }
      i. des. esplits.
      { eapply MAP. }
      { auto. }
      i. des; clarify.
      { exfalso. eapply opt_time_lt_StrOrder.
        eapply opt_time_lt_le_lt.
        { eapply TS1. }
        etrans.
        { apply opt_time_lt_le. eapply o. }
        { eauto. }
      }
      { hexploit LARGER; eauto. }
    }
  }
Qed.

Lemma map_shift_sound_aux l:
  forall f ts fts to fto
         (MAP: map_shift f l ts fts to = Some fto),
    (<<OLD: f to = Some fto>>) \/
    ((<<NEW: List.In to l>>) /\ (<<TS: opt_time_le ts to>>)).
Proof.
  induction l; ss; auto. i. des_ifs.
  { eapply IHl in MAP. des; eauto.
    des_ifs; eauto.
  }
  { eapply IHl in MAP; eauto. des; auto. }
Qed.

Lemma map_shift_sound l:
  forall f ts fts to fto
         (MAP: map_shift f l ts fts to = Some fto)
         (TOP: forall to' fto'
                      (MAP: f to' = Some fto'),
             Time.lt fto' fts)
         (SORTED: times_sorted_opt l)
         (FIN: forall to' fto' (MAP: f to' = Some fto'),
             List.In to' l),
    ((<<OLD: f to = Some fto>>) /\ (<<TS: opt_time_lt to ts>>) /\ (<<TS: Time.lt fto fts>>)) \/
    ((<<NEW: List.In to l>>) /\ (<<TS: opt_time_le ts to>>) /\ (<<TS: Time.le fts fto>>)).
Proof.
  i. hexploit map_shift_sound_aux; eauto. i. des; auto.
  { destruct (opt_time_le_lt_dec ts to); auto.
    { right. splits; auto.
      { eapply FIN; eauto. }
      { splits; auto. hexploit map_shift_correct2; eauto.
        i. des. rewrite MAP in MAP0. clarify.
      }
    }
    { left. splits; auto. eapply TOP; eauto. }
  }
  { right. splits; auto.
    hexploit map_shift_correct2; eauto.
    i. des. rewrite MAP in MAP0. clarify.
  }
Qed.

Lemma shifted_mapping_exists (f0: Mapping.t)
      ts fts
      (TOP: top_time fts f0)
      (WF: Mapping.wf f0)
  :
    exists f1,
      (<<SAME: forall to fto
                      (TS: opt_time_lt to ts)
                      (MAP: sim_timestamp_exact f0 f0.(Mapping.ver) fto to),
          sim_timestamp_exact f1 f1.(Mapping.ver) fto to>>) /\
      (<<TS: sim_timestamp_exact f1 f1.(Mapping.ver) fts ts>>) /\
      (<<LE: Mapping.le f0 f1>>) /\
      (<<WF: Mapping.wf f1>>)
.
Proof.
  hexploit mapping_map_finite_exact; eauto. i. des.
  hexploit (@sorting_opt_sorted (ts::(List.map fst l))); eauto. i. des.
  set (l_sorted := sorting_opt (ts::(List.map fst l))).
  hexploit (@mapping_update_latest_wf f0 (map_shift (f0.(Mapping.map) f0.(Mapping.ver)) l_sorted ts fts)); eauto.
  { eapply map_shift_finite; eauto.
    eapply Mapping.map_finite; eauto. }
  { i. hexploit map_shift_sound; [apply MAP0|..]; eauto.
    { i. eapply COMPLETE. right.
      refine (List.in_map fst _ (_, _) _). eapply H; eauto.
    }
    hexploit map_shift_sound; [apply MAP1|..]; eauto.
    { i. eapply COMPLETE. right.
      refine (List.in_map fst _ (_, _) _). eapply H; eauto.
    }
    i. des.
    { eapply Mapping.mapping_map_lt_iff; eauto. }
    { split.
      { i. eapply TimeFacts.lt_le_lt; eauto. }
      { i. eapply opt_time_lt_le_lt; eauto. }
    }
    { split.
      { i. exfalso. eapply opt_time_lt_StrOrder.
        eapply opt_time_lt_le_lt.
        { eapply TS1. }
        etrans.
        { eapply TS. }
        apply opt_time_lt_le. eauto.
      }
      { i. exfalso. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt.
        { eapply TS2. }
        etrans.
        { eapply TS0. }
        left. auto.
      }
    }
    { destruct (opt_time_le_lt_dec ts1 ts0).
      { apply opt_time_le_inv in o. des; cycle 1.
        { inv o; clarify. split; i; timetac. exfalso. eapply opt_time_lt_StrOrder; eauto. }
        assert (Time.lt fts1 fts0).
        { hexploit map_shift_correct2; [..|eapply NEW0|]; eauto.
          i. des. hexploit LARGER; eauto. i. des.
          rewrite MAP0 in MAP2. clarify.
        }
        split; i.
        { exfalso. eapply opt_time_lt_StrOrder. etrans; [eapply H1|]; eauto. }
        { exfalso. eapply Time.lt_strorder. etrans; [eapply H1|]; eauto. }
      }
      { split; auto. i.
        hexploit map_shift_correct2; [..|eapply NEW|]; eauto.
        i. des. hexploit LARGER; eauto. i. des.
        rewrite MAP1 in MAP2. clarify.
      }
    }
  }
  { i. destruct (opt_time_le_lt_dec ts ts0).
    { hexploit map_shift_correct2; eauto.
      { eapply COMPLETE. right.
        refine (List.in_map fst _ (_, _) _). eapply H; eauto.
      }
      { i. des. esplits; eauto.
        exploit TOP; eauto. i. etrans; eauto. left. auto.
      }
    }
    { erewrite map_shift_correct0; eauto. esplits; eauto. refl. }
  }
  i. des. esplits; [..|eapply MAPWF]; eauto.
  { i. unfold sim_timestamp_exact in *.
    rewrite mapping_update_latest_mapping.
    erewrite map_shift_correct0; eauto.
  }
  { unfold sim_timestamp_exact.
    rewrite mapping_update_latest_mapping.
    erewrite map_shift_correct1; eauto.
    eapply COMPLETE. ss. auto.
  }
Qed.



Variant sim_reserves
        (f: Mapping.ts)
        (prom_src prom_tgt: Memory.t): Prop :=
| sim_reserves_intro
    (MESSAGE: forall loc to from
                     (GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)),
      exists fto ffrom,
        (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom (Some from)>>) /\
          (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto (Some to)>>) /\
          (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)>>))
    (SOUND: forall loc fto ffrom
                   (GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)),
        ((exists to from,
             (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto (Some to)>>) /\
               (<<GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)>>))))
.

Lemma sim_reserves_get
      f prom_src prom_tgt loc from_tgt to_tgt
      (SIM: sim_reserves f prom_src prom_tgt)
      (GET: Memory.get loc to_tgt prom_tgt = Some (from_tgt, Message.reserve))
  :
    exists from_src to_src,
      (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src (Some from_tgt)>>) /\
      (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt)>>) /\
      (<<GET: Memory.get loc to_src prom_src = Some (from_src, Message.reserve)>>).
Proof.
  inv SIM. hexploit MESSAGE; eauto. i. des. esplits; eauto.
Qed.

Lemma sim_reserves_get_if f prom_src prom_tgt loc from_src to_src
      (SIM: sim_reserves f prom_src prom_tgt)
      (GET: Memory.get loc to_src prom_src = Some (from_src, Message.reserve))
  :
  exists from_tgt to_tgt,
    (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src (Some from_tgt)>>) /\
      (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt)>>) /\
      (<<GET: Memory.get loc to_tgt prom_tgt = Some (from_tgt, Message.reserve)>>)
.
Proof.
  inv SIM. hexploit SOUND; eauto. i. des.
  { hexploit MESSAGE; eauto. i. des.
    hexploit GET1. i. des.
    hexploit sim_timestamp_exact_inject.
    { eapply TO. }
    { eapply TO0. }
    i. clarify. esplits; eauto.
  }
Qed.


Lemma add_sim_reserves f mem_tgt0 mem_tgt1 mem_src0 mem_src1
      loc from_tgt to_tgt from_src to_src
      (ADDTGT: Memory.add mem_tgt0 loc from_tgt to_tgt Message.reserve mem_tgt1)
      (PROMS: sim_reserves f mem_src0 mem_tgt0)
      (ADDSRC: Memory.add mem_src0 loc from_src to_src Message.reserve mem_src1)
      (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src (Some from_tgt))
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt))
      (WF: Mapping.wfs f)
  :
    sim_reserves f mem_src1 mem_tgt1.
Proof.
  econs.
  { i. erewrite Memory.add_o in GET; eauto. des_ifs.
    { ss. des; clarify. esplits; eauto.
      i. esplits; eauto.
      eapply Memory.add_get0; eauto. }
    { guardH o. hexploit sim_reserves_get; eauto. i. des.
      esplits; eauto. erewrite Memory.add_o; eauto. des_ifs; eauto.
      exfalso. ss. des; clarify. unguard. des; ss.
      eapply o. cut (Some to = Some to_tgt); i; clarify.
      eapply sim_timestamp_exact_unique; eauto.
      eapply mapping_latest_wf_loc.
    }
  }
  { i. erewrite Memory.add_o in GET; eauto. des_ifs.
    { ss. des; clarify. esplits; eauto.
      eapply Memory.add_get0; eauto. }
    { guardH o. hexploit sim_reserves_get_if; eauto. i. des.
      { esplits; eauto. eapply Memory.add_get1; eauto. }
    }
  }
Qed.

Lemma remove_sim_reserves f mem_tgt0 mem_tgt1 mem_src0 mem_src1
      loc from_tgt to_tgt from_src to_src
      (REMOVETGT: Memory.remove mem_tgt0 loc from_tgt to_tgt Message.reserve mem_tgt1)
      (PROMS: sim_reserves f mem_src0 mem_tgt0)
      (REMOVESRC: Memory.remove mem_src0 loc from_src to_src Message.reserve mem_src1)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt))
      (WF: Mapping.wfs f)
  :
    sim_reserves f mem_src1 mem_tgt1.
Proof.
  econs.
  { i. erewrite Memory.remove_o in GET; eauto. des_ifs.
    guardH o. hexploit sim_reserves_get; eauto. i. des.
    esplits; eauto. erewrite Memory.remove_o; eauto. des_ifs; eauto.
    exfalso. ss. des; clarify. unguard. des; ss.
    eapply o. cut (Some to = Some to_tgt); i; clarify.
    eapply sim_timestamp_exact_unique; eauto.
    eapply mapping_latest_wf_loc.
  }
  { i. erewrite Memory.remove_o in GET; eauto. des_ifs.
    guardH o. hexploit sim_reserves_get_if; eauto. i. des.
    { esplits; eauto. erewrite <- GET0.
      erewrite Memory.remove_o; eauto. des_ifs. exfalso.
      unguard. ss. des; clarify.
      eapply o. eapply sim_timestamp_exact_inject; eauto.
    }
  }
Qed.

Lemma sim_reserves_cancel f mem_tgt0 mem_tgt1 mem_src0
      loc from_tgt to_tgt
      (REMOVETGT: Memory.remove mem_tgt0 loc from_tgt to_tgt Message.reserve mem_tgt1)
      (PROMS: sim_reserves f mem_src0 mem_tgt0)
  :
    exists from_src to_src mem_src1,
      (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src (Some from_tgt)>>) /\
      (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt)>>) /\
      (<<GET: Memory.get loc to_src mem_src0 = Some (from_src, Message.reserve)>>) /\
      (<<GET: Memory.remove mem_src0 loc from_src to_src Message.reserve mem_src1>>).
Proof.
  hexploit sim_reserves_get; eauto.
  { eapply Memory.remove_get0; eauto. }
  i. des. hexploit GET; eauto. i. des.
  hexploit Memory.remove_exists; eauto. i. des. esplits; eauto.
Qed.


Variant no_reserve_covered loc ts mem: Prop :=
| no_reserve_covered_intro
    from to msg
    (GET: Memory.get loc to mem = Some (from, msg))
    (ITV: Interval.mem (from, to) ts)
    (RESERVE: msg <> Message.reserve)
.

Lemma no_reserve_coverd_covered loc ts mem
      (COVER: no_reserve_covered loc ts mem)
  :
    covered loc ts mem.
Proof.
  inv COVER. econs; eauto.
Qed.

Lemma add_no_reserve_covered mem0 mem1 loc from to msg loc' ts'
      (RESERVE: no_reserve_covered loc' ts' mem0)
      (ADD: Memory.add mem0 loc from to msg mem1)
  :
    no_reserve_covered loc' ts' mem1.
Proof.
  inv RESERVE. econs; eauto.
  eapply Memory.add_get1; eauto.
Qed.

Lemma remove_no_reserve_covered mem0 mem1 loc from to loc' ts'
      (RESERVE: no_reserve_covered loc' ts' mem0)
      (REMOVE: Memory.remove mem0 loc from to Message.reserve mem1)
  :
    no_reserve_covered loc' ts' mem1.
Proof.
  hexploit Memory.remove_get0; eauto. i. des.
  inv RESERVE. econs; eauto.
  erewrite Memory.remove_o; eauto. des_ifs.
  ss. des; clarify.
Qed.

Lemma sim_timestamp_exact_bot f v
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    exists fbot,
      (<<SIM: sim_timestamp_exact f v fbot (Some Time.bot)>>) /\
      (<<BOT: forall ts fts (MAP: sim_timestamp_exact f v fts ts),
          Time.le fbot fts>>).
Proof.
  hexploit sim_timestamp_exact_mon_ver.
  { eapply Mapping.mapping_bot; eauto. }
  { lia. }
  { eauto. }
  { eauto. }
  i. des. esplits; eauto. i.
  eapply sim_timestamp_exact_le; eauto. eapply opt_time_bot_spec.
Qed.

Lemma sim_timestamp_exact_bot_if f v ts
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
      (SIM: sim_timestamp_exact f v Time.bot ts)
  :
    ts = Some Time.bot.
Proof.
  eapply opt_time_le_antisym; [|eapply opt_time_bot_spec].
  hexploit sim_timestamp_exact_bot; eauto. i. des.
  eapply sim_timestamp_exact_le_if; eauto. eapply Time.bot_spec.
Qed.

Variant sim_memory
        (flag: Loc.t -> bool)
        (D: Loc.t -> bool)
        (f: Mapping.ts)
        (mem_src mem_tgt: Memory.t)
  : Prop :=
| sim_memory_intro
    (MESSAGE: forall loc to from msg_tgt
                     (GET: Memory.get loc to mem_tgt = Some (from, msg_tgt))
                     (RESERVE: msg_tgt <> Message.reserve)
                     (FLAG: flag loc = false)
                     (GPRM: D loc = false),
        (exists fto ffrom msg_src,
            (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto (Some to)>>) /\
              (<<GET: Memory.get loc fto mem_src = Some (ffrom, msg_src)>>) /\
              (<<MSG: sim_message loc f (Some (Mapping.vers f)) msg_src msg_tgt>>)) \/
          (exists fto to_src from_src val_src,
              (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto (Some to)>>) /\
                (<<SRC: Time.lt fto to_src>>) /\
                (<<GET: Memory.get loc to_src mem_src = Some (from_src, Message.message val_src None true)>>)))
    (SOUND: forall loc fto0 ffrom1 msg_src
                   (GET: Memory.get loc fto0 mem_src = Some (ffrom1, msg_src)),
        (exists fto1 ffrom0 to from,
            (<<TS0: Time.le ffrom0 ffrom1>>) /\
              (<<TS1: Time.le fto0 fto1>>) /\
              (<<FROM: __guard__((ffrom0 = Time.bot /\ from = Time.bot) \/ sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom0 (Some from))>>) /\
              (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto1 (Some to)>>) /\
              (<<COVERED: forall ts (ITV: Interval.mem (from, to) ts),
                  covered loc ts mem_tgt>>)) \/
          (<<OUT: top_time ffrom1 (f loc)>>))
.

Definition max_memory_val
           (f: Mapping.t) (loc: Loc.t) (to: Time.t) (val: Const.t)
           (mem: Memory.t): Prop :=
  exists ts from,
    (<<GET: Memory.get loc to mem = Some (from, Message.message val None true)>>) /\
      (<<MAXSRC: Memory.max_ts loc mem = to>>) /\
      (<<SIMTS: sim_timestamp_exact f f.(Mapping.ver) ts None>>) /\
      (<<TS: Time.lt ts from>>)
.

Lemma max_memory_val_mon_strong f0 f1 loc to val mem
      (MAX: max_memory_val f0 loc to val mem)
      (MAPLE: Mapping.le_strong f0 f1)
      (MAPWF: Mapping.wf f0)
  :
  max_memory_val f1 loc to val mem.
Proof.
  unfold max_memory_val in *. des. subst.
  esplits; eauto. eapply sim_timestamp_exact_mon_strong; eauto.
Qed.

Variant sim_promises_local
        (flag_src: Loc.t -> bool)
        (flag_tgt: Loc.t -> bool)
        (prm_src prm_tgt: BoolMap.t)
  : Prop :=
| sim_promises_local_intro
    (FLAGSRC: forall loc (FLAG: flag_src loc = true), prm_src loc = false)
    (NOFLAG: forall loc (SRC: flag_src loc = false) (TGT: flag_tgt loc = false),
        prm_src loc = prm_tgt loc)
    (FLAGTGT: forall loc (SRC: flag_src loc = false) (TGT: flag_tgt loc = true),
        prm_src loc = true)
.

Variant sim_promises_global
        (flag_src: Loc.t -> bool)
        (gprm_src gprm_tgt: BoolMap.t)
  : Prop :=
| sim_promises_global_intro
    (FLAGSRC: forall loc (FLAG: flag_src loc = true), gprm_src loc = false)
    (SIM: forall loc (FLAGSRC: flag_src loc = false),
        implb (gprm_tgt loc) (gprm_src loc))
.

Definition boolmap_plus (bm0 bm1: BoolMap.t) := fun loc => orb (bm0 loc) (bm1 loc).

Definition own_fp_upd (ctx: Loc.t -> bool): (Loc.t -> bool) -> (Loc.t -> bool) -> Prop :=
  fun lown0 lown1 =>
    forall (DISJOINT: BoolMap.disjoint lown0 ctx),
      BoolMap.disjoint lown1 ctx.

Program Instance own_fp_upd_PreOrder ctx: PreOrder (own_fp_upd ctx).
Next Obligation.
Proof.
  ii. eapply DISJOINT; eauto.
Qed.
Next Obligation.
Proof.
  ii. eapply H0; eauto.
Qed.

Lemma own_fp_upd_eq ctx lown0 lown1
      (UPD: forall loc (CTX: ctx loc = true), lown0 loc = lown1 loc)
  :
  own_fp_upd ctx lown0 lown1.
Proof.
  ii. rewrite <- UPD in GET1; auto. eapply DISJOINT; eauto.
Qed.

Definition wf_D_upd: ((Loc.t -> bool) * (Loc.t -> bool)) -> ((Loc.t -> bool) * (Loc.t -> bool)) -> Prop :=
  fun '(flag0, D0) '(flag1, D1) =>
    forall
      ctx
      (DISJOINT: BoolMap.disjoint flag0 ctx)
      (EQ: D0 = boolmap_plus flag0 ctx),
      (<<DISJOINT: BoolMap.disjoint flag1 ctx>>) /\
        (<<EQ: D1 = boolmap_plus flag1 ctx>>).

Program Instance wf_D_upd_PreOrder: PreOrder wf_D_upd.
Next Obligation.
Proof.
  ii. destruct x as [? ?]. ss.
Qed.
Next Obligation.
Proof.
  ii. destruct x as [? ?], y as [? ?], z as [? ?]. ss.
  i. hexploit H; eauto. i. des. eapply H0; eauto.
Qed.

Lemma wf_D_upd_if flag0 D0 flag1 D1
      (WF: forall loc,
          match (flag0 loc) with
          | false =>
              match (D0 loc) with
              | true => flag1 loc = false /\ D1 loc = true
              | false => flag1 loc = D1 loc
              end
          | true =>
              match (D0 loc) with
              | true => flag1 loc = D1 loc
              | false => True
              end
          end)
  :
  wf_D_upd (flag0, D0) (flag1, D1).
Proof.
  ii. subst. splits.
  { ii. specialize (WF loc). specialize (DISJOINT loc).
    unfold boolmap_plus in *. des_ifs; des; auto; ss.
  }
  { extensionality loc.
    specialize (WF loc). specialize (DISJOINT loc).
    unfold boolmap_plus, orb in *. des_ifs; des; auto; ss.
    destruct (ctx loc); ss. exfalso. auto.
  }
Qed.

Variant owned_future (prom: BoolMap.t):
  (Mapping.ts * Global.t * Global.t) -> (Mapping.ts * Global.t * Global.t) -> Prop :=
| owned_future_intro
    f0 gl_src0 gl_tgt0 f1 gl_src1 gl_tgt1
    (FUTURE: forall loc (OWN: prom loc = true),
        (<<MAP: Mapping.le_strong (f0 loc) (f1 loc)>>) /\
          (<<GLSRC: owned_future_global_loc loc gl_src0 gl_src1>>) /\
          (<<GLTGT: owned_future_global_loc loc gl_tgt0 gl_tgt1>>))
  :
  owned_future prom (f0, gl_src0, gl_tgt0) (f1, gl_src1, gl_tgt1)
.

Global Program Instance owned_future_PreOrder prom:
  PreOrder (owned_future prom).
Next Obligation.
Proof.
  ii. destruct x as [[? ?] ?]. econs; eauto. i. splits; auto.
  { refl. }
  { refl. }
  { refl. }
Qed.
Next Obligation.
Proof.
  ii. inv H. inv H0. econs; eauto. i.
  hexploit FUTURE; eauto. hexploit FUTURE0; eauto.
  i. des. splits; auto.
  { etrans; eauto. }
  { etrans; eauto. }
  { etrans; eauto. }
Qed.

Lemma owned_future_mon_locs prom0 prom1 c0 c1
      (OWNED: owned_future prom1 c0 c1)
      (PROMLE: BoolMap.le prom0 prom1)
  :
  owned_future prom0 c0 c1.
Proof.
  inv OWNED. econs. i. eapply FUTURE; eauto.
Qed.

Lemma owned_future_max_readable gl0 lprm loc ts val released gl1
      (OWNED: owned_future_global_loc loc gl0 gl1)
      (LE: Global.le gl0 gl1)
  :
  max_readable gl0 lprm loc ts val released
  <->
    max_readable gl1 lprm loc ts val released
.
Proof.
  rr in OWNED. des. split; i.
  { inv H. econs.
    { eapply LE; eauto. }
    { rewrite PROM. auto. }
    { i. destruct msg; ss. eapply MEM in GET0. eauto. }
  }
  { inv H. econs.
    { eapply MEM; eauto. }
    { rewrite <- PROM. auto. }
    { i. destruct msg; ss. eapply LE in GET0. eauto. }
  }
Qed.

Lemma sim_promises_src_fulfill
      flag_src flag_tgt lprm_src0 lprm_tgt gprm_src0 gprm_tgt
      loc
      (LPRM: sim_promises_local flag_src flag_tgt lprm_src0 lprm_tgt)
      (GPRM: sim_promises_global flag_src gprm_src0 gprm_tgt)
      (SRCWF: BoolMap.le lprm_src0 gprm_src0)
      (TGTWF: BoolMap.le lprm_tgt gprm_tgt)
      (NORACE: gprm_src0 loc = true -> lprm_src0 loc = true)
  :
  exists lprm_src1 gprm_src1,
    (<<FULFULL: Promises.fulfill lprm_src0 gprm_src0 loc Ordering.na lprm_src1 gprm_src1>>) /\
      (<<LPRM: sim_promises_local (LocFun.add loc true flag_src) flag_tgt lprm_src1 lprm_tgt>>) /\
      (<<GPRM: sim_promises_global (LocFun.add loc true flag_src) gprm_src1 gprm_tgt>>) /\
      (<<UNCH: forall loc0 (OWN: BoolMap.minus gprm_src0 lprm_src0 loc0 = true),
          gprm_src1 loc0 = gprm_src0 loc0>>)
.
Proof.
  destruct (gprm_src0 loc) eqn:EQG.
  { esplits.
    { econs 2; eauto. }
    { inv LPRM. econs; i.
      { setoid_rewrite LocFun.add_spec in FLAG. setoid_rewrite LocFun.add_spec.
        des_ifs. eauto.
      }
      { setoid_rewrite LocFun.add_spec in SRC. setoid_rewrite LocFun.add_spec.
        des_ifs. eauto.
      }
      { setoid_rewrite LocFun.add_spec in SRC. setoid_rewrite LocFun.add_spec.
        des_ifs. eauto.
      }
    }
    { inv GPRM. econs; i.
      { setoid_rewrite LocFun.add_spec in FLAG. setoid_rewrite LocFun.add_spec.
        des_ifs. eauto.
      }
      { setoid_rewrite LocFun.add_spec in FLAGSRC0. setoid_rewrite LocFun.add_spec.
        des_ifs. eapply SIM; eauto.
      }
    }
    { unfold BoolMap.minus, andb, negb. i. rewrite loc_fun_add_spec. des_ifs; auto. }
  }
  { destruct (lprm_src0 loc) eqn:EQL.
    { exfalso. eapply SRCWF in EQL. clarify. }
    esplits.
    { econs 1; eauto. }
    { inv LPRM. econs; i.
      { setoid_rewrite LocFun.add_spec in FLAG.
        des_ifs; auto.
      }
      { setoid_rewrite LocFun.add_spec in SRC.
        des_ifs. eauto.
      }
      { setoid_rewrite LocFun.add_spec in SRC. des_ifs. eauto. }
    }
    { inv GPRM. econs; i.
      { setoid_rewrite LocFun.add_spec in FLAG.
        des_ifs. eauto.
      }
      { setoid_rewrite LocFun.add_spec in FLAGSRC0.
        des_ifs. eapply SIM; eauto.
      }
    }
    { unfold BoolMap.minus, andb, negb. i. des_ifs; auto. }
  }
Qed.

Lemma sim_promises_deflag_unmatch
      flag_src flag_tgt lprm_src0 lprm_tgt gprm_src0 gprm_tgt
      loc
      (LPRM: sim_promises_local flag_src flag_tgt lprm_src0 lprm_tgt)
      (GPRM: sim_promises_global flag_src gprm_src0 gprm_tgt)
      (SRCWF: BoolMap.le lprm_src0 gprm_src0)
      (TGTWF: BoolMap.le lprm_tgt gprm_tgt)
      (FLAG: flag_src loc = true)
  :
  exists lprm_src1 gprm_src1,
    (<<PROMISE: __guard__((<<PROMISE: Promises.promise lprm_src0 gprm_src0 loc lprm_src1 gprm_src1>>) \/ (<<EQ: lprm_src1 = lprm_src0 /\ gprm_src1 = gprm_src0>>))>>) /\
      (<<LPRM: sim_promises_local (LocFun.add loc false flag_src) (LocFun.add loc true flag_tgt) lprm_src1 lprm_tgt>>) /\
      (<<GPRM: sim_promises_global (LocFun.add loc false flag_src) gprm_src1 gprm_tgt>>) /\
      (<<UNCH: forall loc0 (OWN: BoolMap.minus gprm_src0 lprm_src0 loc0 = true),
          gprm_src1 loc0 = gprm_src0 loc0>>)
.
Proof.
  destruct (gprm_src0 loc) eqn:EQG.
  { inv GPRM. rewrite FLAGSRC in EQG; eauto. ss. }
  destruct (lprm_src0 loc) eqn:EQL.
  { inv LPRM. rewrite FLAGSRC in EQL; eauto. ss. }
  esplits.
  { left. econs; eauto. }
  { inv LPRM. econs; i.
    { setoid_rewrite LocFun.add_spec in FLAG0. setoid_rewrite LocFun.add_spec.
      des_ifs; eauto.
    }
    { setoid_rewrite LocFun.add_spec in SRC. setoid_rewrite LocFun.add_spec in TGT.
      setoid_rewrite LocFun.add_spec. des_ifs. eauto.
    }
    { setoid_rewrite LocFun.add_spec in SRC. setoid_rewrite LocFun.add_spec in TGT.
      setoid_rewrite LocFun.add_spec. des_ifs. eauto.
    }
  }
  { inv GPRM. econs; i.
    { setoid_rewrite LocFun.add_spec in FLAG0. setoid_rewrite LocFun.add_spec.
      des_ifs; eauto.
    }
    { setoid_rewrite LocFun.add_spec in FLAGSRC0. setoid_rewrite LocFun.add_spec.
      des_ifs; eauto. destruct (gprm_tgt loc); ss.
    }
  }
  { unfold BoolMap.minus, andb, negb. i. rewrite loc_fun_add_spec. des_ifs; auto. }
Qed.

Lemma sim_promises_deflag_match
      flag_src flag_tgt lprm_src0 lprm_tgt gprm_src0 gprm_tgt
      loc
      (LPRM: sim_promises_local flag_src flag_tgt lprm_src0 lprm_tgt)
      (GPRM: sim_promises_global flag_src gprm_src0 gprm_tgt)
      (SRCWF: BoolMap.le lprm_src0 gprm_src0)
      (TGTWF: BoolMap.le lprm_tgt gprm_tgt)
      (FLAG: flag_src loc = true)
      (NORACE: gprm_tgt loc = true -> lprm_tgt loc = true)
  :
  exists lprm_src1 gprm_src1,
    (<<PROMISE: __guard__((<<PROMISE: Promises.promise lprm_src0 gprm_src0 loc lprm_src1 gprm_src1>>) \/ (<<EQ: lprm_src1 = lprm_src0 /\ gprm_src1 = gprm_src0>>))>>) /\
      (<<LPRM: sim_promises_local (LocFun.add loc false flag_src) (LocFun.add loc false flag_tgt) lprm_src1 lprm_tgt>>) /\
      (<<GPRM: sim_promises_global (LocFun.add loc false flag_src) gprm_src1 gprm_tgt>>) /\
      (<<UNCH: forall loc0 (OWN: BoolMap.minus gprm_src0 lprm_src0 loc0 = true),
          gprm_src1 loc0 = gprm_src0 loc0>>)
.
Proof.
  destruct (gprm_src0 loc) eqn:EQG.
  { inv GPRM. rewrite FLAGSRC in EQG; eauto. ss. }
  destruct (lprm_src0 loc) eqn:EQL.
  { inv LPRM. rewrite FLAGSRC in EQL; eauto. ss. }
  destruct (lprm_tgt loc) eqn:EQP.
  { esplits.
    { left. econs; eauto. }
    { inv LPRM. econs; i.
      { setoid_rewrite LocFun.add_spec in FLAG0. setoid_rewrite LocFun.add_spec.
        des_ifs; eauto.
      }
      { setoid_rewrite LocFun.add_spec in SRC. setoid_rewrite LocFun.add_spec in TGT.
        setoid_rewrite LocFun.add_spec. des_ifs. eauto.
      }
      { setoid_rewrite LocFun.add_spec in SRC. setoid_rewrite LocFun.add_spec in TGT.
        setoid_rewrite LocFun.add_spec. des_ifs. eauto.
      }
    }
    { inv GPRM. econs; i.
      { setoid_rewrite LocFun.add_spec in FLAG0. setoid_rewrite LocFun.add_spec.
        des_ifs; eauto.
      }
      { setoid_rewrite LocFun.add_spec in FLAGSRC0. setoid_rewrite LocFun.add_spec.
        des_ifs; eauto. destruct (gprm_tgt loc); ss.
      }
    }
    { unfold BoolMap.minus, andb, negb. i. rewrite loc_fun_add_spec. des_ifs; auto. }
  }
  { esplits.
    { right. eauto. }
    { inv LPRM. econs; i.
      { setoid_rewrite LocFun.add_spec in FLAG0.
        des_ifs; eauto.
      }
      { setoid_rewrite LocFun.add_spec in SRC. setoid_rewrite LocFun.add_spec in TGT.
        des_ifs. eauto.
      }
      { setoid_rewrite LocFun.add_spec in SRC. setoid_rewrite LocFun.add_spec in TGT.
        des_ifs. eauto.
      }
    }
    { inv GPRM. econs; i.
      { setoid_rewrite LocFun.add_spec in FLAG0.
        des_ifs; eauto.
      }
      { setoid_rewrite LocFun.add_spec in FLAGSRC0.
        des_ifs; eauto. destruct (gprm_tgt loc); ss. hexploit NORACE; ss.
      }
    }
    { unfold BoolMap.minus, andb, negb. i. des_ifs; auto. }
  }
Qed.

Lemma sim_promises_deflag
      b flag_src flag_tgt lprm_src0 lprm_tgt gprm_src0 gprm_tgt
      loc
      (LPRM: sim_promises_local flag_src flag_tgt lprm_src0 lprm_tgt)
      (GPRM: sim_promises_global flag_src gprm_src0 gprm_tgt)
      (SRCWF: BoolMap.le lprm_src0 gprm_src0)
      (TGTWF: BoolMap.le lprm_tgt gprm_tgt)
      (FLAG: flag_src loc = true)
      (NORACE: gprm_tgt loc = true -> lprm_tgt loc = true)
  :
  exists lprm_src1 gprm_src1,
    (<<PROMISE: __guard__((<<PROMISE: Promises.promise lprm_src0 gprm_src0 loc lprm_src1 gprm_src1>>) \/ (<<EQ: lprm_src1 = lprm_src0 /\ gprm_src1 = gprm_src0>>))>>) /\
      (<<LPRM: sim_promises_local (LocFun.add loc false flag_src) (LocFun.add loc b flag_tgt) lprm_src1 lprm_tgt>>) /\
      (<<GPRM: sim_promises_global (LocFun.add loc false flag_src) gprm_src1 gprm_tgt>>) /\
      (<<UNCH: forall loc0 (OWN: BoolMap.minus gprm_src0 lprm_src0 loc0 = true),
          gprm_src1 loc0 = gprm_src0 loc0>>)
.
Proof.
  destruct b.
  { eapply sim_promises_deflag_unmatch; eauto. }
  { eapply sim_promises_deflag_match; eauto. }
Qed.

Lemma sim_promises_tgt_promise
      flag_src flag_tgt lprm_src0 lprm_tgt0 gprm_src0 gprm_tgt0
      loc lprm_tgt1 gprm_tgt1
      (LPRM: sim_promises_local flag_src flag_tgt lprm_src0 lprm_tgt0)
      (GPRM: sim_promises_global flag_src gprm_src0 gprm_tgt0)
      (SRCWF: BoolMap.le lprm_src0 gprm_src0)
      (TGTWF: BoolMap.le lprm_tgt0 gprm_tgt0)
      (PROMISE: Promises.promise lprm_tgt0 gprm_tgt0 loc lprm_tgt1 gprm_tgt1)
      (NORACE: gprm_src0 loc = true -> lprm_src0 loc = true)
  :
  exists lprm_src1 gprm_src1,
    (<<PROMISE: __guard__((<<PROMISE: Promises.promise lprm_src0 gprm_src0 loc lprm_src1 gprm_src1>>) \/ (<<EQ: lprm_src1 = lprm_src0 /\ gprm_src1 = gprm_src0>>))>>) /\
      (<<LPRM: sim_promises_local flag_src flag_tgt lprm_src1 lprm_tgt1>>) /\
      (<<GPRM: sim_promises_global flag_src gprm_src1 gprm_tgt1>>) /\
      (<<UNCH: forall loc0 (OWN: BoolMap.minus gprm_src0 lprm_src0 loc0 = true),
          gprm_src1 loc0 = gprm_src0 loc0 /\ gprm_tgt1 loc0 = gprm_tgt0 loc0>>)
.
Proof.
  inv PROMISE. inv ADD. inv GADD.
  destruct (gprm_src0 loc) eqn:EQG.
  { esplits.
    { right. eauto. }
    { inv LPRM. econs; i.
      { auto. }
      { setoid_rewrite LocFun.add_spec.
        des_ifs; eauto.
      }
      { auto. }
    }
    { inv GPRM. econs; i.
      { auto. }
      { setoid_rewrite LocFun.add_spec.
        des_ifs. eapply SIM; eauto.
      }
    }
    { unfold BoolMap.minus, andb, negb. i. rewrite loc_fun_add_spec. des_ifs; auto.
      split; auto. hexploit NORACE; ss.
    }
  }
  { destruct (lprm_src0 loc) eqn:EQL.
    { exfalso. eapply SRCWF in EQL. clarify. }
    destruct (flag_src loc) eqn:EQF.
    { esplits.
      { right. eauto. }
      { inv LPRM. econs; i.
        { auto. }
        { setoid_rewrite LocFun.add_spec.
          des_ifs; eauto.
        }
        { auto. }
      }
      { inv GPRM. econs; i.
        { auto. }
        { setoid_rewrite LocFun.add_spec.
          des_ifs. eapply SIM; eauto.
        }
      }
      { unfold BoolMap.minus, andb, negb. i. rewrite loc_fun_add_spec. des_ifs; auto. }
    }
    esplits.
    { left. econs 1; eauto. }
    { inv LPRM. econs; i.
      { setoid_rewrite LocFun.add_spec.
        des_ifs; eauto.
      }
      { setoid_rewrite LocFun.add_spec.
        des_ifs. eauto.
      }
      { setoid_rewrite LocFun.add_spec.
        des_ifs. eauto.
      }
    }
    { inv GPRM. econs; i.
      { setoid_rewrite LocFun.add_spec.
        des_ifs. eauto.
      }
      { setoid_rewrite LocFun.add_spec.
        des_ifs. eauto.
      }
    }
    { unfold BoolMap.minus, andb, negb. i. rewrite ! loc_fun_add_spec. des_ifs; auto. }
  }
Qed.

Lemma sim_promises_tgt_fulfill
      flag_src flag_tgt lprm_src0 lprm_tgt0 gprm_src0 gprm_tgt0
      loc lprm_tgt1 gprm_tgt1
      (LPRM: sim_promises_local flag_src flag_tgt lprm_src0 lprm_tgt0)
      (GPRM: sim_promises_global flag_src gprm_src0 gprm_tgt0)
      (SRCWF: BoolMap.le lprm_src0 gprm_src0)
      (TGTWF: BoolMap.le lprm_tgt0 gprm_tgt0)
      (FULFILL: Promises.fulfill lprm_tgt0 gprm_tgt0 loc Ordering.na lprm_tgt1 gprm_tgt1)
      (NORACE: gprm_src0 loc = true -> lprm_src0 loc = true)
  :
  exists lprm_src1 gprm_src1,
    (<<PROMISE: __guard__((<<PROMISE: Promises.promise lprm_src0 gprm_src0 loc lprm_src1 gprm_src1>>) \/ (<<EQ: lprm_src1 = lprm_src0 /\ gprm_src1 = gprm_src0>>))>>) /\
      (<<LPRM: sim_promises_local flag_src (LocFun.add loc true flag_tgt) lprm_src1 lprm_tgt1>>) /\
      (<<GPRM: sim_promises_global flag_src gprm_src1 gprm_tgt1>>) /\
      (<<UNCH: forall loc0 (OWN: BoolMap.minus gprm_src0 lprm_src0 loc0 = true),
          gprm_src1 loc0 = gprm_src0 loc0 /\ gprm_tgt1 loc0 = gprm_tgt0 loc0>>)
.
Proof.
  des. destruct (gprm_src0 loc) eqn:EQG.
  { esplits.
    { right. econs; eauto. }
    { inv LPRM. econs; i.
      { eauto. }
      { inv FULFILL.
        { setoid_rewrite LocFun.add_spec in TGT. des_ifs. eauto. }
        { inv REMOVE. inv GREMOVE.
          setoid_rewrite LocFun.add_spec in TGT.
          setoid_rewrite LocFun.add_spec.  des_ifs; eauto.
        }
      }
      { setoid_rewrite LocFun.add_spec in TGT. des_ifs; eauto. }
    }
    { inv GPRM. econs; i.
      { eauto. }
      { inv FULFILL.
        { eauto. }
        { inv REMOVE. inv GREMOVE.
          setoid_rewrite LocFun.add_spec. des_ifs; eauto.
        }
      }
    }
    { inv FULFILL; auto. inv REMOVE. inv GREMOVE.
      unfold BoolMap.minus, andb, negb. i.
      rewrite ! loc_fun_add_spec. des_ifs; auto.
    }
  }
  destruct (lprm_src0 loc) eqn:EQL.
  { rewrite SRCWF in EQG; ss. }
  destruct (flag_src loc) eqn:EQF.
  { esplits.
    { right. eauto. }
    { inv LPRM. econs; i.
      { eauto. }
      { inv FULFILL.
        { setoid_rewrite LocFun.add_spec in TGT. des_ifs. eauto. }
        { inv REMOVE. inv GREMOVE.
          setoid_rewrite LocFun.add_spec in TGT.
          setoid_rewrite LocFun.add_spec.  des_ifs; eauto.
        }
      }
      { setoid_rewrite LocFun.add_spec in TGT. des_ifs; eauto. }
    }
    { inv GPRM. econs; i.
      { eauto. }
      { inv FULFILL.
        { eauto. }
        { inv REMOVE. inv GREMOVE.
          setoid_rewrite LocFun.add_spec. des_ifs; eauto.
        }
      }
    }
    { inv FULFILL; auto. inv REMOVE. inv GREMOVE.
      unfold BoolMap.minus, andb, negb. i.
      rewrite ! loc_fun_add_spec. des_ifs; auto.
    }
  }
  { esplits.
    { left. econs; eauto. }
    { inv LPRM. econs; i.
      { setoid_rewrite LocFun.add_spec. des_ifs; eauto. }
      { setoid_rewrite LocFun.add_spec.
        inv FULFILL.
        { setoid_rewrite LocFun.add_spec in TGT. des_ifs. eauto. }
        { inv REMOVE. inv GREMOVE.
          setoid_rewrite LocFun.add_spec in TGT.
          setoid_rewrite LocFun.add_spec. des_ifs; eauto.
        }
      }
      { setoid_rewrite LocFun.add_spec in TGT. setoid_rewrite LocFun.add_spec. des_ifs; eauto. }
    }
    { inv GPRM. econs; i.
      { setoid_rewrite LocFun.add_spec. des_ifs; eauto. }
      { setoid_rewrite LocFun.add_spec. inv FULFILL.
        { des_ifs; eauto. destruct (gprm_tgt0 loc); ss. }
        { inv REMOVE. inv GREMOVE.
          setoid_rewrite LocFun.add_spec. des_ifs; eauto.
        }
      }
    }
    { inv FULFILL; auto.
      { unfold BoolMap.minus, andb, negb. i.
        rewrite ! loc_fun_add_spec. des_ifs; auto.
      }
      { inv REMOVE. inv GREMOVE. unfold BoolMap.minus, andb, negb. i.
        rewrite ! loc_fun_add_spec. des_ifs; auto.
      }
    }
  }
Qed.

Lemma sim_memory_get flag gown f mem_src mem_tgt loc from_tgt to_tgt msg_tgt
      (SIM: sim_memory flag gown f mem_src mem_tgt)
      (GET: Memory.get loc to_tgt mem_tgt = Some (from_tgt, msg_tgt))
      (RESERVE: msg_tgt <> Message.reserve)
      (FLAG: flag loc = false)
      (OWN: gown loc = false)
  :
  (exists from_src to_src msg_src,
      (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt)>>) /\
        (<<GET: Memory.get loc to_src mem_src = Some (from_src, msg_src)>>) /\
        (<<MSG: sim_message loc f (Some (Mapping.vers f)) msg_src msg_tgt>>)) \/
    (exists fto to_src from_src val_src,
        (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto (Some to_tgt)>>) /\
          (<<SRC: Time.lt fto to_src>>) /\
          (<<GET: Memory.get loc to_src mem_src = Some (from_src, Message.message val_src None true)>>)).
Proof.
  inv SIM. hexploit MESSAGE; eauto. i. des.
  { left. esplits; eauto. }
  { right. esplits; eauto. }
Qed.

Lemma sim_memory_sound flag gown f mem_src mem_tgt loc fto0 ffrom1 msg_src
      (SIM: sim_memory flag gown f mem_src mem_tgt)
      (GET: Memory.get loc fto0 mem_src = Some (ffrom1, msg_src))
  :
    (exists fto1 ffrom0 to from,
        (<<TS0: Time.le ffrom0 ffrom1>>) /\
        (<<TS1: Time.le fto0 fto1>>) /\
        (<<FROM: __guard__((ffrom0 = Time.bot /\ from = Time.bot) \/ sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom0 (Some from))>>) /\
        (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto1 (Some to)>>) /\
        (<<COVERED: forall ts (ITV: Interval.mem (from, to) ts),
            covered loc ts mem_tgt>>)) \/
      ((<<OUT: top_time ffrom1 (f loc)>>)).
Proof.
  inv SIM. eauto.
Qed.

Lemma sim_memory_sound_strong flag gown f mem_src mem_tgt loc fto0 ffrom1 msg_src
      (SIM: sim_memory flag gown f mem_src mem_tgt)
      (GET: Memory.get loc fto0 mem_src = Some (ffrom1, msg_src))
      (WF: Mapping.wfs f)
  :
    (exists fto1 ffrom0 to from,
        (<<TS0: Time.le ffrom0 ffrom1>>) /\
        (<<TS1: Time.le fto0 fto1>>) /\
        (<<FROM: __guard__((ffrom0 = Time.bot /\ from = Time.bot) \/ sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom0 (Some from))>>) /\
        (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto1 (Some to)>>) /\
        (<<COVERED: forall ts (ITV: Interval.mem (from, to) ts),
            covered loc ts mem_tgt>>) /\
        (<<MAX: forall from' ffrom'
                       (MAP: __guard__((ffrom' = Time.bot /\ from' = Time.bot) \/ sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom' (Some from')))
                       (TS: Time.le ffrom' ffrom1),
            Time.le ffrom' ffrom0>>) /\
        (<<MIN: forall to' fto'
                       (MAP: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto' (Some to'))
                       (TS: Time.le fto0 fto'),
            Time.le fto1 fto'>>)) \/
      ((<<OUT: top_time ffrom1 (f loc)>>)).
Proof.
  pose proof (mapping_latest_wf_loc (f loc)) as VERWF.
  inv SIM. hexploit SOUND; eauto. i. des; eauto. left.
  hexploit mapping_map_finite_exact_some; eauto. i. des.
  hexploit (@finite_greatest (fun ts => Time.le ts ffrom1) (Time.bot::(List.map snd l))). i. des; cycle 1.
  { exfalso. unguard. des.
    { eapply EMPTY.
      { left. auto. }
      { eapply Time.bot_spec. }
    }
    { eapply EMPTY.
      { right. eapply List.in_map. eapply H. eapply FROM. }
      { eauto. }
    }
  }
  hexploit (@finite_least (fun ts => Time.le fto0 ts) (List.map snd l)). i. des; cycle 1.
  { exfalso. eapply EMPTY.
    { eapply List.in_map. eapply H. eapply TO. }
    { eauto. }
  }
  assert (exists t0, __guard__((to0 = Time.bot /\ t0 = Time.bot) \/ sim_timestamp_exact (f loc) (Mapping.ver (f loc)) to0 (Some t0))).
  { ss. des.
    { exists Time.bot. left. auto. }
    { eapply List.in_map_iff in IN. des. clarify.
      destruct x. eapply H in IN1. esplits. right. s. eauto. }
  }
  des. clear IN.
  eapply List.in_map_iff in IN0. des. clarify.
  destruct x. eapply H in IN1. ss.
  eexists t1, to0. esplits; eauto.
  { i. eapply COVERED. eapply Interval.le_mem; eauto. econs; eauto; ss.
    { unguard. des; clarify; try by eapply Time.bot_spec.
      { hexploit (GREATEST ffrom0); eauto.
        { right. refine (List.in_map snd _ (_, _) _). eapply H; eauto. }
        i. destruct (Time.le_lt_dec from Time.bot); auto.
        hexploit sim_timestamp_lt.
        { eapply sim_timestamp_bot; eauto. }
        { eapply FROM. }
        { instantiate (1:=Some _). eauto. }
        { eauto. }
        { eauto. }
        i. exfalso. timetac.
      }
      { eapply opt_time_le_some. eapply sim_timestamp_exact_le_if; eauto.
        eapply GREATEST; eauto. right. refine (List.in_map snd _ (_, _) _).
        eapply H; eauto.
      }
    }
    { eapply opt_time_le_some. eapply sim_timestamp_exact_le_if; eauto.
      eapply LEAST; eauto. refine (List.in_map snd _ (_, _) _).
      eapply H; eauto.
    }
  }
  { i. eapply GREATEST; eauto. inv MAP; des; clarify; auto.
    right. refine (List.in_map snd _ (_, _) _). eapply H; eauto.
  }
  { i. eapply LEAST; eauto.
    refine (List.in_map snd _ (_, _) _). eapply H; eauto.
  }
Qed.

Lemma sim_memory_space flag gown f mem_src mem_tgt loc from_tgt to_tgt from_src to_src
      (SIM: sim_memory flag gown f mem_src mem_tgt)
      (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src (Some from_tgt))
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt))
      (TS: Time.lt from_tgt to_tgt)
      (DISJOINT: forall to2 from2 msg2
                        (GET: Memory.get loc to2 mem_tgt = Some (from2, msg2)),
          Interval.disjoint (from_tgt, to_tgt) (from2, to2))
      (WF: Mapping.wfs f)
  :
    forall to2 from2 msg2
           (GET: Memory.get loc to2 mem_src = Some (from2, msg2)),
      Interval.disjoint (from_src, to_src) (from2, to2).
Proof.
  pose proof (mapping_latest_wf_loc (f loc)) as VERWF.
  eapply covered_disjoint_get_disjoint. ii. inv H.
  hexploit sim_memory_sound; eauto. i. des.
  { assert (Interval.disjoint (from0, to0) (from_tgt, to_tgt)).
    { ii. eapply (get_disjoint_covered_disjoint DISJOINT); eauto. }
    assert (DISJ: Interval.disjoint (ffrom0, fto1) (from_src, to_src)).
    { unguard. des.
      { clarify. hexploit (@sim_timestamp_exact_bot (f loc) (f loc).(Mapping.ver)); eauto.
        i. des. eapply sim_disjoint in H; cycle 1; eauto.
        ii. eapply H; eauto.
        inv LHS. econs; ss.
        inv RHS. ss. eapply TimeFacts.le_lt_lt; [|eauto].
        eapply BOT; eauto.
      }
      { eapply sim_disjoint; eauto. }
    }
    eapply (DISJ ts); auto.
    inv ITV. econs; ss.
    { eapply TimeFacts.le_lt_lt; eauto. }
    { etrans; eauto. }
  }
  { eapply OUT in TO. inv H0. inv ITV. ss.
    eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
    { eapply TO. }
    { transitivity ts; auto. left. auto. }
  }
Qed.

Lemma sim_timestamp_exact_mon_exists
      f0 f1 ts_src0 ts_tgt
      (SIM: sim_timestamp_exact f0 f0.(Mapping.ver) ts_src0 ts_tgt)
      (MAPLE: Mapping.le f0 f1)
      (MAPWF0: Mapping.wf f0)
      (MAPWF1: Mapping.wf f1)
  :
    exists ts_src1,
      (<<SIM: sim_timestamp_exact f1 f1.(Mapping.ver) ts_src1 ts_tgt>>) /\
      (<<TS: Time.le ts_src0 ts_src1>>).
Proof.
  hexploit sim_timestamp_exact_mon_ver.
  { erewrite <- sim_timestamp_exact_mon_mapping; [eapply SIM|..].
    { eauto. }
    { eapply mapping_latest_wf_loc. }
    { eapply MAPLE. }
  }
  { eapply MAPLE. }
  { eauto. }
  { eapply mapping_latest_wf_loc. }
  i. des. esplits; eauto.
Qed.

(* Variant map_future_memory *)
(*         (f0: Mapping.ts) (f1: Mapping.ts) *)
(*         (mem: Memory.t): Prop := *)
(* | map_future_memory_intro *)
(*     (UNDEF: forall loc ts_src ts_tgt *)
(*                    (MAP0: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) ts_src ts_tgt) *)
(*                    (MAP1: ~ sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) ts_src ts_tgt), *)
(*         exists from to val, *)
(*           (<<GET: Memory.get loc to mem = Some (from, Message.undef)>>) /\ *)
(*           (<<TS: Time.le ts_src to>>) /\ *)
(*           (<<TOP: top_time to (f0 loc)>>)) *)
(*     (MAPLE: Mapping.les f0 f1) *)
(* . *)

(* Lemma map_future_memory_les f0 f1 mem *)
(*       (MAP: map_future_memory f0 f1 mem) *)
(*   : *)
(*     Mapping.les f0 f1. *)
(* Proof. *)
(*   inv MAP. auto. *)
(* Qed. *)

(* Lemma map_future_memory_undef f0 f1 mem *)
(*       (MAP: map_future_memory f0 f1 mem) *)
(*       loc ts_src ts_tgt *)
(*       (MAP0: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) ts_src ts_tgt) *)
(*       (MAP1: ~ sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) ts_src ts_tgt) *)
(*   : *)
(*     exists from to, *)
(*       (<<GET: Memory.get loc to mem = Some (from, Message.undef)>>) /\ *)
(*       (<<TS: Time.le ts_src to>>) /\ *)
(*       (<<TOP: top_time to (f0 loc)>>). *)
(* Proof. *)
(*   inv MAP. eapply UNDEF; eauto. *)
(* Qed. *)

(* Lemma map_future_memory_refl *)
(*       f mem *)
(*   : *)
(*   map_future_memory f f mem. *)
(* Proof. *)
(*   econs. *)
(*   { ii. ss. } *)
(*   { red. refl. } *)
(* Qed. *)

Lemma top_time_mon_map f0 f1 ts
      (LE: Mapping.le f0 f1)
      (TOP: top_time ts f1)
      (WF0: Mapping.wf f0)
      (WF1: Mapping.wf f1)
  :
    top_time ts f0.
Proof.
  unfold top_time in *. i.
  hexploit sim_timestamp_exact_mon_exists; eauto.
  i. des. eapply TOP in SIM. eapply TimeFacts.le_lt_lt; eauto.
Qed.

Lemma top_time_mon_strong_map f0 f1 ts
      (LE: Mapping.le_strong f0 f1)
      (TOP: top_time ts f0)
      (WF0: Mapping.wf f0)
      (WF1: Mapping.wf f1)
  :
    top_time ts f1.
Proof.
  destruct (f0.(Mapping.map) 0 None) eqn:EQ.
  2:{ exfalso. eapply WF0. eauto. }
  hexploit sim_timestamp_exact_mon_ver.
  { eapply EQ. }
  { instantiate (1:=f0.(Mapping.ver)). lia. }
  { eauto. }
  { eapply mapping_latest_wf_loc. }
  i. des.
  exploit TOP; eauto. i.
  eapply sim_timestamp_exact_mon_strong in SIM; eauto.
  ii. eapply TimeFacts.le_lt_lt; [|eauto].
  eapply sim_timestamp_exact_le; eauto.
  { destruct ts0; ss. }
  { eapply mapping_latest_wf_loc. }
Qed.

(* Lemma map_future_memory_trans *)
(*       f0 f1 f2 mem0 mem1 *)
(*       (MAP0: map_future_memory f0 f1 mem0) *)
(*       (MAP1: map_future_memory f1 f2 mem1) *)
(*       (FUTURE: Memory.future_weak mem0 mem1) *)
(*       (MAPWF0: Mapping.wfs f0) *)
(*       (MAPWF1: Mapping.wfs f1) *)
(*   : *)
(*   map_future_memory f0 f2 mem1. *)
(* Proof. *)
(*   econs. *)
(*   { ii. destruct (classic (sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) ts_src ts_tgt)). *)
(*     { exploit map_future_memory_undef; [eapply MAP1|..]; eauto. *)
(*       i. des. esplits; eauto. eapply top_time_mon_map; eauto. *)
(*       eapply map_future_memory_les; eauto. *)
(*     } *)
(*     { exploit map_future_memory_undef; [eapply MAP0|..]; eauto. i. des. *)
(*       eapply Memory.future_weak_get1 in GET; eauto; ss. *)
(*       des. inv MSG_LE. *)
(*       esplits; eauto. *)
(*     } *)
(*   } *)
(*   { etrans. *)
(*     { eapply map_future_memory_les; eauto. } *)
(*     { eapply map_future_memory_les; eauto. } *)
(*   } *)
(* Qed. *)

(* Lemma map_future_memory_les_strong *)
(*       f0 f1 mem *)
(*       (MAPLE: Mapping.les_strong f0 f1) *)
(*       (WF: Mapping.wfs f0) *)
(*   : *)
(*   map_future_memory f0 f1 mem. *)
(* Proof. *)
(*   econs. *)
(*   { ii. exfalso. eapply MAP1. *)
(*     eapply sim_timestamp_exact_mon_strong; eauto. } *)
(*   { eapply Mapping.les_strong_les; eauto. } *)
(* Qed. *)


Variant space_future_memory
        (msgs: Loc.t -> Time.t -> Time.t -> Message.t -> Prop)
        (f0: Mapping.ts) (mem0: Memory.t)
        (f1: Mapping.ts) (mem1: Memory.t): Prop :=
| space_future_memory_intro
    (SPACE: forall loc from_tgt to_tgt from0 to0 from1 to1
                   (MSGS: msgs loc to_tgt from_tgt Message.reserve)
                   (FROM0: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) from0 (Some from_tgt))
                   (TO0: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) to0 (Some to_tgt))
                   (FROM1: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) from1 (Some from_tgt))
                   (TO1: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) to1 (Some to_tgt))
                   ts
                   (ITV: Interval.mem (from1, to1) ts)
                   (COVERED: covered loc ts mem1),
        ((<<FROM: from1 = from0>>) /\ (<<TO: to1 = to0>>)) /\ (<<COVERED: covered loc ts mem0>>))
.

Lemma space_future_memory_space msgs mem0 f0 mem1 f1
      (FUTURE: space_future_memory msgs f0 mem0 f1 mem1)
      loc from_tgt to_tgt from0 to0 from1 to1
      (MSGS: msgs loc to_tgt from_tgt Message.reserve)
      (FROM0: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) from0 (Some from_tgt))
      (TO0: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) to0 (Some to_tgt))
      (FROM1: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) from1 (Some from_tgt))
      (TO1: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) to1 (Some to_tgt))
      ts
      (ITV: Interval.mem (from1, to1) ts)
      (COVERED: covered loc ts mem1)
  :
    ((<<FROM: from1 = from0>>) /\ (<<TO: to1 = to0>>)) /\
    (<<COVERED: covered loc ts mem0>>).
Proof.
  inv FUTURE. eauto.
Qed.

Lemma space_future_memory_mon_msgs
      msgs0 msgs1 mem0 f0 mem1 f1
      (FUTURE: space_future_memory msgs1 f0 mem0 f1 mem1)
      (MSGS: msgs0 <4= msgs1)
  :
    space_future_memory msgs0 f0 mem0 f1 mem1.
Proof.
  econs. i. hexploit space_future_memory_space; eauto.
Qed.

Lemma space_future_memory_refl
      msgs mem f0 f1
      (LESTRONG: Mapping.les_strong f0 f1)
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wfs f1)
  :
    space_future_memory msgs f0 mem f1 mem.
Proof.
  pose proof mapping_latest_wf_loc as WF.
  econs. i.
  eapply sim_timestamp_exact_mon_strong in FROM0; eauto.
  eapply sim_timestamp_exact_mon_strong in TO0; eauto.
  eapply sim_timestamp_exact_inject in FROM1; eauto.
  eapply sim_timestamp_exact_inject in TO1; eauto.
Qed.

Lemma space_future_memory_trans
      msgs mem0 mem1 mem2 f0 f1 f2
      (FUTURE0: space_future_memory msgs f0 mem0 f1 mem1)
      (FUTURE1: space_future_memory msgs f1 mem1 f2 mem2)
      (MAPLE0: Mapping.les f0 f1)
      (MAPLE1: Mapping.les f1 f2)
      (MAPWF0: Mapping.wfs f0)
      (MAPWF1: Mapping.wfs f1)
      (MAPWF2: Mapping.wfs f2)
  :
    space_future_memory msgs f0 mem0 f2 mem2.
Proof.
  econs. i.
  hexploit sim_timestamp_exact_mon_exists; [eapply FROM0|..]; eauto. i. des.
  hexploit sim_timestamp_exact_mon_exists; [eapply TO0|..]; eauto. i. des.
  hexploit space_future_memory_space; [eapply FUTURE1|..]; eauto.
  i. des. subst.
  hexploit space_future_memory_space; [eapply FUTURE0|..]; eauto.
Qed.

Lemma space_future_covered_decr
      msgs f mem0 mem1
      (COVERED: forall loc ts (COVERED: covered loc ts mem1), covered loc ts mem0)
  :
    space_future_memory msgs f mem0 f mem1.
Proof.
  econs. i.
  eapply sim_timestamp_exact_inject in FROM0; eauto.
  eapply sim_timestamp_exact_inject in TO0; eauto.
Qed.

Lemma space_future_covered_add
      (msgs: Loc.t -> Time.t -> Time.t -> Message.t -> Prop) f mem0 mem1 loc from to msg
      (ADD: Memory.add mem0 loc from to msg mem1)
      (DISJOINT: forall from_tgt to_tgt from0 to0
                        (MSG: msgs loc to_tgt from_tgt Message.reserve)
                        (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from0 (Some from_tgt))
                        (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to0 (Some to_tgt)),
          Interval.disjoint (from, to) (from0, to0))
  :
  space_future_memory msgs f mem0 f mem1.
Proof.
  econs. i.
  eapply sim_timestamp_exact_inject in FROM0; eauto.
  eapply sim_timestamp_exact_inject in TO0; eauto. subst. splits; auto.
  eapply add_covered in COVERED; eauto. des; auto.
  subst. hexploit DISJOINT; eauto. i.
  exfalso. eapply H; eauto.
Qed.

Lemma unchangable_messages_of_memory
      prom mem
  :
  unchangable mem prom <4= Messages.of_memory mem.
Proof.
  i. inv PR. econs; eauto.
Qed.

Lemma add_space_future_memory flag gown f mem_tgt0 mem_tgt1 mem_src0 mem_src1
      loc from_tgt to_tgt from_src to_src msg_tgt msg_src
      (MEM: sim_memory flag gown f mem_src0 mem_tgt0)
      (ADDTGT: Memory.add mem_tgt0 loc from_tgt to_tgt msg_tgt mem_tgt1)
      (ADDSRC: Memory.add mem_src0 loc from_src to_src msg_src mem_src1)
      (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src (Some from_tgt))
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt))
      (WF: Mapping.wfs f)
  :
  space_future_memory (Messages.of_memory mem_tgt0) f mem_src0 f mem_src1.
Proof.
  econs. i.
  eapply sim_timestamp_exact_inject in FROM0; eauto.
  eapply sim_timestamp_exact_inject in TO0; eauto. subst.
  splits; auto. eapply add_covered in COVERED; eauto.
  des; auto. subst. exfalso.
  inv MSGS. eapply add_succeed_wf in ADDTGT. des.
  eapply DISJOINT in GET. symmetry in GET.
  eapply sim_disjoint in GET; try eassumption; eauto.
  eapply mapping_latest_wf_loc.
Qed.

Lemma add_sim_memory flag gown f mem_tgt0 mem_tgt1 mem_src0 mem_src1
      loc from_tgt to_tgt from_src to_src msg_tgt msg_src
      (ADDTGT: Memory.add mem_tgt0 loc from_tgt to_tgt msg_tgt mem_tgt1)
      (MEM: sim_memory flag gown f mem_src0 mem_tgt0)
      (ADDSRC: Memory.add mem_src0 loc from_src to_src msg_src mem_src1)
      (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src (Some from_tgt))
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt))
      (MSG: sim_message loc f (Some (Mapping.vers f)) msg_src msg_tgt)
      (WF: Mapping.wfs f)
  :
    sim_memory flag gown f mem_src1 mem_tgt1.
Proof.
  econs.
  { i. erewrite Memory.add_o in GET; eauto. des_ifs.
    { ss. des; clarify. left. esplits; eauto.
      { eapply Memory.add_get0; eauto. }
    }
    { guardH o. hexploit sim_memory_get; eauto. i. des.
      { left. esplits; eauto. erewrite Memory.add_o; eauto. des_ifs; eauto.
        exfalso. ss. des; clarify. unguard. des; ss.
        eapply Memory.add_get0 in ADDSRC. des; clarify.
      }
      { right. esplits; eauto. eapply Memory.add_get1; eauto. }
    }
  }
  { i. erewrite Memory.add_o in GET; eauto. des_ifs.
    { ss. des; clarify. left. esplits.
      { refl. }
      { refl. }
      { right. eauto. }
      { eauto. }
      i. econs.
      { eapply Memory.add_get0; eauto. }
      { eauto. }
    }
    { guardH o. hexploit sim_memory_sound; eauto. i. des.
      { left. esplits; eauto. i. eapply COVERED in ITV.
        eapply add_covered; eauto.
      }
      { right. esplits; eauto. }
    }
  }
Qed.

Lemma src_cancel_sim_memory flag gown f
      mem_src0 loc from to mem_src1 mem_tgt
      (REMOVE: Memory.remove mem_src0 loc from to Message.reserve mem_src1)
      (SIM: sim_memory flag gown f mem_src0 mem_tgt)
  :
  sim_memory flag gown f mem_src1 mem_tgt.
Proof.
  econs.
  { i. hexploit sim_memory_get; eauto. i. des.
    { left. esplits; eauto.
      erewrite Memory.remove_o; eauto.
      des_ifs; eauto. ss. des; clarify. exfalso.
      eapply Memory.remove_get0 in REMOVE. des; clarify. inv MSG; ss.
    }
    { hexploit Memory.remove_get1; eauto. i. des; clarify.
      right. esplits; eauto.
    }
  }
  { i. erewrite Memory.remove_o in GET; eauto. des_ifs.
    hexploit sim_memory_sound; eauto.
  }
Qed.

Lemma tgt_cancel_sim_memory flag gown f mem_tgt0 mem_tgt1 mem_src
      loc from_tgt to_tgt from_src to_src
      (REMOVETGT: Memory.remove mem_tgt0 loc from_tgt to_tgt Message.reserve mem_tgt1)
      (MEM: sim_memory flag gown f mem_src mem_tgt0)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt))
      (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src (Some from_tgt))
      (WF: Mapping.wfs f)
      (DISJOINT: forall to from msg (GET: Memory.get loc to mem_src = Some (from, msg)), Interval.disjoint (from_src, to_src) (from, to))
  :
    sim_memory flag gown f mem_src mem_tgt1.
Proof.
  pose proof (mapping_latest_wf_loc (f loc)) as VERWF.
  econs.
  { i. erewrite Memory.remove_o in GET; eauto. des_ifs.
    guardH o. hexploit sim_memory_get; eauto. i. des.
    { left. esplits; eauto. }
    { right. esplits; eauto. }
  }
  { i. hexploit sim_memory_sound_strong; eauto. i. des; eauto.
    left. esplits; eauto. i. eapply remove_covered; eauto.
    splits; auto. eapply not_and_or. ii. des; subst.
    hexploit DISJOINT; eauto. i.
    assert (TIME0: Time.lt from to_tgt).
    { inv ITV. inv H0. ss. eapply TimeFacts.lt_le_lt; eauto. }
    assert (TIME1: Time.lt from_tgt to).
    { inv ITV. inv H0. ss. eapply TimeFacts.lt_le_lt; eauto. }
    assert (FTIME0: Time.lt ffrom0 to_src).
    { unguard. des; subst.
      { eapply sim_timestamp_lt; eauto.
        { eapply sim_timestamp_bot; eauto. }
        { instantiate (1:=Some _). eauto. }
      }
      { eapply sim_timestamp_exact_lt; eauto. }
    }
    assert (FTIME1: Time.lt from_src fto1).
    { eapply sim_timestamp_exact_lt; eauto. }
    destruct (Time.le_lt_dec to_src ffrom1).
    { eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; [eapply FTIME0|].
      eapply MAX; eauto. right. eauto.
    }
    destruct (Time.le_lt_dec fto0 from_src).
    { eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; [eapply FTIME1|].
      eapply MIN; eauto.
    }
    destruct (Time.le_lt_dec to_src fto0).
    { eapply (H to_src).
      { econs; ss.
        { eapply sim_timestamp_exact_lt; eauto.
          eapply Memory.remove_get0 in REMOVETGT. des.
          eapply memory_get_ts_strong in GET0. des; auto.
          subst. inv TIME0.
        }
        { refl. }
      }
      { econs; ss. }
    }
    { eapply (H fto0).
      { econs; ss. left. auto. }
      { econs; ss.
        { eapply memory_get_ts_strong in GET. des; auto.
          subst. inv l0.
        }
        { refl. }
      }
    }
  }
Qed.

Lemma remove_sim_memory flag gown f mem_tgt0 mem_tgt1 mem_src0 mem_src1
      loc from_tgt to_tgt from_src to_src
      (REMOVETGT: Memory.remove mem_tgt0 loc from_tgt to_tgt Message.reserve mem_tgt1)
      (MEM: sim_memory flag gown f mem_src0 mem_tgt0)
      (REMOVESRC: Memory.remove mem_src0 loc from_src to_src Message.reserve mem_src1)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt))
      (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src (Some from_tgt))
      (WF: Mapping.wfs f)
  :
    sim_memory flag gown f mem_src1 mem_tgt1.
Proof.
  eapply src_cancel_sim_memory in MEM; eauto.
  eapply tgt_cancel_sim_memory in MEM; eauto.
  i. erewrite Memory.remove_o in GET; eauto. des_ifs.
  eapply Memory.get_disjoint in GET; [|eapply Memory.remove_get0; eauto].
  ss. des; clarify.
Qed.

Lemma add_src_covered_sim_memory flag gown f mem_src0 mem_src1 mem_tgt
      loc from_tgt to_tgt from_src to_src msg
      (ADD: Memory.add mem_src0 loc from_src to_src msg mem_src1)
      (MEM: sim_memory flag gown f mem_src0 mem_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt))
      (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src (Some from_tgt))
      (WF: Mapping.wfs f)
      (COVERED: forall ts (COVER: Interval.mem (from_tgt, to_tgt) ts), covered loc ts mem_tgt)
  :
    sim_memory flag gown f mem_src1 mem_tgt.
Proof.
  econs.
  { i. hexploit sim_memory_get; eauto. i. des; eauto.
    { left. esplits; eauto. eapply Memory.add_get1; eauto. }
    { right. esplits; eauto. eapply Memory.add_get1; eauto. }
  }
  { i. erewrite Memory.add_o in GET; eauto. des_ifs.
    { ss. des; clarify. left. esplits.
      { refl. }
      { refl. }
      { right. eauto. }
      { eauto. }
      { eauto. }
    }
    { clear o. hexploit sim_memory_sound; eauto. }
  }
Qed.

Lemma sim_memory_add flag gown f mem_tgt0 mem_tgt1 mem_src0
      loc from_tgt to_tgt from_src to_src msg_tgt msg_src
      (ADDTGT: Memory.add mem_tgt0 loc from_tgt to_tgt msg_tgt mem_tgt1)
      (MEM: sim_memory flag gown f mem_src0 mem_tgt0)
      (MSG: sim_message loc f (Some (Mapping.vers f)) msg_src msg_tgt)
      (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src (Some from_tgt))
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt))
      (WF: Mapping.wfs f)
      (MSGWF: Message.wf msg_src)
  :
    exists mem_src1,
      (<<ADD: Memory.add mem_src0 loc from_src to_src msg_src mem_src1>>).
Proof.
  pose proof (mapping_latest_wf_loc (f loc)) as VERWF.
  hexploit add_succeed_wf; eauto. i. des.
  hexploit (@Memory.add_exists mem_src0 loc from_src to_src msg_src).
  { eapply sim_memory_space; eauto. }
  { eapply sim_timestamp_exact_lt; eauto. }
  { eauto. }
  i. des. esplits; eauto.
Qed.

Lemma add_src_sim_memory flag gown f mem_tgt mem_src0 mem_src1
      loc from to val
      (MEM: sim_memory flag gown f mem_src0 mem_tgt)
      (ADD: Memory.add mem_src0 loc from to (Message.message val None true) mem_src1)
      (TOP: top_time from (f loc))
      (WFS: Mapping.wfs f)
  :
    sim_memory (LocFun.add loc true flag) gown f mem_src1 mem_tgt.
Proof.
  econs.
  { i. setoid_rewrite LocFun.add_spec in FLAG.
    des_ifs.
    hexploit sim_memory_get; eauto. i. des.
    { left. esplits; eauto. eapply Memory.add_get1; eauto. }
    { right. esplits; eauto. eapply Memory.add_get1; eauto. }
  }
  { i. erewrite Memory.add_o in GET; eauto.
    destruct (loc_ts_eq_dec (loc0, fto0) (loc, to)).
    { ss. des; clarify. right. des_ifs. }
    { guardH o. hexploit sim_memory_sound; eauto. }
  }
Qed.

Lemma add_tgt_sim_memory flag gown f mem_tgt0 mem_src mem_tgt1
      loc from to val
      (MEM: sim_memory flag gown f mem_src mem_tgt0)
      (ADD: Memory.add mem_tgt0 loc from to (Message.message val None true) mem_tgt1)
  :
    sim_memory (LocFun.add loc true flag) gown f mem_src mem_tgt1.
Proof.
  econs.
  { i. erewrite Memory.add_o in GET; eauto.
    setoid_rewrite LocFun.add_spec in FLAG. des_ifs.
    { ss. des; clarify. }
    guardH o. hexploit sim_memory_get; eauto. i. des.
    { left. esplits; eauto. }
    { right. esplits; eauto. }
  }
  { i. hexploit sim_memory_sound; eauto. i. des.
    { left. esplits; eauto. i. hexploit COVERED; eauto.
      i. inv H. econs; eauto. eapply Memory.add_get1; eauto.
    }
    { right. esplits; eauto. }
  }
Qed.

Lemma add_reserve_owned_future mem0 loc from to mem1 loc0
      (ADD: Memory.add mem0 loc from to Message.reserve mem1)
  :
  owned_future_mem_loc loc0 mem0 mem1.
Proof.
  ii. erewrite Memory.add_o in GET; eauto. des_ifs.
Qed.

Lemma remove_owned_future mem0 loc from to msg mem1 loc0
      (ADD: Memory.remove mem0 loc from to msg mem1)
  :
  owned_future_mem_loc loc0 mem0 mem1.
Proof.
  ii. erewrite Memory.remove_o in GET; eauto. des_ifs.
Qed.

Lemma add_other_owned_future mem0 loc from to msg mem1 loc0
      (ADD: Memory.add mem0 loc from to msg mem1)
      (NEQ: loc0 <> loc)
  :
  owned_future_mem_loc loc0 mem0 mem1.
Proof.
  ii. erewrite Memory.add_o in GET; eauto. des_ifs. ss; des; clarify.
Qed.

Lemma deflag_sim_memory b flag gown f0 mem_tgt mem_src
      loc ts fto ffrom val_src to from val_tgt released na
      (MEM: sim_memory flag gown f0 mem_src mem_tgt)
      (FROM: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) ts None)
      (TS: Time.lt ts ffrom)
      (GETSRC: Memory.get loc fto mem_src = Some (ffrom, Message.message val_src None true))
      (MAXSRC: Memory.max_ts loc mem_src = fto)
      (GETTGT: Memory.get loc to mem_tgt = Some (from, Message.message val_tgt released na))
      (VAL: b = false -> Const.le val_tgt val_src)
      (MAXTGT: forall to0 from0 val0 released0 na0
                   (GET: Memory.get loc to0 mem_tgt = Some (from0, Message.message val0 released0 na0)),
          Time.le to0 to)
      (WF: Mapping.wfs f0)
  :
  exists f1,
    (<<MEM: sim_memory (LocFun.add loc b flag) gown f1 mem_src mem_tgt>>) /\
      (<<UNCH: forall loc0 (NEQ: loc0 <> loc), f1 loc0 = f0 loc0>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<SPACE: space_future_memory (Messages.of_memory mem_tgt) f0 mem_src f1 mem_src>>) /\
      (<<SIM: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) fto (Some to)>>) /\
      (<<MAXNEQ: forall loc0 to0 val0
                        (NEQ: loc0 <> loc),
          max_memory_val (f0 loc0) loc0 to0 val0 mem_src ->
          max_memory_val (f1 loc0) loc0 to0 val0 mem_src>>)
.
Proof.
  hexploit (Cell.finite (mem_tgt loc)). intros [dom DOM].
  hexploit mapping_add_list.
  { eauto. }
  instantiate (1:=loc). instantiate (1:=from::dom).
  i. des.
  assert (TOPTIME0: top_time ffrom (f0 loc)).
  { ii.
    hexploit sim_timestamp_exact_le.
    { eapply MAP0. }
    { eapply FROM. }
    { destruct ts0; ss. }
    { eauto. }
    { eapply mapping_latest_wf_loc. }
    { i. eapply TimeFacts.le_lt_lt; eauto. }
  }
  assert (TOPTIME1: top_time fto f1).
  { eapply top_time_mon_mapping; eauto. eapply top_time_mon; eauto.
    eapply memory_get_ts_le; eauto.
  }
  hexploit shifted_mapping_exists; eauto.
  i. des.
  instantiate (1:=Some to) in SAME.
  set (f := fun loc0 => if Loc.eq_dec loc0 loc then f2 else f0 loc0).
  assert (MAPLES: Mapping.les f0 f).
  { subst f. ii. des_ifs.
    { etrans; [|eauto]. eapply Mapping.le_strong_le; eauto. }
    { reflexivity. }
  }
  assert (MAPWFS: Mapping.wfs f).
  { subst f. ii. des_ifs. }
  assert (UNCHS: forall loc0 (NEQ: loc0 <> loc), f loc0 = f0 loc0).
  { subst f. ii. des_ifs. }
  exists f. esplits; auto.
  { econs; i.
    { erewrite loc_fun_add_spec in FLAG. des_ifs.
      { unfold f. des_ifs.
        destruct msg_tgt; ss. hexploit MAXTGT; eauto.
        i. inv H.
        { right. hexploit MAP.
          { right. eapply DOM; eauto. }
          i. des.
          hexploit sim_timestamp_exact_mon_exists; eauto.
          i. des. esplits; eauto.
          eapply sim_timestamp_exact_lt.
          { eauto. }
          { eauto. }
          { ss. }
          { eauto. }
          { eapply mapping_latest_wf_loc. }
        }
        { inv H0. clarify. left. esplits.
          { eauto. }
          { eauto. }
          { econs; eauto.
            { econs. }
            { destruct na; ss. }
          }
        }
      }
      hexploit sim_memory_get; eauto. i. des.
      { left. esplits; eauto.
        { rewrite UNCHS; eauto. }
        { eapply sim_message_mon_mapping_latest; eauto. }
      }
      { right. esplits; eauto. rewrite UNCHS; eauto. }
    }
    { unfold f. des_ifs.
      { left. hexploit MAP.
        { left. eauto. }
        i. des. destruct (Time.le_lt_dec fts ffrom1).
        { hexploit memory_get_ts_strong; [eapply GETTGT|..].
          i. des.
          { subst. esplits; [| |left; eauto|..].
            { eapply Time.bot_spec. }
            { eapply Memory.max_ts_spec in GET. des. eapply MAX. }
            { eauto. }
            { i. inv ITV. ss. timetac. }
          }
          { esplits.
            { instantiate (1:=fts). auto. }
            { instantiate (1:=(Memory.max_ts loc mem_src)).
              eapply Memory.max_ts_spec in GET. des. clarify.
            }
            { right. eapply SAME; [|eauto]. eauto. }
            { eauto. }
            { i. econs; eauto. }
          }
        }
        { hexploit sim_memory_sound_strong; eauto. i. des.
          { unguard. des.
            { subst. hexploit sim_timestamp_exact_mon_exists.
              { eapply TO. }
              { eauto. }
              { eauto. }
              { eauto. }
              i. des. esplits.
              { eapply TS1. }
              { etrans; [eapply TS2|eapply TS3]. }
              { left. eauto. }
              { unfold f in SIM. des_ifs. eauto. }
              { auto. }
            }
            hexploit sim_timestamp_exact_mon_exists; [eapply TO|..].
            { eauto. }
            { eauto. }
            { eauto. }
            i. des. esplits.
            { eapply TS1. }
            { etrans; [eapply TS2|eapply TS3]. }
            { right. eapply SAME; [|eauto].
              ss. eapply TimeFacts.lt_le_lt.
              2:{ eapply memory_get_ts_le; eauto. }
              eapply opt_time_lt_some.
              eapply sim_timestamp_exact_lt_if.
              { eapply sim_timestamp_exact_mon_strong; [..|eauto]; eauto. }
              { eauto. }
              { eapply TimeFacts.le_lt_lt; eauto. }
              { eauto. }
              { eapply mapping_latest_wf_loc. }
            }
            { unfold f in SIM. des_ifs. eauto. }
            { auto. }
          }
          { exfalso. eapply top_time_mon_mapping in OUT; eauto.
            exploit OUT; [eapply H|..]. i. timetac.
          }
        }
      }
      { hexploit sim_memory_sound; eauto. }
    }
  }
  { econs. i.
    destruct (Loc.eq_dec loc0 loc).
    { subst. split; auto. inv MSGS.
      eapply sim_timestamp_exact_mon_strong in FROM0; eauto.
      eapply sim_timestamp_exact_mon_strong in TO0; eauto.
      hexploit memory_get_disjoint_strong.
      { eapply GET. }
      { eapply GETTGT. }
      i. des; subst; ss.
      { eapply SAME in TO0; ss.
        eapply SAME in FROM0; ss.
        2:{ eapply TimeFacts.le_lt_lt; eauto. eapply memory_get_ts_le; eauto. }
        split.
        { eapply sim_timestamp_exact_inject; eauto. unfold f. des_ifs. }
        { eapply sim_timestamp_exact_inject; eauto. unfold f. des_ifs. }
      }
      { exfalso. inv ITV. inv COVERED. inv ITV. ss.
        hexploit Memory.max_ts_spec; [eapply GET0|..]. i. des.
        eapply sim_timestamp_exact_mon_exists in FROM0; eauto. des.
        unfold f in FROM1. des_ifs. hexploit sim_timestamp_exact_inject.
        { eapply FROM1. }
        { eapply SIM. }
        i. subst. hexploit sim_timestamp_exact_le.
        { eapply TS0. }
        { eapply SIM. }
        { ss. }
        { auto. }
        { eapply mapping_latest_wf_loc. }
        i. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply FROM2. }
        etrans.
        { eapply TO2. }
        etrans.
        { eapply MAX. }
        { eauto. }
      }
    }
    { unfold f in FROM1, TO1. des_ifs. splits; auto.
      { eapply sim_timestamp_exact_inject; eauto. }
      { eapply sim_timestamp_exact_inject; eauto. }
    }
  }
  { unfold f. des_ifs. }
  { i. unfold max_memory_val in *. des.
    unfold f. des_ifs. esplits; eauto.
  }
Qed.

Lemma max_memory_val_add
      mem0 loc0 from0 to0 msg mem1 tto
      f loc to val
      (ADD: Memory.add mem0 loc0 from0 to0 msg mem1)
      (MAX: max_memory_val (f loc) loc to val mem0)
      (SIM: sim_timestamp_exact (f loc0) (f loc0).(Mapping.ver) to0 (Some tto))
      (WF: Mapping.wfs f)
  :
  max_memory_val (f loc) loc to val mem1.
Proof.
  unfold max_memory_val in *. des. esplits; eauto.
  { eapply Memory.add_get1; eauto. }
  subst. hexploit Memory.max_ts_spec.
  { eapply Memory.add_get1; eauto. }
  i. des. eapply TimeFacts.antisym.
  { erewrite Memory.add_o in GET0; eauto. des_ifs.
    { ss. des; clarify.
      hexploit sim_timestamp_exact_lt.
      { eapply SIM. }
      { eapply SIMTS. }
      { ss. }
      { auto. }
      { eapply mapping_latest_wf_loc. }
      i. exfalso. eapply Time.lt_strorder.
      eapply TimeFacts.lt_le_lt.
      { eapply H. }
      etrans.
      { left. apply TS. }
      etrans.
      { eapply memory_get_ts_le; eauto. }
      { auto. }
    }
    { clear o. eapply Memory.max_ts_spec in GET0. des; auto. }
  }
  { auto. }
Qed.

Lemma max_memory_val_cancel
      mem0 loc0 from0 to0 mem1
      f loc to val
      (ADD: Memory.remove mem0 loc0 from0 to0 Message.reserve mem1)
      (MAX: max_memory_val (f loc) loc to val mem0)
  :
  max_memory_val (f loc) loc to val mem1.
Proof.
  unfold max_memory_val in *. des.
  hexploit Memory.remove_get1; eauto. i. des; ss.
  esplits; eauto. subst.
  hexploit Memory.max_ts_spec; eauto. i. des.
  eapply TimeFacts.antisym.
  { erewrite Memory.remove_o in GET0; eauto. des_ifs.
    clear o. eapply Memory.max_ts_spec in GET0. des; auto.
  }
  { auto. }
Qed.

Lemma max_memory_val_add_src
      mem0 loc from to val mem1 f
      (ADD: Memory.add mem0 loc from to (Message.message val None true) mem1)
      (TOP: top_time from (f loc))
      (MAX: Time.le (Memory.max_ts loc mem0) from)
      (WF: Mapping.wfs f)
  :
  (<<MAXEQ: max_memory_val (f loc) loc to val mem1>>) /\
    (<<MAXNEQ: forall loc0 to0 val0
                      (NEQ: loc0 <> loc),
        max_memory_val (f loc0) loc0 to0 val0 mem0 ->
        max_memory_val (f loc0) loc0 to0 val0 mem1>>)
.
Proof.
  split.
  { destruct (Mapping.map (f loc) 0 None) eqn:EQ.
    2:{ exfalso. eapply Mapping.mapping_max; eauto. }
    hexploit sim_timestamp_exact_mon_ver.
    { eapply EQ. }
    { instantiate (1:=(f loc).(Mapping.ver)). lia. }
    { auto.  }
    { apply mapping_latest_wf_loc. }
    i. des.
    exploit TOP; eauto. i.
    rr. esplits; eauto.
    { eapply Memory.add_get0; eauto. }
    { eapply le_add_max_ts; eauto. etrans; eauto.
      eapply add_succeed_wf in ADD. des. left; auto.
    }
  }
  { ii. unfold max_memory_val in *. des. subst.
    hexploit Memory.max_ts_spec.
    { eapply Memory.add_get1; eauto. }
    i. des.
    esplits; eauto.
    { eapply Memory.add_get1; eauto. }
    eapply TimeFacts.antisym; auto.
    erewrite Memory.add_o in GET0; eauto. des_ifs.
    { des; clarify. }
    clear o. eapply Memory.max_ts_spec in GET0. des; auto.
  }
Qed.

(* Lemma add_src_sim_memory_flag_up srctm flag_src f vers mem_tgt mem_src0 mem_src1 *)
(*       loc from to msg *)
(*       (MEM: sim_memory srctm flag_src f vers mem_src0 mem_tgt) *)
(*       (ADD: Memory.add mem_src0 loc from to msg mem_src1) *)
(*       (TOP: top_time from (f loc)) *)
(*       (TS: Time.le (srctm loc) from) *)
(*       (NONE: forall val released (MSG: msg = Message.concrete val released), released = None) *)
(*       (FLAG: flag_src loc = true) *)
(*   : *)
(*     sim_memory (fun loc' => if (Loc.eq_dec loc' loc) then to else srctm loc') flag_src f vers mem_src1 mem_tgt. *)
(* Proof. *)
(*   assert (TOPLE: Time.le (srctm loc) to). *)
(*   { i. etrans; eauto. left. *)
(*     eapply add_succeed_wf in ADD. *)
(*     des. auto. *)
(*   } *)
(*   econs. *)
(*   { i. hexploit sim_memory_get; eauto. i. des. *)
(*     esplits; eauto. eapply Memory.add_get1; eauto. *)
(*   } *)
(*   { i. erewrite Memory.add_o in GET; eauto. *)
(*     destruct (loc_ts_eq_dec (loc0, fto0) (loc, to)). *)
(*     { ss. des; clarify. right. des_ifs. esplits; eauto. *)
(*       { refl. } *)
(*     } *)
(*     { guardH o. hexploit sim_memory_sound; eauto. i. des. *)
(*       { left. esplits; eauto. } *)
(*       { right. des_ifs. esplits; eauto. } *)
(*     } *)
(*   } *)
(*   { i. des_ifs. *)
(*     { eapply top_time_mon; eauto. *)
(*       eapply add_succeed_wf in ADD. *)
(*       des. left. auto. *)
(*     } *)
(*     { eapply sim_memory_top in FLAG0; eauto. } *)
(*   } *)
(*   { i. hexploit sim_memory_undef; eauto. i. des. esplits; eauto. *)
(*     eapply Memory.add_get1; eauto. *)
(*   } *)
(* Qed. *)

Lemma add_src_sim_memory_space_future_aux flag gown f mem_tgt mem_src0 mem_src1
      loc from to msg
      (MEM: sim_memory flag gown f mem_src0 mem_tgt)
      (ADD0: Memory.add mem_src0 loc from to msg mem_src1)
      (TOP: top_time from (f loc))
  :
  space_future_memory (Messages.of_memory mem_tgt) f mem_src0 f mem_src1.
Proof.
  econs. i. inv MSGS.
  eapply sim_timestamp_exact_inject in FROM0; eauto.
  eapply sim_timestamp_exact_inject in TO0; eauto. subst. splits; auto.
  erewrite add_covered in COVERED; eauto. des; subst; auto.
  exfalso. eapply TOP in TO1; eauto.
  inv ITV. inv COVERED0. ss. eapply Time.lt_strorder.
  eapply TimeFacts.lt_le_lt.
  { eapply TO1. }
  etrans.
  { left. eapply FROM0. }
  { auto. }
Qed.

Lemma add_src_sim_memory_space_future flag gown f mem_tgt mem_src0 mem_src1
      loc from to val
      (MEM: sim_memory flag gown f mem_src0 mem_tgt)
      (ADD: Memory.add mem_src0 loc from to (Message.message val None true) mem_src1)
      (TOP: top_time from (f loc))
  :
  space_future_memory (Messages.of_memory mem_tgt) f mem_src0 f mem_src1.
Proof.
  econs. i. inv MSGS.
  eapply sim_timestamp_exact_inject in FROM0; eauto.
  eapply sim_timestamp_exact_inject in TO0; eauto. subst. splits; auto.
  erewrite add_covered in COVERED; eauto. des; subst; auto.
  { exfalso. eapply TOP in TO1; eauto.
    inv ITV. inv COVERED0. ss. eapply Time.lt_strorder.
    eapply TimeFacts.lt_le_lt.
    { eapply TO1. }
    etrans.
    { left. eapply FROM0. }
    { auto. }
  }
Qed.

(* Variant versioned_memory (vers: versions) (mem: Memory.t): Prop := *)
(* | versioned_memory_intro *)
(*     (COMPLETE: forall loc to from val released *)
(*                       (GET: Memory.get loc to mem = Some (from, Message.concrete val (Some released))), *)
(*         exists ver, *)
(*           (<<VER: vers loc to = Some ver>>) /\ *)
(*           (<<FROM: forall ver_from (VER: vers loc from = Some ver_from), *)
(*               version_le ver_from ver>>)) *)
(*     (SOUND: forall loc to ver (VER: vers loc to = Some ver), *)
(*         exists from msg, *)
(*           (<<GET: Memory.get loc to mem = Some (from, msg)>>) /\ (<<RESERVE: msg <> Message.reserve>>)) *)
(* . *)

(* Lemma versioned_memory_lower vers mem0 loc from to msg0 msg1 mem1 *)
(*       (LOWER: Memory.lower mem0 loc from to msg0 msg1 mem1) *)
(*       (VERS: versioned_memory vers mem0) *)
(*   : *)
(*     versioned_memory vers mem1. *)
(* Proof. *)
(*   inv VERS. econs. *)
(*   { i. erewrite Memory.lower_o in GET; eauto. des_ifs. *)
(*     { ss. des; clarify. *)
(*       hexploit lower_succeed_wf; eauto. i. des. *)
(*       inv MSG_LE. inv RELEASED. *)
(*       eapply COMPLETE; eauto. *)
(*     } *)
(*     { eapply COMPLETE; eauto. } *)
(*   } *)
(*   { i. hexploit SOUND; eauto. i. des. *)
(*     eapply Memory.lower_get1 in GET; eauto. des. *)
(*     esplits; eauto. inv MSG_LE; ss. *)
(*   } *)
(* Qed. *)

(* Lemma versioned_memory_cancel vers mem0 loc from to mem1 *)
(*       (CANCEL: Memory.remove mem0 loc from to Message.reserve mem1) *)
(*       (VERS: versioned_memory vers mem0) *)
(*   : *)
(*     versioned_memory vers mem1. *)
(* Proof. *)
(*   inv VERS. econs. *)
(*   { i. erewrite Memory.remove_o in GET; eauto. des_ifs. *)
(*     eapply COMPLETE; eauto. *)
(*   } *)
(*   { i. hexploit SOUND; eauto. i. des. *)
(*     exists from0, msg. erewrite Memory.remove_o; eauto. des_ifs. *)
(*     ss. des; clarify. eapply Memory.remove_get0 in CANCEL. des. clarify. *)
(*   } *)
(* Qed. *)

(* Lemma versioned_memory_cap vers mem0 mem1 *)
(*       (CAP: Memory.cap mem0 mem1) *)
(*       (VERS: versioned_memory vers mem0) *)
(*       (CLOSED: Memory.closed mem0) *)
(*   : *)
(*     versioned_memory vers mem1. *)
(* Proof. *)
(*   inv VERS. econs. *)
(*   { i. eapply Memory.cap_inv in GET; eauto. des; clarify. *)
(*     eapply COMPLETE; eauto. *)
(*   } *)
(*   { i. hexploit SOUND; eauto. i. des. *)
(*     eapply Memory.cap_le in GET; eauto. refl. *)
(*   } *)
(* Qed. *)

(* Lemma versioned_memory_add_non_concrete vers mem0 loc from to msg mem1 *)
(*       (ADD: Memory.add mem0 loc from to msg mem1) *)
(*       (VERS: versioned_memory vers mem0) *)
(*       (CONCRETE: forall val released, msg <> Message.concrete val (Some released)) *)
(*   : *)
(*     versioned_memory vers mem1. *)
(* Proof. *)
(*   inv VERS. econs; eauto. *)
(*   { i. erewrite Memory.add_o in GET; eauto. des_ifs. *)
(*     { ss. des; clarify. exfalso. eapply CONCRETE; eauto. } *)
(*     { eapply COMPLETE; eauto. } *)
(*   } *)
(*   { i. hexploit SOUND; eauto. i. des. eapply Memory.add_get1 in GET; eauto. } *)
(* Qed. *)

(* Lemma versioned_memory_add vers mem0 loc from to msg mem1 v *)
(*       (ADD: Memory.add mem0 loc from to msg mem1) *)
(*       (VERS: versioned_memory vers mem0) *)
(*       (ATTACH: forall (to' : Time.t) (msg' : Message.t) *)
(*                       (GET: Memory.get loc to' mem0 = Some (to, msg')), *)
(*           False) *)
(*       (RESERVE: msg <> Message.reserve) *)
(*   : *)
(*     versioned_memory (fun loc' ts' => if loc_ts_eq_dec (loc', ts') (loc, to) then opt_version_join (vers loc from) (Some v) else (vers loc' ts')) mem1. *)
(* Proof. *)
(*   hexploit add_succeed_wf; eauto. i. des. *)
(*   inv VERS. econs; eauto. *)
(*   { i. erewrite Memory.add_o in GET; eauto. des_ifs. *)
(*     { ss. des; clarify. exfalso. timetac. } *)
(*     { ss. des; clarify. destruct (vers loc from0); ss. *)
(*       { esplits; eauto. i. clarify. eapply version_join_l. } *)
(*       { esplits; eauto. ii. clarify. } *)
(*     } *)
(*     { ss. des; clarify. exfalso. eapply ATTACH; eauto. } *)
(*     { eapply COMPLETE; eauto. } *)
(*   } *)
(*   { i. des_ifs. *)
(*     { ss. des; clarify. esplits. *)
(*       { eapply Memory.add_get0; eauto. } *)
(*       { ss. } *)
(*     } *)
(*     { erewrite Memory.add_o; eauto. des_ifs. *)
(*       { ss. des; clarify. } *)
(*       eapply SOUND; eauto. *)
(*     } *)
(*   } *)
(* Qed. *)

(* Lemma versioned_memory_split vers mem0 loc ts0 ts1 ts2 msg2 msg3 mem1 v *)
(*       (SPLIT: Memory.split mem0 loc ts0 ts1 ts2 msg2 msg3 mem1) *)
(*       (VERS: versioned_memory vers mem0) *)
(*       (VER: forall val0 released0 (MSG: msg3 = Message.concrete val0 (Some released0)), *)
(*           opt_version_le (Some v) (vers loc ts2)) *)
(*       (RESERVE: msg2 <> Message.reserve) *)
(*   : *)
(*     versioned_memory (fun loc' ts' => if loc_ts_eq_dec (loc', ts') (loc, ts1) then opt_version_join (vers loc ts0) (Some v) else (vers loc' ts')) mem1. *)
(* Proof. *)
(*   hexploit split_succeed_wf; eauto. i. des. *)
(*   hexploit Memory.split_get0; eauto. i. des. clarify. *)
(*   inv VERS. econs; eauto. *)
(*   { i. erewrite Memory.split_o in GET4; eauto. des_ifs. *)
(*     { ss. des; clarify. exfalso. timetac. } *)
(*     { ss. des; clarify. destruct (vers loc from); ss. *)
(*       { esplits; eauto. i. clarify. eapply version_join_l. } *)
(*       { esplits; eauto. i. clarify. } *)
(*     } *)
(*     { ss. des; clarify. *)
(*       hexploit COMPLETE; eauto. i. des. *)
(*       hexploit VER; eauto. i. rewrite VER0 in *. esplits; eauto. *)
(*       i. destruct (vers loc ts0) eqn:VER2; ss; clarify. *)
(*       eapply version_join_spec; eauto. *)
(*     } *)
(*     { ss. des; clarify. exfalso. *)
(*       hexploit (@memory_get_from_inj mem1 loc ts1 ts2 to); eauto. *)
(*       { instantiate (1:=Message.concrete val (Some released)). *)
(*         erewrite Memory.split_o; eauto. des_ifs; ss; des; clarify. *)
(*       } *)
(*       { i. des; clarify. } *)
(*     } *)
(*     { ss. des; clarify. } *)
(*     { eapply COMPLETE; eauto. } *)
(*   } *)
(*   { i. des_ifs. *)
(*     { ss. des; clarify. esplits; eauto. } *)
(*     { guardH o. eapply SOUND in VER0. des. *)
(*       eapply Memory.split_get1 in GET4; eauto. des. esplits; eauto. *)
(*     } *)
(*   } *)
(* Qed. *)

(* Definition promise_finalized f (prom_src: Memory.t) (mem_tgt: Memory.t): Prop := *)
(*   forall loc to_src from_src msg_src *)
(*          (GETSRC: Memory.get loc to_src prom_src = Some (from_src, msg_src)) *)
(*          (MSGSRC: msg_src <> Message.reserve), *)
(*   exists to_tgt from_tgt msg_tgt, *)
(*     (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt>>) /\ *)
(*     (<<GETTGT: Memory.get loc to_tgt mem_tgt = Some (from_tgt, msg_tgt)>>) /\ *)
(*     (<<MSGTGT: msg_tgt <> Message.reserve>>) *)
(* . *)

(* Lemma promise_finalized_mon_strong f0 f1 prom_src mem_tgt *)
(*       (FINALIZED: promise_finalized f0 prom_src mem_tgt) *)
(*       (MAPLE: Mapping.les_strong f0 f1) *)
(*       (MAPWF: Mapping.wfs f0) *)
(*   : *)
(*   promise_finalized f1 prom_src mem_tgt. *)
(* Proof. *)
(*   ii. exploit FINALIZED; eauto. i. des. esplits; eauto. *)
(*   eapply sim_timestamp_exact_mon_strong; eauto. *)
(* Qed. *)

(* Lemma promise_finalized_future f prom_src mem_tgt0 mem_tgt1 *)
(*       (FINALIZED: promise_finalized f prom_src mem_tgt0) *)
(*       (FUTURE: Memory.future_weak mem_tgt0 mem_tgt1) *)
(*   : *)
(*   promise_finalized f prom_src mem_tgt1. *)
(* Proof. *)
(*   ii. exploit FINALIZED; eauto. i. des. *)
(*   hexploit Memory.future_weak_get1; eauto. i. des. *)
(*   esplits; eauto. inv MSG_LE; ss. *)
(* Qed. *)

(* Lemma promise_finalized_promise_decr f prom_src0 prom_src1 mem_tgt *)
(*       (FINALIZED: promise_finalized f prom_src0 mem_tgt) *)
(*       (DECR: forall loc to_src from_src msg_src *)
(*                     (GETSRC: Memory.get loc to_src prom_src1 = Some (from_src, msg_src)) *)
(*                     (MSGSRC: msg_src <> Message.reserve), *)
(*           (exists ffrom_src0 msg_src0, *)
(*               (<<GETSRC: Memory.get loc to_src prom_src0 = Some (ffrom_src0, msg_src0)>>) /\ *)
(*               (<<MSGSRC: msg_src0 <> Message.reserve>>)) \/ *)
(*           (exists to_tgt from_tgt msg_tgt, *)
(*               (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt>>) /\ *)
(*               (<<GETTGT: Memory.get loc to_tgt mem_tgt = Some (from_tgt, msg_tgt)>>) /\ *)
(*               (<<MSGTGT: msg_tgt <> Message.reserve>>))) *)
(*   : *)
(*   promise_finalized f prom_src1 mem_tgt. *)
(* Proof. *)
(*   ii. exploit DECR; eauto. i. des. *)
(*   { eapply FINALIZED; eauto. } *)
(*   { esplits; eauto. } *)
(* Qed. *)

Lemma loc_version_wf_mapping_mon f0 f1 ver
      (WF: loc_version_wf f0 ver)
      (LE: Mapping.le f0 f1)
  :
    loc_version_wf f1 ver.
Proof.
  unfold loc_version_wf in *. etrans; eauto. eapply LE.
Qed.

Lemma version_wf_mapping_mon f0 f1 ver
      (WF: version_wf f0 ver)
      (LE: Mapping.les f0 f1)
  :
    version_wf f1 ver.
Proof.
  ii. eapply loc_version_wf_mapping_mon; eauto.
Qed.

Lemma opt_version_wf_mapping_mon f0 f1 ver
      (WF: opt_version_wf f0 ver)
      (LE: Mapping.les f0 f1)
  :
    opt_version_wf f1 ver.
Proof.
  destruct ver; ss. eapply version_wf_mapping_mon; eauto.
Qed.

Lemma versions_wf_mapping_mon f0 f1 vers
      (WF: versions_wf f0 vers)
      (LE: Mapping.les f0 f1)
  :
    versions_wf f1 vers.
Proof.
  ii. eapply opt_version_wf_mapping_mon; eauto.
Qed.

Lemma sim_timemap_mon_latest L f0 f1 tm_src tm_tgt
      (SIM: sim_timemap L f0 (Mapping.vers f0) tm_src tm_tgt)
      (LE: Mapping.les f0 f1)
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wfs f1)
  :
    sim_timemap L f1 (Mapping.vers f1) tm_src tm_tgt.
Proof.
  eapply sim_timemap_mon_ver; auto.
  { erewrite <- sim_timemap_mon_mapping; eauto. eapply mapping_latest_wf. }
  { eapply version_le_version_wf.
    eapply version_wf_mapping_mon; eauto. eapply mapping_latest_wf.
  }
  { eapply mapping_latest_wf. }
Qed.

Lemma sim_view_mon_latest L f0 f1 vw_src vw_tgt
      (SIM: sim_view L f0 (Mapping.vers f0) vw_src vw_tgt)
      (LE: Mapping.les f0 f1)
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wfs f1)
  :
    sim_view L f1 (Mapping.vers f1) vw_src vw_tgt.
Proof.
  econs.
  { eapply sim_timemap_mon_latest; eauto. eapply SIM. }
  { eapply sim_timemap_mon_latest; eauto. eapply SIM. }
Qed.

(* Lemma sim_closed_mon_latest f0 f1 ts *)
(*       (CLOSED: Mapping.closed f0 f0.(Mapping.ver) ts) *)
(*       (LE: Mapping.le f0 f1) *)
(*       (WF0: Mapping.wf f0) *)
(*       (WF1: Mapping.wf f1) *)
(*   : *)
(*     Mapping.closed f1 f1.(Mapping.ver) ts. *)
(* Proof. *)
(*   eapply sim_closed_mon_ver. *)
(*   { erewrite <- sim_closed_mon_mapping; [..|eauto]; eauto. *)
(*     eapply mapping_latest_wf_loc. *)
(*   } *)
(*   { eapply LE. } *)
(*   { eauto. } *)
(*   { eapply mapping_latest_wf_loc. } *)
(* Qed. *)

Lemma sim_memory_mon_strong flag gown f0 f1 mem_src mem_tgt
      (SIM: sim_memory flag gown f0 mem_src mem_tgt)
      (LE: Mapping.les_strong f0 f1)
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wfs f1)
  :
    sim_memory flag gown f1 mem_src mem_tgt.
Proof.
  econs.
  { ii. hexploit sim_memory_get; eauto. i. des.
    { left. esplits; eauto.
      { eapply sim_timestamp_exact_mon_strong; eauto. }
      { eapply sim_message_mon_mapping_latest; eauto.
        eapply Mapping.les_strong_les; eauto.
      }
    }
    { right. esplits; eauto.
      eapply sim_timestamp_exact_mon_strong; eauto.
    }
  }
  { i. hexploit sim_memory_sound; eauto. i. des.
    { left. esplits; eauto.
      { unguard. des; clarify; auto. right. eapply sim_timestamp_exact_mon_strong; eauto. }
      { eapply sim_timestamp_exact_mon_strong; eauto. }
    }
    { right. esplits; eauto. eapply top_time_mon_strong_map; eauto. }
  }
Qed.

Lemma cap_sim_memory flag gown f0 mem_tgt0 mem_tgt1 mem_src0 mem_src1
      (MEM: sim_memory flag gown f0 mem_src0 mem_tgt0)
      (WF: Mapping.wfs f0)
      (CAPTGT: Memory.cap mem_tgt0 mem_tgt1)
      (CAPSRC: Memory.cap mem_src0 mem_src1)
      (CLOSEDTGT: Memory.closed mem_tgt0)
      (CLOSEDSRC: Memory.closed mem_src0)
  :
    exists f1,
      (<<SIM: sim_memory flag gown f1 mem_src1 mem_tgt1>>) /\
      (<<MAPWF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<PRESERVE: forall loc to from msg
                          (GET: Memory.get loc to mem_tgt0 = Some (from, msg))
                          ts fts
                          (TS: Time.le ts to)
                          (MAP: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) fts (Some ts)),
          sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) fts (Some ts)>>)
.
Proof.
  hexploit (choice (fun loc f =>
                      (<<MAPWF: Mapping.wf f>>) /\
                      (<<MAPLE: Mapping.le (f0 loc) f>>) /\
                      (<<PRESERVE: forall to from msg
                                          (GET: Memory.get loc to mem_tgt0 = Some (from, msg))
                                          ts fts
                                          (TS: Time.le ts to)
                                          (MAP: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) fts (Some ts)),
                          sim_timestamp_exact f f.(Mapping.ver) fts (Some ts)>>) /\
                      exists fcap,
                        (<<SIM: sim_timestamp_exact f f.(Mapping.ver) fcap (Some (Time.incr (Memory.max_ts loc mem_tgt0)))>>) /\
                        (<<TS: Time.le (Time.incr (Memory.max_ts loc mem_src0)) fcap>>))).
  { intros loc. hexploit top_time_exists; eauto. i. des.
    hexploit shifted_mapping_exists; eauto. i. des. esplits; eauto.
    { i. eapply SAME; eauto. eapply Memory.max_ts_spec in GET. des.
      eapply TimeFacts.le_lt_lt; eauto.
      eapply TimeFacts.le_lt_lt; eauto.
      eapply Time.incr_spec.
    }
    { left. eauto. }
  }
  i. des. exists f.
  assert ((<<MAPWF: Mapping.wfs f>>) /\
          (<<MAPLE: Mapping.les f0 f>>) /\
          (<<PRESERVE: forall loc to from msg
                              (GET: Memory.get loc to mem_tgt0 = Some (from, msg))
                              ts fts
                              (TS: Time.le ts to)
                              (MAP: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) fts (Some ts)),
              sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fts (Some ts)>>)).
  { splits.
    { ii. specialize (H loc). des; auto. }
    { ii. specialize (H loc). des; auto. }
    { i. hexploit (H loc). i. des; auto. eapply PRESERVE; eauto. }
  }
  des. splits; auto.
  econs.
  { i. eapply Memory.cap_inv in GET; [..|eauto]; eauto. des; ss.
    hexploit sim_memory_get; eauto. i. des.
    { left. esplits.
      { eapply PRESERVE; eauto. refl. }
      { eapply Memory.cap_le; eauto. }
      { eapply sim_message_mon_mapping_latest; eauto. }
    }
    { right. esplits.
      { eapply PRESERVE; eauto. refl. }
      { eauto. }
      { eapply Memory.cap_le; eauto. }
    }
  }
  { i. left. hexploit (H loc). i. des.
    exists fcap, Time.bot, (Time.incr (Memory.max_ts loc mem_tgt0)), Time.bot.
    splits; auto.
    { eapply Time.bot_spec. }
    { etrans; eauto. eapply Memory.max_ts_spec in GET. des.
      erewrite <- Memory.cap_max_ts; eauto. eapply CLOSEDSRC.
    }
    { left. auto. }
    { i. eapply memory_cap_covered; eauto. }
  }
Qed.

(* Lemma added_memory_sim_memory srctm f0 f1 flag_src vers mem_tgt mem_src0 mem_src1 loc *)
(*       ts_tgt from msg msgs from_new msg_new *)
(*       (MEM: sim_memory srctm flag_src f0 vers mem_src0 mem_tgt) *)
(*       (SIMCLOSED: sim_closed_memory f0 mem_src0) *)
(*       (WF: Mapping.wfs f0) *)
(*       (VERS: versions_wf f0 vers) *)
(*       (ADDED: added_memory loc msgs mem_src0 mem_src1) *)
(*       (FLAG: flag_src loc = true) *)
(*       (TS: Memory.get loc (srctm loc) mem_src0 = Some (from_new, msg_new)) *)
(*       (MSGNEW: sim_message false loc f0 (vers loc ts_tgt) msg_new msg) *)
(*       (GETTGT: Memory.get loc ts_tgt mem_tgt = Some (from, msg)) *)
(*       (RESERVE: msg <> Message.reserve) *)
(*       (MSGCOMPLETE: forall to_tgt from_tgt msg_tgt *)
(*                            (RESERVE: msg_tgt <> Message.reserve) *)
(*                            (GETTGT: Memory.get loc to_tgt mem_tgt = Some (from_tgt, msg_tgt)) *)
(*                            (TS: Time.lt ts_tgt to_tgt), *)
(*           exists to_src from_src msg_src, *)
(*             (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\ *)
(*             (<<MSG: sim_message false loc f0 (vers loc to_tgt) msg_src msg_tgt>>) /\ *)
(*             (<<CLOSED: forall val released (MSG: msg_tgt = Message.concrete val released), Mapping.closed f1 f1.(Mapping.ver) to_src>>) /\ *)
(*             (<<IN: List.In (from_src, to_src, msg_src) msgs>>)) *)
(*       (MSGSOUND: forall to_src from_src msg_src *)
(*                         (IN: List.In (from_src, to_src, msg_src) msgs), *)
(*           exists to_tgt from_tgt msg_tgt, *)
(*             (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\ *)
(*             (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\ *)
(*             (<<GET: Memory.get loc to_tgt mem_tgt = Some (from_tgt, msg_tgt)>>)) *)
(*       (MAPWF: Mapping.wf f1) *)
(*       (MAPLE: Mapping.le (f0 loc) f1) *)
(*       (SHIFTSAME: forall to fto *)
(*                          (TS: Time.lt to ts_tgt) *)
(*                          (MAP: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) fto to), *)
(*           sim_timestamp_exact f1 f1.(Mapping.ver) fto to) *)
(*       (SHIFTTS: sim_timestamp_exact f1 f1.(Mapping.ver) (srctm loc) ts_tgt) *)
(*       (CLOSEDTS: Mapping.closed f1 f1.(Mapping.ver) (srctm loc)) *)
(*       (CLOSEDIF: forall ts (CLOSED: Mapping.closed f1 f1.(Mapping.ver) ts), *)
(*           (<<CLOSED: Mapping.closed (f0 loc) (f0 loc).(Mapping.ver) ts>>) \/ *)
(*           (exists from val released, (<<IN: List.In (from, ts, Message.concrete val released) msgs>>)) \/ *)
(*           (exists val released, (<<MSG: msg_new = Message.concrete val released>>) /\ (<<TS: ts = srctm loc>>)) \/ *)
(*           (exists from val released, Memory.get loc ts mem_src0 = Some (from, Message.concrete val released))) *)
(*   : *)
(*   let f' := (fun loc' => if Loc.eq_dec loc' loc then f1 else f0 loc') in *)
(*   (<<SIM: sim_memory *)
(*             srctm *)
(*             (fun loc' => if Loc.eq_dec loc' loc then false else flag_src loc') *)
(*             f' *)
(*             vers mem_src1 mem_tgt>>) /\ *)
(*   (<<FUTURE: map_future_memory f0 f' mem_src1>>) /\ *)
(*   (<<SIMCLOSED: sim_closed_memory f' mem_src1>>) *)
(* . *)
(* Proof. *)
(*   pose proof (mapping_latest_wf_loc (f0 loc)) as VERWF. *)
(*   assert (MAPSLE: Mapping.les f0 (fun loc' => if Loc.eq_dec loc' loc then f1 else f0 loc')). *)
(*   { ii. des_ifs. refl. } *)
(*   assert (MAPSWF: Mapping.wfs (fun loc' => if Loc.eq_dec loc' loc then f1 else f0 loc')). *)
(*   { ii. des_ifs. } *)
(*   hexploit sim_memory_get; eauto. i. des. *)
(*   assert (exists from_src from_tgt, *)
(*              (__guard__((<<BOT: (from_src = Time.bot /\ from_tgt = Time.bot)>>) \/ ((<<TS: Time.lt from_tgt ts_tgt>>) /\ (<<MAP0: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) from_src from_tgt>>) /\ (<<MAP1: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>))) /\ *)
(*               (<<COVERED: forall ts (ITV: Interval.mem (from_tgt, ts_tgt) ts), covered loc ts mem_tgt>>))). *)
(*   { hexploit memory_get_ts_strong. *)
(*     { eapply GETTGT. } *)
(*     i. des. *)
(*     { clarify. esplits. *)
(*       { left. eauto. } *)
(*       { i. econs; eauto. } *)
(*     } *)
(*     hexploit sim_memory_sound_strong; eauto. i. des. *)
(*     { unguard. des; clarify. *)
(*       { esplits; eauto. i. apply COVERED. eapply Interval.le_mem; eauto. *)
(*         econs; ss; [refl|]. eapply sim_timestamp_exact_le_if; eauto. *)
(*       } *)
(*       { assert (LT: Time.lt from0 ts_tgt). *)
(*         { eapply sim_timestamp_exact_lt_if; eauto. *)
(*           eapply TimeFacts.le_lt_lt; eauto. *)
(*           eapply memory_get_ts_strong in GET; eauto. des; clarify. *)
(*           exfalso. hexploit sim_timestamp_exact_bot_if; [..|eapply TO|]; eauto. *)
(*         } *)
(*         exists ffrom0, from0. splits; auto. *)
(*         i. eapply COVERED. eapply Interval.le_mem; eauto. *)
(*         econs; ss; [refl|]. eapply sim_timestamp_exact_le_if; eauto. *)
(*       } *)
(*     } *)
(*     { exfalso. eapply TOP in TO. *)
(*       apply memory_get_ts_le in GET. timetac. *)
(*     } *)
(*   } *)
(*   inv ADDED. subst f'. splits. *)
(*   { econs. *)
(*     { i. destruct (Loc.eq_dec loc0 loc); clarify; cycle 1. *)
(*       { hexploit sim_memory_get; eauto. i. des. *)
(*         esplits; eauto. erewrite <- sim_message_mon_mapping; eauto. *)
(*       } *)
(*       destruct (Time.le_lt_dec to ts_tgt) as [[LT|EQ]|LT]. *)
(*       { hexploit sim_memory_get; eauto. i. des. esplits. *)
(*         { eapply SHIFTSAME; eauto. } *)
(*         { eapply MLE; eauto. } *)
(*         { erewrite <- sim_message_mon_mapping; eauto. } *)
(*         { i. eapply sim_closed_mon_latest; eauto. } *)
(*       } *)
(*       { inv EQ. clarify. esplits; eauto. *)
(*         erewrite <- sim_message_mon_mapping; eauto. *)
(*       } *)
(*       { hexploit MSGCOMPLETE; eauto. i. des. esplits; eauto. *)
(*         { erewrite <- sim_message_mon_mapping; eauto. } *)
(*         { i. subst. inv MSG0; eauto. } *)
(*       } *)
(*     } *)
(*     { i. destruct (Loc.eq_dec loc0 loc); clarify; cycle 1. *)
(*       { rewrite OTHER in GET0; auto. hexploit sim_memory_sound; eauto. } *)
(*       left. eapply SOUND in GET0. des. *)
(*       { hexploit sim_memory_sound_strong; eauto. i. des. *)
(*         { destruct (Time.le_lt_dec ts_tgt to). *)
(*           { inv l. *)
(*             { exists (srctm loc), from_src0, ts_tgt, from_tgt. splits; auto. *)
(*               { inv H; des; clarify. *)
(*                 { eapply Time.bot_spec. } *)
(*                 { hexploit memory_get_from_mon. *)
(*                   { eapply GET. } *)
(*                   { eapply GET1. } *)
(*                   { destruct (Time.le_lt_dec fto0 to_src); auto. *)
(*                     eapply MIN in l; eauto. *)
(*                     eapply sim_timestamp_exact_le_if in l; eauto. *)
(*                     exfalso. timetac. *)
(*                   } *)
(*                   i. etrans; eauto. left. *)
(*                   eapply sim_timestamp_exact_lt;[eapply MAP0|..]; eauto. *)
(*                 } *)
(*               } *)
(*               { etrans; eauto. left. hexploit sim_memory_top; eauto. } *)
(*               { inv H; des; clarify. *)
(*                 { left. auto. } *)
(*                 { right. auto. } *)
(*               } *)
(*             } *)
(*             { inv H0. eapply sim_timestamp_exact_inject in TO; eauto. clarify. *)
(*               hexploit memory_get_ts_strong. *)
(*               { eapply GET1. } *)
(*               i. des; clarify. *)
(*               { assert (ffrom0 = Time.bot). *)
(*                 { eapply TimeFacts.antisym; ss. eapply Time.bot_spec. } *)
(*                 subst. eexists _, Time.bot, to, Time.bot. splits; auto. *)
(*                 { eapply Time.bot_spec. } *)
(*                 { left. auto. } *)
(*                 { eauto. } *)
(*                 { i. eapply COVERED0; eauto. eapply Interval.le_mem; eauto. *)
(*                   econs; ss; [|refl]. inv FROM; des; clarify. *)
(*                   eapply sim_timestamp_exact_bot_if in H0; eauto. *)
(*                   subst. refl. *)
(*                 } *)
(*               } *)
(*               esplits; [eauto| | |eauto|..]; eauto. *)
(*               { etrans; eauto. left. eapply sim_memory_top; eauto. } *)
(*               { inv FROM; des; clarify. *)
(*                 { left. auto. } *)
(*                 { right. eapply SHIFTSAME; eauto. *)
(*                   eapply sim_timestamp_exact_lt_if; eauto. *)
(*                   eapply TimeFacts.le_lt_lt. *)
(*                   { eauto. } *)
(*                   eapply TimeFacts.lt_le_lt; eauto. *)
(*                 } *)
(*               } *)
(*             } *)
(*           } *)
(*           { esplits; eauto. inv FROM. *)
(*             { left. auto. } *)
(*             { right. eapply SHIFTSAME; eauto. *)
(*               eapply sim_timestamp_exact_lt_if; eauto. *)
(*               eapply TimeFacts.le_lt_lt; eauto. *)
(*               eapply TimeFacts.le_lt_lt. *)
(*               { eapply memory_get_ts_le. eapply GET1. } *)
(*               eapply TimeFacts.le_lt_lt. *)
(*               { eauto. } *)
(*               eapply sim_timestamp_exact_lt; eauto. *)
(*             } *)
(*           } *)
(*         } *)
(*         { clarify. exists (srctm loc), from_src0, ts_tgt, from_tgt. splits; auto. *)
(*           { inv H; des; clarify. *)
(*             { eapply Time.bot_spec. } *)
(*             { left. eapply TOP; eauto. } *)
(*           } *)
(*           { inv H; des. *)
(*             { left. auto. } *)
(*             { right. auto. } *)
(*           } *)
(*         } *)
(*       } *)
(*       { hexploit MSGSOUND; eauto. i. des. esplits. *)
(*         { refl. } *)
(*         { refl. } *)
(*         { right. eauto. } *)
(*         { eauto. } *)
(*         { i. econs; eauto. } *)
(*       } *)
(*     } *)
(*     { i. des_ifs. eapply sim_memory_top; eauto. } *)
(*     { i. des_ifs. hexploit sim_memory_undef; eauto. i. des. *)
(*       esplits; eauto. *)
(*     } *)
(*   } *)
(*   { econs. *)
(*     { ii. des_ifs. hexploit sim_memory_undef; eauto. i. des. *)
(*       eapply MLE in GET0. esplits; eauto. *)
(*       { eapply TOP in MAP0. eapply memory_get_ts_le in GET0. *)
(*         etrans; eauto. left. auto. *)
(*       } *)
(*       { eapply top_time_mon; eauto. eapply memory_get_ts_le; eauto. } *)
(*     } *)
(*     { ii. des_ifs. } *)
(*   } *)
(*   { ii. des_ifs. *)
(*     { eapply CLOSEDIF in CLOSED0. des. *)
(*       { eapply SIMCLOSED in CLOSED1. des. esplits. eapply MLE; eauto. } *)
(*       { eapply COMPLETE in IN. eauto. } *)
(*       { subst. esplits. eapply MLE. eauto. } *)
(*       { esplits. eapply MLE. eauto. } *)
(*     } *)
(*     { eapply SIMCLOSED in CLOSED0. des. esplits. eapply MLE; eauto. } *)
(*   } *)
(* Qed. *)

(* Lemma added_memory_sim_promise_match *)
(*       f0 f1 srctm flag_src flag_tgt vers prom_tgt prom_src0 prom_src1 loc *)
(*       msgs *)
(*       (MEM: sim_reserves srctm flag_src flag_tgt f0 vers prom_src0 prom_tgt) *)
(*       (WF: Mapping.wfs f0) *)
(*       (VERS: versions_wf f0 vers) *)
(*       (ADDED: added_memory loc msgs prom_src0 prom_src1) *)
(*       (FLAG: flag_src loc = true) *)
(*       (MSGCOMPLETE: forall to_tgt from_tgt msg_tgt *)
(*                            (GETTGT: Memory.get loc to_tgt prom_tgt = Some (from_tgt, msg_tgt)), *)
(*           exists to_src from_src msg_src, *)
(*             (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\ *)
(*             (<<MSG: sim_message_max false loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>) /\ *)
(*             (<<CLOSED: forall val released (MSG: msg_tgt = Message.concrete val released), Mapping.closed f1 f1.(Mapping.ver) to_src>>) /\ *)
(*             (<<IN: List.In (from_src, to_src, msg_src) msgs>>)) *)
(*       (MSGSOUND: forall to_src from_src msg_src *)
(*                         (IN: List.In (from_src, to_src, msg_src) msgs), *)
(*           exists to_tgt from_tgt msg_tgt, *)
(*             (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\ *)
(*             (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\ *)
(*             (<<GET: Memory.get loc to_tgt prom_tgt = Some (from_tgt, msg_tgt)>>)) *)
(*       (MAPWF: Mapping.wf f1) *)
(*       (MAPLE: Mapping.le (f0 loc) f1) *)
(*   : *)
(*   let f' := (fun loc' => if Loc.eq_dec loc' loc then f1 else f0 loc') in *)
(*   (<<SIM: sim_reserves *)
(*             srctm *)
(*             (fun loc' => if Loc.eq_dec loc' loc then false else flag_src loc') *)
(*             (fun loc' => if Loc.eq_dec loc' loc then false else flag_tgt loc') *)
(*             f' *)
(*             vers prom_src1 prom_tgt>>) *)
(* . *)
(* Proof. *)
(*   pose proof (mapping_latest_wf_loc (f0 loc)) as VERWF. *)
(*   assert (MAPSLE: Mapping.les f0 (fun loc' => if Loc.eq_dec loc' loc then f1 else f0 loc')). *)
(*   { ii. des_ifs. refl. } *)
(*   assert (MAPSWF: Mapping.wfs (fun loc' => if Loc.eq_dec loc' loc then f1 else f0 loc')). *)
(*   { ii. des_ifs. } *)
(*   ii. inv ADDED. econs. *)
(*   { i. des_ifs. *)
(*     { replace (f' loc) with f1. *)
(*       2:{ unfold f'. des_ifs. } *)
(*       hexploit MSGCOMPLETE; eauto. i. des. *)
(*       hexploit MSGSOUND; eauto. i. des. *)
(*       eapply sim_timestamp_exact_unique in TO; eauto; ss. clarify. *)
(*       esplits; eauto. *)
(*       { i. inv MSG; ss; eauto. } *)
(*       i. esplits; eauto. *)
(*       erewrite <- sim_message_max_mon_mapping; eauto. *)
(*     } *)
(*     { hexploit sim_reserves_get; eauto. i. des. *)
(*       replace (f' loc0) with (f0 loc0). *)
(*       { esplits; eauto. i. hexploit GET0; eauto. i. des. esplits; eauto. *)
(*         erewrite <- sim_message_max_mon_mapping; eauto. *)
(*       } *)
(*       { unfold f'. des_ifs. } *)
(*     } *)
(*   } *)
(*   { i. des_ifs. *)
(*     { left. replace (f' loc) with f1. *)
(*       2:{ unfold f'. des_ifs. } *)
(*       hexploit SOUND; eauto. i. des. *)
(*       { exfalso. hexploit sim_reserves_none; eauto. rewrite GET0. ss. } *)
(*       { hexploit MSGSOUND; eauto. i. des. esplits; eauto. } *)
(*     } *)
(*     { replace (f' loc0) with (f0 loc0). *)
(*       2:{ unfold f'. des_ifs. } *)
(*       rewrite OTHER in GET; eauto. *)
(*       hexploit sim_reserves_get_if; eauto. i. des. *)
(*       { left. esplits; eauto. } *)
(*       { right. esplits; eauto. } *)
(*     } *)
(*   } *)
(*   { i. des_ifs. rewrite OTHER; auto. eapply sim_reserves_none; eauto. } *)
(* Qed. *)

(* Lemma added_memory_sim_promise_unmatch *)
(*       f0 f1 srctm flag_src flag_tgt vers prom_tgt prom_src0 prom_src1 loc *)
(*       msgs *)
(*       (MEM: sim_reserves srctm flag_src flag_tgt f0 vers prom_src0 prom_tgt) *)
(*       (WF: Mapping.wfs f0) *)
(*       (VERS: versions_wf f0 vers) *)
(*       (ADDED: added_memory loc msgs prom_src0 prom_src1) *)
(*       (FLAG: flag_src loc = true) *)
(*       (MSGCOMPLETE: forall to_tgt from_tgt msg_tgt *)
(*                            (GETTGT: Memory.get loc to_tgt prom_tgt = Some (from_tgt, msg_tgt)), *)
(*           exists to_src from_src msg_src, *)
(*             (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\ *)
(*             (<<MSG: sim_message_max true loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>) /\ *)
(*             (<<CLOSED: forall val released (MSG: msg_tgt = Message.concrete val released), Mapping.closed f1 f1.(Mapping.ver) to_src>>) /\ *)
(*             (<<IN: List.In (from_src, to_src, msg_src) msgs>>)) *)
(*       (MSGSOUND: forall to_src from_src msg_src *)
(*                         (IN: List.In (from_src, to_src, msg_src) msgs), *)
(*           (exists to_tgt, *)
(*               (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\ *)
(*               ((exists from_tgt msg_tgt, *)
(*                    (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\ *)
(*                    (<<GET: Memory.get loc to_tgt prom_tgt = Some (from_tgt, msg_tgt)>>)) \/ *)
(*                ((<<TS: Time.lt (srctm loc) to_src>>) /\ (<<RESERVE: msg_src <> Message.reserve>>) /\ (<<NONE: forall val released (MSG: msg_src = Message.concrete val (Some released)), False>>) /\ (<<GET: Memory.get loc to_tgt prom_tgt = None>>))))) *)
(*       (MAPWF: Mapping.wf f1) *)
(*       (MAPLE: Mapping.le (f0 loc) f1) *)
(*   : *)
(*   let f' := (fun loc' => if Loc.eq_dec loc' loc then f1 else f0 loc') in *)
(*   (<<SIM: sim_reserves *)
(*             srctm *)
(*             (fun loc' => if Loc.eq_dec loc' loc then false else flag_src loc') *)
(*             (fun loc' => if Loc.eq_dec loc' loc then true else flag_tgt loc') *)
(*             f' *)
(*             vers prom_src1 prom_tgt>>) *)
(* . *)
(* Proof. *)
(*   pose proof (mapping_latest_wf_loc (f0 loc)) as VERWF. *)
(*   assert (MAPSLE: Mapping.les f0 (fun loc' => if Loc.eq_dec loc' loc then f1 else f0 loc')). *)
(*   { ii. des_ifs. refl. } *)
(*   assert (MAPSWF: Mapping.wfs (fun loc' => if Loc.eq_dec loc' loc then f1 else f0 loc')). *)
(*   { ii. des_ifs. } *)
(*   ii. inv ADDED. econs. *)
(*   { i. des_ifs. *)
(*     { replace (f' loc) with f1. *)
(*       2:{ unfold f'. des_ifs. } *)
(*       hexploit MSGCOMPLETE; eauto. i. des. *)
(*       hexploit MSGSOUND; eauto. i. des. *)
(*       { eapply sim_timestamp_exact_unique in TO; eauto; ss. clarify. *)
(*         esplits; eauto. *)
(*         { i. inv MSG; ss; eauto. } *)
(*         i. esplits; eauto. *)
(*         erewrite <- sim_message_max_mon_mapping; eauto. *)
(*       } *)
(*       { eapply sim_timestamp_exact_unique in TO; eauto; ss. clarify. } *)
(*     } *)
(*     { hexploit sim_reserves_get; eauto. i. des. *)
(*       replace (f' loc0) with (f0 loc0). *)
(*       { esplits; eauto. i. hexploit GET0; eauto. i. des. esplits; eauto. *)
(*         erewrite <- sim_message_max_mon_mapping; eauto. *)
(*       } *)
(*       { unfold f'. des_ifs. } *)
(*     } *)
(*   } *)
(*   { i. des_ifs. *)
(*     { replace (f' loc) with f1. *)
(*       2:{ unfold f'. des_ifs. } *)
(*       hexploit SOUND; eauto. i. des. *)
(*       { exfalso. hexploit sim_reserves_none; eauto. rewrite GET0. ss. } *)
(*       { hexploit MSGSOUND; eauto. i. des. *)
(*         { left. esplits; eauto. } *)
(*         { right. esplits; eauto. } *)
(*       } *)
(*     } *)
(*     { replace (f' loc0) with (f0 loc0). *)
(*       2:{ unfold f'. des_ifs. } *)
(*       rewrite OTHER in GET; eauto. *)
(*       hexploit sim_reserves_get_if; eauto. i. des. *)
(*       { left. esplits; eauto. } *)
(*       { right. esplits; eauto. } *)
(*     } *)
(*   } *)
(*   { i. des_ifs. rewrite OTHER; auto. eapply sim_reserves_none; eauto. } *)
(* Qed. *)

(* Lemma lower_lower_memory mem0 mem1 loc from to msg0 msg1 *)
(*       (LOWER: Memory.lower mem0 loc from to msg0 msg1 mem1) *)
(*   : *)
(*     lower_memory mem1 mem0. *)
(* Proof. *)
(*   econs. ii. erewrite (@Memory.lower_o mem1); eauto. des_ifs. *)
(*   { ss. des; clarify. eapply lower_succeed_wf in LOWER. des. *)
(*     rewrite GET. econs; eauto. *)
(*   } *)
(*   { refl. } *)
(* Qed. *)

(* Variant lower_none_content: option (Time.t * Message.t) -> option (Time.t * Message.t) -> Prop := *)
(* | lower_none_content_none *)
(*   : *)
(*     lower_none_content None None *)
(* | lower_none_content_reserve *)
(*     from *)
(*   : *)
(*     lower_none_content (Some (from, Message.reserve)) (Some (from, Message.reserve)) *)
(* | lower_none_content_undef *)
(*     from *)
(*   : *)
(*     lower_none_content (Some (from, Message.undef)) (Some (from, Message.undef)) *)
(* | lower_none_content_concrete *)
(*     from val released *)
(*   : *)
(*     lower_none_content (Some (from, Message.concrete val None)) (Some (from, Message.concrete val released)) *)
(* . *)

(* Variant lower_none_list mem0 mem1 loc (tos: list Time.t): Prop := *)
(* | lower_list_mem_intro *)
(*     (OTHERLOC: forall loc0 ts (NEQ: loc0 <> loc), *)
(*         Memory.get loc0 ts mem1 = Memory.get loc0 ts mem0) *)
(*     (OTHERTS: forall ts (NIN: ~ List.In ts tos), *)
(*         Memory.get loc ts mem1 = Memory.get loc ts mem0) *)
(*     (SAMETS: forall ts (IN: List.In ts tos), *)
(*         lower_none_content (Memory.get loc ts mem1) (Memory.get loc ts mem0)) *)
(* . *)

(* Lemma memory_lower_o2 mem1 mem2 loc from to msg1 msg2 l t *)
(*       (LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2) *)
(*   : *)
(*     Memory.get l t mem1 = *)
(*     (if loc_ts_eq_dec (l, t) (loc, to) *)
(*      then Some (from, msg1) *)
(*      else Memory.get l t mem2). *)
(* Proof. *)
(*   erewrite (@Memory.lower_o mem2 mem1); eauto. des_ifs. *)
(*   ss. des; clarify. eapply Memory.lower_get0 in LOWER. des; auto. *)
(* Qed. *)

(* Lemma memory_lower_max_ts mem0 loc from to msg0 msg1 mem1 *)
(*       (LOWER: Memory.lower mem0 loc from to msg0 msg1 mem1) *)
(*       (INHABITED: Memory.inhabited mem0) *)
(*   : *)
(*     forall loc0, Memory.max_ts loc0 mem1 = Memory.max_ts loc0 mem0. *)
(* Proof. *)
(*   i. specialize (INHABITED loc0). *)
(*   eapply Memory.max_ts_spec in INHABITED. des. *)
(*   hexploit Memory.lower_get1; eauto. i. des. *)
(*   eapply Memory.max_ts_spec in GET2. des. *)
(*   eapply TimeFacts.antisym; eauto. *)
(*   erewrite Memory.lower_o in GET0; eauto. des_ifs. *)
(*   { ss. des; clarify. *)
(*     eapply Memory.lower_get0 in LOWER. des. *)
(*     eapply Memory.max_ts_spec in GET0. des; eauto. *)
(*   } *)
(*   { eapply Memory.max_ts_spec in GET0. des; eauto. } *)
(* Qed. *)

(* Lemma tgt_flag_up_sim_reserves srctm flag_src flag_tgt f vers prom_src0 prom_tgt mem_src0 mem_tgt loc *)
(*       (MEM: sim_memory srctm flag_src f vers mem_src0 mem_tgt) *)
(*       (PROMS: sim_reserves srctm flag_src flag_tgt f vers prom_src0 prom_tgt) *)
(*       (TS: forall from to msg *)
(*                   (GET: Memory.get loc to prom_src0 = Some (from, msg)) *)
(*                   (MSG: msg <> Message.reserve), Time.lt (srctm loc) to) *)
(*       (MLE: Memory.le prom_src0 mem_src0) *)
(*       (INHABITED: Memory.inhabited mem_src0) *)
(*   : *)
(*     forall tvw lang st sc, *)
(*     exists prom_src1 mem_src1, *)
(*       (<<STEPS: rtc (@Thread.tau_step _) *)
(*                     (Thread.mk lang st (Local.mk tvw prom_src0) sc mem_src0) *)
(*                     (Thread.mk _ st (Local.mk tvw prom_src1) sc mem_src1)>>) /\ *)
(*       (<<PROMS: sim_reserves srctm flag_src (fun loc' => if (Loc.eq_dec loc' loc) then true else flag_tgt loc') f vers prom_src1 prom_tgt>>) /\ *)
(*       (<<NONE: forall to from val released (GET: Memory.get loc to prom_src1 = Some (from, Message.concrete val released)), *)
(*           released = None>>) /\ *)
(*       (<<MEM: sim_memory srctm flag_src f vers mem_src1 mem_tgt>>) /\ *)
(*       (<<VALS: forall loc0 to val released, *)
(*           max_readable mem_src0 prom_src0 loc0 to val released *)
(*           <-> *)
(*             max_readable mem_src1 prom_src1 loc0 to val released>>) /\ *)
(*       (<<COVERED: forall loc ts, covered loc ts mem_src1 <-> covered loc ts mem_src0>>) /\ *)
(*       (<<MAXTS: forall loc, Memory.max_ts loc mem_src1 = Memory.max_ts loc mem_src0>>) /\ *)
(*       (<<FINALIZED: promise_finalized f prom_src1 mem_tgt>>) *)
(* . *)
(* Proof. *)
(*   assert (exists dom, *)
(*              (<<DOM: forall to from val released *)
(*                             (GET: Memory.get loc to prom_src0 = Some (from, Message.concrete val (Some released))), *)
(*                  List.In to dom>>)). *)
(*   { hexploit (cell_finite_sound_exists (prom_src0 loc)). i. des. *)
(*     hexploit (@list_filter_exists _ (fun to => exists from val released, Memory.get loc to prom_src0 = Some (from, Message.concrete val (Some released)))). *)
(*     i. des. exists l'. ii. eapply COMPLETE0. splits; eauto. *)
(*     eapply COMPLETE. eauto. *)
(*   } *)
(*   i. des. *)
(*   cut (exists prom_src1 mem_src1, *)
(*           (<<STEPS: rtc (@Thread.tau_step _) *)
(*                         (Thread.mk lang st (Local.mk tvw prom_src0) sc mem_src0) *)
(*                         (Thread.mk _ st (Local.mk tvw prom_src1) sc mem_src1)>>) /\ *)
(*           (<<LOWERPROMS: lower_none_list prom_src0 prom_src1 loc dom>>) /\ *)
(*           (<<VALS: forall loc0 to val released, *)
(*               max_readable mem_src0 prom_src0 loc0 to val released *)
(*               <-> *)
(*               max_readable mem_src1 prom_src1 loc0 to val released>>) /\ *)
(*           (<<MEM: sim_memory srctm flag_src f vers mem_src1 mem_tgt>>) /\ *)
(*           (<<COVERED: forall loc ts, covered loc ts mem_src1 <-> covered loc ts mem_src0>>) /\ *)
(*           (<<MAXTS: forall loc, Memory.max_ts loc mem_src1 = Memory.max_ts loc mem_src0>>) /\ *)
(*           (<<FINALIZED: promise_finalized f prom_src1 mem_tgt>>)). *)
(*   { i. des. esplits. *)
(*     { eauto. } *)
(*     { inv LOWERPROMS. econs. *)
(*       { i. hexploit sim_reserves_get; eauto. i. des. des_ifs. *)
(*         { destruct (classic (List.In to_src dom)). *)
(*           { hexploit SAMETS; eauto. i. esplits; eauto. *)
(*             i. hexploit GET0; eauto. i. des. rewrite GET1 in H0. inv H0. *)
(*             { esplits; eauto. inv MSG; try by (econs; auto). } *)
(*             { esplits; eauto. inv MSG; try by (econs; auto). } *)
(*             { esplits; eauto. inv MSG; try by (econs; auto). } *)
(*           } *)
(*           { hexploit OTHERTS; eauto. i. esplits; eauto. *)
(*             i. hexploit GET0; eauto. i. des. *)
(*             rewrite H0. esplits; eauto. *)
(*             inv MSG; try by (econs; auto). *)
(*             destruct vw_src; try by (econs; auto). *)
(*             exfalso. eapply H. eapply DOM. eauto. *)
(*           } *)
(*         } *)
(*         { esplits; eauto. rewrite OTHERLOC; auto. } *)
(*       } *)
(*       { i. des_ifs. *)
(*         { destruct (classic (List.In fto dom)). *)
(*           { des. hexploit SAMETS; eauto. i. *)
(*             destruct (classic (msg_src = Message.reserve)). *)
(*             { rewrite GET in H0. subst. inv H0. *)
(*               hexploit sim_reserves_get_if. *)
(*               { eauto. } *)
(*               { eauto. } *)
(*               i. des; clarify. left. esplits; eauto. *)
(*             } *)
(*             { right. esplits; eauto. *)
(*               { i. rewrite GET in H0. inv H0; ss. *)
(*                 { eapply TS; eauto; ss. } *)
(*                 { eapply TS; eauto; ss. } *)
(*               } *)
(*               { i. subst. rewrite GET in *. inv H0; ss. } *)
(*             } *)
(*           } *)
(*           { hexploit sim_reserves_get_if. *)
(*             { eauto. } *)
(*             { rewrite <- OTHERTS; eauto. } *)
(*             i. des; clarify. *)
(*             { left. esplits; eauto. } *)
(*             { right. esplits; eauto. } *)
(*           } *)
(*         } *)
(*         { hexploit sim_reserves_get_if. *)
(*           { eauto. } *)
(*           { rewrite <- OTHERLOC; eauto. } *)
(*           i. des. *)
(*           { left. esplits; eauto. } *)
(*           { right. esplits; eauto. } *)
(*         } *)
(*       } *)
(*       { i. hexploit sim_reserves_none; eauto. i. *)
(*         destruct (Loc.eq_dec loc0 loc); subst. *)
(*         { destruct (classic (List.In to dom)). *)
(*           { hexploit SAMETS; eauto. i. *)
(*             rewrite H in H1. inv H1; auto. *)
(*           } *)
(*           { rewrite OTHERTS; auto. } *)
(*         } *)
(*         { rewrite OTHERLOC; eauto. } *)
(*       } *)
(*     } *)
(*     { i. inv LOWERPROMS. destruct (classic (List.In to dom)). *)
(*       { eapply SAMETS in H. rewrite GET in H. inv H. auto. } *)
(*       { rewrite OTHERTS in GET; auto. destruct released; auto. *)
(*         eapply DOM in GET; ss. *)
(*       } *)
(*     } *)
(*     { auto. } *)
(*     { auto. } *)
(*     { auto. } *)
(*     { auto. } *)
(*     { auto. } *)
(*   } *)
(*   { clear TS PROMS. revert prom_src0 mem_src0 DOM MEM MLE INHABITED FINALIZED. *)
(*     induction dom; i; ss. *)
(*     { esplits. *)
(*       { refl. } *)
(*       { econs; ss. } *)
(*       { refl. } *)
(*       { auto. } *)
(*       { auto. } *)
(*       { auto. } *)
(*       { auto. } *)
(*     } *)
(*     { destruct (classic (exists from val released, <<GET: Memory.get loc a prom_src0 = Some (from, Message.concrete val (Some released))>>)). *)
(*       { des. *)
(*         hexploit (@Memory.lower_exists prom_src0 loc from a (Message.concrete val (Some released)) (Message.concrete val None)); auto. *)
(*         { hexploit memory_get_ts_strong. *)
(*           { eapply GET. } *)
(*           i. des; clarify. *)
(*           apply MLE in GET. *)
(*           rewrite INHABITED in GET. clarify. *)
(*         } *)
(*         { econs; eauto. refl. } *)
(*         i. des. *)
(*         hexploit Memory.lower_exists_le; eauto. i. des. *)
(*         assert (LOWER: Memory.promise prom_src0 mem_src0 loc from a (Message.concrete val None) mem2 mem0 (Memory.op_kind_lower (Message.concrete val (Some released)))). *)
(*         { econs; eauto; ss. econs. ss. eapply Time.bot_spec. } *)
(*         hexploit (@IHdom mem2 mem0); auto. *)
(*         { i. erewrite Memory.lower_o in GET0; eauto. des_ifs. *)
(*           hexploit DOM; eauto. i. des; clarify. *)
(*         } *)
(*         { eapply lower_src_sim_memory; eauto. } *)
(*         { eapply promise_memory_le; eauto. } *)
(*         { eapply Memory.lower_inhabited; eauto. } *)
(*         { eapply promise_finalized_promise_decr; eauto. *)
(*           i. erewrite Memory.lower_o in GETSRC; eauto. des_ifs. *)
(*           { ss. des; clarify. left. esplits; eauto; ss. } *)
(*           { left. esplits; eauto. } *)
(*         } *)
(*         i. des. exists prom_src1, mem_src1. esplits; eauto. *)
(*         { econs; [|eapply STEPS]. econs. *)
(*           { econs. econs 1. econs; ss. econs; eauto. } *)
(*           { ss. } *)
(*         } *)
(*         { inv LOWERPROMS. econs. *)
(*           { i. transitivity (Memory.get loc0 ts mem2); auto. *)
(*             erewrite (@Memory.lower_o mem2); eauto. *)
(*             des_ifs. ss. des; clarify. *)
(*           } *)
(*           { i. transitivity (Memory.get loc ts mem2); auto. *)
(*             { apply OTHERTS. ii. apply NIN. ss; auto. } *)
(*             { erewrite (@Memory.lower_o mem2); eauto. *)
(*               des_ifs. ss. des; clarify. exfalso. eapply NIN; auto. *)
(*             } *)
(*           } *)
(*           { i. ss. des. *)
(*             { clarify. destruct (classic (List.In ts dom)); auto. *)
(*               { apply SAMETS in H1. erewrite (@Memory.lower_o mem2) in H1; eauto. *)
(*                 des_ifs. ss. des; clarify. *)
(*                 rewrite GET. inv H1; try econs. *)
(*               } *)
(*               { apply OTHERTS in H1. rewrite H1. *)
(*                 erewrite (@Memory.lower_o mem2); eauto. des_ifs. *)
(*                 { ss. des; clarify. rewrite GET. econs. } *)
(*                 { ss. des; clarify. } *)
(*               } *)
(*             } *)
(*             { eapply SAMETS in IN. erewrite (@Memory.lower_o mem2) in IN; eauto. *)
(*               des_ifs. ss. des; clarify. rewrite GET. *)
(*               inv IN; try by econs. *)
(*             } *)
(*           } *)
(*         } *)
(*         { i. erewrite <- VALS. split; i; des. *)
(*           { inv H1. econs. *)
(*             { erewrite Memory.lower_o; eauto. des_ifs; eauto. *)
(*               exfalso. ss. des; clarify. *)
(*             } *)
(*             { erewrite Memory.lower_o; eauto. des_ifs; eauto. *)
(*               exfalso. ss. des; clarify. *)
(*             } *)
(*             { i. erewrite Memory.lower_o in GET1; eauto. *)
(*               erewrite (@Memory.lower_o mem2 prom_src0); eauto. des_ifs. *)
(*               eapply MAX; eauto. *)
(*             } *)
(*           } *)
(*           { inv H1. erewrite Memory.lower_o in GET0; eauto. *)
(*             erewrite Memory.lower_o in NONE; eauto. des_ifs. guardH o. *)
(*             econs; eauto. i. *)
(*             erewrite memory_lower_o2 in GET1; eauto. *)
(*             erewrite (@memory_lower_o2 prom_src0 mem2); eauto. des_ifs. *)
(*             eapply MAX; eauto. *)
(*           } *)
(*         } *)
(*         { i. etrans; eauto. eapply lower_covered; eauto. } *)
(*         { i. rewrite MAXTS. erewrite memory_lower_max_ts; eauto. } *)
(*       } *)
(*       { hexploit (@IHdom prom_src0 mem_src0); auto. *)
(*         { i. hexploit DOM; eauto. i. des; clarify. *)
(*           exfalso. eapply H; eauto. *)
(*         } *)
(*         i. des. esplits; eauto. inv LOWERPROMS. econs. *)
(*         { i. eapply OTHERLOC. auto. } *)
(*         { i. eapply OTHERTS. ii. eapply NIN. ss; auto. } *)
(*         { i. ss. des; clarify. *)
(*           { destruct (classic (List.In ts dom)); auto. *)
(*             eapply OTHERTS in H0. rewrite H0. *)
(*             destruct (Memory.get loc ts prom_src0) as [[? []]|] eqn:EQ; try econs. *)
(*             destruct released; try econs. *)
(*             exfalso. eapply H; eauto. *)
(*           } *)
(*           { eapply SAMETS. auto. } *)
(*         } *)
(*       } *)
(*     } *)
(*   } *)
(* Qed. *)

(* Lemma src_cancel_sim_reserves srctm flag_src f vers prom_src0 mem_src0 mem_tgt loc from to prom_src1 mem_src1 *)
(*       (CANCEL: Memory.promise prom_src0 mem_src0 loc from to Message.reserve prom_src1 mem_src1 Memory.op_kind_cancel) *)
(*       (MEM: sim_memory srctm flag_src f vers mem_src0 mem_tgt) *)
(*       (MLE: Memory.le prom_src0 mem_src0) *)
(*       (CLOSED: Memory.closed mem_src0) *)
(*       (FINALIZED: promise_finalized f prom_src0 mem_tgt) *)
(*   : *)
(*     (<<MEM: sim_memory srctm flag_src f vers mem_src1 mem_tgt>>) /\ *)
(*     (<<PROM: forall loc0 (NEQ: loc0 <> loc) to0, Memory.get loc0 to0 prom_src1 = Memory.get loc0 to0 prom_src0>>) /\ *)
(*     (<<VALS: forall loc0 to val released, *)
(*         max_readable mem_src0 prom_src0 loc0 to val released *)
(*         <-> *)
(*         max_readable mem_src1 prom_src1 loc0 to val released>>) /\ *)
(*     (<<FINALIZED: promise_finalized f prom_src1 mem_tgt>>) *)
(* . *)
(* Proof. *)
(*   inv CANCEL. splits. *)
(*   { eapply src_cancel_sim_memory; eauto. } *)
(*   { i. erewrite (@Memory.remove_o prom_src1 prom_src0); eauto. des_ifs. *)
(*     ss. des; clarify. *)
(*   } *)
(*   { i. split. *)
(*     { i. inv H. econs. *)
(*       { erewrite Memory.remove_o; eauto. des_ifs; eauto. *)
(*         eapply Memory.remove_get0 in MEM0. exfalso. ss. des; clarify. *)
(*       } *)
(*       { erewrite Memory.remove_o; eauto. des_ifs; eauto. } *)
(*       { i. erewrite (@Memory.remove_o mem_src1 mem_src0) in GET0; eauto. *)
(*         erewrite (@Memory.remove_o prom_src1 prom_src0); eauto. des_ifs; eauto. *)
(*       } *)
(*     } *)
(*     { i. inv H. erewrite (@Memory.remove_o mem_src1 mem_src0) in GET; eauto. *)
(*       erewrite (@Memory.remove_o prom_src1 prom_src0) in NONE; eauto. des_ifs; eauto. *)
(*       econs; eauto. i. hexploit MAX; eauto. *)
(*       { erewrite Memory.remove_o; eauto. des_ifs; eauto. *)
(*         exfalso. apply Memory.remove_get0 in MEM0. ss. des; clarify. *)
(*       } *)
(*       { i. erewrite Memory.remove_o in H; eauto. des_ifs. } *)
(*     } *)
(*   } *)
(*   { eapply promise_finalized_promise_decr; eauto. i. *)
(*     erewrite Memory.remove_o in GETSRC; eauto. des_ifs. left. eauto. *)
(*   } *)
(* Qed. *)

(* Lemma src_cancels_sim_reserves srctm flag_src f vers prom_src0 mem_src0 mem_tgt loc *)
(*       prom_src1 mem_src1 *)
(*       (MEM: sim_memory srctm flag_src f vers mem_src0 mem_tgt) *)
(*       (CANCEL: cancel_future_memory loc prom_src0 mem_src0 prom_src1 mem_src1) *)
(*       (MLE: Memory.le prom_src0 mem_src0) *)
(*       (CLOSED: Memory.closed mem_src0) *)
(*       (FINALIZED: promise_finalized f prom_src0 mem_tgt) *)
(*   : *)
(*     (<<MEM: sim_memory srctm flag_src f vers mem_src1 mem_tgt>>) /\ *)
(*     (<<PROM: forall loc0 (NEQ: loc0 <> loc) to0, Memory.get loc0 to0 prom_src1 = Memory.get loc0 to0 prom_src0>>) /\ *)
(*     (<<VALS: forall loc0 to val released, *)
(*         max_readable mem_src0 prom_src0 loc0 to val released *)
(*         <-> *)
(*         max_readable mem_src1 prom_src1 loc0 to val released>>) /\ *)
(*     (<<FINALIZED: promise_finalized f prom_src1 mem_tgt>>) *)
(* . *)
(* Proof. *)
(*   revert MLE CLOSED. induction CANCEL. *)
(*   { i. splits; auto. } *)
(*   { i. hexploit src_cancel_sim_reserves; eauto. i. des. *)
(*     hexploit IHCANCEL; eauto. *)
(*     { eapply promise_memory_le; eauto. } *)
(*     { eapply Memory.promise_closed; eauto. } *)
(*     i. des. splits; auto. *)
(*     { i. transitivity (Memory.get loc0 to0 prom1); auto. } *)
(*     { i. transitivity (max_readable mem1 prom1 loc0 to0 val released); auto. } *)
(*   } *)
(* Qed. *)

(* Lemma sim_reserves_nonsynch_loc srctm flag_src flag_tgt f vers *)
(*       prom_src prom_tgt loc *)
(*       (SIM: sim_reserves srctm flag_src flag_tgt f vers prom_src prom_tgt) *)
(*       (NONSYNCH: flag_tgt loc = false -> Memory.nonsynch_loc loc prom_tgt) *)
(*   : *)
(*     Memory.nonsynch_loc loc prom_src. *)
(* Proof. *)
(*   ii. hexploit sim_reserves_get_if; eauto. i. des. *)
(*   { inv MSG; ss. hexploit NONSYNCH; eauto. *)
(*     i. eapply H in GET0; eauto. subst. inv SIM0. auto. *)
(*   } *)
(*   { des_ifs. destruct released; auto. exfalso. eapply SYNC; eauto. } *)
(* Qed. *)

(* Lemma sim_reserves_nonsynch srctm flag_src flag_tgt f vers *)
(*       prom_src prom_tgt *)
(*       (SIM: sim_reserves srctm flag_src flag_tgt f vers prom_src prom_tgt) *)
(*       (NONSYNCH: Memory.nonsynch prom_tgt) *)
(*   : *)
(*     Memory.nonsynch prom_src. *)
(* Proof. *)
(*   intros loc. eapply sim_reserves_nonsynch_loc; eauto. *)
(* Qed. *)

(* Lemma sim_reserves_bot srctm flag_src flag_tgt f vers *)
(*       prom_src prom_tgt *)
(*       (SIM: sim_reserves srctm flag_src flag_tgt f vers prom_src prom_tgt) *)
(*       (BOT: prom_tgt = Memory.bot) *)
(*       (FLAG: forall loc (NONE: flag_src loc = false), flag_tgt loc = false) *)
(*   : *)
(*     prom_src = Memory.bot. *)
(* Proof. *)
(*   subst. eapply Memory.ext. i. rewrite Memory.bot_get. *)
(*   destruct (Memory.get loc ts prom_src) eqn:EQ; auto. *)
(*   destruct p. hexploit sim_reserves_get_if; eauto. i. des. *)
(*   { rewrite Memory.bot_get in GET. ss. } *)
(*   { destruct (flag_src loc) eqn:SRC. *)
(*     { hexploit sim_reserves_none; eauto. i. rewrite H in EQ. ss. } *)
(*     { exfalso. eapply FLAG in SRC. clarify. } *)
(*   } *)
(* Qed. *)

(* Variant wf_release_vers (vers: versions) (prom_tgt: Memory.t) (rel_vers: Loc.t -> version): Prop := *)
(*   | wf_release_vers_intro *)
(*       (PROM: forall loc from to msg *)
(*                     (GET: Memory.get loc to prom_tgt = Some (from, msg)) *)
(*                     (MSG: msg <> Message.reserve), *)
(*         exists v, *)
(*           (<<VER: vers loc to = Some v>>) /\ *)
(*             (<<REL: forall val released (MSG: msg = Message.concrete val (Some released)), *)
(*                 version_le (rel_vers loc) v>>)) *)
(* . *)

(* Lemma sim_memory_mon_vers srctm flag_src f vers0 vers1 mem_src mem_tgt *)
(*       (SIM: sim_memory srctm flag_src f vers0 mem_src mem_tgt) *)
(*       (VERS: versions_le vers0 vers1) *)
(*       (WFS: Mapping.wfs f) *)
(*   : *)
(*     sim_memory srctm flag_src f vers1 mem_src mem_tgt. *)
(* Proof. *)
(*   econs. *)
(*   { ii. hexploit sim_memory_get; eauto. i. des. esplits; eauto. inv MSG. *)
(*     { exploit VERS; eauto. intros x. rewrite x. econs 1; eauto. } *)
(*     { exploit VERS; eauto. intros x. rewrite x. econs 2; eauto. } *)
(*     { econs 3; eauto. } *)
(*     { exploit VERS; eauto. intros x. rewrite x. econs 4; eauto. } *)
(*   } *)
(*   { i. hexploit sim_memory_sound; eauto. } *)
(*   { i. eapply sim_memory_top; eauto. } *)
(*   { i. eapply sim_memory_undef; eauto. } *)
(* Qed. *)

(* Lemma sim_reserves_mon_vers srctm flag_src flag_tgt f vers0 vers1 mem_src mem_tgt *)
(*       (SIM: sim_reserves srctm flag_src flag_tgt f vers0 mem_src mem_tgt) *)
(*       (VERS: versions_le vers0 vers1) *)
(*       (WFS: Mapping.wfs f) *)
(*   : *)
(*     sim_reserves srctm flag_src flag_tgt f vers1 mem_src mem_tgt. *)
(* Proof. *)
(*   econs. *)
(*   { ii. hexploit sim_reserves_get; eauto. i. des. esplits; eauto. *)
(*     { i. hexploit VERS0; eauto. i. des. eapply VERS in VER. eauto. } *)
(*     i. hexploit GET0; eauto. i. des. esplits; eauto. inv MSG. *)
(*     { exploit VERS; eauto. intros x. rewrite x. econs 1; eauto. } *)
(*     { exploit VERS; eauto. intros x. rewrite x. econs 2; eauto. } *)
(*     { econs 3; eauto. } *)
(*     { exploit VERS; eauto. intros x. rewrite x. econs 4; eauto. } *)
(*   } *)
(*   { i. hexploit sim_reserves_get_if; eauto. i. des. *)
(*     { left. esplits; eauto. } *)
(*     { right. esplits; eauto. } *)
(*   } *)
(*   { i. hexploit sim_reserves_none; eauto. } *)
(* Qed. *)

(* Lemma sim_reserves_mon_strong srctm flag_src flag_tgt f0 f1 vers mem_src mem_tgt *)
(*       (SIM: sim_reserves f0 vers mem_src mem_tgt) *)
(*       (LE: Mapping.les_strong f0 f1) *)
(*       (WF0: Mapping.wfs f0) *)
(*       (WF1: Mapping.wfs f1) *)
(*       (VERS: versions_wf f0 vers) *)
(*       (SAME: forall loc (FLAG: flag_src loc = true), f1 loc = f0 loc) *)
(*   : *)
(*     sim_reserves srctm flag_src flag_tgt f1 vers mem_src mem_tgt. *)
(* Proof. *)
(*   econs. *)
(*   { ii. hexploit sim_reserves_get; eauto. i. des. esplits; eauto. *)
(*     { eapply sim_timestamp_exact_mon_strong; eauto. } *)
(*     { eapply sim_timestamp_exact_mon_strong; eauto. } *)
(*     { i. hexploit GET0; eauto. i. des. esplits; eauto. *)
(*       erewrite <- sim_message_max_mon_mapping; eauto. *)
(*       eapply Mapping.les_strong_les; eauto. *)
(*     } *)
(*   } *)
(*   { i. hexploit sim_reserves_get_if; eauto. i. des. *)
(*     { left. esplits; eauto. eapply sim_timestamp_exact_mon_strong; eauto. } *)
(*     { right. esplits; eauto. } *)
(*   } *)
(*   { i. hexploit sim_reserves_none; eauto. } *)
(* Qed. *)

(* Lemma version_wf_join f v0 v1 *)
(*       (WF0: version_wf f v0) *)
(*       (WF1: version_wf f v1) *)
(*   : *)
(*     version_wf f (version_join v0 v1). *)
(* Proof. *)
(*   ii. unfold version_join. *)
(*   destruct (Max.max_dec (v0 loc) (v1 loc)). *)
(*   { rewrite e. auto. } *)
(*   { rewrite e. auto. } *)
(* Qed. *)

(* Lemma opt_version_wf_join f v0 v1 *)
(*       (WF0: opt_version_wf f v0) *)
(*       (WF1: opt_version_wf f v1) *)
(*   : *)
(*     opt_version_wf f (opt_version_join v0 v1). *)
(* Proof. *)
(*   destruct v0, v1; ss. eapply version_wf_join; eauto. *)
(* Qed. *)

Lemma sim_reserve_promise
      flag gown f mem_src0 mem_tgt0 prom_src0 prom_tgt0
      loc from_tgt to_tgt prom_tgt1 mem_tgt1
      from_src to_src
      (ADD: Memory.reserve prom_tgt0 mem_tgt0 loc from_tgt to_tgt prom_tgt1 mem_tgt1)
      (MEM: sim_memory flag gown f mem_src0 mem_tgt0)
      (PROM: sim_reserves f prom_src0 prom_tgt0)
      (MAPWF: Mapping.wfs f)
      (MLESRC: Memory.le prom_src0 mem_src0)
      (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src (Some from_tgt))
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt))
  :
  exists prom_src1 mem_src1,
    (<<ADD: Memory.reserve prom_src0 mem_src0 loc from_src to_src prom_src1 mem_src1>>) /\
      (<<MEM: sim_memory flag gown f mem_src1 mem_tgt1>>) /\
      (<<PROM: sim_reserves f prom_src1 prom_tgt1>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0 prom_tgt0) f mem_src0 f mem_src1>>)
.
Proof.
  inv ADD. hexploit add_succeed_wf; eauto. i. des.
  hexploit sim_memory_add; [eapply MEM0|..]; eauto.
  { econs. }
  i. des.
  hexploit add_sim_memory; [eapply MEM0|..]; eauto.
  { econs. }
  intros SIMMEM.
  hexploit Memory.add_exists_le; eauto.
  i. des. hexploit add_sim_reserves; [eapply RSV|..]; eauto.
  intros SIMPROM. esplits; eauto. econs; eauto.
  { eapply space_future_memory_mon_msgs.
    { eapply add_space_future_memory; eauto. }
    { i. eapply unchangable_messages_of_memory; eauto. }
  }
Qed.

Lemma sim_cancel_promise
      flag gown f mem_src0 mem_tgt0 prom_src0 prom_tgt0
      loc from_tgt to_tgt prom_tgt1 mem_tgt1
      (CANCEL: Memory.cancel prom_tgt0 mem_tgt0 loc from_tgt to_tgt prom_tgt1 mem_tgt1)
      (MEM: sim_memory flag gown f mem_src0 mem_tgt0)
      (PROM: sim_reserves f prom_src0 prom_tgt0)
      (MAPWF: Mapping.wfs f)
      (MLESRC: Memory.le prom_src0 mem_src0)
  :
  exists from_src to_src prom_src1 mem_src1,
    (<<CANCEL: Memory.cancel prom_src0 mem_src0 loc from_src to_src prom_src1 mem_src1>>) /\
      (<<MEM: sim_memory flag gown f mem_src1 mem_tgt1>>) /\
      (<<PROM: sim_reserves f prom_src1 prom_tgt1>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0 prom_tgt0) f mem_src0 f mem_src1>>)
.
Proof.
  inv CANCEL. hexploit Memory.remove_get0; eauto. i. des.
  hexploit sim_reserves_cancel; [eapply RSV|..]; eauto.
  i. des.
  hexploit Memory.remove_exists.
  { eapply MLESRC. eapply GET1. }
  i. des. hexploit remove_sim_reserves; [eapply RSV|..]; eauto.
  intros SIMPROM.
  hexploit remove_sim_memory; [eapply MEM0|..]; eauto.
  intros SIMMEM.
  esplits; eauto.
  { eapply space_future_covered_decr; eauto. i.
    eapply remove_covered in COVERED; eauto. des; auto. }
Qed.

Lemma sim_add_write
      flag gown f mem_src0 mem_tgt0
      loc from_tgt to_tgt msg_tgt mem_tgt1
      from_src to_src msg_src
      (ADD: Memory.add mem_tgt0 loc from_tgt to_tgt msg_tgt mem_tgt1)
      (MEM: sim_memory flag gown f mem_src0 mem_tgt0)
      (MAPWF: Mapping.wfs f)
      (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src (Some from_tgt))
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src (Some to_tgt))
      (MSG: sim_message loc f (Some (Mapping.vers f)) msg_src msg_tgt)
      (WF: Message.wf msg_src)
      (MSGTO: Memory.message_to msg_src loc to_src)
  :
  exists mem_src1,
    (<<ADD: Memory.add mem_src0 loc from_src to_src msg_src mem_src1>>) /\
      (<<MEM: sim_memory flag gown f mem_src1 mem_tgt1>>) /\
      (<<SPACE: space_future_memory (Messages.of_memory mem_tgt0) f mem_src0 f mem_src1>>)
.
Proof.
  hexploit add_succeed_wf; eauto. i. des.
  move WF at bottom. hexploit sim_memory_add; [eapply ADD|..]; eauto.
  i. des.
  hexploit add_sim_memory; [eapply ADD|..]; eauto.
  intros SIMMEM.
  esplits; eauto.
  { eapply space_future_memory_mon_msgs.
    { eapply add_space_future_memory; eauto. }
    { i. auto. }
  }
Qed.

(* Lemma sim_closed_memory_map_exists f0 f1 mem0 mem1 *)
(*       (MAPWF: Mapping.wfs f1) *)
(*       (CLOSED: sim_closed_memory f0 mem0) *)
(*       (TIMES: forall loc ts (TIME: Mapping.closed (f1 loc) (f1 loc).(Mapping.ver) ts), *)
(*           Mapping.closed (f0 loc) (f0 loc).(Mapping.ver) ts \/ *)
(*             exists from val released, Memory.get loc ts mem1 = Some (from, Message.concrete val released)) *)
(*       (FUTURE: Memory.future_weak mem0 mem1) *)
(*   : *)
(*   exists f2, *)
(*     (<<MAPWF: Mapping.wfs f2>>) /\ *)
(*       (<<MAPLE: Mapping.les_strong f1 f2>>) /\ *)
(*       (<<CLOSED: sim_closed_memory f2 mem1>>). *)
(* Proof. *)
(*   hexploit (choice (fun loc f => *)
(*                       (<<MAPWF: Mapping.wf f>>) /\ *)
(*                         (<<MAPLE: Mapping.le_strong (f1 loc) f>>) /\ *)
(*                         (<<CLOSED: forall ts (CLOSED: Mapping.closed f f.(Mapping.ver) ts), *)
(*                           exists from val released, *)
(*                             Memory.get loc ts mem1 = Some (from, Message.concrete val released)>>))). *)
(*   { intros loc. *)
(*     hexploit (@mapping_update_times (f1 loc) (fun ts => exists from val released, Memory.get loc ts mem1 = Some (from, Message.concrete val released))); eauto. *)
(*     { hexploit cell_finite_sound_exists. i. des. *)
(*       hexploit (@list_filter_exists _ (fun ts => exists from val released, Memory.get loc ts mem1 = Some (from, Message.concrete val released))). *)
(*       i. des. exists l'. i. *)
(*       des. eapply COMPLETE0. split; eauto. *)
(*       eapply COMPLETE. eauto. *)
(*     } *)
(*     i. des. exists f2. splits; auto. i. *)
(*     eapply TIMES0 in CLOSED0. des; eauto. *)
(*     eapply TIMES in CLOSED0. des; eauto. *)
(*     eapply CLOSED in CLOSED0. des. *)
(*     eapply Memory.future_weak_get1 in CLOSED0; eauto; ss. *)
(*     des. inv MSG_LE. eauto. *)
(*   } *)
(*   i. des. exists f. splits; auto. *)
(*   { ii. eapply H. } *)
(*   { ii. eapply H. } *)
(*   { ii. hexploit (H loc). i. des. eauto. } *)
(* Qed. *)

(* Lemma wf_release_vers_le vers prom_tgt0 prom_tgt1 rel_vers *)
(*       (WF: wf_release_vers vers prom_tgt0 rel_vers) *)
(*       (MLE: Memory.le prom_tgt1 prom_tgt0) *)
(*   : *)
(*   wf_release_vers vers prom_tgt1 rel_vers. *)
(* Proof. *)
(*   inv WF. econs. i. eapply MLE in GET. eauto. *)
(* Qed. *)

(* Lemma wf_release_vers_remove vers prom_tgt0 prom_tgt1 rel_vers loc from to msg *)
(*       (WF: wf_release_vers vers prom_tgt0 rel_vers) *)
(*       (REMOVE: Memory.remove prom_tgt0 loc from to msg prom_tgt1) *)
(*   : *)
(*   wf_release_vers vers prom_tgt1 rel_vers. *)
(* Proof. *)
(*   eapply wf_release_vers_le; eauto. *)
(*   eapply remove_le; eauto. *)
(* Qed. *)

(* Lemma wf_release_vers_lower vers prom_tgt0 prom_tgt1 rel_vers loc from to msg0 msg1 *)
(*       (WF: wf_release_vers vers prom_tgt0 rel_vers) *)
(*       (LOWER: Memory.lower prom_tgt0 loc from to msg0 msg1 prom_tgt1) *)
(*   : *)
(*   wf_release_vers vers prom_tgt1 rel_vers. *)
(* Proof. *)
(*   inv WF. econs. i. erewrite Memory.lower_o in GET; eauto. des_ifs. *)
(*   { ss. des; clarify. eapply Memory.lower_get0 in LOWER. *)
(*     des. hexploit PROM; eauto. *)
(*     { inv MSG_LE; ss. } *)
(*     i. des. esplits; eauto. *)
(*     i. inv MSG_LE; clarify. inv RELEASED. eauto. *)
(*   } *)
(*   { eauto. } *)
(* Qed. *)

(* Lemma wf_release_vers_add_non_concrete vers prom_tgt0 prom_tgt1 rel_vers loc from to *)
(*       (WF: wf_release_vers vers prom_tgt0 rel_vers) *)
(*       (ADD: Memory.add prom_tgt0 loc from to Message.reserve prom_tgt1) *)
(*   : *)
(*   wf_release_vers vers prom_tgt1 rel_vers. *)
(* Proof. *)
(*   inv WF. econs. i. erewrite Memory.add_o in GET; eauto. des_ifs. *)
(*   eapply PROM; eauto. *)
(* Qed. *)

(* Lemma wf_release_vers_add_concrete vers prom_tgt0 prom_tgt1 rel_vers loc from to msg *)
(*       (WF: wf_release_vers vers prom_tgt0 rel_vers) *)
(*       (ADD: Memory.add prom_tgt0 loc from to msg prom_tgt1) *)
(*   : *)
(*   wf_release_vers (fun loc0 ts0 => *)
(*                      if loc_ts_eq_dec (loc0, ts0) (loc, to) *)
(*                      then opt_version_join (vers loc from) (Some (rel_vers loc)) *)
(*                      else vers loc0 ts0) prom_tgt1 rel_vers. *)
(* Proof. *)
(*   inv WF. econs. i. erewrite Memory.add_o in GET; eauto. des_ifs. *)
(*   { ss. des; clarify. destruct (vers loc from0); ss. *)
(*     { esplits; eauto. i. eapply version_join_r. } *)
(*     { esplits; eauto. refl. } *)
(*   } *)
(*   { eapply PROM; eauto. } *)
(* Qed. *)

(* Lemma wf_release_vers_split vers prom_tgt0 prom_tgt1 rel_vers loc from to ts3 msg msg3 *)
(*       (WF: wf_release_vers vers prom_tgt0 rel_vers) *)
(*       (SPLIT: Memory.split prom_tgt0 loc from to ts3 msg msg3 prom_tgt1) *)
(*   : *)
(*   wf_release_vers (fun loc0 ts0 => *)
(*                      if loc_ts_eq_dec (loc0, ts0) (loc, to) *)
(*                      then opt_version_join (vers loc from) (Some (rel_vers loc)) *)
(*                      else vers loc0 ts0) prom_tgt1 rel_vers. *)
(* Proof. *)
(*   inv WF. econs. i. erewrite Memory.split_o in GET; eauto. des_ifs. *)
(*   { ss. des; clarify. destruct (vers loc from0); ss. *)
(*     { esplits; eauto. i. eapply version_join_r. } *)
(*     { esplits; eauto. refl. } *)
(*   } *)
(*   { ss. des; clarify. eapply PROM; auto. eapply Memory.split_get0 in SPLIT. des; eauto. } *)
(*   { eapply PROM; eauto. } *)
(* Qed. *)

(* Lemma promise_versioned_memory *)
(*       f vers0 prom_tgt0 mem_tgt0 loc from to msg kind prom_tgt1 mem_tgt1 rel_vers *)
(*       (PROMISE: Memory.promise prom_tgt0 mem_tgt0 loc from to msg prom_tgt1 mem_tgt1 kind) *)
(*       (VERSWF: versions_wf f vers0) *)
(*       (RELVERS: wf_release_vers vers0 prom_tgt0 rel_vers) *)
(*       (VERSIONED: versioned_memory vers0 mem_tgt0) *)
(*       (VERS: forall loc0, version_wf f (rel_vers loc0)) *)
(*   : *)
(*   exists vers1, *)
(*     (<<VERSWF: versions_wf f vers1>>) /\ *)
(*       (<<RELVERS: wf_release_vers vers1 prom_tgt1 rel_vers>>) /\ *)
(*       (<<VERSIONED: versioned_memory vers1 mem_tgt1>>) /\ *)
(*       (<<VERSLE: versions_le vers0 vers1>>) /\ *)
(*       (<<MSG: msg <> Message.reserve -> *)
(*               exists v0, (<<VER: vers1 loc to = Some v0 >>) *)
(*                          /\ (<<VERLE: forall val released (MSG: msg = Message.concrete val (Some released)), *)
(*                                 opt_version_le (opt_version_join (vers0 loc from) (Some (rel_vers loc))) (Some v0)>>)>>). *)
(* Proof. *)
(*   set (vers' := *)
(*          fun loc0 ts0 => *)
(*            if loc_ts_eq_dec (loc0, ts0) (loc, to) *)
(*            then opt_version_join (vers0 loc from) (Some (rel_vers loc)) *)
(*            else vers0 loc0 ts0). *)
(*   assert (VERSWF1: versions_wf f vers'). *)
(*   { ii. unfold vers'. des_ifs. ss. des; clarify. *)
(*     eapply opt_version_wf_join; eauto; ss. *)
(*   } *)
(*   assert (VERSLE: Memory.get loc to mem_tgt0 = None -> versions_le vers0 vers'). *)
(*   { i. inv VERSIONED. unfold vers'. ii. des_ifs. *)
(*     ss. des; clarify. eapply SOUND in VER. des; clarify. *)
(*   } *)
(*   inv PROMISE. *)
(*   { destruct (classic (msg = Message.reserve)). *)
(*     { subst. exists vers0. esplits; eauto. *)
(*       { eapply wf_release_vers_add_non_concrete; eauto. } *)
(*       { eapply versioned_memory_add_non_concrete; eauto. ss. } *)
(*       { refl. } *)
(*       { ss. } *)
(*     } *)
(*     { exists vers'. esplits; eauto. *)
(*       { eapply wf_release_vers_add_concrete; eauto. } *)
(*       { eapply versioned_memory_add; eauto. } *)
(*       { eapply VERSLE. eapply Memory.add_get0; eauto. } *)
(*       { unfold vers'. i. des_ifs; ss; des; clarify. *)
(*         destruct (vers0 loc from); ss; eauto. *)
(*         { esplits; eauto. refl. } *)
(*         { esplits; eauto. refl. } *)
(*       } *)
(*     } *)
(*   } *)
(*   { exists vers'. esplits; eauto. *)
(*     { eapply wf_release_vers_split; eauto. } *)
(*     { eapply versioned_memory_split; eauto. i. *)
(*       subst. eapply Memory.split_get0 in PROMISES. des. *)
(*       inv RELVERS. eapply PROM in GET0; ss. des. *)
(*       rewrite VER. eapply REL; eauto. *)
(*     } *)
(*     { eapply VERSLE. eapply Memory.split_get0; eauto. } *)
(*     { unfold vers'. i. des_ifs; ss; des; clarify. *)
(*       destruct (vers0 loc from); ss; eauto. *)
(*       { esplits; eauto. refl. } *)
(*       { esplits; eauto. refl. } *)
(*     } *)
(*   } *)
(*   { exists vers0. esplits; eauto. *)
(*     { eapply wf_release_vers_lower; eauto. } *)
(*     { eapply versioned_memory_lower; eauto. } *)
(*     { refl. } *)
(*     { i. inv RELVERS. eapply lower_succeed_wf in PROMISES. des. *)
(*       hexploit PROM; eauto. *)
(*       { inv MSG_LE; ss. } *)
(*       i. des. esplits; eauto. i. eapply opt_version_join_spec. *)
(*       { subst. inv VERSIONED. *)
(*         inv MSG_LE. inv RELEASED. hexploit COMPLETE. *)
(*         { eapply Memory.lower_get0 in MEM. des; eauto. } *)
(*         { i. des. clarify. *)
(*           destruct (vers0 loc from); ss. eauto. *)
(*         } *)
(*       } *)
(*       { ss. hexploit PROM; eauto. *)
(*         { inv MSG_LE; ss. } *)
(*         i. des. clarify. *)
(*         inv MSG_LE. inv RELEASED. eapply REL0; eauto. *)
(*       } *)
(*     } *)
(*   } *)
(*   { exists vers0. esplits; eauto. *)
(*     { eapply wf_release_vers_remove; eauto. } *)
(*     { eapply versioned_memory_cancel; eauto. } *)
(*     { refl. } *)
(*     { ss. } *)
(*   } *)
(* Qed. *)

(* Lemma write_versioned_memory *)
(*       f vers0 prom_tgt0 mem_tgt0 loc from to msg kind prom_tgt1 mem_tgt1 rel_vers *)
(*       (WRITE: Memory.write prom_tgt0 mem_tgt0 loc from to msg prom_tgt1 mem_tgt1 kind) *)
(*       (VERSWF: versions_wf f vers0) *)
(*       (RELVERS: wf_release_vers vers0 prom_tgt0 rel_vers) *)
(*       (VERSIONED: versioned_memory vers0 mem_tgt0) *)
(*       (VERS: forall loc0, version_wf f (rel_vers loc0)) *)
(*   : *)
(*   exists vers1, *)
(*     (<<VERSWF: versions_wf f vers1>>) /\ *)
(*       (<<RELVERS: wf_release_vers vers1 prom_tgt1 rel_vers>>) /\ *)
(*       (<<VERSIONED: versioned_memory vers1 mem_tgt1>>) /\ *)
(*       (<<VERSLE: versions_le vers0 vers1>>) /\ *)
(*       (<<MSG: msg <> Message.reserve -> *)
(*               exists v0, (<<VER: vers1 loc to = Some v0 >>) *)
(*                          /\ (<<VERLE: forall val released (MSG: msg = Message.concrete val (Some released)), *)
(*                                 opt_version_le (opt_version_join (vers0 loc from) (Some (rel_vers loc))) (Some v0)>>)>>). *)
(* Proof. *)
(*   inv WRITE. hexploit promise_versioned_memory; eauto. i. des. *)
(*   esplits; eauto. eapply wf_release_vers_remove; eauto. *)
(* Qed. *)

(* Lemma sim_memory_promise *)
(*       srctm flag_src flag_tgt f0 vers0 mem_src0 mem_tgt0 prom_src0 prom_tgt0 *)
(*       loc from_tgt to_tgt msg_tgt kind_tgt prom_tgt1 mem_tgt1 rel_vers *)
(*       (PROMISE: Memory.promise prom_tgt0 mem_tgt0 loc from_tgt to_tgt msg_tgt prom_tgt1 mem_tgt1 kind_tgt) *)
(*       (MEM: sim_memory srctm flag_src f0 vers0 mem_src0 mem_tgt0) *)
(*       (PROM: sim_reserves srctm flag_src flag_tgt f0 vers0 prom_src0 prom_tgt0) *)
(*       (FLAG: flag_src loc = false) *)
(*       (MAPWF: Mapping.wfs f0) *)
(*       (MLESRC: Memory.le prom_src0 mem_src0) *)
(*       (VERSWF: versions_wf f0 vers0) *)
(*       (RELVERS: wf_release_vers vers0 prom_tgt0 rel_vers) *)
(*       (VERSIONED: versioned_memory vers0 mem_tgt0) *)
(*       (VERS: forall loc0, version_wf f0 (rel_vers loc0)) *)
(*       (MAPCLOSED: sim_closed_memory f0 mem_src0) *)
(*       (FINALIZED: promise_finalized f0 prom_src0 mem_tgt0) *)
(*   : *)
(*   exists f1 vers1 kind_src msg_src from_src to_src prom_src1 mem_src1, *)
(*     (<<CANCEL: Memory.promise prom_src0 mem_src0 loc from_src to_src msg_src prom_src1 mem_src1 kind_src>>) /\ *)
(*       (<<MEM: sim_memory srctm flag_src f1 vers1 mem_src1 mem_tgt1>>) /\ *)
(*       (<<PROM: sim_reserves srctm flag_src flag_tgt f1 vers1 prom_src1 prom_tgt1>>) /\ *)

(*       (<<MAPWF: Mapping.wfs f1>>) /\ *)
(*       (<<MAPLE: Mapping.les_strong f0 f1>>) /\ *)
(*       (<<VERSLE: versions_le vers0 vers1>>) /\ *)

(*       (<<VERSWF: versions_wf f1 vers1>>) /\ *)
(*       (<<RELVERS: wf_release_vers vers1 prom_tgt1 rel_vers>>) /\ *)
(*       (<<VERSIONED: versioned_memory vers1 mem_tgt1>>) /\ *)
(*       (<<TIMES: sim_closed_memory f1 mem_src1>>) /\ *)
(*       (<<MSG: sim_message_max (flag_tgt loc) loc to_src f1 (vers1 loc to_tgt) msg_src msg_tgt>>) /\ *)
(*       (<<SPACE: space_future_memory (unchangable mem_tgt0 prom_tgt0) f0 mem_src0 f1 mem_src1>>) /\ *)
(*       (<<FINALIZED: promise_finalized f1 prom_src1 mem_tgt1>>) *)
(* . *)
(* Proof. *)
(*   assert (exists (f': Mapping.t) from_src to_src, *)
(*              (<<MAPLE: Mapping.le_strong (f0 loc) f'>>) /\ *)
(*                (<<MAPWF: Mapping.wf f'>>) /\ *)
(*                (<<FROM: sim_timestamp_exact f' f'.(Mapping.ver) from_src from_tgt>>) /\ *)
(*                (<<TO: sim_timestamp_exact f' f'.(Mapping.ver) to_src to_tgt>>) /\ *)
(*                (<<TIME: forall ts, *)
(*                    (f'.(Mapping.times) f'.(Mapping.ver) ts) *)
(*                    <-> *)
(*                      ((f0 loc).(Mapping.times) (f0 loc).(Mapping.ver) ts \/ *)
(*                         (ts = to_src /\ exists val released, msg_tgt = Message.concrete val released))>>)). *)
(*   { hexploit (@mapping_add (f0 loc) from_tgt). *)
(*     { eapply MAPWF. } *)
(*     i. des. *)
(*     hexploit (@mapping_add f1 to_tgt); eauto. *)
(*     i. des. *)
(*     hexploit (@mapping_update_times f2 (fun ts => (ts = fts0 /\ exists val released, msg_tgt = Message.concrete val released))); eauto. *)
(*     { exists [fts0]. i. ss. des; eauto. } *)
(*     i. des. exists f3. esplits. *)
(*     { etrans; eauto. etrans; eauto. } *)
(*     { eauto. } *)
(*     { eapply sim_timestamp_exact_mon_strong; [..|eauto]; eauto. etrans; eauto. } *)
(*     { eapply sim_timestamp_exact_mon_strong; [..|eauto]; eauto. } *)
(*     { i. rewrite <- TIMES1. rewrite <- TIMES0. rewrite <- TIMES. auto. } *)
(*   } *)
(*   des. *)
(*   set (f1 := fun loc0 => if Loc.eq_dec loc0 loc then f' else (f0 loc0)). *)
(*   assert (MAPWF1: Mapping.wfs f1). *)
(*   { ii. unfold f1. des_ifs. } *)
(*   assert (MAPSLESTR: Mapping.les_strong f0 f1). *)
(*   { ii. subst f1. ss. des_ifs. refl. } *)
(*   assert (MASPLE: Mapping.les f0 f1). *)
(*   { eapply Mapping.les_strong_les; eauto. } *)
(*   assert (FROM1: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) from_src from_tgt). *)
(*   { unfold f1. des_ifs. } *)
(*   assert (TO1: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) to_src to_tgt). *)
(*   { unfold f1. des_ifs. } *)
(*   assert (CLOSED: forall val released (MSG: msg_tgt = Message.concrete val released), *)
(*              Mapping.closed (f1 loc) (f1 loc).(Mapping.ver) to_src). *)
(*   { i. unfold f1. des_ifs. eapply TIME. right. eauto. } *)
(*   assert (TIMES: forall loc0 ts0 (CLOSED: Mapping.closed (f1 loc0) (f1 loc0).(Mapping.ver) ts0), *)
(*              Mapping.closed (f0 loc0) (f0 loc0).(Mapping.ver) ts0 \/ *)
(*                (loc0 = loc /\ ts0 = to_src /\ exists val released, msg_tgt = Message.concrete val released)). *)
(*   { unfold f1. i. des_ifs; eauto. *)
(*     eapply TIME in CLOSED0. des; eauto. *)
(*     right. esplits; eauto. *)
(*   } *)
(*   assert (exists vers1, *)
(*              (<<VERSWF: versions_wf f1 vers1>>) /\ *)
(*                (<<RELVERS: wf_release_vers vers1 prom_tgt1 rel_vers>>) /\ *)
(*                (<<VERSIONED: versioned_memory vers1 mem_tgt1>>) /\ *)
(*                (<<VERSLE: versions_le vers0 vers1>>) /\ *)
(*                (<<MSG: msg_tgt <> Message.reserve -> *)
(*                        exists v0, (<<VER: vers1 loc to_tgt = Some v0 >>)>>)). *)
(*   { hexploit promise_versioned_memory; eauto. *)
(*     i. des. esplits; eauto. *)
(*     { eapply versions_wf_mapping_mon; eauto. } *)
(*     { i. hexploit MSG; eauto. i. des. eauto. } *)
(*   } *)
(*   des. *)
(*   assert (MEM1: sim_memory srctm flag_src f1 vers1 mem_src0 mem_tgt0). *)
(*   { eapply sim_memory_mon_vers; [|eapply VERSLE|..]; eauto. *)
(*     eapply sim_memory_mon_strong; eauto. i. unfold f1. des_ifs. } *)
(*   assert (PROM1: sim_reserves srctm flag_src flag_tgt f1 vers1 prom_src0 prom_tgt0). *)
(*   { eapply sim_reserves_mon_vers; [|eapply VERSLE|..]; eauto. *)
(*     eapply sim_reserves_mon_strong; eauto. i. unfold f1. des_ifs. } *)
(*   assert (FINALIZED0: promise_finalized f1 prom_src0 mem_tgt0). *)
(*   { eapply promise_finalized_mon_strong; eauto. } *)
(*   hexploit sim_message_max_exists. *)
(*   { eauto. } *)
(*   { i. eapply MSG in RESERVE. des. esplits; [eapply VER|]. *)
(*     specialize (VERSWF0 loc to_tgt). rewrite VER in VERSWF0. auto. *)
(*   } *)
(*   i. des. *)
(*   assert (SPACETRANS: forall mem_src1, space_future_memory (unchangable mem_tgt0 prom_tgt0) f1 mem_src0 f1 mem_src1 -> space_future_memory (unchangable mem_tgt0 prom_tgt0) f0 mem_src0 f1 mem_src1). *)
(*   { i. eapply space_future_memory_trans. *)
(*     { eapply space_future_memory_refl; eauto. } *)
(*     { eauto. } *)
(*     { eapply Mapping.les_strong_les; eauto. } *)
(*     { refl. } *)
(*     { eauto. } *)
(*     { eauto. } *)
(*     { eauto. } *)
(*   } *)
(*   destruct kind_tgt. *)
(*   { hexploit sim_add_promise; eauto. i. des. *)
(*     esplits; eauto. inv ADD. ii. eapply TIMES in CLOSED0. des. *)
(*     { eapply MAPCLOSED in CLOSED0. des. *)
(*       eapply Memory.add_get1 in CLOSED0; eauto. } *)
(*     { eapply Memory.add_get0 in MEM2. des. subst. inv MAX; eauto. } *)
(*   } *)
(*   { hexploit sim_split_promise; eauto. i. des. *)
(*     esplits; eauto. inv SPLIT. ii. eapply TIMES in CLOSED0. des. *)
(*     { eapply MAPCLOSED in CLOSED0. des. *)
(*       eapply Memory.split_get1 in CLOSED0; eauto. des. eauto. } *)
(*     { eapply Memory.split_get0 in MEM2. des. subst. inv MAX; eauto. } *)
(*   } *)
(*   { hexploit sim_lower_promise; eauto. i. des. *)
(*     esplits; eauto. inv LOWER. ii. eapply TIMES in CLOSED0. des. *)
(*     { eapply MAPCLOSED in CLOSED0. des. *)
(*       eapply Memory.lower_get1 in CLOSED0; eauto. des. inv MSG_LE; eauto. } *)
(*     { eapply Memory.lower_get0 in MEM2. des. subst. inv MAX; eauto. } *)
(*   } *)
(*   { hexploit sim_cancel_promise; eauto. i. des. *)
(*     esplits; eauto. inv CANCEL. ii. eapply TIMES in CLOSED0. des. *)
(*     { eapply MAPCLOSED in CLOSED0. des. *)
(*       erewrite Memory.remove_o; eauto. des_ifs; eauto. *)
(*       ss. des; clarify. eapply Memory.remove_get0 in MEM2. des; clarify. *)
(*     } *)
(*     { inv PROMISE. ss. } *)
(*     { inv PROMISE. inv CANCEL. econs; eauto. } *)
(*   } *)
(* Qed. *)

(* Lemma sim_memory_write *)
(*       srctm flag_src flag_tgt f0 vers0 mem_src0 mem_tgt0 prom_src0 prom_tgt0 *)
(*       loc from_tgt to_tgt msg_tgt kind_tgt prom_tgt1 mem_tgt1 rel_vers msg_src to_src *)
(*       (WRITE: Memory.write prom_tgt0 mem_tgt0 loc from_tgt to_tgt msg_tgt prom_tgt1 mem_tgt1 kind_tgt) *)
(*       (MEM: sim_memory srctm flag_src f0 vers0 mem_src0 mem_tgt0) *)
(*       (PROM: sim_reserves srctm flag_src flag_tgt f0 vers0 prom_src0 prom_tgt0) *)
(*       (FLAG: flag_src loc = false) *)
(*       (MAPWF: Mapping.wfs f0) *)
(*       (MLESRC: Memory.le prom_src0 mem_src0) *)
(*       (VERSWF: versions_wf f0 vers0) *)
(*       (RELVERS: wf_release_vers vers0 prom_tgt0 rel_vers) *)
(*       (VERSIONED: versioned_memory vers0 mem_tgt0) *)
(*       (VERS: forall loc0, version_wf f0 (rel_vers loc0)) *)
(*       (MAPCLOSED: sim_closed_memory f0 mem_src0) *)
(*       (MSG: sim_message (flag_tgt loc) loc f0 (opt_version_join (vers0 loc from_tgt) (Some (rel_vers loc))) msg_src msg_tgt) *)
(*       (TO: sim_timestamp_exact (f0 loc) (Mapping.ver (f0 loc)) to_src to_tgt) *)
(*       (WF: Message.wf msg_src) *)
(*       (MSGTO: Memory.message_to msg_src loc to_src) *)
(*       (CONCRETE: __guard__(exists val released, msg_tgt = Message.concrete val released)) *)
(*       (FINALIZED: promise_finalized f0 prom_src0 mem_tgt0) *)
(*   : *)
(*   exists f1 vers1 kind_src from_src prom_src1 mem_src1, *)
(*     (<<CANCEL: Memory.write prom_src0 mem_src0 loc from_src to_src msg_src prom_src1 mem_src1 kind_src>>) /\ *)
(*       (<<MEM: sim_memory srctm flag_src f1 vers1 mem_src1 mem_tgt1>>) /\ *)
(*       (<<PROM: sim_reserves srctm flag_src flag_tgt f1 vers1 prom_src1 prom_tgt1>>) /\ *)
(*       (<<FROM: sim_timestamp_exact (f1 loc) (Mapping.ver (f1 loc)) from_src from_tgt>>) /\ *)

(*       (<<MAPWF: Mapping.wfs f1>>) /\ *)
(*       (<<MAPLE: Mapping.les_strong f0 f1>>) /\ *)
(*       (<<VERSLE: versions_le vers0 vers1>>) /\ *)

(*       (<<VERSWF: versions_wf f1 vers1>>) /\ *)
(*       (<<RELVERS: wf_release_vers vers1 prom_tgt1 rel_vers>>) /\ *)
(*       (<<VERSIONED: versioned_memory vers1 mem_tgt1>>) /\ *)
(*       (<<TIMES: sim_closed_memory f1 mem_src1>>) /\ *)
(*       (<<CLOSED: Mapping.closed (f1 loc) (Mapping.vers f1 loc) to_src>>) /\ *)
(*       (<<SPACE: space_future_memory (unchangable mem_tgt0 prom_tgt0) f0 mem_src0 f1 mem_src1>>) /\ *)
(*       (<<FINALIZED: promise_finalized f1 prom_src1 mem_tgt1>>) *)
(* . *)
(* Proof. *)
(*   assert (exists (f': Mapping.t) from_src, *)
(*              (<<MAPLE: Mapping.le_strong (f0 loc) f'>>) /\ *)
(*                (<<MAPWF: Mapping.wf f'>>) /\ *)
(*                (<<FROM: sim_timestamp_exact f' f'.(Mapping.ver) from_src from_tgt>>) /\ *)
(*                (<<TIME: forall ts, *)
(*                    (f'.(Mapping.times) f'.(Mapping.ver) ts) *)
(*                    <-> *)
(*                      ((f0 loc).(Mapping.times) (f0 loc).(Mapping.ver) ts \/ *)
(*                         (ts = to_src))>>)). *)
(*   { hexploit (@mapping_add (f0 loc) from_tgt). *)
(*     { eapply MAPWF. } *)
(*     i. des. *)
(*     hexploit (@mapping_update_times f1 (fun ts => (ts = to_src))); eauto. *)
(*     { exists [to_src]. i. ss. des; eauto. } *)
(*     i. des. exists f2. esplits. *)
(*     { etrans; eauto. } *)
(*     { eauto. } *)
(*     { eapply sim_timestamp_exact_mon_strong; [..|eauto]; eauto. } *)
(*     { i. rewrite <- TIMES0. rewrite <- TIMES. auto. } *)
(*   } *)
(*   des. *)
(*   set (f1 := fun loc0 => if Loc.eq_dec loc0 loc then f' else (f0 loc0)). *)
(*   assert (MAPWF1: Mapping.wfs f1). *)
(*   { ii. unfold f1. des_ifs. } *)
(*   assert (MAPSLESTR: Mapping.les_strong f0 f1). *)
(*   { ii. subst f1. ss. des_ifs. refl. } *)
(*   assert (MASPLE: Mapping.les f0 f1). *)
(*   { eapply Mapping.les_strong_les; eauto. } *)
(*   assert (FROM1: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) from_src from_tgt). *)
(*   { unfold f1. des_ifs. } *)
(*   assert (TO1: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) to_src to_tgt). *)
(*   { eapply sim_timestamp_exact_mon_strong; [..|eauto]; eauto. } *)
(*   assert (CLOSED: Mapping.closed (f1 loc) (f1 loc).(Mapping.ver) to_src). *)
(*   { i. unfold f1. des_ifs. eapply TIME. right. eauto. } *)
(*   assert (TIMES: forall loc0 ts0 (CLOSED: Mapping.closed (f1 loc0) (f1 loc0).(Mapping.ver) ts0), *)
(*              Mapping.closed (f0 loc0) (f0 loc0).(Mapping.ver) ts0 \/ *)
(*                (loc0 = loc /\ ts0 = to_src)). *)
(*   { unfold f1. i. des_ifs; eauto. *)
(*     eapply TIME in CLOSED0. des; eauto. *)
(*   } *)
(*   assert (exists vers1, *)
(*              (<<VERSWF: versions_wf f1 vers1>>) /\ *)
(*                (<<RELVERS: wf_release_vers vers1 prom_tgt1 rel_vers>>) /\ *)
(*                (<<VERSIONED: versioned_memory vers1 mem_tgt1>>) /\ *)
(*                (<<VERSLE: versions_le vers0 vers1>>) /\ *)
(*                (<<MSG: msg_tgt <> Message.reserve -> *)
(*                        exists v0, (<<VER: vers1 loc to_tgt = Some v0 >>) *)
(*                                   /\ (<<VERLE: forall val released (MSG: msg_tgt = Message.concrete val (Some released)), *)
(*                                            opt_version_le (opt_version_join (vers0 loc from_tgt) (Some (rel_vers loc))) (Some v0)>>)>>)). *)
(*   { hexploit write_versioned_memory; eauto. *)
(*     i. des. esplits; eauto. *)
(*     eapply versions_wf_mapping_mon; eauto. *)
(*   } *)
(*   des. *)
(*   assert (FINALIZED0: promise_finalized f1 prom_src0 mem_tgt0). *)
(*   { eapply promise_finalized_mon_strong; eauto. } *)
(*   assert (MSG1: sim_message (flag_tgt loc) loc f1 (vers1 loc to_tgt) msg_src msg_tgt). *)
(*   { unguard. des. clarify. hexploit MSG0; ss. i. des. destruct released. *)
(*     { hexploit VERLE; eauto. i. *)
(*       eapply sim_message_mon_ver; eauto. *)
(*       { erewrite <- sim_message_mon_mapping; eauto. *)
(*         eapply opt_version_wf_join; eauto. eapply VERS. } *)
(*       { rewrite VER in *. destruct (vers0 loc from_tgt); ss. } *)
(*     } *)
(*     { rewrite VER. inv MSG. *)
(*       { inv SIM. econs 1; auto. econs. } *)
(*       { econs 4; auto. } *)
(*     } *)
(*   } *)
(*   assert (MEM1: sim_memory srctm flag_src f1 vers1 mem_src0 mem_tgt0). *)
(*   { eapply sim_memory_mon_vers; [|eapply VERSLE|..]; eauto. *)
(*     eapply sim_memory_mon_strong; eauto. i. unfold f1. des_ifs. } *)
(*   assert (PROM1: sim_reserves srctm flag_src flag_tgt f1 vers1 prom_src0 prom_tgt0). *)
(*   { eapply sim_reserves_mon_vers; [|eapply VERSLE|..]; eauto. *)
(*     eapply sim_reserves_mon_strong; eauto. i. unfold f1. des_ifs. } *)
(*   assert (exists val released, msg_src = Message.concrete val released). *)
(*   { unguard. des. clarify. inv MSG1; eauto. } *)
(*   assert (SPACETRANS: forall mem_src1, space_future_memory (unchangable mem_tgt0 prom_tgt0) f1 mem_src0 f1 mem_src1 -> space_future_memory (unchangable mem_tgt0 prom_tgt0) f0 mem_src0 f1 mem_src1). *)
(*   { i. eapply space_future_memory_trans. *)
(*     { eapply space_future_memory_refl; eauto. } *)
(*     { eauto. } *)
(*     { eapply Mapping.les_strong_les; eauto. } *)
(*     { refl. } *)
(*     { eauto. } *)
(*     { eauto. } *)
(*     { eauto. } *)
(*   } *)
(*   destruct kind_tgt. *)
(*   { hexploit sim_add_write; eauto. i. des. *)
(*     esplits; eauto. inv ADD. inv PROMISE. ii. eapply TIMES in CLOSED0. des. *)
(*     { eapply MAPCLOSED in CLOSED0. des. *)
(*       eapply Memory.add_get1 in CLOSED0; eauto. } *)
(*     { eapply Memory.add_get0 in MEM2. des. subst. eauto. } *)
(*   } *)
(*   { hexploit sim_split_write; eauto. i. des. *)
(*     esplits; eauto. inv SPLIT. inv PROMISE. ii. eapply TIMES in CLOSED0. des. *)
(*     { eapply MAPCLOSED in CLOSED0. des. *)
(*       eapply Memory.split_get1 in CLOSED0; eauto. des. eauto. } *)
(*     { eapply Memory.split_get0 in MEM2. des. subst. eauto. } *)
(*   } *)
(*   { hexploit sim_lower_write; eauto. i. des. *)
(*     esplits; eauto. inv LOWER. inv PROMISE. ii. eapply TIMES in CLOSED0. des. *)
(*     { eapply MAPCLOSED in CLOSED0. des. *)
(*       eapply Memory.lower_get1 in CLOSED0; eauto. des. inv MSG_LE; eauto. } *)
(*     { eapply Memory.lower_get0 in MEM2. des. subst. eauto. } *)
(*   } *)
(*   { inv WRITE. inv PROMISE. unguard. des; clarify. } *)
(* Qed. *)
