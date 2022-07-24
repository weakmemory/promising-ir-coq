Require Import RelationClasses.
Require Import Coq.Logic.PropExtensionality.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
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

Require Import PFCertify.

Set Implicit Arguments.
Set Nested Proofs Allowed.


Module FutureCertify.
  Let map_t: Type := Loc.t -> Time.t -> Time.t -> Prop.

  Section FutureCertify.
    Variable f: map_t.

    Definition map_eq: Prop :=
      forall loc x y fx fy
        (EQ: x = y)
        (MAP1: f loc x fx)
        (MAP2: f loc y fy),
        fx = fy.

    Definition map_eq_inv: Prop :=
      forall loc x y fx fy
        (EQ: fx = fy)
        (MAP1: f loc x fx)
        (MAP2: f loc y fy),
        x = y.

    Definition map_lt: Prop :=
      forall loc x y fx fy
        (LT: Time.lt x y)
        (MAP1: f loc x fx)
        (MAP2: f loc y fy),
        Time.lt fx fy.

    Definition map_lt_inv: Prop :=
      forall loc x y fx fy
        (LT: Time.lt fx fy)
        (MAP1: f loc x fx)
        (MAP2: f loc y fy),
        Time.lt x y.

    Variant map_wf: Prop :=
      | map_wf_intro
          (MAP_EQ: map_eq)
          (MAP_EQ_INV: map_eq_inv)
          (MAP_LT: map_lt)
          (MAP_LT_INV: map_lt_inv)
    .

    Definition map_complete (mem fmem: Memory.t): Prop :=
      forall loc ts fts (MAP: f loc ts fts),
        (<<COMPLETE: exists from to msg,
            (<<GET: Memory.get loc to mem = Some (from, msg)>>) /\
            (<<TS: ts = from \/ ts = to>>)>>) /\
        (<<FCOMPLETE: exists ffrom fto fmsg,
            (<<FGET: Memory.get loc fto fmem = Some (ffrom, fmsg)>>) /\
            (<<FTS: fts = ffrom \/ fts = fto>>)>>)
    .

    Definition timemap_map (tm ftm: TimeMap.t): Prop :=
      forall loc, f loc (tm loc) (ftm loc).

    Variant view_map (view fview: View.t): Prop :=
      | view_map_intro
          (RLX: timemap_map view.(View.rlx) (fview.(View.rlx)))
          (PLN: timemap_map view.(View.pln) (fview.(View.pln)))
    .

    Variant opt_view_map: forall (view fview: option View.t), Prop :=
      | opt_view_map_None:
        opt_view_map None None
      | opt_view_map_Some
          view fview
          (VIEW: view_map view fview):
        opt_view_map (Some view) (Some fview)
    .

    Variant tview_map (tview ftview: TView.t): Prop :=
      | tview_map_intro
          (REL: forall loc, view_map (TView.rel tview loc) (TView.rel ftview loc))
          (CUR: view_map (TView.cur tview) (TView.cur ftview))
          (ACQ: view_map (TView.acq tview) (TView.acq ftview))
    .

    Variant message_map: forall (msg fmsg: Message.t), Prop :=
      | message_map_intro
          val view fview na
          (RELEASED: opt_view_map view fview):
        message_map (Message.mk val view na) (Message.mk val fview na)
    .

    Variant memory_map_loc (loc: Loc.t) (max: Time.t): forall (rsv: bool) (mem fmem: Memory.t), Prop :=
      | memory_map_loc_reserved
          mem fmem
          fmax
          (SOUND: forall from to msg (GET: Memory.get loc to mem = Some (from, msg)),
            exists ffrom fto fmsg,
              (<<FGET: Memory.get loc fto fmem = Some (ffrom, fmsg)>>) /\
              (<<FROM: f loc from ffrom>>) /\
              (<<TO: f loc to fto>>) /\
              (<<MSG: message_map msg fmsg>>) /\
              (<<FTO_IN: Time.lt fto fmax>>))
          (COMPLETE: forall ffrom fto fmsg
                       (FGET: Memory.get loc fto fmem = Some (ffrom, fmsg)),
              (<<FFROM_OUT: Time.lt fmax ffrom>>) \/
              (<<FTO_IN: Time.lt fto fmax>>) /\
              exists from to msg,
                (<<GET: Memory.get loc to mem = Some (from, msg)>>) /\
                (<<FROM: f loc from ffrom>>) /\
                (<<TO: f loc to fto>>) /\
                (<<MSG: message_map msg fmsg>>)):
        memory_map_loc loc max true mem fmem
      | memory_map_loc_non_reserved
          mem fmem
          fmin
          (SOUND: forall from to msg (GET: Memory.get loc to mem = Some (from, msg)),
            exists ffrom fto fmsg,
              (<<FGET: Memory.get loc fto fmem = Some (ffrom, fmsg)>>) /\
              (<<FROM: f loc from ffrom>>) /\
              (<<TO: f loc to fto>>) /\
              (<<MSG: message_map msg fmsg>>))
          (COMPLETE: forall ffrom fto fmsg
                       (FGET: Memory.get loc fto fmem = Some (ffrom, fmsg))
                       (FTO_IN: Time.lt fmin fto),
              (<<FFROM_IN: Time.lt fmin ffrom>>) /\
              exists from to msg,
                (<<GET: Memory.get loc to mem = Some (from, msg)>>) /\
                (<<FROM: f loc from ffrom>>) /\
                (<<TO: f loc to fto>>) /\
                (<<MSG: message_map msg fmsg>>) /\
                (<<TO_IN: Time.lt max to>>)):
        memory_map_loc loc max false mem fmem
    .

    Definition memory_map (max: TimeMap.t) (rsv: BoolMap.t) (mem fmem: Memory.t): Prop :=
      forall loc, memory_map_loc loc (max loc) (rsv loc) mem fmem.
  End FutureCertify.


  Definition map_add (loc: Loc.t) (ts fts: Time.t) (f: map_t): map_t :=
    fun loc' ts' fts' =>
      (loc' = loc /\ ts' = ts /\ fts' = fts) \/ f loc' ts' fts'.

  Lemma map_add_eq
        (f: map_t) loc ts fts
        (MAP: f loc ts fts):
    map_add loc ts fts f = f.
  Proof.
    extensionality loc'.
    extensionality ts'.
    extensionality fts'.
    apply propositional_extensionality.
    unfold map_add.
    split; auto. i. des; subst; ss.
  Qed.

  Lemma lt_get_from
        mem loc
        from1 to1 msg1
        from2 to2 msg2
        (LT: Time.lt to1 to2)
        (GET1: Memory.get loc to1 mem = Some (from1, msg1))
        (GET2: Memory.get loc to2 mem = Some (from2, msg2)):
    Time.le to1 from2.
  Proof.
    exploit Memory.get_ts; try exact GET1. i. des.
    { subst. timetac. }
    exploit Memory.get_disjoint; [exact GET1|exact GET2|]. i. des.
    { subst. timetac. }
    destruct (TimeFacts.le_lt_dec to1 from2); ss. exfalso.
    apply (x1 to1); econs; ss; try refl. econs. ss.
  Qed.

  Lemma add_cases
        mem1 loc from to msg mem2
        (INHABITED: Memory.inhabited mem1)
        (ADD: Memory.add mem1 loc from to msg mem2):
    exists pfrom pto pmsg,
      (<<PGET: Memory.get loc pto mem1 = Some (pfrom, pmsg)>>) /\
      (<<PREV_FROM: Time.le pto from>>) /\
      (<<PREV_TO: Time.lt pto to>>) /\
      (<<PEMPTY: Memory.empty mem1 loc pto to>>) /\
      __guard__ (
          (exists nfrom nto nmsg,
              (<<NGET: Memory.get loc nto mem1 = Some (nfrom, nmsg)>>) /\
              (<<NEXT_FROM: Time.le to nfrom>>) /\
              (<<NEXT_TO: Time.lt to nto>>) /\
              (<<NEMPTY: Memory.empty mem1 loc to nto>>)) \/
          (<<LATEST: forall ts (LT: Time.lt to ts), Memory.get loc ts mem1 = None>>)).
  Proof.
    exploit Memory.add_ts; eauto. i.
    hexploit Memory.add_inhabited; eauto. i. des.
    exploit Memory.add_get0; eauto. i. des.
    exploit (@Memory.prev_exists to mem2 loc); try apply H.
    { eapply TimeFacts.le_lt_lt; eauto. apply Time.bot_spec. }
    i. des.
    revert x1. erewrite Memory.add_o; eauto. condtac; ss.
    { des. subst. timetac. }
    clear o COND. i.
    esplits; try eapply x1; eauto.
    { exploit Memory.add_get1; try exact x1; eauto. i.
      eapply lt_get_from; eauto.
    }
    { ii. exploit x3; eauto.
      erewrite Memory.add_o; eauto. condtac; ss.
    }
    destruct (TimeFacts.le_lt_dec (Memory.max_ts loc mem1) to).
    { right. i.
      destruct (Memory.get loc ts mem1) as [[]|] eqn:GET'; ss.
      exploit Memory.max_ts_spec; try exact GET'. i. des.
      rewrite l in MAX. timetac.
    }
    { left.
      exploit Memory.next_exists; try exact l; eauto. i. des.
      esplits; eauto.
      exploit Memory.add_get1; try exact x6; eauto. i.
      eapply lt_get_from; eauto.
    }
  Qed.

  Lemma memory_map_add
        f1 max rsv mem1 fmem1
        loc from to msg mem2
        fmsg
        (WF1: map_wf f1)
        (COMPLETE1: map_complete f1 mem1 fmem1)
        (MAP1: memory_map f1 max rsv mem1 fmem1)
        (INHABITED1: Memory.inhabited mem1)
        (ADD: Memory.add mem1 loc from to msg mem2)
        (RESERVE: rsv loc = false -> Time.lt (max loc) from)
        (MSG_WF: Message.wf fmsg):
    exists ffrom fto f2 fmem2,
      (<<F2: f2 = fun loc' ts fts =>
                    (loc' = loc /\ ts = to /\ fts = fto) \/
                    (loc' = loc /\ ts = from /\ fts = ffrom) \/
                    f1 loc' ts fts>>) /\
      (<<FADD: Memory.add fmem1 loc ffrom fto fmsg fmem2>>) /\
      (<<WF2: map_wf f2>>) /\
      (<<COMPLETE2: map_complete f2 mem2 fmem2>>) /\
      (<<MAP2: message_map f2 msg fmsg -> memory_map f2 max rsv mem2 fmem2>>).
  Proof.
    inv WF1.
    exploit Memory.add_ts; eauto. intro TS.
    exploit add_cases; eauto. i. des.
    destruct (rsv loc) eqn:RSV.
    { (* reserved *)
      destruct (MAP1 loc); ss.
      unguard. des.

      { (* non-latest *)
        exploit Memory.get_ts; try exact NGET. i. des; subst; timetac.
        assert (Time.lt pto nfrom).
        { eapply TimeFacts.lt_le_lt; try exact PREV_TO. ss. }
        exploit SOUND; try exact PGET. i. des.
        rename ffrom into fpfrom, fto into fpto, fmsg0 into fpmsg.
        exploit SOUND; try exact NGET. i. des.
        rename ffrom into fnfrom, fto into fnto, fmsg0 into fnmsg.
        assert (exists fto,
                   (<<FPREV_TO: Time.lt fpto fto>>) /\
                   (<<FNEXT_FROM: Time.le fto fnfrom>>) /\
                   (<<FNEXT_TO: Time.lt fto fnto>>) /\
                   (<<NEXT_EQ: __guard__ (to = nfrom <-> fto = fnfrom)>>)).
        { inv NEXT_FROM.
          - exploit MAP_LT; try exact H; eauto. i.
            exists (Time.middle fpto fnfrom).
            exploit Time.middle_spec; try exact x1. i. des.
            unguard. splits; ss.
            + econs. ss.
            + etrans; try exact x3. eapply MAP_LT; try exact x0; eauto.
            + split; i; subst; timetac.
              rewrite <- H1 in x3 at 2. timetac.
          - inv H0. exists fnfrom. unguard. splits; ss.
            + eapply MAP_LT; try exact H; eauto.
            + refl.
            + eapply MAP_LT; try exact x0; eauto.
        }
        des.
        assert (exists ffrom,
                   (<<FTS: Time.lt ffrom fto>>) /\
                   (<<FPREV_FROM: Time.le fpto ffrom>>) /\
                   (<<PREV_EQ: __guard__ (pto = from <-> fpto = ffrom)>>)).
        { inv PREV_FROM.
          - exists (Time.middle fpto fto).
            exploit Time.middle_spec; try exact FPREV_TO. i. des.
            unguard. splits; ss.
            + econs. ss.
            + split; i; subst; timetac.
              rewrite H1 in x1 at 1. timetac.
          - inv H0. exists fpto. unguard. splits; ss. refl.
        }
        des.
        exploit (@Memory.add_exists fmem loc); try exact FTS; try exact MSG_WF.
        { admit.
        }
        i. des. esplits; try exact x1; eauto; try refl.
        - admit.
        - admit.
        - admit.
      }

      { (* latest *)
        admit.
      }
    }

    { (* non-reserved *)
      admit.
    }
  Admitted.
End FutureCertify.