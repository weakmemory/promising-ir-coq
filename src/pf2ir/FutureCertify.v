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
  Definition map_t: Type := Loc.t -> Time.t -> Time.t -> Prop.

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

    Lemma map_le
          loc x y fx fy
          (MAP_EQ: map_eq)
          (MAP_LT: map_lt)
          (LE: Time.le x y)
          (MAP1: f loc x fx)
          (MAP2: f loc y fy):
      Time.le fx fy.
    Proof.
      inv LE.
      - left. eauto.
      - right. eapply MAP_EQ; eauto.
    Qed.

    Lemma map_le_inv
          loc x y fx fy
          (MAP_EQ_INV: map_eq_inv)
          (MAP_LT_INV: map_lt_inv)
          (LE: Time.le fx fy)
          (MAP1: f loc x fx)
          (MAP2: f loc y fy):
      Time.le x y.
    Proof.
      inv LE.
      - left. eauto.
      - right. eapply MAP_EQ_INV; eauto.
    Qed.

    Variant map_wf: Prop :=
      | map_wf_intro
          (MAP_EQ: map_eq)
          (MAP_EQ_INV: map_eq_inv)
          (MAP_LT: map_lt)
          (MAP_LT_INV: map_lt_inv)
    .

    Definition map_complete (mem fmem: Memory.t): Prop :=
      forall loc ts fts (MAP: f loc ts fts),
      exists from to msg ffrom fto fmsg,
        (<<GET: Memory.get loc to mem = Some (from, msg)>>) /\
        (<<FGET: Memory.get loc fto fmem = Some (ffrom, fmsg)>>) /\
        (__guard__ ((<<TS: ts = from>>) /\ (<<FTS: fts = ffrom>>) \/
                    (<<TS: ts = to>>) /\ (<<FTS: fts = fto>>)))
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

  Lemma map_add_incr loc ts fts f:
    f <3= map_add loc ts fts f.
  Proof.
    unfold map_add. auto.
  Qed.

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

  Lemma add_map_eq
        f loc ts fts
        (MAP_EQ: map_eq f)
        (ADD_EX: forall fts' (MAP: f loc ts fts'), fts' = fts):
    map_eq (map_add loc ts fts f).
  Proof.
    unfold map_add. ii. des; subst; ss.
    - exploit ADD_EX; eauto.
    - exploit ADD_EX; eauto.
    - exploit MAP_EQ; eauto.
  Qed.

  Lemma add_map_eq_inv
        f loc ts fts
        (MAP_EQ_INV: map_eq_inv f)
        (ADD_EX: forall ts' (MAP: f loc ts' fts), ts' = ts):
    map_eq_inv (map_add loc ts fts f).
  Proof.
    unfold map_add. ii. des; subst; ss.
    - exploit ADD_EX; eauto.
    - exploit ADD_EX; eauto.
    - exploit MAP_EQ_INV; eauto.
  Qed.

  Lemma add_map_lt
        f loc ts fts
        (MAP_LT: map_lt f)
        (ADD_EX: forall ts' fts' (MAP: f loc ts' fts'),
            Time.lt ts' ts /\ Time.lt fts' fts \/
              ts' = ts /\ fts' = fts \/
              Time.lt ts ts' /\ Time.lt fts fts'):
    map_lt (map_add loc ts fts f).
  Proof.
    unfold map_add. ii. des; subst; eauto; timetac.
    - exploit ADD_EX; try exact MAP1. i. des; timetac.
    - exploit ADD_EX; try exact MAP2. i. des; timetac.
  Qed.

  Lemma add_map_lt_inv
        f loc ts fts
        (MAP_LT_INV: map_lt_inv f)
        (ADD_EX: forall ts' fts' (MAP: f loc ts' fts'),
            Time.lt ts' ts /\ Time.lt fts' fts \/
              ts' = ts /\ fts' = fts \/
              Time.lt ts ts' /\ Time.lt fts fts'):
    map_lt_inv (map_add loc ts fts f).
  Proof.
    unfold map_add. ii. des; subst; eauto; timetac.
    - exploit ADD_EX; try exact MAP1. i. des; timetac.
    - exploit ADD_EX; try exact MAP2. i. des; timetac.
  Qed.

  Lemma timemap_map_incr
        f1 f2
        (INCR: f1 <3= f2):
    timemap_map f1 <2= timemap_map f2.
  Proof.
    ii. auto.
  Qed.

  Lemma view_map_incr
        f1 f2
        (INCR: f1 <3= f2):
    view_map f1 <2= view_map f2.
  Proof.
    i. inv PR. econs; eauto using timemap_map_incr.
  Qed.

  Lemma opt_view_map_incr
        f1 f2
        (INCR: f1 <3= f2):
    opt_view_map f1 <2= opt_view_map f2.
  Proof.
    i. inv PR; econs.
    eauto using view_map_incr.
  Qed.

  Lemma message_map_incr
        f1 f2
        (INCR: f1 <3= f2):
    message_map f1 <2= message_map f2.
  Proof.
    i. inv PR. econs.
    eauto using opt_view_map_incr.
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
        (WF1: map_wf f1)
        (COMPLETE1: map_complete f1 mem1 fmem1)
        (MAP1: memory_map f1 max rsv mem1 fmem1)
        (INHABITED1: Memory.inhabited mem1)
        (ADD: Memory.add mem1 loc from to msg mem2)
        (RESERVE: rsv loc = false -> Time.lt (max loc) from):
    exists ffrom fto f2,
      (<<F2: f2 = map_add loc from ffrom (map_add loc to fto f1)>>) /\
      forall fmsg
        (FMSG_WF: Message.wf fmsg)
        (MSG_MAP: message_map f2 msg fmsg),
      exists fmem2,
        (<<FADD: Memory.add fmem1 loc ffrom fto fmsg fmem2>>) /\
        (<<WF2: map_wf f2>>) /\
        (<<COMPLETE2: map_complete f2 mem2 fmem2>>) /\
        (<<MAP2: memory_map f2 max rsv mem2 fmem2>>).
  Proof.
    inv WF1.
    exploit Memory.add_ts; eauto. intro TS.
    exploit add_cases; eauto. i. des.
    destruct (rsv loc) eqn:RSV.
    { (* reserved *)
      generalize (MAP1 loc). rewrite RSV. i. inv H.
      unguard. des.

      { (* non-latest *)
        assert (EMPTY: forall ts fts
                         (LT1: Time.lt pto ts)
                         (LT2: Time.lt ts nfrom)
                         (MAP: f1 loc ts fts),
                   False).
        { i. exploit COMPLETE1; try exact MAP. i. unguardH x0. des; subst.
          - destruct (TimeFacts.le_lt_dec to to0); cycle 1.
            { exploit PEMPTY; try exact l; try congr.
              exploit Memory.get_ts; try exact GET. i.
              des; subst; timetac. etrans; eauto.
            }
            inv l; cycle 1.
            { inv H. exploit Memory.add_get0; try exact ADD. i. des. congr. }
            destruct (TimeFacts.le_lt_dec nto to0); cycle 1.
            { exploit NEMPTY; try exact l; ss. congr. }
            exploit Memory.get_disjoint; [exact NGET|exact GET|].
            i. des; subst; timetac.
            exploit Memory.get_ts; try exact NGET. i. des; subst; timetac.
            apply (x0 nto); econs; ss; try refl.
            etrans; eauto.
          - destruct (TimeFacts.le_lt_dec to to0); cycle 1.
            { exploit PEMPTY; try exact l; try congr. }
            inv l; cycle 1.
            { inv H. exploit Memory.add_get0; try exact ADD. i. des. congr. }
            exploit NEMPTY; try exact H; try congr.
            exploit Memory.get_ts; try exact NGET. i. des; subst; timetac.
            etrans; eauto.
        }

        exploit Memory.get_ts; try exact NGET. i. des; subst; timetac.
        assert (Time.lt pto nfrom).
        { eapply TimeFacts.lt_le_lt; try exact PREV_TO. ss. }
        exploit SOUND; try exact PGET. i. des.
        rename ffrom into fpfrom, fto into fpto, fmsg into fpmsg.
        exploit SOUND; try exact NGET. i. des.
        rename ffrom into fnfrom, fto into fnto, fmsg into fnmsg.

        assert (FEMPTY: forall ts fts
                          (LT1: Time.lt fpto fts)
                          (LT2: Time.lt fts fnfrom)
                          (MAP: f1 loc ts fts),
                   False).
        { i. eapply EMPTY; try exact MAP.
          - eapply MAP_LT_INV; try exact LT1; eauto.
          - eapply MAP_LT_INV; try exact LT2; eauto.
        }

        (* find ffrom and fto *)
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
        exists ffrom, fto. esplits; [refl|]. i.

        exploit (@Memory.add_exists fmem1 loc); try exact FTS; try exact FMSG_WF.
        { ii. inv LHS. inv RHS. ss.
          exploit TimeFacts.lt_le_lt; [exact FROM1|exact TO2|]. i.
          exploit TimeFacts.lt_le_lt; [exact FROM2|exact TO1|]. i.
          clear x FROM1 TO1 FROM2 TO2.
          exploit COMPLETE; try exact GET2. i. des.
          { rewrite x3 in FFROM_OUT.
            rewrite FFROM_OUT in FTO_IN0.
            timetac.
          }
          exploit TimeFacts.le_lt_lt; [exact FPREV_FROM|exact x2|]. i.
          exploit TimeFacts.lt_le_lt; [exact x3|exact FNEXT_FROM|]. i.
          exploit MAP_LT_INV; try exact x1; try eassumption. i.
          exploit MAP_LT_INV; try exact x4; try eassumption. i.
          destruct (TimeFacts.le_lt_dec to to0); cycle 1.
          { exploit PEMPTY; try exact l; try eassumption. i. congr. }
          inv l; cycle 1.
          { exploit Memory.add_get0; try eassumption. i. des. congr. }
          destruct (TimeFacts.le_lt_dec nto to0); cycle 1.
          { exploit NEMPTY; try exact l; try eassumption. i. congr. }
          exploit Memory.get_disjoint; [exact GET|exact NGET|]. i.
          des; subst; timetac.
          apply (x7 nto); econs; ss; try refl.
          etrans; eauto.
        }
        i. des. esplits; try exact x1.

        { (* map_wf *)
          econs.
          - (* map_eq *)
            apply add_map_eq.
            { apply add_map_eq; ss. i.
              inv NEXT_FROM.
              - exfalso. eapply EMPTY; try exact MAP; ss.
              - inv H0. unguard. des. rewrite NEXT_EQ in *; ss.
                eapply MAP_EQ; try exact MAP; ss.
            }
            unfold map_add. i. des; subst; timetac.
            inv PREV_FROM.
            + exfalso. eapply EMPTY; try exact MAP; ss. 
              exploit Memory.add_ts; try exact ADD. i.
              eapply TimeFacts.lt_le_lt; try exact x2; eassumption.
            + inv H0. unguard. des. rewrite PREV_EQ in *; ss.
              eapply MAP_EQ; try exact MAP; ss.
          - (* map_eq_inv *)
            apply add_map_eq_inv.
            { apply add_map_eq_inv; ss. i.
              inv FNEXT_FROM.
              - exfalso. eapply FEMPTY; try exact MAP; ss.
              - inv H0. unguard. des. rewrite NEXT_EQ0 in *; ss.
                eapply MAP_EQ_INV; try exact MAP; ss.
            }
            unfold map_add. i. des; subst; timetac.
            inv FPREV_FROM.
            + exfalso. eapply FEMPTY; try exact MAP; ss. 
              exploit Memory.add_ts; try exact ADD. i.
              eapply TimeFacts.lt_le_lt; try exact x2; eassumption.
            + inv H0. unguard. des. rewrite PREV_EQ0 in *; ss.
              eapply MAP_EQ_INV; try exact MAP; ss.
          - (* map_lt *)
            apply add_map_lt.
            { apply add_map_lt; ss. i.
              destruct (TimeFacts.le_lt_dec ts' pto).
              { left. split.
                - eapply TimeFacts.le_lt_lt; try exact l.
                  eapply TimeFacts.le_lt_lt; eauto.
                - exploit map_le; try exact l; try eassumption. i.
                  eapply TimeFacts.le_lt_lt; try exact x2. ss.
              }
              destruct (TimeFacts.le_lt_dec nfrom ts'); cycle 1.
              { exploit EMPTY; try exact MAP; ss. }
              inv l0; cycle 1.
              { inv H0. inv NEXT_FROM.
                - right. right. split; ss.
                  exploit MAP_EQ; [|exact FROM0|exact MAP|]; ss. i. subst.
                  inv FNEXT_FROM; ss. inv H1. unguard. des.
                  rewrite NEXT_EQ0 in *; ss. timetac.
                - inv H0. right. left. split; ss.
                  unguard. des. rewrite NEXT_EQ in *; ss.
                  eapply MAP_EQ; try eassumption. ss.
              }
              right. right. split.
              - eapply TimeFacts.le_lt_lt; try exact H0; ss.
              - exploit MAP_LT; try exact H0; try eassumption. i.
                eapply TimeFacts.le_lt_lt; try exact x2; ss.
            }
            unfold map_add. i. des; subst; timetac.
            destruct (TimeFacts.le_lt_dec pto ts'); cycle 1.
            { left. split.
              - eapply TimeFacts.lt_le_lt; try exact l; ss.
              - exploit MAP_LT; try exact l; try eassumption. i.
                eapply TimeFacts.lt_le_lt; try exact x2; ss.
            }
            inv l; cycle 1.
            { inv H0. inv PREV_FROM.
              - left. split; ss.
                exploit MAP_EQ;[|exact TO|exact MAP|]; ss. i. subst.
                inv FPREV_FROM; ss. inv H1. unguard. des.
                rewrite PREV_EQ0 in *; ss. timetac.
              - inv H0. right. left. split; ss.
                unguard. des. rewrite PREV_EQ in *; ss.
                eapply MAP_EQ; try eassumption; ss.
            }
            destruct (TimeFacts.le_lt_dec nfrom ts'); cycle 1.
            { exploit EMPTY; try exact MAP; ss. }
            right. right. split.
            + eapply TimeFacts.lt_le_lt; try exact l.
              eapply TimeFacts.lt_le_lt; eauto.
            + exploit map_le; try exact l; try eassumption. i.
              eapply TimeFacts.lt_le_lt; try exact x2.
              eapply TimeFacts.lt_le_lt; eauto.
          - (* map_lt_inv *)
            apply add_map_lt_inv.
            { apply add_map_lt_inv; ss. i.
              destruct (TimeFacts.le_lt_dec fts' fpto).
              { left. split.
                - exploit map_le_inv; try exact l; try eassumption. i.
                  eapply TimeFacts.le_lt_lt; try exact x2. ss.
                - eapply TimeFacts.le_lt_lt; try exact l.
                  eapply TimeFacts.le_lt_lt; eauto.
              }
              destruct (TimeFacts.le_lt_dec fnfrom fts'); cycle 1.
              { exploit FEMPTY; try exact MAP; ss. }
              inv l0; cycle 1.
              { inv H0. inv FNEXT_FROM.
                - right. right. split; ss.
                  exploit MAP_EQ_INV; [|exact FROM0|exact MAP|]; ss. i. subst.
                  inv NEXT_FROM; ss. inv H1. unguard. des.
                  rewrite NEXT_EQ in *; ss. timetac.
                - inv H0. right. left. split; ss.
                  unguard. des. rewrite NEXT_EQ0 in *; ss.
                  eapply MAP_EQ_INV; try eassumption. ss.
              }
              right. right. split.
              - exploit MAP_LT_INV; try exact H0; try eassumption. i.
                eapply TimeFacts.le_lt_lt; try exact x2; ss.
              - eapply TimeFacts.le_lt_lt; try exact H0; ss.
            }
            unfold map_add. i. des; subst; timetac.
            destruct (TimeFacts.le_lt_dec fpto fts'); cycle 1.
            { left. split.
              - exploit MAP_LT_INV; try exact l; try eassumption. i.
                eapply TimeFacts.lt_le_lt; try exact x2; ss.
              - eapply TimeFacts.lt_le_lt; try exact l; ss.
            }
            inv l; cycle 1.
            { inv H0. inv FPREV_FROM.
              - left. split; ss.
                exploit MAP_EQ_INV;[|exact TO|exact MAP|]; ss. i. subst.
                inv PREV_FROM; ss. inv H1. unguard. des.
                rewrite PREV_EQ in *; ss. timetac.
              - inv H0. right. left. split; ss.
                unguard. des. rewrite PREV_EQ0 in *; ss.
                eapply MAP_EQ_INV; try eassumption; ss.
            }
            destruct (TimeFacts.le_lt_dec fnfrom fts'); cycle 1.
            { exploit FEMPTY; try exact MAP; ss. }
            right. right. split.
            + exploit map_le_inv; try exact l; try eassumption. i.
              eapply TimeFacts.lt_le_lt; try exact x2.
              eapply TimeFacts.lt_le_lt; eauto.
            + eapply TimeFacts.lt_le_lt; try exact l.
              eapply TimeFacts.lt_le_lt; eauto.
        }

        { (* map_complete *)
          exploit Memory.add_get0; try exact ADD. i. des.
          exploit Memory.add_get0; try exact x1. i. des.
          unfold map_add. ii. des; subst.
          - esplits; eauto. unguard. auto.
          - esplits; eauto. unguard. auto.
          - exploit COMPLETE1; try exact MAP. i. des.
            exploit Memory.add_get1; try exact GET3; eauto. i.
            exploit Memory.add_get1; try exact FGET1; eauto. i.
            esplits; try exact x2; try exact x3; eauto.
        }

        { (* memory_map *)
          ii. destruct (Loc.eq_dec loc0 loc); cycle 1.
          { destruct (MAP1 loc0).
            - econs 1.
              + instantiate (1:=fmax0). i. revert GET.
                erewrite Memory.add_o; eauto. condtac; ss.
                { des. subst. congr. }
                i. guardH o.
                exploit SOUND0; eauto. i. des.
                exploit Memory.add_get1; try exact FGET1; eauto. i.
                esplits; try exact x2; eauto using map_add_incr.
                do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
              + i. revert FGET1.
                erewrite Memory.add_o; eauto. condtac; ss.
                { des. subst. congr. }
                i. guardH o.
                exploit COMPLETE0; eauto. i. des; eauto. right.
                exploit Memory.add_get1; try exact GET; eauto. i.
                esplits; try exact x2; eauto using map_add_incr.
                do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
            - econs 2.
              + i. revert GET.
                erewrite Memory.add_o; eauto. condtac; ss.
                { des. subst. congr. }
                i. guardH o.
                exploit SOUND0; eauto. i. des.
                exploit Memory.add_get1; try exact FGET1; eauto. i.
                esplits; try exact x2; eauto using map_add_incr.
                do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
              + instantiate (1:=fmin). i. revert FGET1.
                erewrite Memory.add_o; eauto. condtac; ss.
                { des. subst. congr. }
                i. guardH o.
                exploit COMPLETE0; eauto. i. des.
                exploit Memory.add_get1; try exact GET; eauto. i.
                esplits; try exact x2; eauto using map_add_incr.
                do 2 (eapply message_map_incr; try eapply map_add_incr). ss.
          }

          subst. rewrite RSV. econs.
          { admit.
          }
          { admit.
          }
        }
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
