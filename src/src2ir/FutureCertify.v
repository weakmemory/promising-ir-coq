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
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Global.
Require Import Local.
Require Import Thread.

Require Import Cover.
Require Import Mapping.
Require Import PFConsistent.
Require Import Certify.

Require Import SrcToIRThread.

Set Implicit Arguments.


Module FutureCertify.
Section FutureCertify.
  Variable lang: language.

  Lemma future_get_inv
        mem1 mem2
        loc from to msg
        (FUTURE: Memory.future mem1 mem2)
        (GET2: Memory.get loc to mem2 = Some (from, msg)):
    forall f m
           (GET1: Memory.get loc to mem1 = Some (f, m)),
      f = from /\ m = msg \/ m = Message.reserve.
  Proof.
    induction FUTURE; i.
    { rewrite GET1 in *. inv GET2. auto. }
    destruct m; auto.
    exploit Memory.future_get1; try exact GET1.
    { econs 2; try exact H. refl. }
    i. des.
    exploit IHFUTURE; eauto.
  Qed.

  Lemma future_get
        rsv mem1 mem2
        loc from to msg
        (FUTURE: Memory.messages_le mem1 mem2)
        (LE1: Memory.le rsv mem1)
        (LE2: Memory.le rsv mem2)
        (GET1: Memory.get loc to mem1 = Some (from, msg))
        (MSG: msg <> Message.reserve \/
                exists f m, Memory.get loc to rsv = Some (f, m)):
    Memory.get loc to mem2 = Some (from, msg).
  Proof.
    des.
    - destruct msg; ss. eauto.
    - exploit LE1; eauto. i.
      rewrite x0 in GET1. inv GET1. eauto.
  Qed.

  Lemma map_get_merge
        rsv mem loc ts
        (LE: Memory.le rsv mem)
        (GET: (exists from to val released na,
                  Memory.get loc to mem = Some (from, Message.message val released na) /\
                  __guard__ (ts = from \/ ts = to)) \/
              (exists from to msg,
                  Memory.get loc to rsv = Some (from, msg) /\
                   __guard__ (ts = from \/ ts = to))):
    exists from to msg,
      Memory.get loc to mem = Some (from, msg) /\
      __guard__ (ts = from \/ ts = to).
  Proof.
    des; eauto. exploit LE; eauto.
  Qed.

  Lemma future_map
        rsv mem mem_future fmem
        mem_cap
        (ONLY: Memory.reserve_only rsv)
        (LE: Memory.le rsv mem)
        (CLOSED: Memory.closed mem)
        (FUTURE: Memory.messages_le mem mem_future)
        (FUTURE_LE: Memory.le rsv mem_future)
        (SIM: SrcToIRThread.sim_memory fmem mem_future)
        (CAP: Memory.cap mem mem_cap):
    exists f,
      (<<F: f = fun loc ts fts =>
                  ts = fts /\
                  ((exists from to val released na,
                       Memory.get loc to mem = Some (from, Message.message val released na) /\
                       __guard__ (ts = from \/ ts = to)) \/
                   (exists from to msg,
                       Memory.get loc to rsv = Some (from, msg) /\
                       __guard__ (ts = from \/ ts = to))) \/
                  ts = Time.incr (Memory.max_ts loc mem) /\
                  fts = Time.join
                          (Time.incr (Memory.max_ts loc mem))
                          (Time.incr (Memory.max_ts loc fmem))>>) /\
      (<<MAP_WF: map_wf f>>) /\
      (<<MAP: memory_map f rsv mem_cap fmem>>).
  Proof.
    esplits; [refl|..].
    { (* map_wf *)
      econs; ii; subst.
      { left. splits; ss. left.
        esplits; try eapply CLOSED; ss. left. ss.
      }
      { exists ((Time.incr (Memory.max_ts loc mem)) ::
                (List.concat
                   (List.map (fun e => [fst e; fst (snd e)]) (DOMap.elements (Cell.raw (mem loc)))))).
        i. des.
        - right. exploit DOMap.elements_correct; eauto. i.
          remember (DOMap.elements (Cell.raw (mem loc))) as l.
          clear - l x0 MAP1.
          revert ts from to val released na MAP1 x0.
          induction l; ss; i. des; eauto.
          subst. ss. unguard. des; auto.
        - right. exploit LE; eauto. i. clear MAP0.
          exploit DOMap.elements_correct; eauto. i.
          remember (DOMap.elements (Cell.raw (mem loc))) as l.
          clear - l x1 MAP1.
          revert ts from to msg MAP1 x1.
          induction l; ss; i. des; eauto.
          subst. ss. unguard. des; auto.
        - left. subst. ss.
      }
      { inv MAP1; inv MAP2; try by (des; subst; ss).
        - exfalso.
          inv H. exploit map_get_merge; try exact H2; ss. i. clear H2. des. subst.
          exploit Memory.max_ts_spec; eauto. i. des. clear GET.
          unguard. des; subst.
          + exploit Memory.get_ts; eauto. i. des.
            { exploit Time.incr_spec. rewrite x1. i. timetac. }
            eapply Time.lt_strorder.
            etrans; [|exact x1].
            eapply TimeFacts.le_lt_lt; [|apply Time.incr_spec]. ss.
          + eapply Time.lt_strorder.
            eapply TimeFacts.le_lt_lt; eauto. apply Time.incr_spec.
        - exfalso.
          inv H0. exploit map_get_merge; try exact H2; ss. i. clear H2. des. subst.
          exploit Memory.max_ts_spec; eauto. i. des. clear GET.
          unguard. des; subst.
          + exploit Memory.get_ts; eauto. i. des.
            { exploit Time.incr_spec. rewrite x1. i. timetac. }
            eapply Time.lt_strorder.
            etrans; [|exact x1].
            eapply TimeFacts.le_lt_lt; [|apply Time.incr_spec]. ss.
          + eapply Time.lt_strorder.
            eapply TimeFacts.le_lt_lt; eauto. apply Time.incr_spec.
      }
      { inv MAP1; inv MAP2; try by (des; subst; ss).
        - exfalso. inv H. inv H0.
          exploit map_get_merge; try exact H2; ss. i. clear H2. des.
          exploit Memory.max_ts_spec; eauto. i. des.
          unguard. des; subst.
          + eapply Time.lt_strorder.
            eapply TimeFacts.le_lt_lt; try exact MAX.
            exploit Memory.get_ts; try exact x0. i. des.
            { rewrite x2, <- x1.
              eapply TimeFacts.lt_le_lt; [|apply Time.join_l].
              apply Time.incr_spec.
            }
            etrans; eauto.
            eapply TimeFacts.lt_le_lt; [|apply Time.join_l].
            apply Time.incr_spec.
          + eapply Time.lt_strorder.
            eapply TimeFacts.le_lt_lt; try exact MAX.
            eapply TimeFacts.lt_le_lt; [|apply Time.join_l].
            apply Time.incr_spec.
        - exfalso. inv H. inv H0.
          exploit map_get_merge; try exact H1; ss. i. clear H1. des.
          exploit Memory.max_ts_spec; eauto. i. des.
          unguard. des; subst.
          + eapply Time.lt_strorder.
            eapply TimeFacts.le_lt_lt; try exact MAX.
            exploit Memory.get_ts; try exact x0. i. des.
            { rewrite x2, <- x1.
              eapply TimeFacts.lt_le_lt; [|apply Time.join_l].
              apply Time.incr_spec.
            }
            etrans; eauto.
            eapply TimeFacts.lt_le_lt; [|apply Time.join_l].
            apply Time.incr_spec.
          + eapply Time.lt_strorder.
            eapply TimeFacts.le_lt_lt; try exact MAX.
            eapply TimeFacts.lt_le_lt; [|apply Time.join_l].
            apply Time.incr_spec.
      }
      { inv MAP1; inv MAP2; try by (des; subst; ss).
        - inv H. inv H0.
          exploit map_get_merge; try exact H2; ss. i. clear H2. des.
          exploit Memory.max_ts_spec; eauto. i. des. clear GET.
          unguard. des; subst.
          + exploit Memory.get_ts_le; eauto. i.
            ett; try exact x1.
            ett; try exact MAX.
            tet; try apply Time.join_l.
            apply Time.incr_spec.
          + ett; try exact MAX.
            tet; try apply Time.join_l.
            apply Time.incr_spec.
        - exfalso. inv H. inv H0.
          exploit map_get_merge; try exact H1; ss. i. clear H1. des.
          exploit Memory.max_ts_spec; eauto. i. des. clear GET.
          unguard. des; subst.
          + exploit Memory.get_ts_le; eauto. i.
            eapply Time.lt_strorder.
            ett; try exact x1.
            ett; try exact MAX.
            etrans; eauto.
            apply Time.incr_spec.
          + eapply Time.lt_strorder.
            ett; try exact MAX.
            etrans; eauto.
            apply Time.incr_spec.
        - des. subst. timetac.
      }
      { inv MAP1; inv MAP2; try by (des; subst; ss).
        - inv H. inv H0.
          exploit map_get_merge; try exact H2; ss. i. clear H2. des.
          exploit Memory.max_ts_spec; eauto. i. des. clear GET.
          unguard. des; subst.
          + exploit Memory.get_ts_le; eauto. i.
            ett; try exact x1.
            ett; try exact MAX.
            apply Time.incr_spec.
          + ett; try exact MAX.
            apply Time.incr_spec.
        - exfalso. inv H. inv H0.
          exploit map_get_merge; try exact H1; ss. i. clear H1. des.
          exploit Memory.max_ts_spec; eauto. i. des. clear GET.
          unguard. des; subst.
          + exploit Memory.get_ts_le; eauto. i.
            eapply Time.lt_strorder.
            ett; try exact x1.
            ett; try exact MAX.
            etrans; eauto.
            tet; try apply Time.incr_spec.
            apply Time.join_l.
          + eapply Time.lt_strorder.
            ett; try exact MAX.
            etrans; eauto.
            tet; try apply Time.incr_spec.
            apply Time.join_l.
        - des. subst. timetac.
      }
    }

    { (* memory_map *)
      econs; i.
      { destruct msg; auto. right.
        exploit Memory.cap_inv; try exact GET; eauto. i. des; ss.
        exploit Memory.future_get1; try exact x0; eauto. i. des.
        inv SIM. exploit COMPLETE; eauto. i.
        esplits; try exact x2.
        - left. splits; ss.
          left. esplits; eauto. left. ss.
        - left. splits; ss.
          left. esplits; eauto. right. ss.
        - inv CLOSED. exploit CLOSED0; eauto. i. des.
          eapply closed_message_map; eauto. i.
          left. splits; ss.
          left. esplits; eauto. right. ss.
      }

      { destruct fmsg; cycle 1.
        { inv SIM. exploit GRESERVES; eauto. ss. }
        inv SIM. exploit SOUND; eauto. intro GET_FUTURE.
        specialize (Memory.min_exists
                      (fun to =>
                         Time.le fto to /\
                         (exists from msg,
                             Memory.get loc to mem = Some (from, msg) /\
                             __guard__ (
                                 msg <> Message.reserve \/
                                 exists f m, Memory.get loc to rsv = Some (f, m))))
                      loc mem). i. des.
        { (* future message after lastest *)
          specialize (Memory.max_exists
                        (fun to =>
                           (exists from msg,
                             Memory.get loc to mem = Some (from, msg) /\
                             __guard__ (
                                 msg <> Message.reserve \/
                                 exists f m, Memory.get loc to rsv = Some (f, m))))
                        loc mem). i. des.
          { exfalso. eapply NONE0; try apply CLOSED.
            esplits; try apply CLOSED. left. ss.
          }
          rewrite SAT in GET. inv GET.
          destruct (TimeFacts.le_lt_dec fto to_max).
          { exploit NONE; try exact SAT; ss. esplits; eauto. }
          exists to_max.
          exists (Time.join
                    (Time.incr (Memory.max_ts loc mem))
                    (Time.incr (Memory.max_ts loc fmem))).
          exists to_max.
          exists (Time.incr (Memory.max_ts loc mem)).
          splits.
          - exploit future_get; try exact SAT; eauto. i.
            exploit Memory.lt_get; try exact l; try exact x0; eauto.
          - exploit Memory.max_ts_spec; try exact FGET. i. des.
            etrans; eauto. etrans; [|apply Time.join_r].
            econs. apply Time.incr_spec.
          - left. split; ss. unguard. des.
            + left. destruct msg_max; ss. esplits; try exact SAT. auto.
            + right. esplits; try exact SAT0. auto.
          - right. ss.
          - i. eapply cap_covered; eauto.
            eapply Interval.le_mem; try exact ITV.
            econs; s; try refl. apply Time.bot_spec.
          - i. exploit LE; try exact GET. i.
            exploit MAX; try exact x0.
            { esplits; try exact x0. right. eauto. }
            ii. inv LHS. inv RHS. ss.
            exploit TimeFacts.lt_le_lt; try exact FROM0; try exact TO. i. timetac.
        }

        (* future message before latest *)
        rewrite SAT0 in GET. inv GET. inv SAT; cycle 1.
        { inv H. exploit future_get; try exact SAT0; eauto. i.
          exploit SOUND; eauto. i.
          rewrite x0 in *. inv x1.
          unguard. des; cycle 1.
          { exploit ONLY; eauto. i. subst.
            exploit LE; eauto. i. congr.
          }
          esplits; [refl|refl|..].
          - left. split; try refl. left. esplits; eauto.
          - left. split; try refl. left. esplits; eauto.
          - inv CAP. exploit SOUND0; eauto. i. econs; eauto.
          - i. exploit ONLY; eauto. i. subst.
            exploit LE; eauto. i.
            exploit Memory.get_disjoint; [exact x1|exact SAT0|]. i. des; ss.
        }
        exploit Memory.lt_get; try apply H; i.
        { eapply SOUND; eauto. }
        { eapply future_get; eauto. }
        specialize (Memory.max_exists
                      (fun to =>
                         Time.lt to fto /\
                         (exists from msg,
                             Memory.get loc to mem = Some (from, msg) /\
                             __guard__ (
                                 msg <> Message.reserve \/
                                 exists f m, Memory.get loc to rsv = Some (f, m))))
                      loc mem). i. des.
        { exfalso.
          destruct (Time.eq_dec fto Time.bot); subst.
          - exploit MIN; try apply CLOSED.
            { esplits; try refl; try apply CLOSED. left. ss. }
            i. exploit TimeFacts.lt_le_lt; try exact H; try exact x1. timetac.
          - eapply NONE; try apply CLOSED.
            esplits; try apply CLOSED; try (left; ss).
            specialize (Time.bot_spec fto). i. inv H0; ss. congr.
        }
        rewrite SAT2 in GET. inv GET; i.
        exploit Memory.lt_get; try exact SAT.
        { eapply future_get; try exact SAT2; eauto. }
        { eapply SOUND; eauto. }
        exists to_max, from_min, to_max, from_min.
        splits; ss.
        - left. split; ss. unguardH SAT3. des.
          + left. destruct msg_max; ss.
            esplits; try exact SAT2. right. ss.
          + right. esplits; try exact SAT3. right. ss.
        - left. split; ss. unguardH SAT1. des.
          + left. destruct msg_min; ss.
            esplits; try exact SAT0. left. ss.
          + exploit LE; eauto. i.
            rewrite x2 in *. inv SAT0.
            right. esplits; try exact SAT1. left. ss.
        - i. eapply cap_covered; eauto.
          eapply Interval.le_mem; try exact ITV.
          econs; s; try apply Time.bot_spec.
          exploit Memory.max_ts_spec; try exact SAT0. i. des.
          etrans; [|econs; apply Time.incr_spec].
          etrans; try exact MAX0.
          exploit Memory.get_ts; try exact SAT0. i. des; timetac.
        - ii. inv LHS. inv RHS. ss.
          exploit LE; eauto. i.
          destruct (TimeFacts.le_lt_dec fto t).
          + exploit MIN; try exact x3.
            { split; ss. esplits; eauto. right. eauto. }
            i. inv x4.
            * exploit Memory.lt_get; try exact H0; eauto. i.
              exploit TimeFacts.lt_le_lt; try exact FROM; try exact TO0. i.
              exploit Memory.get_ts; try exact SAT0. i. des; timetac.
              rewrite x6 in x5. timetac.
            * inv H0. rewrite x3 in *. inv SAT0. timetac.
          + exploit MAX; try exact x3.
            { split; ss. esplits; eauto. right. eauto. }
            i. exploit TimeFacts.lt_le_lt; try exact FROM0; try exact TO. i. timetac.
      }
    }
  Qed.

  Lemma future_certify
        fth
        th loc mem_future
        (STATE: Thread.state th = Thread.state fth)
        (TVIEW: Local.tview (Thread.local th) = Local.tview (Thread.local fth))
        (FPROMISES: Local.promises (Thread.local fth) = BoolMap.bot)
        (FUTURE: Memory.messages_le (Global.memory (Thread.global th)) mem_future)
        (SIM: SrcToIRThread.sim_memory (Global.memory (Thread.global fth)) mem_future)
        (LC_WF: Local.wf (Thread.local th) (Thread.global th))
        (GL_WF: Global.wf (Thread.global th))
        (LE_FUTURE: Memory.le (Local.reserves (Thread.local th)) mem_future)
        (FLC_WF: Local.wf (Thread.local fth) (Thread.global fth))
        (FGL_WF: Global.wf (Thread.global fth))
        (CERTIFY: certify loc (Thread.cap_of th)):
    @pf_certify lang loc fth.
  Proof.
    exploit Thread.cap_wf; try exact LC_WF; eauto. i. des.
    exploit future_map; try exact FUTURE; try exact SIM;
      try apply LC_WF; try apply GL_WF; ss.
    { apply Memory.cap_of_cap. }
    i. des.
    eapply map_certify; try exact CERTIFY; eauto.
    econs; ss.
    econs. rewrite <- TVIEW.
    eapply closed_tview_map; try apply LC_WF; eauto.
    i. subst. left. split; ss.
    left. esplits; eauto. right. ss.
  Qed.
End FutureCertify.
End FutureCertify.
