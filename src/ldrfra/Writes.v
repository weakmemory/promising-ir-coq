Require Import Lia.
Require Import Bool.
Require Import RelationClasses.

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

Require Import OrdStep.

Set Implicit Arguments.


Module Writes.
  Section Writes.
    Variable L: Loc.t -> bool.

    Definition t: Type := list (Loc.t * Time.t * Ordering.t).

    Definition append (e: ThreadEvent.t) (rels: t): t :=
      match ThreadEvent.is_writing e with
      | Some (loc, from, to, val, released, ord) =>
        if L loc
        then (loc, to, ord) :: rels
        else rels
      | None => rels
      end.

    Variant wf (rels: t) (mem: Memory.t): Prop :=
    | wf_intro
        (SOUND: forall loc to ord (IN: List.In (loc, to, ord) rels),
            L loc /\
            exists from val released na,
              Memory.get loc to mem = Some (from, Message.message val released na))
        (COMPLETE: forall loc from to val released na
                     (LOC: L loc)
                     (TO: to <> Time.bot)
                     (GET: Memory.get loc to mem = Some (from, Message.message val released na)),
            exists ord, List.In (loc, to, ord) rels)
    .

    Lemma append_app e rels1 rels2:
      append e rels1 ++ rels2 = append e (rels1 ++ rels2).
    Proof.
      unfold append. des_ifs.
    Qed.

    Lemma add_wf
          ord
          rels mem1 loc from to msg mem2
          (RELS1: wf rels mem1)
          (MSG: L loc -> exists val released na, msg = Message.message val released na)
          (ADD: Memory.add mem1 loc from to msg mem2):
      wf (if L loc then (loc, to, ord) :: rels else rels) mem2.
    Proof.
      condtac; cycle 1.
      { inv RELS1. econs; i.
        - exploit SOUND; eauto. i. des. splits; ss.
          erewrite Memory.add_o; eauto.
          condtac; ss; eauto. des. subst. congr.
        - revert GET. erewrite Memory.add_o; eauto.
          condtac; ss; eauto. des. subst. congr.
      }
      inv RELS1. econs; i.
      { inv IN.
        { clarify. split; ss.
          exploit MSG; eauto. i. des. subst.
          exploit Memory.add_get0; eauto. i. des. eauto.
        }
        exploit SOUND; eauto. i. des. split; ss.
        exploit Memory.add_get1; try exact x1; eauto.
      }
      { revert GET. erewrite Memory.add_o; eauto. condtac; ss.
        - i. des. clarify. eauto.
        - guardH o. i.
          exploit COMPLETE; eauto. i. des.
          esplits; eauto.
      }
    Qed.

    Lemma add_wf_other
          rels mem1 loc from to msg mem2
          (RELS1: wf rels mem1)
          (LOC: ~ L loc)
          (ADD: Memory.add mem1 loc from to msg mem2):
      wf rels mem2.
    Proof.
      exploit (@add_wf Ordering.na); try exact ADD; eauto; ss.
      condtac; ss.
    Qed.

    Lemma step_wf
          ordcr ordcw rels lang e e1 e2
          (RELS1: wf rels (Global.memory (Thread.global e1)))
          (STEP: @OrdThread.step lang L ordcr ordcw e e1 e2):
      wf (append e rels) (Global.memory (Thread.global e2)).
    Proof.
      unfold append.
      inv STEP; inv LOCAL; try inv LOCAL0; ss.
      - inv STEP. ss. eapply add_wf; eauto.
      - inv LOCAL1. inv STEP. inv LOCAL2. inv STEP. ss.
        eapply add_wf; eauto.
    Qed.
  End Writes.
End Writes.
