From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Event.

Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.

Set Implicit Arguments.


Module MemoryReorder.
  Lemma add_add
        mem0 loc1 from1 to1 msg1
        mem1 loc2 from2 to2 msg2
        mem2
        (ADD1: Memory.add mem0 loc1 from1 to1 msg1 mem1)
        (ADD2: Memory.add mem1 loc2 from2 to2 msg2 mem2):
    exists mem1',
      <<ADD1: Memory.add mem0 loc2 from2 to2 msg2 mem1'>> /\
      <<ADD2: Memory.add mem1' loc1 from1 to1 msg1 mem2>> /\
      <<LOCTS: (loc1, to1) <> (loc2, to2)>>.
  Proof.
    exploit (@Memory.add_exists mem0 loc2 from2 to2).
    { i. inv ADD2. inv ADD. eapply DISJOINT.
      etrans; [eapply Memory.add_o; eauto|]. condtac; ss; eauto.
      des. subst. exploit Memory.add_get0; eauto. i. des. congr.
    }
    { inv ADD2. inv ADD. auto. }
    { inv ADD2. inv ADD. eauto. }
    i. des.
    exploit (@Memory.add_exists mem3 loc1 from1 to1).
    { i. revert GET2. erewrite Memory.add_o; eauto. condtac; ss.
      - des. subst. i. inv GET2.
        exploit Memory.add_get0; try exact ADD2; eauto.
        inv ADD2. inv ADD. symmetry. eapply DISJOINT.
        etrans; [eapply Memory.add_o; eauto|]. condtac; ss. des; congr.
      - guardH o. i. inv ADD1. inv ADD. eapply DISJOINT; eauto.
    }
    { inv ADD1. inv ADD. auto. }
    { inv ADD1. inv ADD. eauto. }
    i. des.
    esplits; eauto; cycle 1.
    { ii. inv H.
      exploit Memory.add_get0; try exact ADD2; eauto.
      erewrite Memory.add_o; eauto. condtac; s; i; des; congr.
    }
    cut (mem4 = mem2); [by i; subst; eauto|].
    apply Memory.ext. i.
    setoid_rewrite Memory.add_o; cycle 1; eauto.
    erewrite (@Memory.add_o mem3); eauto. erewrite (@Memory.add_o mem1); eauto.
    repeat (condtac; ss). des. subst.
    exploit Memory.add_get0; try exact ADD1; eauto. i. des.
    exploit Memory.add_get0; try exact ADD2; eauto. i. des.
    congr.
  Qed.

  Lemma add_remove
        mem0 loc1 from1 to1 msg1
        mem1 loc2 from2 to2 msg2
        mem2
        (LOCTS1: (loc1, to1) <> (loc2, to2))
        (ADD1: Memory.add mem0 loc1 from1 to1 msg1 mem1)
        (REMOVE2: Memory.remove mem1 loc2 from2 to2 msg2 mem2):
    exists mem1',
      <<REMOVE1: Memory.remove mem0 loc2 from2 to2 msg2 mem1'>> /\
      <<ADD2: Memory.add mem1' loc1 from1 to1 msg1 mem2>>.
  Proof.
    exploit (@Memory.remove_exists mem0 loc2 from2 to2).
    { hexploit Memory.remove_get0; eauto.
      erewrite Memory.add_o; eauto. condtac; ss; i; des; subst; eauto. congr.
    }
    i. des.
    exploit (@Memory.add_exists mem3 loc1 from1 to1);
      try by inv ADD1; inv ADD; eauto.
    { i. revert GET2. erewrite Memory.remove_o; eauto. condtac; ss.
      inv ADD1. inv ADD. eauto.
    }
    i. des.
    cut (mem4 = mem2); [by i; subst; eauto|].
    apply Memory.ext. i.
    erewrite Memory.add_o; eauto. erewrite Memory.remove_o; eauto.
    erewrite (@Memory.remove_o mem2); eauto. erewrite (@Memory.add_o mem1); eauto.
    repeat (condtac; ss). des. repeat subst. congr.
  Qed.

  Lemma add_remove_same
        mem0 loc1 from1 to1 msg1
        mem1 from2 msg2
        mem2
        (ADD1: Memory.add mem0 loc1 from1 to1 msg1 mem1)
        (REMOVE2: Memory.remove mem1 loc1 from2 to1 msg2 mem2):
    from1 = from2 /\ msg1 = msg2 /\ mem0 = mem2.
  Proof.
    exploit Memory.add_get0; eauto. i. des.
    exploit Memory.remove_get0; eauto. i. des.
    rewrite GET0 in *. inv GET1. splits; auto.
    apply Memory.ext. i.
    erewrite (@Memory.remove_o mem2); eauto. condtac; ss.
    - des. subst. ss.
    - erewrite (@Memory.add_o mem1); eauto. condtac; ss.
  Qed.

  Lemma remove_add
        mem0 loc1 from1 to1 msg1
        mem1 loc2 from2 to2 msg2
        mem2
        mem1'
        (REMOVE1: Memory.remove mem0 loc1 from1 to1 msg1 mem1)
        (ADD2: Memory.add mem1 loc2 from2 to2 msg2 mem2)
        (ADD1: Memory.add mem0 loc2 from2 to2 msg2 mem1'):
    Memory.remove mem1' loc1 from1 to1 msg1 mem2.
  Proof.
    exploit Memory.remove_get0; try eexact REMOVE1; eauto. i. des.
    exploit (@Memory.remove_exists mem1' loc1 from1 to1 msg1); eauto.
    { erewrite Memory.add_o; eauto. condtac; ss; eauto.
      des. subst. exploit Memory.add_get0; eauto. i. des. congr.
    }
    i. des.
    cut (mem3 = mem2); [by i; subst|].
    apply Memory.ext. i.
    erewrite Memory.remove_o; eauto. erewrite Memory.add_o; eauto.
    erewrite (@Memory.add_o mem2); eauto. erewrite (@Memory.remove_o mem1); eauto.
    repeat (condtac; ss). des. subst. subst.
    exploit Memory.add_get0; try eexact ADD1; eauto. i. des. congr.
  Qed.

  Lemma remove_remove
        promises0 loc1 from1 to1 msg1
        promises1 loc2 from2 to2 msg2
        promises2
        (REMOVE1: Memory.remove promises0 loc1 from1 to1 msg1 promises1)
        (REMOVE2: Memory.remove promises1 loc2 from2 to2 msg2 promises2):
    exists promises1',
      <<REMOVE1: Memory.remove promises0 loc2 from2 to2 msg2 promises1'>> /\
      <<REMOVE2: Memory.remove promises1' loc1 from1 to1 msg1 promises2>>.
  Proof.
    exploit Memory.remove_get0; try apply REMOVE2; eauto. i. des.
    revert GET. erewrite Memory.remove_o; eauto. condtac; ss. guardH o. i.
    exploit Memory.remove_exists; eauto. i. des.
    hexploit Memory.remove_get0; try apply REMOVE1; eauto. i. des.
    exploit (@Memory.remove_exists mem2 loc1 from1 to1 msg1); eauto.
    { erewrite Memory.remove_o; eauto. condtac; ss. des. subst. congr. }
    i. des.
    esplits; eauto.
    cut (mem0 = promises2); [by i; subst|].
    apply Memory.ext. i.
    erewrite Memory.remove_o; eauto. erewrite Memory.remove_o; eauto.
    erewrite (@Memory.remove_o promises2); eauto. erewrite (@Memory.remove_o promises1); eauto.
    repeat (condtac; ss).
  Qed.
End MemoryReorder.
