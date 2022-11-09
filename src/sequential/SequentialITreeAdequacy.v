From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.

From PromisingLib Require Import Event.
Require Import Configuration.
Require Import Behavior.

Require Import ITreeLang.
Require Import Sequential.
Require Import SequentialITree.
Require Import SequentialCompatibility.
Require Import SequentialAdequacy.

Set Implicit Arguments.


Section ADEQUACY.
  Theorem sequential_adequacy_context A B
          (prog_src prog_tgt: (lang A).(Language.syntax))
          (SIM: sim_seq_itree eq prog_src prog_tgt)
          (ctx_seq: itree MemE.t A -> itree MemE.t B)
          (ctx_ths: Threads.syntax) (tid: Ident.t)
          (CTX: @itree_context A B ctx_seq)
    :
      behaviors
        Configuration.step
        (Configuration.init (IdentMap.add tid (existT _ (lang B) (ctx_seq prog_tgt)) ctx_ths))
      <2=
      behaviors
        Configuration.step
        (Configuration.init (IdentMap.add tid (existT _ (lang B) (ctx_seq prog_src)) ctx_ths)).
  Proof.
    eapply sequential_adequacy_concurrent_context; auto.
    esplits. hexploit itree_sim_seq_context; eauto. ii. eapply H.
  Qed.
End ADEQUACY.
