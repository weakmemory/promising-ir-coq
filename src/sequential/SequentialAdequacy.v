From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.

From PromisingLib Require Import Event.
Require Import Configuration.
Require Import Behavior.

Require Import Sequential.
Require Import SequentialBehavior.
Require Import SequentialRefinement.
Require Import Program.

Set Implicit Arguments.


Section ADEQUACY.
  Theorem sequential_adequacy (progs_src progs_tgt: Threads.syntax)
          (SIM: forall tid,
              option_rel
                (fun '(existT _ lang_src prog_src) '(existT _ lang_tgt prog_tgt) =>
                   exists sim_ret, @sim_seq_all
                                     _ _ sim_ret
                                     (lang_src.(Language.init) prog_src)
                                     (lang_tgt.(Language.init) prog_tgt))
                (IdentMap.find tid progs_src)
                (IdentMap.find tid progs_tgt))
    :
      behaviors
        Configuration.step
        (Configuration.init progs_tgt)
      <2=
      behaviors
        Configuration.step
        (Configuration.init progs_src).
  Proof.
    (* to be ported from promising-seq-coq project *)
  Admitted.

  Theorem sequential_adequacy_concurrent_context
          (ctx: Threads.syntax) (tid: Ident.t)
          (lang_src: language) (prog_src: lang_src.(Language.syntax))
          (lang_tgt: language) (prog_tgt: lang_tgt.(Language.syntax))
          (SIM: exists sim_ret, @sim_seq_all
                                  _ _ sim_ret
                                  (lang_src.(Language.init) prog_src)
                                  (lang_tgt.(Language.init) prog_tgt))
    :
      behaviors
        Configuration.step
        (Configuration.init (IdentMap.add tid (existT _ lang_tgt prog_tgt) ctx))
      <2=
      behaviors
        Configuration.step
        (Configuration.init (IdentMap.add tid (existT _ lang_src prog_src) ctx)).
  Proof.
    eapply sequential_adequacy.
    { i. rewrite ! IdentMap.gsspec. des_ifs; ss.
      destruct (IdentMap.find tid0 ctx) as [[lang prog]|]; ss.
      esplits. eapply sim_seq_all_refl.
    }
  Qed.

  Theorem sequential_refinement_adequacy_concurrent_context
          (ctx: Threads.syntax) (tid: Ident.t)
          (lang_src: language) (prog_src: lang_src.(Language.syntax))
          (lang_tgt: language) (prog_tgt: lang_tgt.(Language.syntax))
          (REFINE: SeqBehavior.refine _ _ (lang_tgt.(Language.init) prog_tgt) (lang_src.(Language.init) prog_src))
          (DETERM: deterministic _ (lang_src.(Language.init) prog_src))
          (RECEPTIVE: receptive _ (lang_tgt.(Language.init) prog_tgt))
          (MONOTONE: monotone_read_state lang_src (lang_src.(Language.init) prog_src))
    :
      behaviors
        Configuration.step
        (Configuration.init (IdentMap.add tid (existT _ lang_tgt prog_tgt) ctx))
      <2=
      behaviors
        Configuration.step
        (Configuration.init (IdentMap.add tid (existT _ lang_src prog_src) ctx)).
  Proof.
    eapply sequential_adequacy_concurrent_context; eauto.
    esplits. eapply refinement_implies_simulation; eauto.
  Qed.
End ADEQUACY.
