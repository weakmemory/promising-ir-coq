Require Import Program.
From sflib Require Import sflib.
From Paco Require Import paco.
From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Event.

Require Import Sequential.

Set Implicit Arguments.

Module CertOracle.
  Definition t := Loc.t -> Const.t.

  Definition output (e: ProgramEvent.t): Oracle.output :=
    Oracle.mk_output
      (if is_accessing e then Some Perm.high else None)
      (if is_acquire e then Some (fun _ => Perm.low, fun _ => Const.undef) else None)
      (if is_release e then Some (fun _ => Perm.high) else None)
  .

  Variant step (e: ProgramEvent.t) (i: Oracle.input) (o: Oracle.output) (vs: t): t -> Prop :=
    | step_read
        loc ord
        (EVENT: e = ProgramEvent.read loc (vs loc) ord)
        (INPUT: Oracle.wf_input e i)
        (OUTPUT: o = output e)
      :
      step e i o vs vs
    | step_write
        loc val ord
        (EVENT: e = ProgramEvent.write loc val ord)
        (INPUT: Oracle.wf_input e i)
        (OUTPUT: o = output e)
      :
      step e i o vs (fun loc0 => if Loc.eq_dec loc0 loc then val else vs loc0)
    | step_update
        loc valw ordr ordw
        (EVENT: e = ProgramEvent.update loc (vs loc) valw ordr ordw)
        (INPUT: Oracle.wf_input e i)
        (OUTPUT: o = output e)
      :
      step e i o vs (fun loc0 => if Loc.eq_dec loc0 loc then valw else vs loc0)
    | step_fence
        ordr ordw
        (EVENT: e = ProgramEvent.fence ordr ordw)
        (INPUT: Oracle.wf_input e i)
        (OUTPUT: o = output e)
      :
      step e i o vs vs
    | step_syscall
        ev
        (EVENT: e = ProgramEvent.syscall ev)
        (INPUT: Oracle.wf_input e i)
        (OUTPUT: o = output e)
      :
      step e i o vs vs
  .

  Definition to_oracle (vs: t): Oracle.t := @Oracle.mk t step vs.

  Lemma to_oracle_wf vs: Oracle.wf (to_oracle vs).
  Proof.
    revert vs. pcofix CIH. i. pfold. econs.
    { i. dependent destruction STEP. inv STEP.
      { splits; auto. red. splits; ss; des_ifs. }
      { splits; auto. red. splits; ss; des_ifs. }
      { splits; auto. red. splits; ss; des_ifs. }
      { splits; auto. red. splits; ss; des_ifs. }
      { splits; auto. red. splits; ss; des_ifs. }
    }
    { i. exists (vs loc). splits.
      { econs. esplits.
        { econs. eapply step_read; eauto. }
        { red. splits; ss; des_ifs. }
      }
      { i. econs. esplits.
        { econs. eapply step_update; eauto. }
        { red. splits; ss; des_ifs. }
      }
    }
    { i. econs. esplits.
      { econs. eapply step_write; eauto. }
      { red. splits; ss; des_ifs. }
    }
    { i. econs. esplits.
      { econs. eapply step_fence; eauto. }
      { red. splits; ss; des_ifs. }
    }
    { i. econs. esplits.
      { econs. eapply step_syscall; eauto. }
      { red. splits; ss; des_ifs. }
    }
  Qed.
End CertOracle.
