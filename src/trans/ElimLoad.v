From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Language.
From PromisingLib Require Import Event.

Require Import Time.
Require Import View.
Require Import BoolMap.
Require Import Promises.
Require Import Cell.
Require Import Memory.
Require Import Global.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import Progress.

Require Import SimLocal.
Require Import SimMemory.
Require Import SimGlobal.
Require Import SimThread.
Require Import Compatibility.

Require Import ITreeLang.
Require Import ITreeLib.

Set Implicit Arguments.


(* NOTE: Elimination of a unused relaxed load is unsound under the
 * liveness-aware semantics.  Consider the following example:

    while (!y_plain) {
        r = x_rlx;
        fence(acquire);
    }

    ||

    y =rlx 1;
    x =rel 1;

 * Under the liveness-aware semantics, the loop *should* break, as
 * once `x_rlx` will read `x =rel 1` and the acquire fence guarantees
 * that `y_plain` will read 1.  However, the elimination of
 * `x_rlx` will allow the loop to run forever.
 *)

Lemma elim_load_sim_itree
      loc ord
      (ORD: Ordering.le ord Ordering.plain):
  sim_itree (fun _ _ => True)
            (ITree.trigger (MemE.read loc ord);; Ret tt)
            (Ret tt).
Proof.
  unfold trigger. rewrite bind_vis.
  pcofix CIH. ii. subst. pfold. ii. splits; i.
  { right.
    exploit progress_read_step_plain; try exact LC_WF_SRC; eauto. i. des.
    esplits.
    - econs 2; [|refl]. econs.
      + econs 2; [|econs 2]; eauto. econs. refl.
      + ss.
    - ss.
    - rewrite bind_ret_l. ss.
    - ss.
    - rewrite bind_ret_l. econs; eauto.
  }
  { i. right. esplits; eauto.
    inv LOCAL. congr.
  }
  ii. right.
  inv STEP_TGT; [|inv STATE].
  exploit sim_local_internal; eauto. i. des.
  esplits; try apply GL2; eauto. inv LOCAL0; ss.
Qed.
