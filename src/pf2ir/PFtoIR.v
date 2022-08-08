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
Require Import Configuration.

Require Import PFConsistent.
Require Import FutureCertify.

Set Implicit Arguments.


Module PFtoIR.
  Variant sim_thread_sl (gl_pf gl_ir: Global.t):
    forall (sl_pf sl_ir: {lang: language & Language.state lang} * Local.t), Prop :=
    | sim_thread_sl_intro
        lang
        st_pf lc_pf
        st_ir lc_ir
        (STATE: st_pf = st_ir)
        (TVIEW: Local.tview lc_pf = Local.tview lc_ir)
        (PROMISES: Local.promises lc_pf = BoolMap.bot)
        (RESERVES: Local.reserves lc_pf = BoolMap.bot)
        (SC: Global.sc gl_pf = Global.sc gl_ir)
        (GPROMISES: Global.promises gl_pf = BoolMap.bot)
        (GRESERVES: Global.reserves gl_pf = BoolMap.bot)
        (MEMORY: Global.memory gl_pf = Global.memory gl_ir)
      : sim_thread_sl gl_pf gl_ir (existT _ lang st_pf, lc_pf) (existT _ lang st_ir, lc_ir)
  .

  Variant sim_conf: forall (c_pf c_ir: Configuration.t), Prop :=
    | sim_conf_intro
        ths_pf gl_pf
        ths_ir gl_ir
        (THS: forall tid,
            option_rel
              (sim_thread_sl gl_pf gl_ir)
              (IdentMap.find tid ths_pf)
              (IdentMap.find tid ths_ir)):
      sim_conf (Configuration.mk ths_pf gl_pf) (Configuration.mk ths_ir gl_ir)
  .
End PFtoIR.
