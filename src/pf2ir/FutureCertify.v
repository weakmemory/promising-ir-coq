Require Import RelationClasses.

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


Module FutureCertify.
  Let map_t: Type := Loc.t -> Time.t -> Time.t -> Prop.

  Section FutureCertify.
    Variable f: map_t.

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
          f mem fmem
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
        memory_map_loc loc max false mem fmem
      | memory_map_loc_non_reserved
          f mem fmem
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
End FutureCertify.
