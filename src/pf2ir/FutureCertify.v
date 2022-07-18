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
  Section FutureCertify.
    Let map_t: Type := Loc.t -> Time.t -> Time.t -> Prop.

    Definition timemap_map (f: map_t) (tm ftm: TimeMap.t): Prop :=
      forall loc, f loc (tm loc) (ftm loc).

    Variant view_map (f: map_t) (view fview: View.t): Prop :=
      | view_map_intro
          (RLX: timemap_map f view.(View.rlx) (fview.(View.rlx)))
          (PLN: timemap_map f view.(View.pln) (fview.(View.pln)))
    .

    Variant opt_view_map (f: map_t): forall (view fview: option View.t), Prop :=
      | opt_view_map_None:
        opt_view_map f None None
      | opt_view_map_Some
          view fview
          (VIEW: view_map f view fview):
        opt_view_map f (Some view) (Some fview)
    .

    Variant message_map (f: map_t): forall (msg fmsg: Message.t), Prop :=
      | message_map_intro
          val view fview na
          (RELEASED: opt_view_map f view fview):
        message_map f (Message.mk val view na) (Message.mk val fview na)
    .

    Variant memory_map_loc (loc: Loc.t) (max: Time.t):
      forall (rsv: bool) (f: map_t) (mem fmem: Memory.t), Prop :=
      | memory_map_loc_non_reserved
          f mem fmem
          fmax
          (SOUND: forall from to msg (GET: Memory.get loc to mem = Some (from, msg)),
            exists ffrom fto fmsg,
              (<<FGET: Memory.get loc fto fmem = Some (ffrom, fmsg)>>) /\
              (<<FROM: f loc from ffrom>>) /\
              (<<TO: f loc to fto>>) /\
              (<<MSG: message_map f msg fmsg>>))
          (COMPLETE: forall ffrom fto fmsg
                       (FGET: Memory.get loc fto fmem = Some (ffrom, fmsg))
                       (FTO: Time.lt fmax fto),
              (<<FFROM: Time.lt fmax ffrom>>) /\
              exists from to msg,
                (<<GET: Memory.get loc to mem = Some (from, msg)>>) /\
                (<<FROM: f loc from ffrom>>) /\
                (<<TO: f loc to fto>>) /\
                (<<MSG: message_map f msg fmsg>>)):
        memory_map_loc loc max false f mem fmem
    .
  End FutureCertify.
End FutureCertify.
