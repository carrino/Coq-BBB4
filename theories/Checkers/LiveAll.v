(** * Assembling [NeverQuasiHaltsSt] from four per-state liveness facts

    Every liveness engine in the tree ([ReachStI.reach_sti_recurs],
    [ReachSt], the hand measure arguments in [Machines/Mxdys4]) produces
    the SAME per-state shape:

        forall N, exists m, N <= m /\ VisitsAt tm q m

    -- "state [q] is visited at unboundedly large indices".  That is
    already [NeverQuasiHaltsSt]'s conclusion for the single state [q].
    What was missing was the trivial closer that turns four of them into
    the theorem: [NeverQuasiHaltsSt] quantifies over [q] and hands back a
    [Visited] hypothesis which four total facts simply do not need.

    Before this file every board that wanted the four-way combination had
    to route through a checker that produces [NeverQuasiHaltsSt] whole
    ([ngramhist_check_neverqh_lex_ext_sound] and friends).  A row whose
    [NGramHist] closure covers NOTHING -- so there is no checker to route
    through -- but whose states are each independently live had no way to
    state its own conclusion.  [neverqh_of_live4] is that way.

    The [Visited] hypothesis is discarded, so these lemmas are strictly
    stronger than [NeverQuasiHaltsSt] requires: they prove every state
    live, not merely every VISITED state.  That is what the engines give
    and there is no reason to weaken it. *)

From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement.

(** The recurrence obligation for one state, in exactly the form
    [reach_sti_recurs] and [reach_sti_recurs_b] return it. *)
Definition LiveSt (tm : TM) (q : St) : Prop :=
  forall N, exists m, N <= m /\ VisitsAt tm q m.

(** The closer.  Four total facts, one per state of the 4-state alphabet;
    [Visited] is not needed and is dropped. *)
Lemma neverqh_of_live4 : forall tm,
  LiveSt tm StA -> LiveSt tm StB -> LiveSt tm StC -> LiveSt tm StD ->
  NeverQuasiHaltsSt tm.
Proof.
  intros tm HA HB HC HD q _ N; destruct q.
  - exact (HA N).
  - exact (HB N).
  - exact (HC N).
  - exact (HD N).
Qed.

(** The same thing driven off a total function, for emitters that would
    rather build one [match] than pass four arguments. *)
Lemma neverqh_of_live_all : forall tm,
  (forall q, LiveSt tm q) -> NeverQuasiHaltsSt tm.
Proof. intros tm H q _ N. exact (H q N). Qed.

(** [reach_sti_recurs_b] returns [NonHalt tm /\ LiveSt tm qgoal] as a
    conjunction; this projects the half that [neverqh_of_live4] wants, so
    a caller can write [live_of_recurs (reach_sti_recurs_b ...)] with no
    intervening [destruct]. *)
Lemma live_of_recurs : forall tm q,
  NonHalt tm /\ (forall N, exists m, N <= m /\ VisitsAt tm q m) ->
  LiveSt tm q.
Proof. intros tm q [_ H]. exact H. Qed.

(** [NonHalt] also follows from any ONE live state, without going through
    [NeverQuasiHaltsSt] and its [Visited] obligation. *)
Lemma nonhalt_of_live : forall tm q, LiveSt tm q -> NonHalt tm.
Proof.
  intros tm q H n Hnone.
  destruct (H n) as (m & Hm & c & Hc & _).
  replace m with (n + (m - n)) in Hc by lia.
  rewrite stepn_add, Hnone in Hc. discriminate.
Qed.
