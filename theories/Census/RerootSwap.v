(** * RerootSwap: the relabelling half of the shadow argument, stated once

    A SHADOW is a frozen row whose start transition writes the blank, so it
    runs an all-blank prefix and thereafter IS its re-root [TM_swap StA q*]
    started fresh -- and whose re-root is some CORE row with non-start states
    relabelled and possibly mirrored.  Boarding a shadow is therefore two
    transports composed:

      - across the blank prefix.  [Census/Reroot.v] already has this, for both
        outcomes: [neverqh_reroot] for a never-quasihalter, and
        [qhbound_reroot] for the [NonHalt / QHBound (B+t) / QuasiHaltsSt]
        triple, with the bound shifted by the prefix length.
      - across the relabelling.  [QHBound] already has both halves
        ([TNF_QH.qhbound_swap], [TNF_QH.qhbound_mirror]).
        [NeverQuasiHaltsSt] had NEITHER, and that is what this file adds.

    WHY A SEPARATE FILE.  [neverqh_swap] belongs beside [Reroot.neverqh_reroot]
    and was written that way the first time -- as a LOCAL copy inside
    [Machines/Counters/RRNQ_0RB0RD_1RC____1RD1LC_0LC1RA.v], whose header says
    it "is general and belongs beside [Reroot.neverqh_reroot]; it is kept local
    here only because [Census/Reroot.v] sits under the whole census and
    closeout, and moving a lemma into it costs a full rebuild of both."  That
    cost is real but it is avoidable: Coq rebuilds the dependents of CHANGED
    files, so a NEW module that [Require]s [Reroot] costs one file's compile
    and rebuilds nothing.  Hence this file rather than an edit next door.

    Everything here is general -- no machine is named, and nothing below
    mentions a row.  Per-shadow files supply only the two literal tables and
    four [Visited] witnesses; [tools/closeout/gen_shadow.py] generates them.

    Axiom footprint: whatever [CTape.lift] and [Census/TNF_QH] already carry
    ([functional_extensionality_dep]); this file assumes nothing new. *)
From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From BBB4.Census Require Import TNF_QH.
Import ListNotations.

(** ** Relabelling two NON-start states

    [VisitsAt] transports both ways: the swapped machine visits [q] at step
    [n] exactly when the original visits [St_swap u v q] there.  The
    [u <> StA] and [v <> StA] side conditions are what keep the START state
    fixed, so the two runs begin at the same configuration
    ([TNF_QH.es_swap_init]) and stay in lockstep ([TNF_QH.stepn_swap]). *)
Lemma visitsat_swap : forall u v m q n,
  u <> StA -> v <> StA ->
  (VisitsAt (TM_swap u v m) q n <-> VisitsAt m (St_swap u v q) n).
Proof.
  intros u v m q n Hu Hv. unfold VisitsAt.
  rewrite stepn_swap, (es_swap_init u v Hu Hv).
  destruct (stepn m n InitES) as [c0|]; cbn [option_map].
  - split.
    + intros (c & Hc & Hq). injection Hc as <-.
      exists c0. split; [reflexivity|].
      unfold es_swap in Hq; cbn [fst] in Hq.
      rewrite <- Hq, St_swap_swap. reflexivity.
    + intros (c & Hc & Hq). injection Hc as <-.
      eexists. split; [reflexivity|].
      unfold es_swap; cbn [fst]. rewrite Hq, St_swap_swap. reflexivity.
  - split; intros (c & Hc & _); discriminate.
Qed.

(** Never-quasihalting is invariant under relabelling two non-start states.

    A state [q] of the relabelled machine is live exactly when its preimage
    [St_swap u v q] is live in the original, and recurrence transports back
    along the same equivalence. *)
Lemma neverqh_swap : forall u v m,
  u <> StA -> v <> StA ->
  NeverQuasiHaltsSt m -> NeverQuasiHaltsSt (TM_swap u v m).
Proof.
  intros u v m Hu Hv H q Hvis N.
  assert (Hv' : Visited m (St_swap u v q)).
  { destruct Hvis as (n & Hn). exists n.
    exact (proj1 (visitsat_swap u v m q n Hu Hv) Hn). }
  destruct (H (St_swap u v q) Hv' N) as (n & Hn & Hvn).
  exists n. split; [exact Hn|].
  exact (proj2 (visitsat_swap u v m q n Hu Hv) Hvn).
Qed.

(** ** Mirroring

    [Mirror.mirror_visits] is the [VisitsAt] equivalence; unlike the swap it
    moves no state at all, so this is the same argument with the identity in
    place of [St_swap]. *)
Lemma neverqh_mirror : forall m,
  NeverQuasiHaltsSt m -> NeverQuasiHaltsSt (mirror_tm m).
Proof.
  intros m H q Hvis N.
  assert (Hv' : Visited m q).
  { destruct Hvis as (n & Hn). exists n. exact (proj1 (mirror_visits m q n) Hn). }
  destruct (H q Hv' N) as (n & Hn & Hvn).
  exists n. split; [exact Hn|].
  exact (proj2 (mirror_visits m q n) Hvn).
Qed.

(** ** Discharging [Visited] by a concrete run

    [Reroot.visited_prefix] only reaches the states of the blank prefix, and a
    re-root writes on its first step, so the four witnesses a shadow board
    needs are ordinary short runs read off [csteps].  Stating the bridge once
    means each generated board spends one [vm_compute] per state and no
    reasoning. *)
Lemma visited_csteps : forall m n q,
  match csteps m n c0 with Some c => st_eqb (fst c) q | None => false end = true ->
  Visited m q.
Proof.
  intros m n q H. destruct (csteps m n c0) as [c|] eqn:E; [|discriminate].
  apply st_eqb_spec in H.
  exists n, (lift c). split.
  - rewrite <- lift_c0. apply csteps_lift. exact E.
  - rewrite lift_state. exact H.
Qed.
