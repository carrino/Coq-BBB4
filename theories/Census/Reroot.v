(** * Census/Reroot: the re-root bridge lemma family.

    A census machine [m] whose canonical first transition writes the
    blank symbol (a "0RB" machine, [mode reroot] in the recon mapping)
    runs a short blank-tape PREFIX -- writing only [S0], so the tape
    stays all-blank -- until, at step [t*], a state [q*] first fires a
    1-write.  Because the head-relative tape after a run of blank
    writes is untouched (writing [S0] on blank and moving keeps the
    all-blank tape, [snd InitES]), the configuration at step [t*] is
    exactly [(q*, snd InitES)]: [InitES] with the state component
    changed from [StA] to [q*].

    The re-root of [m] is therefore [TM_swap StA q* m] -- the census's
    OWN state-transposition machinery (TNF_QH.v), applied to the START
    state.  Its blank-start behaviour is [m]'s behaviour from step [t*]
    onward, relabelled by [es_swap StA q*].  So any decision the
    verified census checkers reach on the re-root [TM_swap StA q* m]
    (never-quasihalting, or the [NonHalt / QHBound / QuasiHaltsSt]
    quasihalting triple) TRANSFERS to [m] with a [t*]-step shift.

    This is BRIDGE.md section 4: the general [stepn_swap] (u,v arbitrary,
    already proved in TNF_QH.v) plus a per-machine <=4-step prefix
    reflexivity [stepn m t* InitES = Some (q*, snd InitES)] REPLACES the
    [es_swap_init] step that the u,v<>StA swap lemmas use (here the
    re-root touches [StA], so [es_swap StA q* InitES <> InitES] and
    [es_swap_init] does not apply).

    No new trust surface: the decisions on the re-root come from the
    existing sound checkers; these lemmas only move a decision across a
    concrete finite prefix.  Axiom footprint: [functional_extensionality_dep]
    only (inherited from TNF_QH's [TM_swap_swap]; the lemmas here add none). *)

From Coq Require Import Arith Lia List.
From Coq Require Import FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
Import ListNotations.

Set Default Goal Selector "!".

(** ** The blank-tape prefix

    Up to the first 1-write, [m] writes only [S0], so on the all-blank
    tape the head-relative representation is UNCHANGED: writing [S0] and
    moving keeps [snd InitES].  (The two sides are only EXTENSIONALLY
    blank after a push/tail, so this needs [functional_extensionality] --
    the sole axiom in the whole re-root family.)  [bstep] is the single
    prefix step; the per-machine prefix identity chains at most 4 of them. *)

Lemma push_side_blank : push_side S0 blank_side = blank_side.
Proof. apply functional_extensionality. intros [|n]; reflexivity. Qed.

Lemma tail_side_blank : tail_side blank_side = blank_side.
Proof. apply functional_extensionality. intro n. reflexivity. Qed.

Lemma tape_move_S0_blank : forall d, tape_move d S0 (snd InitES) = snd InitES.
Proof.
  intros []; unfold tape_move, InitES; simpl;
    rewrite push_side_blank, tail_side_blank; reflexivity.
Qed.

(** one blank step: a state whose read-[S0] transition writes [S0]
    moves to its target with the tape still [snd InitES]. *)
Lemma bstep : forall m q d q',
  m q S0 = Some (mkTrans S0 d q') ->
  step m (q, snd InitES) = Some (q', snd InitES).
Proof.
  intros m q d q' H. unfold step.
  replace (t_head (snd InitES)) with S0 by reflexivity.
  rewrite H. simpl. rewrite tape_move_S0_blank. reflexivity.
Qed.

(** the initial configuration written as a blank config with state [StA] *)
Lemma InitES_blank : InitES = (StA, snd InitES).
Proof. reflexivity. Qed.

(** ** The trusted prefix gate

    A [vm_compute]-decidable boolean re-derivation of the per-machine
    prefix identity, using the census's OWN concrete-tape engine
    ([csteps]/[c0], CTape.v) whose [lift] commutes with [stepn].  A
    reroot board's only per-machine obligation is [prefix_ok m qs t =
    true]: at step [t] the concrete tape is EXACTLY the blank cconf
    [([], S0, [])] (empty half-tapes, blank head) in state [qs].  The
    empty-list tapes are what force "the tape is still blank"; a
    tampered [(qs, t)] that reaches any non-blank configuration is
    rejected.  [prefix_ok_sound] lifts the concrete check to the
    [stepn] identity the re-root lemmas consume -- no [reflexivity] on
    non-normal tape functions is ever needed. *)

Definition cconf_blank (c : cconf) (qs : St) : bool :=
  let '(q, (l, h, r)) := c in
  st_eqb q qs && all_blank l && sym_eqb h S0 && all_blank r.

Definition prefix_ok (tm : TM) (qs : St) (t : nat) : bool :=
  match csteps tm t c0 with
  | Some c => cconf_blank c qs
  | None => false
  end.

Lemma all_blank_lift_side : forall l,
  all_blank l = true -> lift_side l = blank_side.
Proof.
  intros l H. apply functional_extensionality; intro n.
  unfold lift_side. rewrite (all_blank_nthb l H n). reflexivity.
Qed.

Lemma prefix_ok_sound : forall tm qs t,
  prefix_ok tm qs t = true ->
  stepn tm t InitES = Some (qs, snd InitES).
Proof.
  intros tm qs t H. unfold prefix_ok in H.
  destruct (csteps tm t c0) as [c|] eqn:E; [|discriminate].
  destruct c as [q [[l h] r]]. unfold cconf_blank in H.
  apply andb_prop in H as [H Hr].
  apply andb_prop in H as [H Hh].
  apply andb_prop in H as [Hq Hl].
  apply st_eqb_spec in Hq. subst q.
  apply sym_eqb_spec in Hh. subst h.
  pose proof (csteps_lift tm t c0 (qs, (l, S0, r)) E) as Hstep.
  rewrite lift_c0 in Hstep.
  (* lift (qs, (l, S0, r)) = (qs, snd InitES) since l, r are all-blank *)
  unfold lift, lift_tape, InitES in Hstep |- *; simpl in Hstep |- *.
  rewrite (all_blank_lift_side l Hl), (all_blank_lift_side r Hr) in Hstep.
  exact Hstep.
Qed.

(** ** The re-root step relation

    [es_swap StA qs] sends [InitES] to [(qs, snd InitES)] -- the prefix
    endpoint.  Combined with the general [stepn_swap] and the prefix
    identity, the re-root's trace is [m]'s trace shifted by [t]. *)

Lemma es_swap_StA_init : forall qs,
  es_swap StA qs InitES = (qs, snd InitES).
Proof.
  intro qs. unfold es_swap, InitES; simpl.
  unfold St_swap. rewrite st_eqb_refl. reflexivity.
Qed.

(** The linchpin (BRIDGE.md section 4(i)): stepping the re-root [n]
    times from [InitES] equals stepping [m] [(t + n)] times, up to the
    state relabel.  The only per-machine input is the prefix identity. *)
Lemma stepn_reroot : forall m qs t n,
  stepn m t InitES = Some (qs, snd InitES) ->
  stepn (TM_swap StA qs m) n InitES
    = option_map (es_swap StA qs) (stepn m (t + n) InitES).
Proof.
  intros m qs t n Hpre.
  rewrite stepn_swap, es_swap_StA_init.
  rewrite stepn_add, Hpre. reflexivity.
Qed.

(** Visits of the re-root at index [n] are exactly [m]'s visits of the
    swapped state at index [t + n]. *)
Lemma visitsat_reroot : forall m qs t q n,
  stepn m t InitES = Some (qs, snd InitES) ->
  (VisitsAt (TM_swap StA qs m) q n <-> VisitsAt m (St_swap StA qs q) (t + n)).
Proof.
  intros m qs t q n Hpre. unfold VisitsAt.
  rewrite (stepn_reroot m qs t n Hpre).
  destruct (stepn m (t + n) InitES) as [c0|]; simpl.
  - split.
    + intros (c & Hc & Hq). injection Hc as <-.
      exists c0. split; [reflexivity|].
      unfold es_swap in Hq; simpl in Hq.
      rewrite <- Hq, St_swap_swap. reflexivity.
    + intros (c & Hc & Hq). injection Hc as <-.
      eexists. split; [reflexivity|].
      unfold es_swap; simpl. rewrite Hq, St_swap_swap. reflexivity.
  - split; intros (c & Hc & _); discriminate.
Qed.

(** ** Non-halting transfer *)

Lemma nonhalt_reroot : forall m qs t,
  stepn m t InitES = Some (qs, snd InitES) ->
  NonHalt (TM_swap StA qs m) ->
  NonHalt m.
Proof.
  intros m qs t Hpre Hnh n Hnone.
  destruct (le_lt_dec t n) as [Hle | Hlt].
  - (* n >= t: fold through the re-root relation *)
    apply (Hnh (n - t)).
    rewrite (stepn_reroot m qs t (n - t) Hpre).
    replace (t + (n - t)) with n by lia.
    rewrite Hnone. reflexivity.
  - (* n < t: the prefix reaches [Some] at [t], so its prefix at [n] is [Some] *)
    destruct (stepn_prefix m n t InitES (qs, snd InitES)
                ltac:(lia) Hpre) as (cm & Hcm & _).
    rewrite Hcm in Hnone. discriminate.
Qed.

(** ** Never-quasihalting transfer (list C)

    If the re-root never quasihalts AND visits every state (the
    "drop-0" condition: no prefix state of [m] becomes quiet, which is
    exactly what never-QH forces -- BRIDGE.md section 4), then [m]
    never quasihalts.  The [Visited] hypothesis is discharged per
    machine by four concrete witnesses (one is [StA] at index 0). *)
Lemma neverqh_reroot : forall m qs t,
  stepn m t InitES = Some (qs, snd InitES) ->
  NeverQuasiHaltsSt (TM_swap StA qs m) ->
  (forall q, Visited (TM_swap StA qs m) q) ->
  NeverQuasiHaltsSt m.
Proof.
  intros m qs t Hpre Hnqh Hall q _ N.
  (* the swapped state is visited by the re-root, hence recurs i.o. *)
  set (q' := St_swap StA qs q).
  destruct (Hnqh q' (Hall q') N) as (n' & Hn' & Hvis).
  exists (t + n'). split; [lia|].
  apply (visitsat_reroot m qs t q' n' Hpre) in Hvis.
  unfold q' in Hvis. rewrite St_swap_swap in Hvis. exact Hvis.
Qed.

(** ** Quasihalting transfer (list B)

    The re-root's [NonHalt / QHBound B / QuasiHaltsSt] triple transfers
    to [m], with the bound shifted by the prefix length [t]: every
    quiet state of [m] is either a pure-prefix state (last visit
    [< t]) or the swap-image of a quiet state of the re-root (last
    visit [< B] there, so [< B + t] in [m]).  The generator picks a
    re-root bound [B] with [B + t <= 2000] so the census-grade
    [QHBound 2000] follows by monotonicity. *)
Lemma qhbound_reroot : forall m qs t B,
  stepn m t InitES = Some (qs, snd InitES) ->
  NonHalt (TM_swap StA qs m) ->
  QHBound B (TM_swap StA qs m) ->
  QuasiHaltsSt (TM_swap StA qs m) ->
  NonHalt m /\ QHBound (B + t) m /\ QuasiHaltsSt m.
Proof.
  intros m qs t B Hpre Hnh Hqb Hqh.
  split; [exact (nonhalt_reroot m qs t Hpre Hnh)|].
  split.
  - (* QHBound (B + t) m *)
    intros q s [Hvis Hlast].
    destruct (le_lt_dec t s) as [Hle | Hlt]; [| lia].
    (* s >= t: s = t + (s - t); the swap-image is quiet in the re-root *)
    set (n0 := s - t).
    set (q' := St_swap StA qs q).
    assert (Hstn : s = t + n0) by (unfold n0; lia).
    assert (Hqa : QuietAfter (TM_swap StA qs m) q' n0).
    { split.
      - apply (proj2 (visitsat_reroot m qs t q' n0 Hpre)).
        unfold q'. rewrite St_swap_swap.
        replace (t + n0) with s by lia. exact Hvis.
      - intros n Hn Hv.
        apply (visitsat_reroot m qs t q' n Hpre) in Hv.
        unfold q' in Hv. rewrite St_swap_swap in Hv.
        apply (Hlast (t + n)); [lia | exact Hv]. }
    specialize (Hqb q' n0 Hqa). lia.
  - (* QuasiHaltsSt m *)
    destruct Hqh as (q' & Hvq' & N' & HN').
    exists (St_swap StA qs q'). split.
    + (* visited *)
      destruct Hvq' as (n' & Hv').
      exists (t + n').
      apply (visitsat_reroot m qs t q' n' Hpre) in Hv'. exact Hv'.
    + (* quiet from [t + N'] *)
      exists (t + N'). intros n Hn Hv.
      destruct (le_lt_dec t n) as [Hle | Hlt]; [| lia].
      apply (HN' (n - t)); [lia|].
      apply (proj2 (visitsat_reroot m qs t q' (n - t) Hpre)).
      replace (t + (n - t)) with n by lia. exact Hv.
Qed.
