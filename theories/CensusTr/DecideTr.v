(** * CensusTr/DecideTr: the transition-level census decider skeleton.

    The transition-level fork of Census/Decide.v's pipeline, phase-0
    scope (SCOPING_INSTR.md section 5): the tiers that STRENGTHEN
    MECHANICALLY are ported now -- halting, in-place cycles, translated
    cycles, and the three lookup tiers -- and everything else falls to
    [R_Unknown].  A cycle repeats the exact head-relative
    configuration, head symbol included, so the cycle tiers' conclusion
    lifts from "quiet states last visited before the anchor" to "quiet
    INSTRUCTIONS last fired before the anchor" with the same
    certificates and the same computational checks.

    Everything computational is REUSED from Census/Decide.v --
    [find_halt], the one-pass loop scan ([lp_candidates], [lp_check],
    [scan_loops]), the lookup maps ([dmap_of], [deferred_lookup]) --
    so a transition-level walk pops nodes at the same cost as the
    state-level one on these tiers.  Only the soundness layer is new.

    The n-gram / rank / wrapped-QHBound / RepWL tiers are NOT here
    yet: machines they used to decide fall through to [R_Unknown] and
    surface in the collection walk's back queue -- that back queue IS
    the burn-down list this skeleton exists to produce. *)

From Coq Require Import Arith Lia Bool List NArith PArith ZArith.
From Coq Require Import FSets.FMapPositive MSets.MSetPositive.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape GTape Mirror.
From BBB4.Checkers Require Import Cycle TCycler NGram NGramTr WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Census Require Import TNF_QH Decide RankSearch.
From BBB4.CensusTr Require Import TNF_QHTr RepWLTr.
Import ListNotations.
Open Scope nat_scope.

Set Default Goal Selector "!".

(** last fire of [tg] among the configurations at offsets
    [k .. k + gas - 1] (untrusted: the QHBoundTr checker re-verifies
    the returned index) *)
Fixpoint last_fire (tm : TM) (gas : nat) (c : cconf) (k : nat)
    (tg : Instr) (best : option nat) : option nat :=
  match gas with
  | 0 => best
  | S g =>
      let best' := if instr_eqb (cinstr c) tg then Some k else best in
      match cstep tm c with
      | None => best'
      | Some c' => last_fire tm g c' (S k) tg best'
      end
  end.

(** Collect all eight last-fire times in one simulation. A concrete record
    makes the scan evaluate once before the eight lookups, including under
    the native evaluator; no chain of function updates retains old tapes. *)
Record FireTimes := mkFireTimes {
  fire_A0 : option nat; fire_A1 : option nat;
  fire_B0 : option nat; fire_B1 : option nat;
  fire_C0 : option nat; fire_C1 : option nat;
  fire_D0 : option nat; fire_D1 : option nat
}.

Definition no_fires : FireTimes :=
  mkFireTimes None None None None None None None None.

Definition fire_time (times : FireTimes) (tg : Instr) : option nat :=
  match tg with
  | (StA, S0) => fire_A0 times | (StA, S1) => fire_A1 times
  | (StB, S0) => fire_B0 times | (StB, S1) => fire_B1 times
  | (StC, S0) => fire_C0 times | (StC, S1) => fire_C1 times
  | (StD, S0) => fire_D0 times | (StD, S1) => fire_D1 times
  end.

Definition record_fire (times : FireTimes) (tg : Instr) (k : nat) : FireTimes :=
  let '(mkFireTimes a0 a1 b0 b1 c0 c1 d0 d1) := times in
  match tg with
  | (StA, S0) => mkFireTimes (Some k) a1 b0 b1 c0 c1 d0 d1
  | (StA, S1) => mkFireTimes a0 (Some k) b0 b1 c0 c1 d0 d1
  | (StB, S0) => mkFireTimes a0 a1 (Some k) b1 c0 c1 d0 d1
  | (StB, S1) => mkFireTimes a0 a1 b0 (Some k) c0 c1 d0 d1
  | (StC, S0) => mkFireTimes a0 a1 b0 b1 (Some k) c1 d0 d1
  | (StC, S1) => mkFireTimes a0 a1 b0 b1 c0 (Some k) d0 d1
  | (StD, S0) => mkFireTimes a0 a1 b0 b1 c0 c1 (Some k) d1
  | (StD, S1) => mkFireTimes a0 a1 b0 b1 c0 c1 d0 (Some k)
  end.

Lemma fire_time_record : forall times fired tg k,
  fire_time (record_fire times fired k) tg =
  (if instr_eqb fired tg then Some k else fire_time times tg).
Proof.
  intros [] [q s] [q' s'] k. destruct q, s, q', s'; reflexivity.
Qed.

Fixpoint last_fires (tm : TM) (gas : nat) (c : cconf) (k : nat)
    (times : FireTimes) : FireTimes :=
  match gas with
  | 0 => times
  | S g =>
      let times' := record_fire times (cinstr c) k in
      match cstep tm c with
      | None => times'
      | Some c' => last_fires tm g c' (S k) times'
      end
  end.

Lemma last_fires_spec : forall tm gas c k times tg,
  fire_time (last_fires tm gas c k times) tg =
  last_fire tm gas c k tg (fire_time times tg).
Proof.
  intros tm gas. induction gas as [|gas IH]; intros c k times tg;
    cbn [last_fires last_fire]; [reflexivity|].
  destruct (cstep tm c).
  - rewrite IH, fire_time_record. reflexivity.
  - apply fire_time_record.
Qed.

(** A resumable scan. [Some (c,k)] means that configuration [c] at
    index [k] has NOT been inspected yet. [None] means a halt was observed:
    its instruction was recorded once, and every later resume is a no-op.
    The recursive call is in tail position; the cursor record is allocated
    only when the scan stops, not at every simulated instruction. *)
Record FireScan := mkFireScan {
  scan_times : FireTimes;
  scan_next : option (cconf * nat)
}.

Fixpoint last_fires_scan (tm : TM) (gas : nat) (c : cconf) (k : nat)
    (times : FireTimes) : FireScan :=
  match gas with
  | 0 => mkFireScan times (Some (c, k))
  | S g =>
      let times' := record_fire times (cinstr c) k in
      match cstep tm c with
      | None => mkFireScan times' None
      | Some c' => last_fires_scan tm g c' (S k) times'
      end
  end.

Definition resume_last_fires (tm : TM) (gas : nat) (scan : FireScan)
    : FireScan :=
  match scan_next scan with
  | None => scan
  | Some (c, k) => last_fires_scan tm gas c k (scan_times scan)
  end.

(** Exact prefix projection, for arbitrary initial times and indices. *)
Lemma last_fires_scan_times : forall tm gas c k times,
  scan_times (last_fires_scan tm gas c k times) =
  last_fires tm gas c k times.
Proof.
  intros tm gas. induction gas as [|gas IH]; intros c k times.
  - reflexivity.
  - cbn [last_fires_scan last_fires].
    destruct (cstep tm c) as [c'|].
    + apply IH.
    + reflexivity.
Qed.

(** Exact composition of the ENTIRE scan result, including cursor and halt
    status. No nonhalting premise or positive-fuel premise is needed. *)
Lemma last_fires_scan_resume : forall tm prefix suffix c k times,
  resume_last_fires tm suffix (last_fires_scan tm prefix c k times) =
  last_fires_scan tm (prefix + suffix) c k times.
Proof.
  intros tm prefix. induction prefix as [|prefix IH];
    intros suffix c k times.
  - reflexivity.
  - cbn [last_fires_scan Nat.add].
    destruct (cstep tm c) as [c'|].
    + apply IH.
    + reflexivity.
Qed.

Lemma last_fires_resume_times : forall tm prefix suffix c k times,
  scan_times
    (resume_last_fires tm suffix (last_fires_scan tm prefix c k times)) =
  last_fires tm (prefix + suffix) c k times.
Proof.
  intros tm prefix suffix c k times.
  rewrite last_fires_scan_resume. apply last_fires_scan_times.
Qed.

(** Boundary facts spell out the cases that are easy to get off by one.
    In particular, fuel zero does not inspect or record a halting cell. *)
Lemma last_fires_scan_zero : forall tm c k times,
  last_fires_scan tm 0 c k times = mkFireScan times (Some (c, k)).
Proof. intros tm c k times. reflexivity. Qed.

Lemma resume_last_fires_zero : forall tm scan,
  resume_last_fires tm 0 scan = scan.
Proof.
  intros tm [times next]. destruct next as [[c k]|]; reflexivity.
Qed.

Lemma last_fires_scan_halt : forall tm gas c k times,
  cstep tm c = None ->
  last_fires_scan tm (S gas) c k times =
  mkFireScan (record_fire times (cinstr c) k) None.
Proof.
  intros tm gas c k times Hhalt. cbn [last_fires_scan].
  rewrite Hhalt. reflexivity.
Qed.

Lemma resume_last_fires_halted : forall tm gas times,
  resume_last_fires tm gas (mkFireScan times None) = mkFireScan times None.
Proof. intros tm gas times. reflexivity. Qed.

Lemma last_fires_scan_cursor : forall tm gas c k times c' k',
  scan_next (last_fires_scan tm gas c k times) = Some (c', k') ->
  k' = k + gas /\ csteps tm gas c = Some c'.
Proof.
  intros tm gas. induction gas as [|gas IH];
    intros c k times c' k' Hnext.
  - cbn [last_fires_scan scan_next] in Hnext.
    inversion Hnext; subst. split; [lia|reflexivity].
  - cbn [last_fires_scan] in Hnext.
    destruct (cstep tm c) as [c1|] eqn:Estep; [|discriminate].
    destruct (IH c1 (S k) (record_fire times (cinstr c) k) c' k' Hnext)
      as [Hindex Hsteps].
    split; [lia|]. cbn [csteps]. rewrite Estep. exact Hsteps.
Qed.

Definition fire_candidates (times : FireTimes) : list (Instr * nat) :=
  fold_right (fun tg acc =>
    match fire_time times tg with
    | Some s => (tg, s) :: acc
    | None => acc end) [] all_Instr.

(** Later simulation cannot introduce a last-fire timestamp below an
    earlier cutoff. These structural lemmas also cover halted scans. *)
Definition old_fire_before (cut : nat) (time : option nat) : bool :=
  match time with Some s => s <? cut | None => false end.

Lemma last_fire_after_cut : forall tm gas c k tg best cut s,
  cut <= k -> s < cut -> last_fire tm gas c k tg best = Some s ->
  best = Some s.
Proof.
  intros tm gas. induction gas as [|gas IH]; intros c k tg best cut s Hcut Hs H.
  - exact H.
  - cbn [last_fire] in H.
    destruct (cstep tm c) as [c'|] eqn:Estep.
    + specialize (IH c' (S k) tg _ cut s ltac:(lia) Hs H).
      destruct (instr_eqb (cinstr c) tg); [inversion IH; lia|exact IH].
    + destruct (instr_eqb (cinstr c) tg); [inversion H; lia|exact H].
Qed.

Lemma last_fire_prefix_old : forall tm prefix suffix c k tg best cut s,
  cut <= k + prefix -> s < cut ->
  last_fire tm (prefix + suffix) c k tg best = Some s ->
  last_fire tm prefix c k tg best = Some s.
Proof.
  intros tm prefix. induction prefix as [|prefix IH];
    intros suffix c k tg best cut s Hcut Hs H.
  - cbn in *. exact (last_fire_after_cut tm suffix c k tg best cut s ltac:(lia) Hs H).
  - cbn [Nat.add last_fire] in *.
    destruct (cstep tm c) as [c'|] eqn:Estep; [|exact H].
    eapply IH with (cut := cut); eauto. lia.
Qed.

Lemma fold_fire_candidates : forall cut times tgs,
  existsb (fun p => snd p <? cut)
    (fold_right (fun tg acc =>
      match fire_time times tg with
      | Some s => (tg,s)::acc | None => acc end) [] tgs) =
  existsb (fun tg => old_fire_before cut (fire_time times tg)) tgs.
Proof.
  intros cut times tgs. induction tgs as [|tg tgs IH]; cbn [fold_right existsb]; [reflexivity|].
  destruct (fire_time times tg); cbn [existsb old_fire_before snd];
    rewrite IH; reflexivity.
Qed.

(** ** The cycle tiers at transition level

    [glift] plants the window's head cell regardless of the abstract
    far-tape [rho], so a pumped window occurrence fires the same
    instruction. *)

Lemma glift_instr : forall rho rho' g,
  instr_of (glift rho g) = instr_of (glift rho' g).
Proof. intros rho rho' [q [[l h] r]]. reflexivity. Qed.

(** fires at or after an in-place cycle's start recur forever, so any
    eventually-quiet instruction last fired strictly before [n1] *)
Lemma cycle_qhboundtr : forall tm n1 p E,
  0 < p ->
  stepn tm n1 InitES = Some E ->
  stepn tm p E = Some E ->
  QHBoundTr n1 tm.
Proof.
  intros tm n1 p E Hp H1 Hloop t s [Hf Hq].
  destruct (le_lt_dec n1 s) as [Hge | Hlt]; [| lia].
  exfalso.
  destruct Hf as (c & Hc & Htc).
  apply (Hq (s + p)); [lia|].
  exists c. split; [| exact Htc].
  replace (s + p) with (n1 + (p + (s - n1))) by lia.
  rewrite stepn_add, H1.
  change (stepn tm (p + (s - n1)) E = Some c).
  rewrite stepn_add, Hloop.
  change (stepn tm (s - n1) E = Some c).
  replace s with (n1 + (s - n1)) in Hc by lia.
  rewrite stepn_add, H1 in Hc.
  exact Hc.
Qed.

Lemma cycle_leaf_check_sound_tr : forall tm n1 p,
  cycle_leaf_check tm n1 p = true ->
  NonHalt tm /\ QHBoundTr n1 tm.
Proof.
  intros tm n1 p H.
  rewrite cycle_leaf_check_spec in H.
  unfold cycle_leaf_check_reference in H.
  apply andb_prop in H as [Hp H].
  apply Nat.ltb_lt in Hp.
  destruct (csteps tm n1 c0) as [a|] eqn:Ea; [|discriminate].
  destruct (csteps tm (n1 + p) c0) as [b|] eqn:Eb; [|discriminate].
  apply ceqb_lift in H.
  pose proof (csteps_lift tm n1 c0 a Ea) as Ha.
  pose proof (csteps_lift tm (n1 + p) c0 b Eb) as Hb.
  rewrite lift_c0 in Ha, Hb.
  rewrite <- H in Hb.
  assert (Hloop : stepn tm p (lift a) = Some (lift a)).
  { rewrite stepn_add, Ha in Hb. exact Hb. }
  split.
  - exact (cycle_nonhalt tm n1 p (lift a) Hp Ha Hloop).
  - exact (cycle_qhboundtr tm n1 p (lift a) Hp Ha Hloop).
Qed.

Lemma tcycler_leaf_check_sound_tr : forall tm n1 P W,
  tcycler_leaf_check tm n1 P W = true ->
  NonHalt tm /\ QHBoundTr n1 tm.
Proof.
  intros tm n1 P W H.
  unfold tcycler_leaf_check in H.
  apply andb_prop in H as [Hp H].
  apply Nat.ltb_lt in Hp.
  destruct (csteps tm n1 c0) as [[q1 [[l1 h1] r1]]|] eqn:E1; [|discriminate].
  destruct (gsteps tm P (q1, (firstn_pad W l1, h1, r1))) as [g2|] eqn:E2;
    [|discriminate].
  pose proof (anchor_instance tm n1 W q1 l1 h1 r1 E1) as HA.
  set (g1 := (q1, (firstn_pad W l1, h1, r1)) : cconf) in *.
  set (rho0 := fun n => nthb l1 (n + W)) in *.
  split.
  - (* non-halting, exactly as at state level *)
    intros n HN.
    destruct (le_lt_dec n1 n) as [Hge | Hlt].
    + destruct (tcycler_fold tm n1 P g1 g2 rho0 Hp HA E2 H n Hge)
        as (i & gi & rho & Hi & Hgi & Hfold).
      rewrite Hfold in HN. discriminate.
    + destruct (csteps_prefix tm n n1 c0 (q1, (l1, h1, r1)))
        as (cm & Hcm & _); [lia | exact E1 |].
      assert (Hl : stepn tm n InitES = Some (lift cm)).
      { rewrite <- lift_c0. apply csteps_lift; assumption. }
      rewrite Hl in HN. discriminate.
  - (* any quiet instruction last fired before the anchor *)
    intros t s [Hf Hq].
    destruct (le_lt_dec n1 s) as [Hge | Hlt]; [| lia].
    exfalso.
    destruct Hf as (c & Hc & Htc).
    destruct (tcycler_fold tm n1 P g1 g2 rho0 Hp HA E2 H s Hge)
      as (i & gi & rho & Hi & Hgi & Hfold).
    rewrite Hfold in Hc. injection Hc as <-.
    (* pump the window occurrence one lap past s: the pumped config
       fires the same instruction ([glift_instr]) *)
    destruct (tcycler_laps tm n1 P g1 g2 rho0 HA E2 H (S s)) as [rho' Hrho'].
    apply (Hq (n1 + (S s) * P + i)); [nia|].
    exists (glift rho' gi).
    split.
    + replace (n1 + (S s) * P + i) with ((n1 + (S s) * P) + i) by lia.
      rewrite stepn_add, Hrho'.
      apply gsteps_lift; exact Hgi.
    + rewrite (glift_instr rho' rho gi). exact Htc.
Qed.

Corollary tcycler_leaf_check_sound_tr_L : forall tm n1 P W,
  tcycler_leaf_check (mirror_tm tm) n1 P W = true ->
  NonHalt tm /\ QHBoundTr n1 tm.
Proof.
  intros tm n1 P W H.
  destruct (tcycler_leaf_check_sound_tr (mirror_tm tm) n1 P W H) as [Hnh Hb].
  split.
  - apply mirror_nonhalt; exact Hnh.
  - apply qhboundtr_mirror; exact Hb.
Qed.

(** ** The pipeline (phase-0 tier stack) *)

(** ** The instruction-target rank/lex certificate search

    Census/RankSearch.v's procedure with the avoid-filter moved from
    states to instructions; everything downstream of the adjacency
    build (Kosaraju SCCs, condensation ranks, rules (a)/(b) over the
    count-of-1s measures) is reused by import.  UNTRUSTED: a wrong
    certificate merely fails the verified lex checker. *)

Definition qsuccs_tr (tm : TM) (lset rset : gset) (tg : Instr)
    (a : cconf) : list cconf :=
  match ng_succs tm lset rset a with
  | Some l => filter (fun b => negb (instr_eqb (cinstr b) tg)) l
  | None => []
  end.

Definition build_adj_tr (tm : TM) (lset rset : gset) (tg : Instr)
    (nodes : list cconf) : Adj :=
  fold_left (fun g a => adj_set g a (qsuccs_tr tm lset rset tg a))
            nodes (PositiveMap.empty _).

Definition rank_procedure_tr (tm : TM) (lset rset : gset)
    (closure : list cconf) (tg : Instr) : list ngcomp :=
  let nodes := filter (fun a => negb (instr_eqb (cinstr a) tg)) closure in
  let g := build_adj_tr tm lset rset tg nodes in
  let Kc := S (S (length nodes)) in
  let rfuel := S (length nodes * 8 + 8) in
  match proc_rounds 200 tm Kc rfuel nodes g [] with
  | Some comps => comps
  | None => []
  end.

(** the never-QH rank tier (RankSearch.v's [rank_tier] at instruction
    targets): grow the sets once, enumerate the closure, search a
    certificate per fired instruction, verify through the lex-gated
    checker *)
Definition rank_tier_tr (tm : TM) (n t fuel rounds : nat) : bool :=
  match csteps tm t c0 with
  | None => false
  | Some cc =>
      let '(q0, (l, h, r)) := cc in
      let lset0 := gadds (ng_seed_side n l) gempty in
      let rset0 := gadds (ng_seed_side n r) gempty in
      let a0 := ng_start n cc in
      let '(lset, rset) := ng_grow tm a0 fuel rounds lset0 rset0 in
      let closure :=
        ng_explore tm lset rset fuel [] PositiveSet.empty [a0] in
      ngram_check_neverqhtr_lex_with tm n t fuel lset rset
        (fun tg => rank_procedure_tr tm lset rset closure tg)
  end.

Theorem rank_tier_tr_sound : forall tm n t fuel rounds,
  rank_tier_tr tm n t fuel rounds = true -> NeverQuasiHaltsTr tm.
Proof.
  intros tm n t fuel rounds H.
  unfold rank_tier_tr in H.
  destruct (csteps tm t c0) as [[q0 [[l h] r]]|]; [|discriminate].
  match type of H with
  | (let '(_, _) := ?G in _) = true => destruct G as [lset rset]
  end.
  cbv beta iota zeta in H.
  exact (ngram_check_neverqhtr_lex_with_sound tm n t fuel lset rset _ H).
Qed.

Section PipelineTr.

Variable B : nat.              (** global transition-score bound *)
Variable D : list TM.          (** the deferred list (empty in the
                                   collection walk; frozen afterwards) *)
Variable halt_gas : nat.       (** gas for the halt search + cheap scan rung *)
Variable loop_gas : nat.       (** gas for the full loop-scan rung *)
Variable ng_fuel : nat.        (** worklist fuel for the n-gram closures *)
Variable ng_rounds : nat.      (** growth rounds for the n-gram sets *)
Variable ng_rungs : list (nat * nat).   (** (window n, prefix t) ladder,
                                            never tier *)
Variable rank_rungs : list (nat * nat). (** ladder for the rank-rules
                                            never tier *)
Variable qhb_rungs : list (nat * nat).  (** (window n, prefix t) ladder,
                                            wrapped-QHBoundTr tier *)
Variable qhb_lex_rungs : list (nat * nat).  (** the lex ladder's own
                                            (usually shorter) rung list:
                                            a lex rung re-grows the sets
                                            and runs the certificate
                                            search per instruction, so
                                            failing machines pay it in
                                            full *)
Variable rw_qhb_rungs : list (nat * nat * nat).  (** (L, T, t) ladder
                                            for the WRAPPED RepWL tier
                                            (Tier W-wrap): the 7.1m
                                            suspects' pins are tape-value
                                            exclusions the n-gram window
                                            cannot hold, so their rungs
                                            close over [rw_succs_cut] of
                                            the wrapped machine instead *)
Variable rw_rungs : list (nat * nat * nat).  (** (L, T, t) ladder for
                                            the RepWL tier *)
Variable rw_fuel : nat.        (** closure fuel for the RepWL tier *)
Variable rw_cut : nat.         (** RepWL node-size cut (M4): abandon a
                                   closure popping a node with more
                                   run-length items than this *)
Variable Prov : list TM.       (** proven [NeverQuasiHaltsTr] machines *)
Hypothesis HP : Forall NeverQuasiHaltsTr Prov.
Variable ProvQH : list TM.     (** proven census-grade transition-QH machines *)
Hypothesis HPQ :
  Forall (fun tm => NonHalt tm /\ QHBoundTr B tm /\ QuasiHaltsTr tm) ProvQH.

(** the reused one-pass candidates, re-checked by the reused verified
    checkers, concluded at transition level *)
Lemma lp_check_sound_tr : forall tm cand,
  lp_check B tm cand = true -> NonHalt tm /\ QHBoundTr B tm.
Proof.
  intros tm cand H.
  rewrite lp_check_spec in H.
  destruct cand as [n1 p | [|] n1 P];
    unfold lp_check_reference in H;
    apply andb_prop in H as [Hb H];
    apply Nat.leb_le in Hb.
  - destruct (cycle_leaf_check_sound_tr tm n1 p H) as [Hnh Hq].
    split; [exact Hnh | exact (qhboundtr_mono n1 B tm Hb Hq)].
  - destruct (tcycler_leaf_check_sound_tr_L tm n1 P _ H) as [Hnh Hq].
    split; [exact Hnh | exact (qhboundtr_mono n1 B tm Hb Hq)].
  - destruct (tcycler_leaf_check_sound_tr tm n1 P _ H) as [Hnh Hq].
    split; [exact Hnh | exact (qhboundtr_mono n1 B tm Hb Hq)].
Qed.

Lemma scan_loops_sound_tr : forall tm gas,
  scan_loops B tm gas = true -> NonHalt tm /\ QHBoundTr B tm.
Proof.
  intros tm gas H.
  rewrite scan_loops_spec in H.
  unfold scan_loops_reference in H.
  rewrite anyb_existsb in H.
  apply existsb_exists in H.
  destruct H as (cand & _ & Hc).
  exact (lp_check_sound_tr tm cand Hc).
Qed.

(** *** Tier N: the per-instruction n-gram ladder *)

Fixpoint try_ngram_tr (rungs : list (nat * nat)) (tm : TM) : QHResult :=
  match rungs with
  | [] => R_Unknown
  | (n, t) :: rest =>
      if ngram_check_neverqhtr tm n t ng_fuel ng_rounds
      then R_NeverQH
      else try_ngram_tr rest tm
  end.

Lemma try_ngram_tr_cases : forall rungs tm,
  (try_ngram_tr rungs tm = R_NeverQH /\ NeverQuasiHaltsTr tm) \/
  try_ngram_tr rungs tm = R_Unknown.
Proof.
  induction rungs as [| [n t] rest IH]; intros tm; simpl.
  - right; reflexivity.
  - destruct (ngram_check_neverqhtr tm n t ng_fuel ng_rounds) eqn:E.
    + left. split; [reflexivity|].
      exact (ngram_check_neverqhtr_sound tm n t ng_fuel ng_rounds E).
    + exact (IH tm).
Qed.

(** *** Tier R: the rank-rules never ladder *)

Fixpoint try_rank_tr (rungs : list (nat * nat)) (tm : TM) : QHResult :=
  match rungs with
  | [] => R_Unknown
  | (n, t) :: rest =>
      if rank_tier_tr tm n t ng_fuel ng_rounds
      then R_NeverQH
      else try_rank_tr rest tm
  end.

Lemma try_rank_tr_cases : forall rungs tm,
  (try_rank_tr rungs tm = R_NeverQH /\ NeverQuasiHaltsTr tm) \/
  try_rank_tr rungs tm = R_Unknown.
Proof.
  induction rungs as [| [n t] rest IH]; intros tm; simpl.
  - right; reflexivity.
  - destruct (rank_tier_tr tm n t ng_fuel ng_rounds) eqn:E.
    + left. split; [reflexivity|].
      exact (rank_tier_tr_sound tm n t ng_fuel ng_rounds E).
    + exact (IH tm).
Qed.

(** *** Tier Q: the wrapped QHBoundTr ladder, behind an untrusted
    quiet-candidate filter (the 8-way analog of [qh_candidate]) *)

Definition qhb_tmax_tr : nat :=
  fold_left Nat.max (map snd qhb_rungs) 0.

(** ONE long last-fire scan per machine, shared by every rung of both
    ladders (untrusted -- the checker re-verifies each pin via
    [wrap_pin_ok]).  The 16x look-ahead is the payer filter: a
    never-quasihalting drifter whose instruction recurs with period up
    to 16 x tmax is never pinned and never pays for a closure, and a
    genuinely quiet instruction's last fire is exact.  Scanning only
    the rung's own [t] steps would "pin" every busy instruction at its
    last within-window fire near the window edge. *)
Definition qh_last_fires (tm : TM) : list (Instr * nat) :=
  let times := last_fires tm (16 * qhb_tmax_tr) c0 0 no_fires in
  fold_right
    (fun tg acc =>
       match fire_time times tg with
       | Some s => (tg, s) :: acc
       | None => acc
       end) [] all_Instr.

(** Exact equality with the old eight simulations, including list order,
    never-fired targets, the halting configuration and the horizon boundary. *)
Lemma qh_last_fires_spec : forall tm,
  qh_last_fires tm =
  fold_right
    (fun tg acc =>
       match last_fire tm (16 * qhb_tmax_tr) c0 0 tg None with
       | Some s => (tg, s) :: acc
       | None => acc
       end) [] all_Instr.
Proof.
  intros tm. unfold qh_last_fires.
  generalize all_Instr. intros tgs. induction tgs as [|[q s] tgs IH];
    cbn [fold_right].
  - reflexivity.
  - rewrite last_fires_spec, IH. destruct q, s; reflexivity.
Qed.

(** the claimed-quiet set at horizon [t]: a transition-QH machine
    typically quiets SEVERAL instructions, and the wrapped closure's
    liveness gate only passes when all of them are wrapped, so the
    whole set goes in one checker call *)
Definition qh_pins_of (lf : list (Instr * nat)) (t : nat)
  : list (Instr * nat) :=
  filter (fun p => snd p <? t) lf.

Definition try_qhbtr_at (tm : TM) (lf : list (Instr * nat))
    (nt : nat * nat) : bool :=
  let '(n, t) := nt in
  (S t <=? B) &&
  ngram_check_qhboundtr tm (qh_pins_of lf t) n t ng_fuel ng_rounds.

(** the lex rung: same wrapped closure, but each appearing
    instruction may be discharged by a RankSearch certificate --
    the plain rank cannot exist once the abstract closure self-loops
    inside a sweep's uniform runs, which is nearly every machine the
    candidate filter passes *)
Definition try_qhbtr_lex_at (tm : TM) (lf : list (Instr * nat))
    (nt : nat * nat) : bool :=
  let '(n, t) := nt in
  (S t <=? B) &&
  match csteps tm t c0 with
  | None => false
  | Some ct =>
      let pins := qh_pins_of lf t in
      let tmw := tm_wrap_trs tm (map fst pins) in
      let '(q1, (l, h, r)) := ct in
      let lset0 := gadds (ng_seed_side n l) gempty in
      let rset0 := gadds (ng_seed_side n r) gempty in
      let a0 := ng_start n ct in
      let '(lset, rset) :=
        ng_grow tmw a0 ng_fuel ng_rounds lset0 rset0 in
      let closure :=
        ng_explore tmw lset rset ng_fuel [] PositiveSet.empty [a0] in
      ngram_check_qhboundtr_lex tm pins n t ng_fuel ng_rounds
        (fun tg' => rank_procedure_tr tmw lset rset closure tg')
  end.

(** nested [if] rather than [||], the state census's own trap
    (Census/Decide.v [try_qhb]): [orb] is a function, so under
    call-by-value both ladders would evaluate even when the plain one
    wins *)
(** the wrapped-RepWL rung (CensusTr/RepWLTr [rw_tier_qhbtr]) *)
Definition try_rw_qhbtr_at (tm : TM) (lf : list (Instr * nat))
    (r : nat * nat * nat) : bool :=
  let '(L, T, t) := r in
  (S t <=? B) && rw_tier_qhbtr tm lf L T t rw_fuel rw_cut.

(** The candidate list is untrusted: the existing rung checkers verify
    every pin. Sharing this code lets a shorter scan try the same checkers. *)
Definition try_qhbtr_with_lf (tm : TM) (lf : list (Instr * nat)) : bool :=
  if existsb (fun p => snd p <? qhb_tmax_tr) lf then
    if anyb (try_qhbtr_at tm lf) qhb_rungs then true
    else if anyb (try_qhbtr_lex_at tm lf) qhb_lex_rungs then true
    else anyb (try_rw_qhbtr_at tm lf) rw_qhb_rungs
  else false.

Lemma try_qhbtr_with_lf_sound : forall tm lf,
  try_qhbtr_with_lf tm lf = true ->
  NonHalt tm /\ QHBoundTr B tm /\ QuasiHaltsTr tm.
Proof.
  intros tm lf H.
  unfold try_qhbtr_with_lf in H.
  apply andb_prop in H as [_ H].
  (* [if b then true else c] IS [orb b c] by definition *)
  apply orb_prop in H; destruct H as [H | H];
    [| apply orb_prop in H; destruct H as [H | H]].
  - (* plain acyclicity gate *)
    rewrite anyb_existsb in H; apply existsb_exists in H;
      destruct H as ([n t] & _ & H);
      unfold try_qhbtr_at in H;
      apply andb_prop in H as [HB H]; apply Nat.leb_le in HB.
    destruct (ngram_check_qhboundtr_sound tm
                (qh_pins_of lf t) n t
                ng_fuel ng_rounds H) as (Hnh & Hqb & Hqh).
    split; [exact Hnh|].
    split; [|exact Hqh].
    intros tg' s' Hq.
    specialize (Hqb tg' s' Hq). lia.
  - (* lex gate *)
    rewrite anyb_existsb in H; apply existsb_exists in H;
      destruct H as ([n t] & _ & H);
      unfold try_qhbtr_lex_at in H;
      apply andb_prop in H as [HB H]; apply Nat.leb_le in HB.
    destruct (csteps tm t c0) as [[q1 [[l h] r]]|] eqn:Ect; [|discriminate].
    match type of H with
    | (let '(_, _) := ?G in _) = true => destruct G as [lset rset]
    end.
    cbv beta iota zeta in H.
    destruct (ngram_check_qhboundtr_lex_sound tm
                (qh_pins_of lf t) n t
                ng_fuel ng_rounds _ H) as (Hnh & Hqb & Hqh).
    split; [exact Hnh|].
    split; [|exact Hqh].
    intros tg' s' Hq.
    specialize (Hqb tg' s' Hq). lia.
  - (* wrapped-RepWL gate *)
    rewrite anyb_existsb in H; apply existsb_exists in H;
      destruct H as ([[L T] t] & _ & H);
      unfold try_rw_qhbtr_at in H;
      apply andb_prop in H as [HB H]; apply Nat.leb_le in HB.
    destruct (rw_tier_qhbtr_sound tm lf L T t
                rw_fuel rw_cut H) as (Hnh & Hqb & Hqh).
    split; [exact Hnh|].
    split; [|exact Hqh].
    intros tg' s' Hq.
    specialize (Hqb tg' s' Hq). lia.
Qed.

(** The original sixteen-times-lookahead checker remains the fallback. *)
Definition try_qhbtr_reference (tm : TM) : bool :=
  try_qhbtr_with_lf tm (qh_last_fires tm).

(** A successful short scan avoids the longer simulation. Every candidate
    still passes the same verified checkers; a failed attempt falls back to
    the original horizon and rung order, preserving all old successes. *)
Definition qh_last_fires_prefix (tm : TM) : list (Instr * nat) :=
  let times := last_fires tm (4 * qhb_tmax_tr) c0 0 no_fires in
  fold_right (fun tg acc =>
    match fire_time times tg with
    | Some s => (tg, s) :: acc
    | None => acc end) [] all_Instr.

(** Every full-horizon candidate below the rung cutoff is already present
    after the short prefix. Never-fired instructions cause no exception:
    their first later timestamp is at or beyond the cutoff. *)
Lemma qh_full_candidate_has_prefix : forall tm,
  existsb (fun p => snd p <? qhb_tmax_tr) (qh_last_fires tm) = true ->
  existsb (fun p => snd p <? qhb_tmax_tr) (qh_last_fires_prefix tm) = true.
Proof.
  intros tm H. unfold qh_last_fires, qh_last_fires_prefix in *.
  rewrite fold_fire_candidates in *.
  apply existsb_exists in H. destruct H as [tg [Hin H]].
  apply existsb_exists. exists tg. split; [exact Hin|].
  rewrite last_fires_spec in *.
  unfold old_fire_before in H.
  destruct (last_fire tm (16 * qhb_tmax_tr) c0 0 tg
    (fire_time no_fires tg)) as [s|] eqn:E; [|discriminate].
  apply Nat.ltb_lt in H.
  replace (16 * qhb_tmax_tr) with
    (4 * qhb_tmax_tr + 12 * qhb_tmax_tr) in E by lia.
  pose proof (last_fire_prefix_old tm (4*qhb_tmax_tr) (12*qhb_tmax_tr)
    c0 0 tg (fire_time no_fires tg) qhb_tmax_tr s ltac:(lia) H E) as Es.
  rewrite Es. unfold old_fire_before. apply Nat.ltb_lt. exact H.
Qed.

Lemma qh_prefix_negative_reference : forall tm,
  existsb (fun p => snd p <? qhb_tmax_tr) (qh_last_fires_prefix tm) = false ->
  try_qhbtr_reference tm = false.
Proof.
  intros tm Hprefix. unfold try_qhbtr_reference, try_qhbtr_with_lf.
  destruct (existsb (fun p => snd p <? qhb_tmax_tr) (qh_last_fires tm))
    eqn:Efull; [|reflexivity].
  apply qh_full_candidate_has_prefix in Efull.
  rewrite Hprefix in Efull. discriminate.
Qed.

(** The previous short-success/full-fallback implementation is retained
    for the exact equality theorem below. *)
Definition try_qhbtr_before_prefix_negative (tm : TM) : bool :=
  if try_qhbtr_with_lf tm (qh_last_fires_prefix tm) then true
  else try_qhbtr_reference tm.

(** Retained verbatim as the exact behavioral reference. *)
Definition try_qhbtr_prefix_negative_reference (tm : TM) : bool :=
  let lf := qh_last_fires_prefix tm in
  if try_qhbtr_with_lf tm lf then true
  else if existsb (fun p => snd p <? qhb_tmax_tr) lf
       then try_qhbtr_reference tm
       else false.

Definition qh_fire_scan_prefix (tm : TM) : FireScan :=
  last_fires_scan tm (4 * qhb_tmax_tr) c0 0 no_fires.

Lemma qh_fire_scan_prefix_candidates : forall tm,
  fire_candidates (scan_times (qh_fire_scan_prefix tm)) =
  qh_last_fires_prefix tm.
Proof.
  intros tm. unfold qh_fire_scan_prefix, qh_last_fires_prefix.
  rewrite last_fires_scan_times. reflexivity.
Qed.

Lemma qh_fire_scan_full_candidates : forall tm,
  fire_candidates
    (scan_times
      (resume_last_fires tm (12 * qhb_tmax_tr) (qh_fire_scan_prefix tm))) =
  qh_last_fires tm.
Proof.
  intros tm. unfold qh_fire_scan_prefix, qh_last_fires.
  rewrite last_fires_resume_times.
  replace (4 * qhb_tmax_tr + 12 * qhb_tmax_tr)
    with (16 * qhb_tmax_tr) by lia.
  reflexivity.
Qed.

(** Strict evaluation shares [prefix] between the short attempt and its
    continuation. Only a failed short attempt with an eligible old fire
    resumes; that resume performs at most 12*tmax new steps. *)
Definition try_qhbtr (tm : TM) : bool :=
  let prefix := qh_fire_scan_prefix tm in
  let lf := fire_candidates (scan_times prefix) in
  if try_qhbtr_with_lf tm lf then true
  else if existsb (fun p => snd p <? qhb_tmax_tr) lf
       then try_qhbtr_with_lf tm
         (fire_candidates
           (scan_times (resume_last_fires tm (12 * qhb_tmax_tr) prefix)))
       else false.

Lemma try_qhbtr_resume_spec : forall tm,
  try_qhbtr tm = try_qhbtr_prefix_negative_reference tm.
Proof.
  intros tm. unfold try_qhbtr, try_qhbtr_prefix_negative_reference.
  cbn zeta.
  repeat rewrite qh_fire_scan_prefix_candidates.
  rewrite qh_fire_scan_full_candidates.
  reflexivity.
Qed.

Lemma try_qhbtr_prefix_negative_spec : forall tm,
  try_qhbtr tm = try_qhbtr_before_prefix_negative tm.
Proof.
  intros tm. rewrite try_qhbtr_resume_spec.
  unfold try_qhbtr_prefix_negative_reference, try_qhbtr_before_prefix_negative.
  cbn zeta.
  destruct (try_qhbtr_with_lf tm (qh_last_fires_prefix tm)); [reflexivity|].
  destruct (existsb (fun p => snd p <? qhb_tmax_tr) (qh_last_fires_prefix tm))
    eqn:Eprefix; [reflexivity|].
  symmetry. apply qh_prefix_negative_reference. exact Eprefix.
Qed.

Lemma try_qhbtr_sound : forall tm,
  try_qhbtr tm = true ->
  NonHalt tm /\ QHBoundTr B tm /\ QuasiHaltsTr tm.
Proof.
  intros tm H. rewrite try_qhbtr_prefix_negative_spec in H.
  unfold try_qhbtr_before_prefix_negative in H.
  destruct (try_qhbtr_with_lf tm (qh_last_fires_prefix tm)) eqn:Es.
  - exact (try_qhbtr_with_lf_sound tm _ Es).
  - exact (try_qhbtr_with_lf_sound tm _ H).
Qed.

Lemma try_qhbtr_preserves : forall tm,
  try_qhbtr_reference tm = true -> try_qhbtr tm = true.
Proof.
  intros tm H. rewrite try_qhbtr_prefix_negative_spec.
  unfold try_qhbtr_before_prefix_negative.
  destruct (try_qhbtr_with_lf tm (qh_last_fires_prefix tm)); auto.
Qed.

(** *** Tier W: the RepWL ladder *)

Definition try_rw_tr (tm : TM) : bool :=
  anyb (fun '(L, T, t) => rw_tier_tr tm L T t rw_fuel rw_cut) rw_rungs.

Lemma try_rw_tr_sound : forall tm,
  try_rw_tr tm = true -> NeverQuasiHaltsTr tm.
Proof.
  intros tm H.
  unfold try_rw_tr in H.
  rewrite anyb_existsb in H.
  apply existsb_exists in H.
  destruct H as ([[L T] t] & _ & H).
  exact (rw_tier_tr_sound tm L T t rw_fuel rw_cut H).
Qed.

(** the walk decider: halting, lookups, cycles, the per-instruction
    n-gram never tier, the rank-rules never tier, the wrapped
    QHBoundTr tier, the RepWL never tier, defer the rest *)
Definition decide_easy_tr (pm qm dm : DeferredMap) (tm : TM) : QHResult :=
  match find_halt tm halt_gas 0 c0 with
  | Some (n, s, i) => if S n <=? B then R_Halt s i else R_Unknown
  | None =>
      if deferred_lookup pm tm then R_NeverQH else
      if deferred_lookup qm tm then R_QH else
      if deferred_lookup dm tm then R_Deferred else
      if scan_loops B tm halt_gas then R_Leaf else
      if scan_loops B tm loop_gas then R_Leaf else
      match try_ngram_tr ng_rungs tm with
      | R_NeverQH => R_NeverQH
      | _ =>
          match try_rank_tr rank_rungs tm with
          | R_NeverQH => R_NeverQH
          | _ =>
              if try_qhbtr tm then R_QH
              else if try_rw_tr tm then R_NeverQH
              else R_Unknown
          end
      end
  end.

Definition decide_easy_tr_before_resume (pm qm dm : DeferredMap) (tm : TM) : QHResult :=
  match find_halt tm halt_gas 0 c0 with
  | Some (n, s, i) => if S n <=? B then R_Halt s i else R_Unknown
  | None =>
      if deferred_lookup pm tm then R_NeverQH else
      if deferred_lookup qm tm then R_QH else
      if deferred_lookup dm tm then R_Deferred else
      if scan_loops B tm halt_gas then R_Leaf else
      if scan_loops B tm loop_gas then R_Leaf else
      match try_ngram_tr ng_rungs tm with
      | R_NeverQH => R_NeverQH
      | _ =>
          match try_rank_tr rank_rungs tm with
          | R_NeverQH => R_NeverQH
          | _ =>
              if try_qhbtr_prefix_negative_reference tm then R_QH
              else if try_rw_tr tm then R_NeverQH
              else R_Unknown
          end
      end
  end.

(** The whole decider has exactly the prefix-negative version's verdict. *)
Lemma decide_easy_tr_resume_spec : forall pm qm dm tm,
  decide_easy_tr pm qm dm tm = decide_easy_tr_before_resume pm qm dm tm.
Proof.
  intros pm qm dm tm. unfold decide_easy_tr, decide_easy_tr_before_resume.
  rewrite try_qhbtr_resume_spec. reflexivity.
Qed.

(** The dynamic checks may use a small search bound while stored proofs
    use the published bound. Only the former is evaluated by every walk
    worker; enlarging its certified bounds is purely logical. *)
Theorem decide_easy_tr_WF_larger : forall bound,
  B <= bound ->
  Forall (fun tm => NonHalt tm /\ QHBoundTr bound tm /\ QuasiHaltsTr tm) ProvQH ->
  QHDeciderTr_WF bound D
    (decide_easy_tr (dmap_of Prov) (dmap_of ProvQH) (dmap_of D)).
Proof.
  intros bound Hbound HPQ_bound tm.
  unfold decide_easy_tr.
  destruct (find_halt tm halt_gas 0 c0) as [[[n s] i]|] eqn:Eh.
  { destruct (S n <=? B) eqn:EB; [|exact I].
    apply Nat.leb_le in EB.
    destruct (find_halt_sound tm halt_gas 0 c0 n s i (eq_refl) Eh)
      as (tp & Hst & Hhd & Hnone).
    exists n, tp. repeat split; try assumption; lia. }
  destruct (deferred_lookup (dmap_of Prov) tm) eqn:Ep.
  { rewrite Forall_forall in HP.
    apply HP. apply deferred_lookup_In; exact Ep. }
  destruct (deferred_lookup (dmap_of ProvQH) tm) eqn:Epq.
  { rewrite Forall_forall in HPQ_bound.
    apply HPQ_bound. apply deferred_lookup_In; exact Epq. }
  destruct (deferred_lookup (dmap_of D) tm) eqn:Ed.
  { apply deferred_lookup_In; exact Ed. }
  destruct (scan_loops B tm halt_gas) eqn:El1.
  { destruct (scan_loops_sound_tr tm halt_gas El1) as [Hnh Hqb].
    split; [exact Hnh|]. eapply qhboundtr_mono; eauto. }
  destruct (scan_loops B tm loop_gas) eqn:El2.
  { destruct (scan_loops_sound_tr tm loop_gas El2) as [Hnh Hqb].
    split; [exact Hnh|]. eapply qhboundtr_mono; eauto. }
  destruct (try_ngram_tr_cases ng_rungs tm) as [[En Hn] | En]; rewrite En.
  { exact Hn. }
  destruct (try_rank_tr_cases rank_rungs tm) as [[Er Hr] | Er]; rewrite Er.
  { exact Hr. }
  destruct (try_qhbtr tm) eqn:Eq.
  { destruct (try_qhbtr_sound tm Eq) as [Hnh [Hqb Hqh]].
    split; [exact Hnh|]. split; [|exact Hqh].
    eapply qhboundtr_mono; eauto. }
  destruct (try_rw_tr tm) eqn:Ew.
  { exact (try_rw_tr_sound tm Ew). }
  exact I.
Qed.

Theorem decide_easy_tr_WF :
  QHDeciderTr_WF B D
    (decide_easy_tr (dmap_of Prov) (dmap_of ProvQH) (dmap_of D)).
Proof. apply decide_easy_tr_WF_larger; [lia|exact HPQ]. Qed.

End PipelineTr.
