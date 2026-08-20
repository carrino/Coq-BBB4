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
From BBB4.CensusTr Require Import TNF_QHTr.
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
  unfold cycle_leaf_check in H.
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
  destruct cand as [n1 p | [|] n1 P];
    unfold lp_check in H;
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
  unfold scan_loops in H.
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
  fold_right
    (fun tg acc =>
       match last_fire tm (16 * qhb_tmax_tr) c0 0 tg None with
       | Some s => (tg, s) :: acc
       | None => acc
       end) [] all_Instr.

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
Definition try_qhbtr (tm : TM) : bool :=
  let lf := qh_last_fires tm in
  existsb (fun p => snd p <? qhb_tmax_tr) lf &&
  (if anyb (try_qhbtr_at tm lf) qhb_rungs then true
   else anyb (try_qhbtr_lex_at tm lf) qhb_lex_rungs).

Lemma try_qhbtr_sound : forall tm,
  try_qhbtr tm = true ->
  NonHalt tm /\ QHBoundTr B tm /\ QuasiHaltsTr tm.
Proof.
  intros tm H.
  unfold try_qhbtr in H.
  apply andb_prop in H as [_ H].
  (* [if b then true else c] IS [orb b c] by definition *)
  apply orb_prop in H; destruct H as [H | H];
    rewrite anyb_existsb in H;
    apply existsb_exists in H;
    destruct H as ([n t] & _ & H);
    unfold try_qhbtr_at, try_qhbtr_lex_at in H;
    apply andb_prop in H as [HB H];
    apply Nat.leb_le in HB.
  - (* plain acyclicity gate *)
    destruct (ngram_check_qhboundtr_sound tm
                (qh_pins_of (qh_last_fires tm) t) n t
                ng_fuel ng_rounds H) as (Hnh & Hqb & Hqh).
    split; [exact Hnh|].
    split; [|exact Hqh].
    intros tg' s' Hq.
    specialize (Hqb tg' s' Hq). lia.
  - (* lex gate *)
    destruct (csteps tm t c0) as [[q1 [[l h] r]]|] eqn:Ect; [|discriminate].
    match type of H with
    | (let '(_, _) := ?G in _) = true => destruct G as [lset rset]
    end.
    cbv beta iota zeta in H.
    destruct (ngram_check_qhboundtr_lex_sound tm
                (qh_pins_of (qh_last_fires tm) t) n t
                ng_fuel ng_rounds _ H) as (Hnh & Hqb & Hqh).
    split; [exact Hnh|].
    split; [|exact Hqh].
    intros tg' s' Hq.
    specialize (Hqb tg' s' Hq). lia.
Qed.

(** the phase-1 decider: halting, lookups, cycles, the per-instruction
    n-gram never tier, the wrapped QHBoundTr tier, defer the rest *)
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
          | _ => if try_qhbtr tm then R_QH else R_Unknown
          end
      end
  end.

Theorem decide_easy_tr_WF :
  QHDeciderTr_WF B D
    (decide_easy_tr (dmap_of Prov) (dmap_of ProvQH) (dmap_of D)).
Proof.
  intro tm.
  unfold decide_easy_tr.
  destruct (find_halt tm halt_gas 0 c0) as [[[n s] i]|] eqn:Eh.
  { destruct (S n <=? B) eqn:EB; [|exact I].
    apply Nat.leb_le in EB.
    destruct (find_halt_sound tm halt_gas 0 c0 n s i (eq_refl) Eh)
      as (tp & Hst & Hhd & Hnone).
    exists n, tp. auto. }
  destruct (deferred_lookup (dmap_of Prov) tm) eqn:Ep.
  { rewrite Forall_forall in HP.
    apply HP. apply deferred_lookup_In; exact Ep. }
  destruct (deferred_lookup (dmap_of ProvQH) tm) eqn:Epq.
  { rewrite Forall_forall in HPQ.
    apply HPQ. apply deferred_lookup_In; exact Epq. }
  destruct (deferred_lookup (dmap_of D) tm) eqn:Ed.
  { apply deferred_lookup_In; exact Ed. }
  destruct (scan_loops B tm halt_gas) eqn:El1.
  { exact (scan_loops_sound_tr tm halt_gas El1). }
  destruct (scan_loops B tm loop_gas) eqn:El2.
  { exact (scan_loops_sound_tr tm loop_gas El2). }
  destruct (try_ngram_tr_cases ng_rungs tm) as [[En Hn] | En]; rewrite En.
  { exact Hn. }
  destruct (try_rank_tr_cases rank_rungs tm) as [[Er Hr] | Er]; rewrite Er.
  { exact Hr. }
  destruct (try_qhbtr tm) eqn:Eq.
  { exact (try_qhbtr_sound tm Eq). }
  exact I.
Qed.

End PipelineTr.
