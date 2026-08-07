(** * Census/Decide: the quasihalting decider pipeline for the census.

    The Loops-tier + n-gram-tier + deferred-lookup pipeline run on
    every node of the TNF tree (NEXT_SESSION.md "Scope B"), built the
    repo way: UNTRUSTED in-Coq searches propose parameters, verified
    checkers re-derive everything.

    Tiers, in order:

    - halt search ([find_halt], verified): the machine reached its
      undefined transition -> [R_Halt] (the tree expands there);

    - in-place cycle ([scan_cycle] untrusted -> [cycle_leaf_check]
      verified): head-relative configuration repeats; gives [NonHalt]
      and [QHBound n1] (any eventually-quiet state made its last visit
      before the cycle started) -> [R_Leaf];

    - translated cycle ([tc_candidates]/[tc_measure_W] untrusted ->
      [tcycler_leaf_check] verified, both sides via [mirror_tm]): the
      guarded-window lap argument of Checkers/TCycler.v, reduced to
      the census contract [NonHalt /\ QHBound n1] -> [R_Leaf];

    - n-gram CPS ladder ([ngram_check_neverqh], the existing fully
      generic verified decider): -> [R_NeverQH];

    - deferred lookup: machine is in the explicit deferred list
      (holdout list + measured hard residue) -> [R_Deferred];

    - ranking rules ladder ([rank_tier]) -> [R_NeverQH];

    - wrapped QHBound ladder ([ngram_check_qhbound] plain acyclicity,
      then [ngram_check_qhbound_lex] with the in-Coq RankSearch
      certificates, both behind an untrusted quiet-candidate filter):
      prefix-quiet quasihalters -> [R_QH];

    - RepWL ladder ([rw_tier]: block-list abstraction closure + the
      in-Coq RepWLSearch rules-(a)/(b) certificates through the
      verified [rw_check_neverqh]) -> [R_NeverQH].

    Everything else falls to [R_Unknown] and would sit in the queue's
    back list -- the census closes only if that never happens. *)

From Coq Require Import Arith Lia Bool List NArith PArith ZArith.
From Coq Require Import FSets.FMapPositive.
From Coq Require Import FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement CTape GTape Mirror PosEnc.
From BBB4.Checkers Require Import Cycle TCycler NGram Wrap RepWL.
From BBB4.Census Require Import TNF_QH RankSearch RepWLSearch.
Import ListNotations.

Set Default Goal Selector "!".

(** ** Tier H: verified halt search *)

Fixpoint find_halt (tm : TM) (gas k : nat) (c : cconf)
  : option (nat * St * Sym) :=
  match gas with
  | 0 => None
  | S g =>
      match cstep tm c with
      | Some c' => find_halt tm g (S k) c'
      | None => let '(q, (l, h, r)) := c in Some (k, q, h)
      end
  end.

Lemma cstep_none : forall tm q l h r,
  cstep tm (q, (l, h, r)) = None -> tm q h = None.
Proof.
  intros tm q l h r H. unfold cstep in H.
  destruct (tm q h) as [tr|]; [discriminate | reflexivity].
Qed.

Lemma find_halt_sound : forall tm gas k c n s i,
  csteps tm k c0 = Some c ->
  find_halt tm gas k c = Some (n, s, i) ->
  exists tp, stepn tm n InitES = Some (s, tp) /\ t_head tp = i /\ tm s i = None.
Proof.
  intros tm.
  induction gas; intros k c n s i Hk H; simpl in H; [discriminate|].
  destruct (cstep tm c) as [c'|] eqn:E.
  - apply (IHgas (S k) c'); [|assumption].
    replace (S k) with (k + 1) by lia.
    rewrite csteps_add, Hk, csteps_1. exact E.
  - destruct c as [q [[l h] r]].
    injection H as <- <- <-.
    exists (lift_tape (l, h, r)).
    pose proof (csteps_lift tm k c0 (q, (l, h, r)) Hk) as Hl.
    rewrite lift_c0 in Hl.
    split; [exact Hl|].
    split; [reflexivity|].
    exact (cstep_none tm q l h r E).
Qed.

(** ** Tier C: in-place (head-relative) cycles *)

Definition cycle_leaf_check (tm : TM) (n1 p : nat) : bool :=
  (0 <? p) &&
  match csteps tm n1 c0, csteps tm (n1 + p) c0 with
  | Some a, Some b => ceqb a b
  | _, _ => false
  end.

(** visits at or after the cycle start recur forever, so any
    eventually-quiet state was last seen strictly before [n1] *)
Lemma cycle_qhbound : forall tm n1 p E,
  0 < p ->
  stepn tm n1 InitES = Some E ->
  stepn tm p E = Some E ->
  QHBound n1 tm.
Proof.
  intros tm n1 p E Hp H1 Hloop q s [Hvis Hq].
  destruct (le_lt_dec n1 s) as [Hge | Hlt]; [| lia].
  exfalso.
  destruct Hvis as (c & Hc & Hqc).
  apply (Hq (s + p)); [lia|].
  exists c. split; [| exact Hqc].
  (* the configuration at s recurs at s + p: fold through the loop *)
  replace (s + p) with (n1 + (p + (s - n1))) by lia.
  rewrite stepn_add, H1.
  change (stepn tm (p + (s - n1)) E = Some c).
  rewrite stepn_add, Hloop.
  change (stepn tm (s - n1) E = Some c).
  replace s with (n1 + (s - n1)) in Hc by lia.
  rewrite stepn_add, H1 in Hc.
  exact Hc.
Qed.

Lemma cycle_leaf_check_sound : forall tm n1 p,
  cycle_leaf_check tm n1 p = true ->
  NonHalt tm /\ QHBound n1 tm.
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
  - exact (cycle_qhbound tm n1 p (lift a) Hp Ha Hloop).
Qed.

(** ** Tier T: translated cycles (guarded-window laps) *)

Definition tcycler_leaf_check (tm : TM) (n1 P W : nat) : bool :=
  (0 <? P) &&
  match csteps tm n1 c0 with
  | Some (q1, (l1, h1, r1)) =>
      let g1 : cconf := (q1, (firstn_pad W l1, h1, r1)) in
      match gsteps tm P g1 with
      | Some g2 => gmatch g1 g2
      | None => false
      end
  | None => false
  end.

Lemma tcycler_leaf_check_sound : forall tm n1 P W,
  tcycler_leaf_check tm n1 P W = true ->
  NonHalt tm /\ QHBound n1 tm.
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
  - (* non-halting, exactly as in tcycler_check_qh_sound *)
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
  - (* any quiet state was last visited before the anchor *)
    intros q s [Hvis Hq].
    destruct (le_lt_dec n1 s) as [Hge | Hlt]; [| lia].
    exfalso.
    destruct Hvis as (c & Hc & Hqc).
    destruct (tcycler_fold tm n1 P g1 g2 rho0 Hp HA E2 H s Hge)
      as (i & gi & rho & Hi & Hgi & Hfold).
    rewrite Hfold in Hc. injection Hc as <-.
    (* pump the window occurrence one lap past s *)
    destruct (tcycler_laps tm n1 P g1 g2 rho0 HA E2 H (S s)) as [rho' Hrho'].
    apply (Hq (n1 + (S s) * P + i)); [nia|].
    exists (glift rho' gi).
    split.
    + replace (n1 + (S s) * P + i) with ((n1 + (S s) * P) + i) by lia.
      rewrite stepn_add, Hrho'.
      apply gsteps_lift; exact Hgi.
    + rewrite glift_state.
      rewrite glift_state in Hqc. exact Hqc.
Qed.

Corollary tcycler_leaf_check_sound_L : forall tm n1 P W,
  tcycler_leaf_check (mirror_tm tm) n1 P W = true ->
  NonHalt tm /\ QHBound n1 tm.
Proof.
  intros tm n1 P W H.
  destruct (tcycler_leaf_check_sound (mirror_tm tm) n1 P W H) as [Hnh Hb].
  split.
  - apply mirror_nonhalt; exact Hnh.
  - apply qhbound_mirror; exact Hb.
Qed.

(** ** Untrusted searches

    These only propose (n1, p) / (n1, P, W) candidates; the verified
    checkers above re-derive everything, so nothing here needs (or
    has) a proof. *)

(** rolling hash of the head-relative tape: [hrel] tracks
    (sum over 1-cells j of r^(j - head)) mod M, so equal head-relative
    configurations (what [ceqb] compares, padding-blind) share keys.
    A write toggles the head cell (+/- r^0 = 1); a head move rescales
    by r or its inverse.  M = 2^31 - 1; hashRinv * hashR = 1 mod M. *)
Definition hashM : N := 2147483647%N.
Definition hashR : N := 1234577%N.
Definition hashRinv : N := 1020407710%N.

Definition sym1 (s : Sym) : N := match s with S0 => 0 | S1 => 1 end.

Definition scan_key (q : St) (h : Sym) (hrel : N) : positive :=
  N.succ_pos ((N.of_nat (St_to_nat q) * 2 + sym1 h) * hashM + hrel).

(** in-place-cycle scan: walk [gas] steps keeping a hash-keyed map of
    seen configurations (one slot per key; a key hit is confirmed by
    [ceqb] and otherwise overwritten, so hash collisions can only delay
    detection, never fake it -- and the verified [cycle_leaf_check]
    re-derives everything anyway).  Returns the first exact
    head-relative repeat (n1, p). *)
Fixpoint scan_cycle0 (tm : TM) (gas k : nat) (c : cconf) (hrel : N)
    (seen : PositiveMap.tree (nat * cconf))
  : option (nat * nat) :=
  match gas with
  | 0 => None
  | S g =>
      let '(q, (l, h, r)) := c in
      let key := scan_key q h hrel in
      let step_on :=
        fun (seen' : PositiveMap.tree (nat * cconf)) =>
        match tm q h with
        | None => None
        | Some tr =>
            match cstep tm c with
            | None => None
            | Some c' =>
                let hrel1 :=
                  match h, t_write tr with
                  | S0, S1 => ((hrel + 1) mod hashM)%N
                  | S1, S0 => ((hrel + (hashM - 1)) mod hashM)%N
                  | _, _ => hrel
                  end in
                let hrel2 :=
                  match t_dir tr with
                  | DR => ((hrel1 * hashRinv) mod hashM)%N
                  | DL => ((hrel1 * hashR) mod hashM)%N
                  end in
                scan_cycle0 tm g (S k) c' hrel2 seen'
            end
        end in
      match PositiveMap.find key seen with
      | Some (k0, c0') =>
          if ceqb c0' c then Some (k0, k - k0)
          else step_on (PositiveMap.add key (k, c) seen)
      | None => step_on (PositiveMap.add key (k, c) seen)
      end
  end.

Definition scan_cycle (tm : TM) (gas : nat) : option (nat * nat) :=
  scan_cycle0 tm gas 0 c0 0%N (PositiveMap.empty _).

(** record log: configuration indices (and states) where the head
    stands on never-visited ground, per side *)
Fixpoint scan_records0 (tm : TM) (gas k : nat) (c : cconf)
    (accR accL : list (nat * St))
  : list (nat * St) * list (nat * St) :=
  match gas with
  | 0 => (accR, accL)
  | S g =>
      let '(q, (l, h, r)) := c in
      match tm q h with
      | None => (accR, accL)
      | Some tr =>
          match cstep tm c with
          | None => (accR, accL)
          | Some c' =>
              (* a record = stepping OFF the visited extent: a right
                 move from the right edge (r = []), symmetrically left *)
              let recR := match t_dir tr, r with
                          | DR, [] => true | _, _ => false end in
              let recL := match t_dir tr, l with
                          | DL, [] => true | _, _ => false end in
              scan_records0 tm g (S k) c'
                (if recR then (S k, fst c') :: accR else accR)
                (if recL then (S k, fst c') :: accL else accL)
          end
      end
  end.

(** the blank start configuration is itself on virgin ground, so it
    counts as a record on both sides (the C measurement tool seeds the
    same baseline entry) *)
Definition scan_records (tm : TM) (gas : nat)
  : list (nat * St) * list (nat * St) :=
  scan_records0 tm gas 0 c0 [(0, StA)] [(0, StA)].

(** the canonical anchor pairs: for each of the two newest records,
    its nearest earlier same-state record.  Verified re-checks are the
    expensive part, so at most 2 candidates per side; the C measurement
    tool uses the same rule. *)
Fixpoint first_same (q : St) (l : list (nat * St)) : option nat :=
  match l with
  | [] => None
  | (a, qa) :: t => if st_eqb qa q then Some a else first_same q t
  end.

Definition tc_pairs (recs : list (nat * St)) : list (nat * nat) :=
  match recs with
  | (b1, q1) :: t1 =>
      (match first_same q1 t1 with
       | Some a => [(a, b1 - a)] | None => [] end) ++
      (match t1 with
       | (b2, q2) :: t2 =>
           match first_same q2 t2 with
           | Some a => [(a, b2 - a)] | None => [] end
       | [] => [] end)
  | [] => []
  end.

(** measure the lap's excursion below the anchor head: walk [P] steps
    from the configuration at [n1], tracking max depth below start *)
Fixpoint lap_depth0 (tm : TM) (p : nat) (c : cconf) (cur maxd : Z) : Z :=
  match p with
  | 0 => maxd
  | S p' =>
      let '(q, (l, h, r)) := c in
      match tm q h with
      | None => maxd
      | Some tr =>
          match cstep tm c with
          | None => maxd
          | Some c' =>
              let cur' := match t_dir tr with
                          | DL => (cur + 1)%Z
                          | DR => (cur - 1)%Z
                          end in
              lap_depth0 tm p' c' cur' (Z.max maxd cur')
          end
      end
  end.

Definition tc_measure_W (tm : TM) (n1 P : nat) : nat :=
  match csteps tm n1 c0 with
  | Some c => Z.to_nat (lap_depth0 tm P c 0 0)
  | None => 0
  end.

(** last visit of [q] among the configurations at offsets
    [k .. k + gas - 1] (untrusted: the QHBound checkers re-verify
    the returned index) *)
Fixpoint last_visit (tm : TM) (gas : nat) (c : cconf) (k : nat)
    (q : St) (best : option nat) : option nat :=
  match gas with
  | 0 => best
  | S g =>
      let best' := if st_eqb (fst c) q then Some k else best in
      match cstep tm c with
      | None => best'
      | Some c' => last_visit tm g c' (S k) q best'
      end
  end.

(** ** The one-pass loop scan (BB5's loop1_decider, adapted)

    UNTRUSTED candidate generator replacing the per-step hash+map
    [scan_cycle] and the [scan_records]/[tc_pairs] record walk: ONE
    simulation pass consing a compact per-step entry (state, read
    symbol, head position, edge flags -- no hashing, no maps), then
    ONE backward scan from the last configuration proposing in-place
    ([LpCycle]) and translated ([LpTC], both directions -- no mirror
    re-scan) candidates, each confirmed by the EXISTING verified
    checkers ([cycle_leaf_check] / [tcycler_leaf_check]).  Mirrors
    Coq-BB5's [find_loop1] design: state+symbol compare first, so
    mismatched rewinds cost ~nothing. *)

Record lp_ent : Type := mkLpEnt {
  lp_q : St; lp_s : Sym; lp_pos : Z;
  lp_rrec : bool; lp_lrec : bool; lp_k : N }.

Inductive lp_cand : Type :=
  | LpCycle (n1 p : nat)
  | LpTC (d : Dir) (n1 P : nat).

Fixpoint lp_run (tm : TM) (gas : nat) (k : N) (c : cconf) (pos : Z)
    (hist : list lp_ent) : list lp_ent :=
  match gas with
  | 0 => hist
  | S g =>
      let '(q, (l, h, r)) := c in
      let e := mkLpEnt q h pos
                 (match r with [] => true | _ :: _ => false end)
                 (match l with [] => true | _ :: _ => false end) k in
      match tm q h with
      | None => hist
      | Some tr =>
          match cstep tm c with
          | None => hist
          | Some c' =>
              let pos' := match t_dir tr with
                          | DR => (pos + 1)%Z
                          | DL => (pos - 1)%Z
                          end in
              lp_run tm g (N.succ k) c' pos' (e :: hist)
          end
      end
  end.

(** pairwise state+symbol rewind of the two history chains.

    Written with NESTED IFS rather than [&&]: Coq's [&&] is [andb], a
    function, so under call-by-value BOTH arguments are evaluated --
    the recursive call ran even when the head comparison had already
    failed, making every rewind walk its full [n] entries regardless.
    This is the same boolean function (see
    Tests/Loop1Scan_Regression.v, which pins it against a reference
    copy of the [&&] form), so no candidate, catch or census result
    changes; only the cost does. *)
Fixpoint lp_rewind (l0 l1 : list lp_ent) (n : N) : bool :=
  match l0, l1 with
  | a :: l0', b :: l1' =>
      if N.eqb n 0 then true
      else if st_eqb (lp_q a) (lp_q b)
           then if sym_eqb (lp_s a) (lp_s b)
                then lp_rewind l0' l1' (N.pred n)
                else false
           else false
  | _, _ => N.eqb n 0
  end.

(** backward scan: [h0]/[tl0] fixed at the last configuration, [l1]
    walks deeper; [cap] bounds emitted candidates (each costs one
    verified re-check downstream).  The rewind filter is skipped when
    the history is too short to rewind a full period (the verified
    check is the authority either way).

    The guard nests its tests instead of using [&&] for the reason
    given at [lp_rewind]: with [andb] the rewind was evaluated for
    EVERY history entry, including the overwhelming majority whose
    state or symbol already differs -- an O(n) rewind per entry over
    an O(n) history, i.e. the quadratic that made the gas-512 rung
    cost 13.4x the gas-130 one for 4x the gas.  Same boolean, same
    candidates; only the cost changes. *)
Definition lp_guard (h0 h1 : lp_ent) (tl0 l1' : list lp_ent) : bool :=
  let P := N.sub (lp_k h0) (lp_k h1) in
  if st_eqb (lp_q h0) (lp_q h1)
  then if sym_eqb (lp_s h0) (lp_s h1)
       then (if N.leb (N.mul 2 P) (lp_k h0) then lp_rewind tl0 l1' P
             else true)
       else false
  else false.

Fixpoint lp_scan (h0 : lp_ent) (tl0 l1 : list lp_ent) (cap : nat)
    (acc : list lp_cand) : list lp_cand :=
  match l1 with
  | [] => rev acc
  | h1 :: l1' =>
      match cap with
      | 0 => rev acc
      | S cap' =>
          let P := N.sub (lp_k h0) (lp_k h1) in
          if lp_guard h0 h1 tl0 l1'
          then
            match
              match Z.compare (lp_pos h0) (lp_pos h1) with
              | Eq => Some (fun n1 => LpCycle n1 (N.to_nat P))
              | Gt => if lp_rrec h1
                      then Some (fun n1 => LpTC DR n1 (N.to_nat P))
                      else None
              | Lt => if lp_lrec h1
                      then Some (fun n1 => LpTC DL n1 (N.to_nat P))
                      else None
              end
            with
            | Some mk =>
                (* anchor reduction: the verified checks re-simulate
                   [n1] steps, so try phase-equivalent EARLY anchors
                   first (they fail harmlessly if they land in the
                   transient prefix) and the found anchor last.
                   [N.modulo _ 0 = 0] where [Nat.modulo _ 0 = n], so
                   the P = 0 case is guarded to keep the binary form
                   computing exactly what the unary one did. *)
                let n1 := lp_k h1 in
                let b := if N.eqb P 0 then n1 else N.modulo n1 P in
                let mkn := fun x : N => mk (N.to_nat x) in
                let cs :=
                  if N.ltb (N.add b P) n1
                  then [mkn b; mkn (N.add b P); mkn n1]
                  else if N.ltb b n1 then [mkn b; mkn n1]
                  else [mkn n1] in
                lp_scan h0 tl0 l1' cap' (rev_append cs acc)
            | None => lp_scan h0 tl0 l1' (S cap') acc
            end
          else lp_scan h0 tl0 l1' (S cap') acc
      end
  end.

(** record-pair candidates from the SAME history, replicating
    [scan_records]/[tc_pairs] EXACTLY.

    The first cut of this rule approximated records by the entry
    flags alone ([lp_rrec e] = "standing at the right edge"), pairing
    PRE-move states at pre-move indices.  [scan_records0] is
    stricter: a record is a step OFF the visited extent -- a DR move
    from [r = []] (symmetrically left) -- logged at the POST-move
    index with the POST-move state.  The mismatch left translated
    cyclers only the old [scan_ct] block could catch (measured: 46 of
    1,440 sampled machines), which is what kept that 42.6 ms/machine
    block alive as a fallback.

    Both configs of every step sit in the history as CONSECUTIVE
    entries, and the move direction is the sign of the position
    delta, so the exact record list is recoverable with no second
    walk.  The one step the history does not contain is the last one
    ([lp_run] conses pre-step entries only), recovered from the head
    entry's own transition. *)

Fixpoint lp_reclists (hist : list lp_ent)
  : list (N * St) * list (N * St) :=
  match hist with
  | e2 :: ((e1 :: _) as t) =>
      let '(rR, rL) := lp_reclists t in
      if (lp_pos e1 <? lp_pos e2)%Z
      then (if lp_rrec e1
            then ((lp_k e2, lp_q e2) :: rR, rL) else (rR, rL))
      else (if lp_lrec e1
            then (rR, (lp_k e2, lp_q e2) :: rL) else (rR, rL))
  | _ =>
      (* the blank start is itself on virgin ground on both sides --
         the same baseline entry [scan_records] seeds *)
      ([(0%N, StA)], [(0%N, StA)])
  end.

Definition lp_records (tm : TM) (hist : list lp_ent)
  : list (N * St) * list (N * St) :=
  let '(rR, rL) := lp_reclists hist in
  match hist with
  | h0 :: _ =>
      match tm (lp_q h0) (lp_s h0) with
      | Some tr =>
          match t_dir tr with
          | DR => if lp_rrec h0
                  then ((N.succ (lp_k h0), t_next tr) :: rR, rL)
                  else (rR, rL)
          | DL => if lp_lrec h0
                  then (rR, (N.succ (lp_k h0), t_next tr) :: rL)
                  else (rR, rL)
          end
      | None => (rR, rL)
      end
  | [] => (rR, rL)
  end.

Fixpoint lp_first_st (q : St) (l : list (N * St)) : option N :=
  match l with
  | [] => None
  | (a, qa) :: t => if st_eqb qa q then Some a else lp_first_st q t
  end.

(** the first [k] same-state record indices, nearest first *)
Fixpoint lp_first_sts (k : nat) (q : St) (l : list (N * St))
  : list N :=
  match k with
  | 0 => []
  | S k' =>
      match l with
      | [] => []
      | (a, qa) :: t =>
          if st_eqb qa q then a :: lp_first_sts k' q t
          else lp_first_sts k q t
      end
  end.

(** [tc_pairs] verbatim -- for each of the two newest records, a
    [LpTC] on its nearest earlier same-state record -- plus CYCLE
    twins on the [lp_cycle_K] nearest same-state records.

    The twins are what let this block subsume [scan_cycle] as well as
    the record walk: the model is head-relative, so a cycler that
    DRIFTS but repeats in padded-[cconf] space ([lpad_eqb] ignores a
    blank trail) is a plain [cycle_leaf_check] cycle -- which the
    guarded-window TCycler check, a different sufficient condition,
    can fail to certify.  A drifting cycler extends its extent every
    period, so its period is SOME record gap -- but not necessarily
    the nearest same-state gap: several same-state records can fall
    inside one period (measured on the 5-in-600 machines the block
    otherwise loses), so the twins try the [lp_cycle_K] nearest.
    [cycle_leaf_check] is two plain re-simulations, so the extra
    candidates stay cheap. *)
Definition lp_cycle_K : nat := 4.

Definition lp_pair_cands (d : Dir) (b : N) (q : St)
    (earlier : list (N * St)) : list lp_cand :=
  (match lp_first_st q earlier with
   | Some a => [LpTC d (N.to_nat a) (N.to_nat (N.sub b a))]
   | None => [] end) ++
  map (fun a => LpCycle (N.to_nat a) (N.to_nat (N.sub b a)))
      (lp_first_sts lp_cycle_K q earlier).

Definition lp_tc_pairs (d : Dir) (recs : list (N * St))
  : list lp_cand :=
  match recs with
  | (b1, q1) :: t1 =>
      lp_pair_cands d b1 q1 t1 ++
      (match t1 with
       | (b2, q2) :: t2 => lp_pair_cands d b2 q2 t2
       | [] => [] end)
  | [] => []
  end.

Definition lp_candidates (tm : TM) (gas : nat) : list lp_cand :=
  match lp_run tm gas 0%N c0 0%Z [] with
  | [] => []
  | (h0 :: tl) as hist =>
      let '(rR, rL) := lp_records tm hist in
      lp_scan h0 tl tl 6 []
      ++ lp_tc_pairs DR rR
      ++ lp_tc_pairs DL rL
  end.

(** ** Deferred lookup *)

Definition dir_eqb (a b : Dir) : bool :=
  match a, b with DL, DL | DR, DR => true | _, _ => false end.

Lemma dir_eqb_eq : forall a b, dir_eqb a b = true -> a = b.
Proof. intros [] []; simpl; congruence. Qed.

Definition otrans_eqb (a b : option Trans) : bool :=
  match a, b with
  | None, None => true
  | Some x, Some y =>
      sym_eqb (t_write x) (t_write y) &&
      dir_eqb (t_dir x) (t_dir y) &&
      st_eqb (t_next x) (t_next y)
  | _, _ => false
  end.

Lemma otrans_eqb_eq : forall a b, otrans_eqb a b = true -> a = b.
Proof.
  intros [x|] [y|] H; simpl in H; try discriminate; [|reflexivity].
  apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2].
  apply sym_eqb_spec in H1. apply dir_eqb_eq in H2. apply st_eqb_spec in H3.
  destruct x, y; simpl in *; congruence.
Qed.

Definition tm_eqb (a b : TM) : bool :=
  otrans_eqb (a StA S0) (b StA S0) && otrans_eqb (a StA S1) (b StA S1) &&
  otrans_eqb (a StB S0) (b StB S0) && otrans_eqb (a StB S1) (b StB S1) &&
  otrans_eqb (a StC S0) (b StC S0) && otrans_eqb (a StC S1) (b StC S1) &&
  otrans_eqb (a StD S0) (b StD S0) && otrans_eqb (a StD S1) (b StD S1).

Lemma tm_eqb_eq : forall a b, tm_eqb a b = true -> a = b.
Proof.
  intros a b H.
  unfold tm_eqb in H.
  repeat (apply andb_prop in H as [H ?]).
  apply functional_extensionality; intro q.
  apply functional_extensionality; intro s.
  destruct q, s; apply otrans_eqb_eq; assumption.
Qed.

Definition slot_code (o : option Trans) : N :=
  match o with
  | None => 0
  | Some tr =>
      (1 + (match t_write tr with S0 => 0 | S1 => 1 end) +
       2 * (match t_dir tr with DL => 0 | DR => 1 end) +
       4 * N.of_nat (St_to_nat (t_next tr)))%N
  end.

Definition tm_enc (tm : TM) : positive :=
  N.succ_pos
    (fold_left (fun acc o => (17 * acc + slot_code o)%N)
       [tm StA S0; tm StA S1; tm StB S0; tm StB S1;
        tm StC S0; tm StC S1; tm StD S0; tm StD S1] 0%N).

Definition DeferredMap : Type := PositiveMap.tree TM.

Definition dmap_of (D : list TM) : DeferredMap :=
  fold_right (fun h m => PositiveMap.add (tm_enc h) h m)
             (PositiveMap.empty TM) D.

Lemma dmap_of_In : forall D k h,
  PositiveMap.find k (dmap_of D) = Some h -> In h D.
Proof.
  induction D as [| h0 D IH]; intros k h H; simpl in H.
  - rewrite PositiveMap.gempty in H. discriminate.
  - destruct (Pos.eq_dec k (tm_enc h0)) as [-> | Hne].
    + rewrite PositiveMap.gss in H. injection H as <-. left; reflexivity.
    + rewrite PositiveMap.gso in H by exact Hne.
      right. exact (IH k h H).
Qed.

Definition deferred_lookup (dm : DeferredMap) (tm : TM) : bool :=
  match PositiveMap.find (tm_enc tm) dm with
  | Some h => tm_eqb tm h
  | None => false
  end.

Lemma deferred_lookup_In : forall D tm,
  deferred_lookup (dmap_of D) tm = true -> In tm D.
Proof.
  intros D tm H.
  unfold deferred_lookup in H.
  destruct (PositiveMap.find (tm_enc tm) (dmap_of D)) as [h|] eqn:E;
    [|discriminate].
  apply tm_eqb_eq in H. rewrite H.
  exact (dmap_of_In D (tm_enc tm) h E).
Qed.

(** The proven-machines tier reuses exactly the deferred map machinery
    (same [DeferredMap], [dmap_of], [tm_enc] + [tm_eqb] re-check); only
    the pipeline's response to a hit differs (R_NeverQH, not R_Deferred),
    justified by a [Forall NeverQuasiHaltsSt] certificate on the list. *)
Definition proven_lookup (pm : DeferredMap) (tm : TM) : bool :=
  deferred_lookup pm tm.

Lemma proven_lookup_In : forall P tm,
  proven_lookup (dmap_of P) tm = true -> In tm P.
Proof. exact deferred_lookup_In. Qed.

(** ** The pipeline *)

(** ** Winning-rung hints (BB5's [tm_decider_table] pattern)

    ADVISORY per-machine ladder hints generated offline by the C
    mirror (tools/census_ladder.c): [0] = the n-gram ladder is
    measured futile, go straight to the rank tier; [S k] = start the
    n-gram ladder at rung [S k] (1-based; rung 1 hints are omitted at
    generation, they save nothing).  A wrong or stale hint costs one
    extra ladder attempt and then falls back to the FULL ladder, so
    hints carry no soundness weight (the WF lemma quantifies over the
    map) and no completeness weight (the fallback is total). *)
Definition HintMap : Type := PositiveMap.tree nat.

Definition hmap_of (rows : list (positive * nat)) : HintMap :=
  fold_right (fun '(k, v) m => PositiveMap.add k v m)
             (PositiveMap.empty _) rows.

Definition hint_lookup (hm : HintMap) (tm : TM) : option nat :=
  PositiveMap.find (tm_enc tm) hm.

Section Pipeline.

Variable B : nat.              (** global score bound *)
Variable D : list TM.          (** the deferred list *)

Variable halt_gas : nat.       (** gas for the halt search *)
Variable loop_gas : nat.       (** gas for the cycle/record scans *)
Variable ng_fuel : nat.        (** worklist fuel for the n-gram closures *)
Variable ng_rounds : nat.      (** growth rounds for the n-gram sets *)
Variable ng_rungs : list (nat * nat).   (** (window n, prefix t) ladder *)
Variable rank_rungs : list (nat * nat). (** ladder for the rank-rules tier *)
Variable qhb_rungs : list (nat * nat).  (** (window n, prefix t) ladder for
                                            the wrapped-QHBound tiers *)
Variable rw_rungs : list (nat * nat * nat). (** (block L, threshold T,
                                            prefix t) ladder, RepWL tier *)
Variable rw_fuel : nat.                 (** closure fuel for the RepWL tier *)
Variable Prov : list TM.       (** the proven never-quasihalting list *)
Hypothesis HP : Forall NeverQuasiHaltsSt Prov. (** its in-Coq certificate *)
Variable ProvQH : list TM.     (** the proven census-grade QUASIHALTING list *)
(** its in-Coq certificate: each machine is non-halting, has every quiet
    state's last visit bounded by [B] ([QHBound B]), and quasihalts.  This
    is exactly the [R_QH] contract, so a lookup hit discharges it directly. *)
Hypothesis HPQ :
  Forall (fun tm => NonHalt tm /\ QHBound B tm /\ QuasiHaltsSt tm) ProvQH.

Definition try_tc_cands (tm : TM) (mirrored : bool)
    (cands : list (nat * nat)) : bool :=
  existsb (fun '(n1, P) =>
    (n1 <=? B) &&
    tcycler_leaf_check tm n1 P (tc_measure_W tm n1 P)) cands.

Fixpoint try_ngram (rungs : list (nat * nat)) (tm : TM) : QHResult :=
  match rungs with
  | [] => R_Unknown
  | (n, t) :: rest =>
      if ngram_check_neverqh tm n t ng_fuel ng_rounds
      then R_NeverQH
      else try_ngram rest tm
  end.

Fixpoint try_rank (rungs : list (nat * nat)) (tm : TM) : QHResult :=
  match rungs with
  | [] => R_Unknown
  | (n, t) :: rest =>
      if rank_tier tm n t ng_fuel ng_rounds
      then R_NeverQH
      else try_rank rest tm
  end.

(** *** Tier Q: wrapped QHBound (prefix-quiet quasihalters)

    Mirrored by tools/sweep_qhbound_residue.py (plain acyclicity) and
    tools/sweep_qhbound_lex.py (the RankSearch-certified lex gate).
    An untrusted candidate filter guards the ladders: [q] is worth
    trying only if its last visit inside a window of 4x the largest
    prefix rung still lies under that rung -- a genuinely caught
    quiet state is never visited after its [s < t <= qhb_tmax], so
    the filter cannot lose a machine the ladder would catch, and on
    never-quasihalting machines every recurring state fails it. *)

Definition qhb_tmax : nat :=
  fold_left Nat.max (map snd qhb_rungs) 0.

Definition qh_candidate (tm : TM) (q : St) : bool :=
  match last_visit tm (4 * qhb_tmax) c0 0 q None with
  | Some s => s <? qhb_tmax
  | None => false
  end.

Definition try_qhb_at (tm : TM) (q : St) (nt : nat * nat) : bool :=
  let '(n, t) := nt in
  (S t <=? B) &&
  match last_visit tm t c0 0 q None with
  | Some s => ngram_check_qhbound tm q s n t ng_fuel ng_rounds
  | None => false
  end.

Definition try_qhb_lex_at (tm : TM) (q : St) (nt : nat * nat) : bool :=
  let '(n, t) := nt in
  (S t <=? B) &&
  match last_visit tm t c0 0 q None with
  | None => false
  | Some s =>
      match csteps tm t c0 with
      | None => false
      | Some ct =>
          let tmw := tm_wrap tm q in
          let '(q1, (l, h, r)) := ct in
          let lset0 := gadds (ng_seed_side n l) gempty in
          let rset0 := gadds (ng_seed_side n r) gempty in
          let a0 := ng_start n ct in
          let '(lset, rset) :=
            ng_grow tmw a0 ng_fuel ng_rounds lset0 rset0 in
          let closure :=
            ng_explore tmw lset rset ng_fuel [] PositiveSet.empty [a0] in
          ngram_check_qhbound_lex tm q s n t ng_fuel ng_rounds
            (fun q' => rank_procedure tmw lset rset closure q')
      end
  end.

(** nested [if] rather than [||]: [orb] is a function, so under
    call-by-value BOTH ladders evaluated -- a machine caught by the
    plain-acyclicity ladder still paid the full lex ladder (per-rung
    [ng_grow] + [ng_explore] per state) for nothing.  Same trap as
    the [lp_rewind] one (Tests/Loop1Scan_Regression.v), same shape of
    fix; the boolean value is unchanged. *)
Definition try_qhb (tm : TM) : bool :=
  existsb (fun q =>
      if existsb (try_qhb_at tm q) qhb_rungs then true
      else existsb (try_qhb_lex_at tm q) qhb_rungs)
    (filter (qh_candidate tm) all_St).

(** *** Tier W: RepWL block-list abstraction

    Mirrored by tools/sweep_repwl_residue.py; parameter-closed --
    the certificates come from the in-Coq RepWLSearch, never from
    per-machine tables. *)

Definition try_rw (tm : TM) : bool :=
  existsb (fun '(L, T, t) => rw_tier tm L T t rw_fuel) rw_rungs.

(** *** Tiers C+T at one gas rung

    In-place cycle scan + verified re-check, then translated cycles
    on both sides (one record walk serves both: the mirror machine's
    right records are the left records -- same steps and states).
    [decide_easy] escalates this block: the cheap rung [halt_gas]
    first (catches the short-cycle bulk at ~1/4 the scan cost), the
    full [loop_gas] rung only for its survivors. *)
Definition scan_ct (tm : TM) (gas : nat) : bool :=
  (match scan_cycle tm gas with
   | Some (n1, p) => (n1 <=? B) && cycle_leaf_check tm n1 p
   | None => false
   end) ||
  (let '(recR, recL) := scan_records tm gas in
   try_tc_cands tm false (tc_pairs recR)
   || try_tc_cands (mirror_tm tm) true (tc_pairs recL)).

(** verified confirmation of a one-pass candidate *)
Definition lp_check (tm : TM) (cand : lp_cand) : bool :=
  match cand with
  | LpCycle n1 p => (n1 <=? B) && cycle_leaf_check tm n1 p
  | LpTC DR n1 P =>
      (n1 <=? B) && tcycler_leaf_check tm n1 P (tc_measure_W tm n1 P)
  | LpTC DL n1 P =>
      (n1 <=? B) &&
      tcycler_leaf_check (mirror_tm tm) n1 P
        (tc_measure_W (mirror_tm tm) n1 P)
  end.

Definition scan_loops (tm : TM) (gas : nat) : bool :=
  existsb (lp_check tm) (lp_candidates tm gas).

Definition try_ladder (tm : TM) : QHResult :=
  match try_ngram ng_rungs tm with
  | R_NeverQH => R_NeverQH
  | _ =>
      match try_rank rank_rungs tm with
      | R_NeverQH => R_NeverQH
      | _ =>
          if try_qhb tm then R_QH
          else if try_rw tm then R_NeverQH
          else R_Unknown
      end
  end.

Definition decide_easy (pm qm dm : DeferredMap) (hm : HintMap)
    (tm : TM) : QHResult :=
  (* tier H: halting *)
  match find_halt tm halt_gas 0 c0 with
  | Some (n, s, i) => if S n <=? B then R_Halt s i else R_Unknown
  | None =>
  (* lookup tiers FIRST: proven / proven-QH / deferred machines skip
     the scans entirely (a gas-512 scan block costs ~15-25 ms native;
     a lookup is microseconds).  Tier P: committed [NeverQuasiHaltsSt]
     theorems; tier PQ: committed census-grade quasihalting theorems;
     tier D: the deferred list -- all three ahead of the (expensive,
     failing-on-them) scans and ladders. *)
  if deferred_lookup pm tm then R_NeverQH else
  if deferred_lookup qm tm then R_QH else
  if deferred_lookup dm tm then R_Deferred else
  (* tiers C+T: the one-pass loop scan, escalating rungs.  The old
     hash+map block ([scan_ct]) is GONE: with the record list derived
     exactly from the one-pass history ([lp_records]) and the cycle
     twins on record pairs, its catches are subsumed -- validated at
     records-bit-equality on 1,440 machines and zero lost verdicts --
     so every fall-through machine stops paying its 42.6 ms and its
     per-step PositiveMap snapshot allocation. *)
  if scan_loops tm halt_gas then R_Leaf else
  if scan_loops tm loop_gas then R_Leaf else
  (* tier N: n-gram ladder, then tier R: the ranking rules (a)/(b),
     then tier Q: wrapped QHBound, then tier W: RepWL -- with the
     winning-rung hint consulted first (fallback = the full ladder) *)
  match hint_lookup hm tm with
  | Some 0 =>
      match try_rank rank_rungs tm with
      | R_NeverQH => R_NeverQH
      | _ => try_ladder tm
      end
  | Some (S k) =>
      match try_ngram (skipn k ng_rungs) tm with
      | R_NeverQH => R_NeverQH
      | _ => try_ladder tm
      end
  | None => try_ladder tm
  end
  end.

(** *** Soundness *)

Lemma try_tc_cands_sound : forall tm cands,
  try_tc_cands tm false cands = true ->
  NonHalt tm /\ QHBound B tm.
Proof.
  intros tm cands H.
  unfold try_tc_cands in H.
  apply existsb_exists in H.
  destruct H as ([n1 P] & _ & H).
  apply andb_prop in H as [Hb H].
  apply Nat.leb_le in Hb.
  destruct (tcycler_leaf_check_sound tm n1 P _ H) as [Hnh Hq].
  split; [exact Hnh|].
  exact (qhbound_mono n1 B tm Hb Hq).
Qed.

Lemma try_tc_cands_sound_L : forall tm cands,
  try_tc_cands (mirror_tm tm) true cands = true ->
  NonHalt tm /\ QHBound B tm.
Proof.
  intros tm cands H.
  unfold try_tc_cands in H.
  apply existsb_exists in H.
  destruct H as ([n1 P] & _ & H).
  apply andb_prop in H as [Hb H].
  apply Nat.leb_le in Hb.
  destruct (tcycler_leaf_check_sound_L tm n1 P _ H) as [Hnh Hq].
  split; [exact Hnh|].
  exact (qhbound_mono n1 B tm Hb Hq).
Qed.

Lemma scan_ct_sound : forall tm gas,
  scan_ct tm gas = true -> NonHalt tm /\ QHBound B tm.
Proof.
  intros tm gas H.
  unfold scan_ct in H.
  apply orb_prop in H; destruct H as [H | H].
  - destruct (scan_cycle tm gas) as [[n1 p]|]; [|discriminate].
    apply andb_prop in H as [Hb Hc].
    apply Nat.leb_le in Hb.
    destruct (cycle_leaf_check_sound tm n1 p Hc) as [Hnh Hq].
    split; [exact Hnh|].
    exact (qhbound_mono n1 B tm Hb Hq).
  - destruct (scan_records tm gas) as [recR recL].
    apply orb_prop in H; destruct H as [H | H].
    + exact (try_tc_cands_sound tm (tc_pairs recR) H).
    + exact (try_tc_cands_sound_L tm (tc_pairs recL) H).
Qed.

Lemma lp_check_sound : forall tm cand,
  lp_check tm cand = true -> NonHalt tm /\ QHBound B tm.
Proof.
  intros tm cand H.
  destruct cand as [n1 p | [|] n1 P];
    unfold lp_check in H;
    apply andb_prop in H as [Hb H];
    apply Nat.leb_le in Hb.
  - destruct (cycle_leaf_check_sound tm n1 p H) as [Hnh Hq].
    split; [exact Hnh | exact (qhbound_mono n1 B tm Hb Hq)].
  - destruct (tcycler_leaf_check_sound_L tm n1 P _ H) as [Hnh Hq].
    split; [exact Hnh | exact (qhbound_mono n1 B tm Hb Hq)].
  - destruct (tcycler_leaf_check_sound tm n1 P _ H) as [Hnh Hq].
    split; [exact Hnh | exact (qhbound_mono n1 B tm Hb Hq)].
Qed.

Lemma scan_loops_sound : forall tm gas,
  scan_loops tm gas = true -> NonHalt tm /\ QHBound B tm.
Proof.
  intros tm gas H.
  unfold scan_loops in H.
  apply existsb_exists in H.
  destruct H as (cand & _ & Hc).
  exact (lp_check_sound tm cand Hc).
Qed.

Lemma try_ngram_cases : forall rungs tm,
  (try_ngram rungs tm = R_NeverQH /\ NeverQuasiHaltsSt tm) \/
  try_ngram rungs tm = R_Unknown.
Proof.
  induction rungs as [| [n t] rest IH]; intros tm; simpl.
  - right; reflexivity.
  - destruct (ngram_check_neverqh tm n t ng_fuel ng_rounds) eqn:E.
    + left. split; [reflexivity|].
      exact (ngram_check_neverqh_sound tm n t ng_fuel ng_rounds E).
    + exact (IH tm).
Qed.

Lemma try_rank_cases : forall rungs tm,
  (try_rank rungs tm = R_NeverQH /\ NeverQuasiHaltsSt tm) \/
  try_rank rungs tm = R_Unknown.
Proof.
  induction rungs as [| [n t] rest IH]; intros tm; simpl.
  - right; reflexivity.
  - destruct (rank_tier tm n t ng_fuel ng_rounds) eqn:E.
    + left. split; [reflexivity|].
      exact (rank_tier_sound tm n t ng_fuel ng_rounds E).
    + exact (IH tm).
Qed.

Lemma try_qhb_sound : forall tm,
  try_qhb tm = true ->
  NonHalt tm /\ QHBound B tm /\ QuasiHaltsSt tm.
Proof.
  intros tm H.
  unfold try_qhb in H.
  apply existsb_exists in H.
  destruct H as (q & _ & H).
  apply orb_prop in H; destruct H as [H | H];
    apply existsb_exists in H;
    destruct H as ([n t] & _ & H);
    unfold try_qhb_at, try_qhb_lex_at in H;
    apply andb_prop in H as [HB H];
    apply Nat.leb_le in HB.
  - (* plain acyclicity gate *)
    destruct (last_visit tm t c0 0 q None) as [s|]; [|discriminate].
    destruct (ngram_check_qhbound_sound tm q s n t ng_fuel ng_rounds H)
      as (Hnh & Hqb & Hqh).
    split; [exact Hnh|].
    split; [|exact Hqh].
    exact (qhbound_mono (S t) B tm HB Hqb).
  - (* lex gate *)
    destruct (last_visit tm t c0 0 q None) as [s|]; [|discriminate].
    destruct (csteps tm t c0) as [[q1 [[l h] r]]|] eqn:Ect; [|discriminate].
    match type of H with
    | (let '(_, _) := ?G in _) = true => destruct G as [lset rset]
    end.
    cbv beta iota zeta in H.
    destruct (ngram_check_qhbound_lex_sound tm q s n t ng_fuel ng_rounds
                _ H) as (Hnh & Hqb & Hqh).
    split; [exact Hnh|].
    split; [|exact Hqh].
    exact (qhbound_mono (S t) B tm HB Hqb).
Qed.

Lemma try_rw_sound : forall tm,
  try_rw tm = true -> NeverQuasiHaltsSt tm.
Proof.
  intros tm H.
  unfold try_rw in H.
  apply existsb_exists in H.
  destruct H as ([[L T] t] & _ & H).
  exact (rw_tier_sound tm L T t rw_fuel H).
Qed.

Theorem decide_easy_WF : forall hm,
  QHDecider_WF B D
    (decide_easy (dmap_of Prov) (dmap_of ProvQH) (dmap_of D) hm).
Proof.
  intro hm.
  intro tm.
  unfold decide_easy.
  destruct (find_halt tm halt_gas 0 c0) as [[[n s] i]|] eqn:Eh.
  { (* halt tier *)
    destruct (S n <=? B) eqn:EB; [|exact I].
    apply Nat.leb_le in EB.
    destruct (find_halt_sound tm halt_gas 0 c0 n s i (eq_refl) Eh)
      as (tp & Hst & Hhd & Hnone).
    exists n, tp. auto. }
  (* proven tier: a hit is never-quasihalting by the [Forall] cert *)
  destruct (deferred_lookup (dmap_of Prov) tm) eqn:Ep.
  { rewrite Forall_forall in HP.
    apply HP. apply deferred_lookup_In; exact Ep. }
  (* proven-QH tier: a hit is census-grade quasihalting by its [Forall]
     cert (NonHalt /\ QHBound B /\ QuasiHaltsSt = exactly the R_QH contract) *)
  destruct (deferred_lookup (dmap_of ProvQH) tm) eqn:Epq.
  { rewrite Forall_forall in HPQ.
    apply HPQ. apply deferred_lookup_In; exact Epq. }
  (* deferred tier *)
  destruct (deferred_lookup (dmap_of D) tm) eqn:Ed.
  { apply deferred_lookup_In; exact Ed. }
  (* cycle/TC tiers: the one-pass rungs *)
  destruct (scan_loops tm halt_gas) eqn:El1.
  { exact (scan_loops_sound tm halt_gas El1). }
  destruct (scan_loops tm loop_gas) eqn:El2.
  { exact (scan_loops_sound tm loop_gas El2). }
  (* the ladder, behind the advisory hint dispatch: every path ends
     in a tier whose soundness lemma is hint-independent *)
  assert (Hlad : match try_ladder tm with
                 | R_NeverQH => NeverQuasiHaltsSt tm
                 | R_QH => NonHalt tm /\ QHBound B tm /\ QuasiHaltsSt tm
                 | R_Unknown => True
                 | _ => False
                 end).
  { unfold try_ladder.
    destruct (try_ngram_cases ng_rungs tm) as [[En Hn] | En]; rewrite En.
    - exact Hn.
    - destruct (try_rank_cases rank_rungs tm) as [[Er Hr] | Er]; rewrite Er.
      + exact Hr.
      + destruct (try_qhb tm) eqn:Eq.
        * exact (try_qhb_sound tm Eq).
        * destruct (try_rw tm) eqn:Ew.
          -- exact (try_rw_sound tm Ew).
          -- exact I. }
  destruct (hint_lookup hm tm) as [[|k]|].
  - (* hint 0: rank first *)
    destruct (try_rank_cases rank_rungs tm) as [[Er Hr] | Er]; rewrite Er.
    + exact Hr.
    + destruct (try_ladder tm); cbn in Hlad;
        solve [exact Hlad | destruct Hlad | exact I].
  - (* hint S k: start the ngram ladder at rung S k *)
    destruct (try_ngram_cases (skipn k ng_rungs) tm) as [[En Hn] | En];
      rewrite En.
    + exact Hn.
    + destruct (try_ladder tm); cbn in Hlad;
        solve [exact Hlad | destruct Hlad | exact I].
  - (* no hint *)
    destruct (try_ladder tm); cbn in Hlad;
      solve [exact Hlad | destruct Hlad | exact I].
Qed.

End Pipeline.
