(** * 1RB0RB_1LC0RC_1RA0LD_0LB0LC -- never quasihalts.

    Row 1 of [docs/WAVE38_REST_FOUR.md], the quadratic unary counter.

    [ReachStI] certifies [StA], [StB] and [StC] live on this row.  The three
    lemmas below are the whole of that, re-checked by [vm_compute] inside
    each proof: nothing in [tools/reachsti/] carries weight, a wrong constant
    just makes [drop_ok] evaluate to [false].

    [StD] is PERMANENTLY outside the [ReachStI] tier.  [drop_ok]'s measure is

        mu = B * ones l + C * ones r + rk (q, chd l, h, chd r)

    and it must strictly drop on every [StD]-avoiding step, but

        (StA,1,1,0) --A1=0RB--> (StB,0,0,0) --B0=1LC--> (StC,0,0,1)
                    --C0=1RA--> (StA,1,1,0)

    is a [StD]-avoiding cycle that returns [rk] to its start while [ones l]
    gains 1 and [ones r] is unchanged, so [mu] cannot drop around it for ANY
    [B, C >= 0].  With the word-rewriting lever, [NGramHist] and [RepWL] all
    measured dead too (write-up sections 1, 2b, 2d), [StD] is proved here BY
    HAND, off the row's own lap structure, and
    [Checkers/LiveAll.neverqh_of_live4] closes the row from the four states
    exactly as this file always said it would.

    THE LAP STRUCTURE (the "quadratic-counter argument" section 2d asked
    for).  The orbit is a bouncer between a leftward-marching wall and a
    slowly-growing counter word at the right.  At every left turnaround the
    configuration is EXACTLY

        Cn W z p = (StC, ([], S0, [S1] ++ 0^z ++ W ++ (011)^p ++ 010011111))

    -- the whole tape is the right half-list: a marker cell, a desert of [z]
    blanks, a bounded boundary word [W], [p] stripes [011] and a fixed tail.
    Nine boundary words [W0..W8] cycle with period nine; measured over 500+
    consecutive laps the law never breaks (idx = 9j+phase):

        z = 24j + c_phase,   p = j + d_phase,   lap length 96j + b_phase.

    One lap decomposes into five machine-checkable segments:

      prep      3 steps          the left turnaround writes the new marker
      refill    3 per cell       B-C-A cycle converts [0^z] into [1^z]
      dance     n_phase steps    a BOUNDED window rewrite [1 W_i -> W_i+1]
                                 at the desert/word boundary ([wsteps],
                                 walled both sides; 6..66 steps; the stripe
                                 block and tail are never entered -- the new
                                 stripe at phase 3 is EMITTED by the window)
      sweep     1 per cell       C-D alternation zeroes the run pairwise
                                 ([cycL] at [1 1] -> [0 0]; [StD] fires here
                                 every second step)
      turn      3 steps          C1-D0-B0 write the next marker 3 cells left

    The segments compose into [lap_R1]: from any anchor [Cn (W f) z p] with
    [z] even, one lap of [8u + 11 + n_f + 2h_f] steps reaches the anchor
    [Cn (W (next f)) (z + 2h_f + 2) (p + d_f)] -- for EVERY even [z >= 2]
    and EVERY [p], which is strictly more than the orbit needs.  The anchor
    set is therefore closed, every lap passes through [StD] (first step of
    the sweep), and the orbit boots into the anchor set at step 7,455
    ([vm_compute]).  That yields [LiveSt tm StD]; the quadratic growth
    ([t ~ 434 p^2]) is exactly [sum of laps ~ (96/2) (9j)^2 / 81]-shaped and
    never needs to be stated. *)

From Coq Require Import Arith Lia List.
Import ListNotations.
From BBB4 Require Import BBB4_Statement CTape Checkers.ReachStI Checkers.LiveAll.
From BBB4.Counters Require Import WTape.

Definition tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB) | StA, S1 => Some (mkTrans S0 DR StB)
  | StB, S0 => Some (mkTrans S1 DL StC) | StB, S1 => Some (mkTrans S0 DR StC)
  | StC, S0 => Some (mkTrans S1 DR StA) | StC, S1 => Some (mkTrans S0 DL StD)
  | StD, S0 => Some (mkTrans S0 DL StB) | StD, S1 => Some (mkTrans S0 DL StC)
  end.

Definition allowed_1RB0RB_1LC0RC_1RA0LD_0LB0LC : list St := [StA; StB; StC; StD].

Definition rkA_1RB0RB_1LC0RC_1RA0LD_0LB0LC (nd : mnode) : nat :=
  match nd with
  | (StA, S0, S0, S0) => 4
  | (StA, S0, S0, S1) => 4
  | (StA, S0, S1, S0) => 4
  | (StA, S0, S1, S1) => 4
  | (StA, S1, S0, S0) => 4
  | (StA, S1, S0, S1) => 4
  | (StA, S1, S1, S0) => 4
  | (StA, S1, S1, S1) => 4
  | (StB, S0, S0, S0) => 1
  | (StB, S0, S0, S1) => 4
  | (StB, S0, S1, S0) => 4
  | (StB, S0, S1, S1) => 4
  | (StB, S1, S0, S0) => 1
  | (StB, S1, S0, S1) => 4
  | (StB, S1, S1, S0) => 4
  | (StB, S1, S1, S1) => 4
  | (StC, S0, S0, S0) => 3
  | (StC, S0, S1, S0) => 3
  | (StC, S0, S1, S1) => 3
  | (StC, S1, S0, S0) => 3
  | (StC, S1, S1, S0) => 4
  | (StC, S1, S1, S1) => 3
  | (StD, S0, S0, S0) => 2
  | (StD, S0, S0, S1) => 4
  | (StD, S0, S1, S0) => 4
  | (StD, S0, S1, S1) => 4
  | (StD, S1, S0, S0) => 2
  | (StD, S1, S0, S1) => 4
  | (StD, S1, S1, S0) => 4
  | (StD, S1, S1, S1) => 4
  | _ => 0
  end.

Lemma liveA_1RB0RB_1LC0RC_1RA0LD_0LB0LC :
  NonHalt tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC
  /\ forall N, exists n, N <= n /\ VisitsAt tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC StA n.
Proof.
  apply (reach_sti_recurs_b tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC allowed_1RB0RB_1LC0RC_1RA0LD_0LB0LC StA 3 0 rkA_1RB0RB_1LC0RC_1RA0LD_0LB0LC 0);
    vm_compute; reflexivity.
Qed.

Definition rkB_1RB0RB_1LC0RC_1RA0LD_0LB0LC (nd : mnode) : nat :=
  match nd with
  | (StA, S0, S0, S0) => 3
  | (StA, S0, S0, S1) => 3
  | (StA, S0, S1, S0) => 3
  | (StA, S0, S1, S1) => 3
  | (StA, S1, S1, S0) => 1
  | (StA, S1, S1, S1) => 1
  | (StB, S0, S0, S0) => 3
  | (StB, S0, S0, S1) => 3
  | (StB, S0, S1, S0) => 3
  | (StB, S0, S1, S1) => 3
  | (StB, S1, S0, S0) => 3
  | (StB, S1, S0, S1) => 3
  | (StB, S1, S1, S0) => 3
  | (StB, S1, S1, S1) => 3
  | (StC, S0, S0, S0) => 2
  | (StC, S0, S0, S1) => 3
  | (StC, S0, S1, S0) => 3
  | (StC, S0, S1, S1) => 3
  | (StC, S1, S0, S0) => 2
  | (StC, S1, S0, S1) => 3
  | (StC, S1, S1, S0) => 3
  | (StC, S1, S1, S1) => 3
  | (StD, S0, S0, S0) => 2
  | (StD, S0, S0, S1) => 3
  | (StD, S0, S1, S0) => 3
  | (StD, S0, S1, S1) => 3
  | (StD, S1, S0, S0) => 2
  | (StD, S1, S0, S1) => 3
  | (StD, S1, S1, S0) => 3
  | (StD, S1, S1, S1) => 3
  | _ => 0
  end.

Lemma liveB_1RB0RB_1LC0RC_1RA0LD_0LB0LC :
  NonHalt tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC
  /\ forall N, exists n, N <= n /\ VisitsAt tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC StB n.
Proof.
  apply (reach_sti_recurs_b tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC allowed_1RB0RB_1LC0RC_1RA0LD_0LB0LC StB 1 0 rkB_1RB0RB_1LC0RC_1RA0LD_0LB0LC 0);
    vm_compute; reflexivity.
Qed.

Definition rkC_1RB0RB_1LC0RC_1RA0LD_0LB0LC (nd : mnode) : nat :=
  match nd with
  | (StA, S0, S0, S0) => 1
  | (StA, S0, S0, S1) => 1
  | (StA, S0, S1, S0) => 1
  | (StA, S0, S1, S1) => 1
  | (StA, S1, S0, S0) => 1
  | (StA, S1, S0, S1) => 1
  | (StA, S1, S1, S0) => 1
  | (StA, S1, S1, S1) => 1
  | (StC, S0, S0, S0) => 1
  | (StC, S0, S0, S1) => 1
  | (StC, S0, S1, S0) => 1
  | (StC, S0, S1, S1) => 1
  | (StC, S1, S0, S0) => 1
  | (StC, S1, S0, S1) => 1
  | (StC, S1, S1, S0) => 1
  | (StC, S1, S1, S1) => 1
  | (StD, S0, S0, S0) => 1
  | (StD, S0, S0, S1) => 1
  | (StD, S0, S1, S0) => 1
  | (StD, S0, S1, S1) => 1
  | (StD, S1, S0, S0) => 1
  | (StD, S1, S0, S1) => 1
  | (StD, S1, S1, S0) => 1
  | (StD, S1, S1, S1) => 1
  | _ => 0
  end.

Lemma liveC_1RB0RB_1LC0RC_1RA0LD_0LB0LC :
  NonHalt tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC
  /\ forall N, exists n, N <= n /\ VisitsAt tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC StC n.
Proof.
  apply (reach_sti_recurs_b tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC allowed_1RB0RB_1LC0RC_1RA0LD_0LB0LC StC 0 0 rkC_1RB0RB_1LC0RC_1RA0LD_0LB0LC 0);
    vm_compute; reflexivity.
Qed.


(** The three, restated as [LiveSt] -- the shape [neverqh_of_live4] consumes. *)
Lemma liveStA_1RB0RB_1LC0RC_1RA0LD_0LB0LC : LiveSt tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC StA.
Proof. exact (live_of_recurs _ _ liveA_1RB0RB_1LC0RC_1RA0LD_0LB0LC). Qed.

Lemma liveStB_1RB0RB_1LC0RC_1RA0LD_0LB0LC : LiveSt tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC StB.
Proof. exact (live_of_recurs _ _ liveB_1RB0RB_1LC0RC_1RA0LD_0LB0LC). Qed.

Lemma liveStC_1RB0RB_1LC0RC_1RA0LD_0LB0LC : LiveSt tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC StC.
Proof. exact (live_of_recurs _ _ liveC_1RB0RB_1LC0RC_1RA0LD_0LB0LC). Qed.

(** Any ONE of them already gives non-halting, with no [Visited] obligation. *)
Theorem nonhalt_1RB0RB_1LC0RC_1RA0LD_0LB0LC : NonHalt tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC.
Proof. exact (nonhalt_of_live _ StA liveStA_1RB0RB_1LC0RC_1RA0LD_0LB0LC). Qed.

(** ** The lap system, and [StD] *)

Local Notation tm := tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC.

(** The nine boundary words, in tape order (nearest cell first), and the
    fixed right tail [010011111].  Extracted from the orbit and verified
    over 500+ consecutive laps; nothing here is trusted -- a wrong word
    makes [dance_R1] fail to compile. *)
Definition W0_R1 : list Sym := [S1; S0; S0; S1; S0; S1; S1; S0; S1; S0; S0; S0; S1; S1; S0].
Definition W1_R1 : list Sym := [S1; S0; S0; S0; S0; S1; S1; S0; S1; S1; S0; S0; S1; S0; S0; S0].
Definition W2_R1 : list Sym := [S1; S1; S1; S0; S1; S1; S0; S1; S1; S0; S0; S1; S0; S0; S0].
Definition W3_R1 : list Sym := [S1; S0; S0; S1; S0; S1; S1; S0; S1; S1; S0; S0; S1; S0; S0; S0].
Definition W4_R1 : list Sym := [S1; S0; S0; S0; S0; S1; S0; S0; S1; S1; S0; S1; S1; S0].
Definition W5_R1 : list Sym := [S1; S1; S1; S0; S1; S0; S0; S1; S1; S0; S1; S1; S0].
Definition W6_R1 : list Sym := [S1; S0; S0; S1; S0; S1; S0; S0; S1; S1; S0; S1; S1; S0].
Definition W7_R1 : list Sym := [S1; S0; S0; S0; S0; S1; S1; S0; S1; S0; S0; S0; S1; S1; S0].
Definition W8_R1 : list Sym := [S1; S1; S1; S0; S1; S1; S0; S1; S0; S0; S0; S1; S1; S0].
Definition TT_R1 : list Sym := [S0; S1; S0; S0; S1; S1; S1; S1; S1].

Inductive rph : Type := RP0 | RP1 | RP2 | RP3 | RP4 | RP5 | RP6 | RP7 | RP8.

Definition rphW (f : rph) : list Sym :=
  match f with
  | RP0 => W0_R1 | RP1 => W1_R1 | RP2 => W2_R1
  | RP3 => W3_R1 | RP4 => W4_R1 | RP5 => W5_R1
  | RP6 => W6_R1 | RP7 => W7_R1 | RP8 => W8_R1
  end.

(** Dance length, half the extra run cells the dance leaves ([a = 2h]),
    stripes emitted, and the successor phase. *)
Definition rphN (f : rph) : nat :=
  match f with
  | RP0 => 54 | RP1 => 16 | RP2 => 6
  | RP3 => 66 | RP4 => 16 | RP5 => 6
  | RP6 => 36 | RP7 => 16 | RP8 => 6
  end.

Definition rphH (f : rph) : nat :=
  match f with RP1 | RP4 | RP7 => 1 | _ => 0 end.

Definition rphD (f : rph) : nat :=
  match f with RP3 => 1 | _ => 0 end.

Definition rphS (f : rph) : rph :=
  match f with
  | RP0 => RP1 | RP1 => RP2 | RP2 => RP3
  | RP3 => RP4 | RP4 => RP5 | RP5 => RP6
  | RP6 => RP7 | RP7 => RP8 | RP8 => RP0
  end.

(** The nine dance facts: bounded runs, walled on BOTH sides, so the
    window transformation transports under any deeper context
    ([wsteps_frame]).  The window never pops below the run built by the
    refill and never reads past the boundary word; phase 3's window emits
    the new stripe. *)
Lemma dance_R1 : forall f,
  wsteps true true tm (rphN f) (StC, ([], S0, [S1] ++ rphW f))
  = Some (StC, (rep [S1] (2 * rphH f), S1,
                rphW (rphS f) ++ rep [S0; S1; S1] (rphD f))).
Proof. destruct f; vm_compute; reflexivity. Qed.

(** The left turnaround: three steps write the new marker and enter the
    refill cycle. *)
Lemma prep_R1 : forall z RR,
  csteps tm 3 (StC, ([], S0, [S1] ++ rep [S0] (S z) ++ RR))
  = Some (StC, ([S1], S0, [S1] ++ rep [S0] z ++ RR)).
Proof. intros. reflexivity. Qed.

(** The refill: the B-C-A cycle converts the desert to a unary run at
    three steps per cell. *)
Lemma refill_R1 : forall m l RR,
  csteps tm (3 * m) (StC, (l, S0, [S1] ++ rep [S0] m ++ RR))
  = Some (StC, (rep [S1] m ++ l, S0, [S1] ++ RR)).
Proof.
  induction m as [|m IH]; intros l RR.
  - reflexivity.
  - replace (3 * S m) with (3 + 3 * m) by lia.
    eapply csteps_chain
      with (c1 := (StC, (S1 :: l, S0, [S1] ++ rep [S0] m ++ RR))).
    + reflexivity.
    + rewrite IH. rewrite <- rep_slide. reflexivity.
Qed.

(** The zeroing sweep: C and D alternate leftward over the run, two cells
    per two steps; [StD] fires at every second step. *)
Lemma unitCD_R1 : wsteps true true tm 2 (StC, ([S1; S1], S1, []))
                = Some (StC, ([], S1, [S0; S0])).
Proof. reflexivity. Qed.

Lemma sweep_R1 : forall k L R,
  csteps tm (2 * k) (StC, (rep [S1; S1] k ++ L, S1, R))
  = Some (StC, (L, S1, rep [S0; S0] k ++ R)).
Proof. exact (cycL tm 2 StC S1 [S1; S1] [] [S0; S0] unitCD_R1). Qed.

(** The right turnaround at the run's far end: the sweep runs off the
    ones, C1-D0-B0 write the next lap's marker three cells further left. *)
Lemma turn_R1 : forall R0,
  csteps tm 3 (StC, ([], S1, R0)) = Some (StC, ([], S0, [S1; S0; S0] ++ R0)).
Proof. intros. reflexivity. Qed.

(** Regrouping helpers. *)
Lemma rep1_snoc_R1 : forall k, rep [S1] k ++ [S1] = rep [S1] (S k).
Proof. intro k. rewrite rep_shift. reflexivity. Qed.

Lemma ones_regroup_R1 : forall h u,
  rep [S1] (2 * h) ++ rep [S1] (S (2 * u)) ++ [S1]
  = rep [S1] (S (S (2 * (u + h)))).
Proof.
  intros h u. rewrite rep1_snoc_R1, <- rep_add. f_equal. lia.
Qed.

Lemma zeros_regroup_R1 : forall m,
  [S0; S0] ++ rep [S0; S0] (S m) = rep [S0] (S (S (2 * (m + 1)))).
Proof.
  intro m.
  change ([S0; S0] ++ rep [S0; S0] (S m)) with (rep [S0; S0] (S (S m))).
  rewrite rep_dbl. f_equal. lia.
Qed.

(** The anchor: the whole tape as the right half-list. *)
Definition AnR1 (P : list Sym) (z p : nat) : cconf :=
  (StC, ([], S0, [S1] ++ rep [S0] z ++ P ++ rep [S0; S1; S1] p ++ TT_R1)).

(** Prep + refill + dance: from an anchor to the sweep entry. *)
Lemma entry_R1 : forall f u p,
  csteps tm (6 + 6 * u + rphN f) (AnR1 (rphW f) (S (S (2 * u))) p)
  = Some (StC, (rep [S1] (S (S (2 * (u + rphH f)))), S1,
                rphW (rphS f) ++ rep [S0; S1; S1] (rphD f)
                  ++ rep [S0; S1; S1] p ++ TT_R1)).
Proof.
  intros f u p.
  replace (6 + 6 * u + rphN f) with (3 + (3 * S (2 * u) + rphN f)) by lia.
  unfold AnR1.
  eapply csteps_chain
    with (c1 := (StC, ([S1], S0,
           [S1] ++ rep [S0] (S (2 * u)) ++ rphW f
                ++ rep [S0; S1; S1] p ++ TT_R1))).
  - apply prep_R1.
  - eapply csteps_chain
      with (c1 := (StC, (rep [S1] (S (2 * u)) ++ [S1], S0,
             [S1] ++ rphW f ++ rep [S0; S1; S1] p ++ TT_R1))).
    + apply refill_R1.
    + rewrite <- (ones_regroup_R1 (rphH f) u).
      rewrite (app_assoc (rphW (rphS f)) (rep [S0; S1; S1] (rphD f))
                 (rep [S0; S1; S1] p ++ TT_R1)).
      exact (wsteps_frame tm (rphN f) StC [] S0 ([S1] ++ rphW f) StC
               (rep [S1] (2 * rphH f)) S1
               (rphW (rphS f) ++ rep [S0; S1; S1] (rphD f))
               (rep [S1] (S (2 * u)) ++ [S1])
               (rep [S0; S1; S1] p ++ TT_R1) (dance_R1 f)).
Qed.

(** One whole lap: anchor to anchor, for EVERY even desert width and
    EVERY stripe count. *)
Lemma lap_R1 : forall f u p,
  csteps tm (8 * u + 11 + rphN f + 2 * rphH f)
    (AnR1 (rphW f) (S (S (2 * u))) p)
  = Some (AnR1 (rphW (rphS f)) (S (S (2 * (u + rphH f + 1)))) (rphD f + p)).
Proof.
  intros f u p.
  replace (8 * u + 11 + rphN f + 2 * rphH f)
    with ((6 + 6 * u + rphN f) + (2 * S (u + rphH f) + 3)) by lia.
  eapply csteps_chain; [apply entry_R1|].
  eapply csteps_chain
    with (c1 := (StC, ([], S1, rep [S0; S0] (S (u + rphH f))
           ++ rphW (rphS f) ++ rep [S0; S1; S1] (rphD f)
           ++ rep [S0; S1; S1] p ++ TT_R1))).
  - replace (S (S (2 * (u + rphH f)))) with (2 * S (u + rphH f)) by lia.
    rewrite <- rep_dbl.
    rewrite <- (app_nil_r (rep [S1; S1] (S (u + rphH f)))).
    apply sweep_R1.
  - rewrite turn_R1. unfold AnR1.
    do 2 f_equal.
    change ([S1; S0; S0]
              ++ rep [S0; S0] (S (u + rphH f))
              ++ rphW (rphS f) ++ rep [S0; S1; S1] (rphD f)
              ++ rep [S0; S1; S1] p ++ TT_R1)
      with ([S1] ++ ([S0; S0] ++ rep [S0; S0] (S (u + rphH f)))
              ++ rphW (rphS f) ++ rep [S0; S1; S1] (rphD f)
              ++ rep [S0; S1; S1] p ++ TT_R1).
    rewrite zeros_regroup_R1.
    rewrite (app_assoc (rep [S0; S1; S1] (rphD f)) (rep [S0; S1; S1] p)
               TT_R1).
    rewrite <- rep_add.
    reflexivity.
Qed.

(** The anchor set, closed under one lap. *)
Definition GR1 (c : cconf) : Prop :=
  exists f u p, c = AnR1 (rphW f) (S (S (2 * u))) p.

Lemma g_step_R1 : forall c, GR1 c ->
  exists m c', 1 <= m /\ csteps tm m c = Some c' /\ GR1 c'.
Proof.
  intros c (f & u & p & ->).
  exists (8 * u + 11 + rphN f + 2 * rphH f),
         (AnR1 (rphW (rphS f)) (S (S (2 * (u + rphH f + 1)))) (rphD f + p)).
  split; [lia|].
  split; [apply lap_R1|].
  exists (rphS f), (u + rphH f + 1), (rphD f + p). reflexivity.
Qed.

(** [StD] is hit from every anchor: it is the first step of the sweep. *)
Lemma hitD_R1 : forall c, GR1 c ->
  exists n cc, 1 <= n /\ csteps tm n c = Some cc /\ fst cc = StD.
Proof.
  intros c (f & u & p & ->).
  exists (6 + 6 * u + rphN f + 1),
         (StD, (rep [S1] (S (2 * (u + rphH f))), S1,
                S0 :: rphW (rphS f) ++ rep [S0; S1; S1] (rphD f)
                   ++ rep [S0; S1; S1] p ++ TT_R1)).
  split; [lia|]. split; [|reflexivity].
  rewrite csteps_add, entry_R1. reflexivity.
Qed.

(** [StD] at arbitrarily large indices, by induction over laps. *)
Lemma liveD_lap_R1 : forall N c, GR1 c ->
  exists m cc, N <= m /\ csteps tm m c = Some cc /\ fst cc = StD.
Proof.
  induction N as [|N IHN]; intros c HG.
  - destruct (hitD_R1 c HG) as (n & cc & H1 & H2 & H3).
    exists n, cc. split; [lia | split; assumption].
  - destruct (g_step_R1 c HG) as (n & c' & Hn & Hstep & HG').
    destruct (IHN c' HG') as (m & cc & Hm & Hc & Hq).
    exists (n + m), cc. split; [lia|].
    split; [rewrite csteps_add, Hstep; exact Hc | exact Hq].
Qed.

(** The orbit enters the anchor set at step 7,455 (phase 4, [z = 94],
    no stripes yet), checked cell by cell in the kernel. *)
Lemma boot_R1 : csteps tm 7455 c0 = Some (AnR1 W4_R1 94 0).
Proof. vm_compute. reflexivity. Qed.

Lemma liveStD_1RB0RB_1LC0RC_1RA0LD_0LB0LC : LiveSt tm StD.
Proof.
  intro N.
  destruct (liveD_lap_R1 N (AnR1 W4_R1 94 0)) as (m & cc & Hm & Hc & Hq).
  { exists RP4, 46, 0. reflexivity. }
  exists (7455 + m). split; [lia|].
  exists (lift cc). split.
  - rewrite <- lift_c0. apply csteps_lift.
    rewrite csteps_add, boot_R1. exact Hc.
  - rewrite lift_state. exact Hq.
Qed.

(** ** The theorem: the three banked states plus the lap-borne fourth. *)

Theorem nqh_1RB0RB_1LC0RC_1RA0LD_0LB0LC :
  NeverQuasiHaltsSt tm_1RB0RB_1LC0RC_1RA0LD_0LB0LC.
Proof.
  exact (neverqh_of_live4 tm
           liveStA_1RB0RB_1LC0RC_1RA0LD_0LB0LC
           liveStB_1RB0RB_1LC0RC_1RA0LD_0LB0LC
           liveStC_1RB0RB_1LC0RC_1RA0LD_0LB0LC
           liveStD_1RB0RB_1LC0RC_1RA0LD_0LB0LC).
Qed.
