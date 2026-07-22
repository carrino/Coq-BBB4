(** * Tests/RerootStage_Corruption: negative controls for the wave-2
    re-root staging recipes.

    The staged re-root tier (tools/gen_reroot.py --staged, files
    theories/Machines/RerootStage/RRStage_*.v) boards a census 0RB
    machine [m] with [rrqh m] = [NonHalt /\ QHBound 2000 /\
    QuasiHaltsSt] through [qh_reroot] (Census/Reroot.v).  Wave 1 proved
    the re-root core [TM_swap StA q* m] NEVER-quasihalting with a single
    recipe ([rw_tier]); wave 2 ADDS recipes -- [rank_tier] (NGram +
    Bellman ranking) and plain [ngram_check_neverqh] -- so the ~89% of
    small cores [rw_tier] alone missed now board.

    The re-root MECHANISM's gates (the [prefix_ok] blank-prefix identity
    and the [closed_b] reachable-state closure that certifies the silent
    dropped-prefix state) are covered by Tests/Reroot_Corruption.v.  The
    ONLY new trust surface here is that the ADDED never-QH recipes are
    still SOUND in this use: they must never certify a machine that is
    not never-quasihalting, else [qh_reroot] would transfer a bogus
    quasihalting verdict.  Every control below is closed by [vm_compute];
    a regression that made [rank_tier] / [ngram_check_neverqh] /
    [rw_tier] unsound (accepting a halter or a genuine quasihalter as
    never-QH) flips a [= false] control and BREAKS THIS FILE.

    (These reuse the already-sound RankSearch.rank_tier_sound /
    NGram.ngram_check_neverqh_sound / RepWLSearch.rw_tier_sound; the
    wave-2 emitter only CHOOSES which to apply per core.) *)

From Coq Require Import List.
From BBB4 Require Import BBB4_Statement.
From BBB4.Checkers Require Import RepWL NGram.
From BBB4.Census Require Import TNF_QH RepWLSearch RankSearch Deferred_Defs.
Import ListNotations.

(** ** A genuine wave-2 re-root core

    [core_real] is the re-root core of RRStage_00's machine [s_00000]
    ([TM_swap StA StD] of [0RB..._..._0LD0RC_1RC1LD]).  It is a small
    never-quasihalting left-growing bouncer on live states {A,C}; the
    [rank_tier] recipe (n=3) certifies it, but the wave-1 [rw_tier]
    recipe at the census rungs does NOT -- exactly why wave 2 is needed. *)
Definition core_real : TM :=
  row_to_tm [t1RC; t1LA; t0LC; tN; t0LA; t0RC; t0RB; tN].

(** the added recipe FIRES on the genuine never-QH core ... *)
Example rank_accepts_real : rank_tier core_real 3 0 20000 64 = true.
Proof. vm_compute. reflexivity. Qed.

(** ... and this core is exactly one wave-1 [rw_tier] misses at the
    census parameters (so the recipe extension is load-bearing, not
    redundant) *)
Example rw_misses_real : rw_tier core_real 2 2 0 8192 = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Negative control 1 -- a HALTING core is rejected

    [core_halt] mutates [core_real]'s [StA] read-0 to undefined: from
    the blank tape it halts at step 0.  A halting machine is NOT
    never-quasihalting ([never_qh_nonhalt : NeverQuasiHaltsSt -> NonHalt]),
    so a SOUND recipe must return [false].  If any recipe were corrupted
    to accept it, the matching [= false] below would fail to compile. *)
Definition core_halt : TM :=
  row_to_tm [tN; t1LA; t0LC; tN; t0LA; t0RC; t0RB; tN].

Example rank_rejects_halt : rank_tier core_halt 3 0 20000 64 = false.
Proof. vm_compute. reflexivity. Qed.
Example ngram_rejects_halt : ngram_check_neverqh core_halt 3 0 20000 64 = false.
Proof. vm_compute. reflexivity. Qed.
Example rw_rejects_halt : rw_tier core_halt 2 2 0 8192 = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Negative control 2 -- a QUASIHALTING core is rejected

    [core_qh]: [StA] fires once from blank ([0,R] to [StB]) and is never
    re-entered, while {B,C} bounce forever -- so [StA] goes quiet and the
    machine genuinely QUASIHALTS ([NeverQuasiHaltsSt] is false).  Again a
    sound never-QH recipe must reject it. *)
Definition core_qh : TM :=
  row_to_tm [t0RB; t1LA; t1RC; t0LB; t1LB; t0RC; tN; tN].

Example rank_rejects_qh : rank_tier core_qh 3 0 20000 64 = false.
Proof. vm_compute. reflexivity. Qed.
Example ngram_rejects_qh : ngram_check_neverqh core_qh 3 0 20000 64 = false.
Proof. vm_compute. reflexivity. Qed.
Example rw_rejects_qh : rw_tier core_qh 2 2 0 8192 = false.
Proof. vm_compute. reflexivity. Qed.
