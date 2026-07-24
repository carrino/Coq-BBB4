# v5 rule-replay gap — staging + hand-off

_Written 2026-07-23 (branch `claude/coq-bbb4-v5gap-<suffix>`), a
standalone parallel track to the wave-4 harvest._

## What the "v5 gap" is

`bin/verify` (the C prover) proves all 45 machines in `tools/v5gap.txt`
never quasihalt.  These are the un-annotated (non-`RECOVERED`) rows of
`tools/irulesnqh_refused.txt` — the wave-3 sweep produced never-QH
irules certificates for them, but the landed Coq oracle
`MetaBlkPfx.irulesblkpfx_check_neverqh` returned `false`, so wave-3 never
boarded them (kernel-refused = never boarded).

Derive the set:

```
grep -v '^#' tools/irulesnqh_refused.txt | grep -v RECOVERED | cut -f1 > tools/v5gap.txt   # 45
```

Diagnosis (fresh certs, `bin/irules --max-steps 200000 --cert-dir
results/certs_v5gap tools/v5gap.txt`, then `Eval vm_compute` of the
checker's sub-terms) found the 45 split across **two distinct corners**,
both in the meta-cycle replay `breplayKP`, neither of which the landed
Phase-2 engine covers.  Rule validation (`check_rulesBlkP`) and the meta
replay's *structure* are fine; the anchor re-simulation and coverage are
fine.  The gaps are downstream.

### Gap 1 — the cell-stream end-match (LANDED, 20 boarded)

The meta cycle template@k → template@(a·k+b) closes on a configuration
that is **cell-equal** to the shifted template `bwantp_cfg` but whose run
decomposition splits a variable-count block run against surrounding
constant runs.  Concretely (machine `1RB0RC_1LC1LD_1RA0LB_1LD1LA`): the
replay reaches, cell-for-cell identical to the C prover's `iv_step`
trace, the config `b1^2 . b2^(4+3k) . b0 . b1` — which denotes the same
tape as the want `b1^2 . b2^(5+3k)` because the trailing `b0.b1` respells
one more copy of `b2 = [S0;S1]`.

The landed `RulesBlk.bend_eqb` only re-encodes **constant**-count
multi-cell blocks (`bstreams_eq` / `bcanon_rle`), so it cannot expand the
variable `b2^(4+3k)` and refuses.  The C verifier's `iv_streams_eq` walks
the cells symbolically (phase + remainder two-pointer) and accepts.

**Fix (this branch):**

- `theories/Checkers/IRules/StreamEq.v` — the new trust surface.  Because
  the meta replay has a **single variable** `k` (`lo = [kmin]`), each
  side of the tape has one-pump shape `U ++ W^(k−k0) ++ V` (`U`,`V`
  constant cell words, `W` the per-`k` growth of the one variable run).
  Two one-pump words are equal for **all** `k ≥ k0` iff they are equal at
  `k0` and `k0+1` — a five-line conjugacy induction (`one_pump_all`; from
  `U V = U' V'` and `U W V = U' W' V'` derive `W D = D W'` and iterate).
  No combinatorics-on-words decision procedure.  `cseq` extracts
  `(U,W,V)` (`exp1`) and does two concrete cell-string comparisons;
  `cseq_sound` closes with **zero axioms**; `bend_eqb2 = bend_eqb || cseq`
  with `bend_eqb2_bsem`.
- `theories/Checkers/IRules/MetaBlkPfxV5.v` — `irulesblkpfx_check_neverqh_v5`
  forks the landed checker changing **only** the meta-cycle `endt` to
  `bend_eqb2`; `irulesblkpfx_check_neverqh_v5_sound` reuses the
  `MetaBlkPfx` proof verbatim with `bend_eqb_bsem → bend_eqb2_bsem` at
  the single cycle-closing step.  `Print Assumptions` =
  `functional_extensionality_dep` only.
- Corruption tests: `theories/Tests/IRulesV5_Corruption.v` (see below).
- Boards: **20 of 45** — the machines whose only obstacle is the
  end-match — in `theories/Machines/ListCV5Stage/LCV5_00..03.v`, manifest
  `tools/listc_v5_manifest.tsv`, emitter `tools/gen_listc_v5_stage.py`.

### Gap 2 — the engine re-blocking (LANDED, 16 boarded)

The other 25 get stuck BEFORE the end-match: the Coq replay's engine step
`EngineKS.beng_stepS` returns `None` (verified structural -- still `None`
at cfuel 5e6), because the config's near-head single-cell runs were never
re-encoded into the multi-cell block a certificate rule expects.  The C
verifier's `iv_reblock_side` / `iv_enc_side` re-blocks them -- e.g.
`b0.b1^4.b0^4.b1^4... -> b2^2` -- and THAT re-blocked shape is what lets
`iv_rule_try` match.  Crucially the re-block is needed in BOTH rule
validation (`check_rulesBlkP = None` otherwise) and the meta replay.

Fix (this branch):

- `theories/Checkers/IRules/Reblock.v` -- the untrusted greedy
  factorization (`reblock_side`, mirror of `iv_enc_side`: block length
  <=8, >=2 primitive reps, coverage >=16) + the VERIFIED `breblock_side`:
  accept the candidate only when `RulesBlk.bstreams_eq` re-checks it
  denotes the same cells (the affected near-head prefix is all
  constant-count, so `bstreams_eq` decides it -- the same
  untrusted-candidate/verified-by-bstreams pattern as `bcanon`).
  `breblock_cfg_bsemX` is denotation-preserving with ZERO axioms.
- `theories/Checkers/IRules/MetaBlkPfxV5b.v` -- `breplayRB` forks
  `breplayKP` applying `breblock_cfg` after every engine step, in BOTH
  rule validation (`check_rulesRB`) and the meta replay.  `breplayRB_sound`
  is `breplayKP_sound` verbatim + one `breblock_cfg_bsemX` rewrite; the
  whole soundness chain is unchanged.
  `irulesblkpfx_check_neverqh_v5b_sound`: Print Assumptions =
  functional_extensionality_dep only.
- Corruption tests: `theories/Tests/IRulesV5b_Corruption.v` (re-block
  load-bearing; block/meta mutants, halter, mutant machine rejected).
- Boards: 16 of 25 -- `theories/Machines/ListCV5Stage/LCV5B_00..03.v`,
  manifest `tools/listc_v5b_manifest.tsv`, emitter
  `tools/gen_listc_v5b_stage.py`.

### The last 9 (`tools/listc_v5_uncaught.txt`) -- two remaining frontiers

- 1 matrix-meta cert (`0RB0LA_1LC1LD_1RD0RD_1LA0RC`, v7, `meta_a=0
  meta_b=0`, a `rulerunm` lattice run): the scalar `a*k+b` meta layer that
  `MetaBlkPfx`/`...V5`/`...V5b` all reuse does not cover the matrix
  meta-map ("0 of the 50 Phase-2 certs use the matrix meta-map").  Closing
  it needs the matrix meta layer ported -- a separate feature, orthogonal
  to the v5 gap.
- 8 scalar certs need a `beng_stepS` variable-block hop.  Measured (e.g.
  `1RB0LC_0LB1RC_1RD1LA_1LA0RC`): their rules validate (2/2 with re-block)
  and BOTH rules fire in the meta replay at the same ops as the C prover
  (RULE 0 ~op 28, RULE 1 ~op 73), config bounded (nl<=16, nr<=18); then
  `beng_stepS` returns `None` on a configuration where the head must hop
  over a VARIABLE-count multi-cell block, which the C `iv_step` summarises
  but `EngineKS.beng_stepS` (block peel + chain/block hops) does not.
  Re-block does NOT help here (the stall is after both rules fire, in pure
  engine stepping); the `iv_absorb_side` variant (absorb completed copies
  into a following block) was implemented and measured to help NONE of the
  8, confirming the stall is `beng_stepS`, not canonicalization.  Closing
  these needs a genuine `beng_stepS` extension (peel/hop a variable-count
  block) with its own soundness proof -- the largest remaining engine
  surface.

  Investigated in depth (this session); the crossing is a full symbolic
  zipper and needs several composed pieces, each necessary but jointly
  still insufficient in the measured cases:
  (a) BLOCK-HOP CLOSURE -- the head crosses a block cleanly but the output
      word is a rotation of a declared block not itself in the table
      (e.g. crossing b10=[S1;S1;S1;S1;S0] in StC yields [S0;S1;S1;S0;S1],
      a rotation of b7), so `bhop_result`'s `blk_find` misses.  Fix:
      augment `cp_blks` with the hop-closure (untrusted; soundness holds
      for any table).  Measured: the closure is small (often +1 block) and
      terminates.
  (b) PEEL WITH COUNT>=1 -- when a block does NOT hop cleanly (bounces off
      its first cell, e.g. b6=[S0;S1;S1;S1;S1] with StC,S0->DR reversing),
      `beng_crossS` must peel one copy and let the head stop at the bounce;
      the landed guard requires the run count `>= 2`, but these runs are
      `k - c` with value 1 at kmin.  Relaxing to `expr_ge lo e 1` (sound:
      `cnt e >= 1` still splits the denotation) advances the replay one
      more copy.
  (c) The residual: after (a)+(b) the same run reaches count `k - c` = 0
      at kmin (empty for one k, non-empty above) -- a genuine
      empty-vs-nonempty case split the one-directional `beng_crossS`
      cannot make.  Flooring the meta-replay `lo` at `k0` (sound -- the
      tiling only uses the cycle for `k >= k0`, and `k0 >> kmin`) makes
      such runs provably non-empty, but the measured configs still stall
      afterward: the head genuinely enters a block and returns to the
      departed side, which the current one-pass crossing cannot represent.
  The clean fix is to replace `beng_crossS` with a general bounded
  symbolic zipper (mirror of the C `iv_step` inner loop) that lets the
  head cross AND bounce back, returning "did not cross" -- then compose
  (a) block-closure + this zipper.  That is a core-engine rewrite with its
  own soundness proof (the largest single piece of the whole v5 gap) and
  is left for a dedicated session.

## Files (this branch)

| file | role | axioms |
|---|---|---|
| `theories/Checkers/IRules/StreamEq.v` | `cseq` + `cseq_sound`, `bend_eqb2` + `bend_eqb2_bsem` (new trust surface) | `cseq_sound`: none; `bend_eqb2_bsem`: `functional_extensionality_dep` |
| `theories/Checkers/IRules/MetaBlkPfxV5.v` | `irulesblkpfx_check_neverqh_v5` + `_sound` | `functional_extensionality_dep` |
| `theories/Machines/ListCV5Stage/LCV5_00..03.v` | the 20 gap-1 boards (`lcv5_NN` + `Forall NeverQuasiHaltsSt`) | `functional_extensionality_dep` |
| `theories/Checkers/IRules/Reblock.v` | `reblock_side` (untrusted) + verified `breblock_side` + `breblock_cfg_bsemX` (gap-2 trust surface) | `breblock_cfg_bsemX`: none |
| `theories/Checkers/IRules/MetaBlkPfxV5b.v` | `irulesblkpfx_check_neverqh_v5b` + `_sound` (re-blocking replay) | `functional_extensionality_dep` |
| `theories/Machines/ListCV5Stage/LCV5B_00..03.v` | the 16 gap-2 boards (`lcv5b_NN` + `Forall NeverQuasiHaltsSt`) | `functional_extensionality_dep` |
| `theories/Tests/IRulesV5_Corruption.v`, `IRulesV5b_Corruption.v` | MUST-fail negative controls | (Examples) |
| `tools/gen_listc_v5_stage.py`, `gen_listc_v5b_stage.py` | emitters (v5 / v5b) | — |
| `tools/listc_v5_manifest.tsv`, `listc_v5b_manifest.tsv` | the 20 + 16 boarded | — |
| `tools/listc_v5_uncaught.txt` | the 9 still-uncaught (1 matrix-meta + 8 beng_stepS-hop) | — |
| `tools/v5gap.txt` | the derived 45-machine set | — |

The checker files (`StreamEq.v`, `MetaBlkPfxV5.v`, `Reblock.v`,
`MetaBlkPfxV5b.v`) + the corruption tests are wired into `_CoqProject`
(base build);
the staged `ListCV5Stage/**` are self-contained and outside the census
target closure (validate each with `coqc -Q theories BBB4 <file>`), exactly
like wave-3's `ListCStage2/**`.

## Wire-in (box follow-up, when the census is next re-certified)

The 36 boards join the **proven (R_NeverQH) tier**, same conveyor belt as
wave-2/3 (`docs/IRULESQH_WAVE3.md`, `tools/wire_wave3.py`):

1. Append `lcv5_00..03` + `lcv5b_00..03` to `proven_list`
   (`Census/Proven_Data.v`).
2. Add `theories/Machines/ListCV5Stage/*` to `_CoqProject`.
3. Extend the drop list (`proven_listc_dropped.txt`) with
   `tools/listc_v5_manifest.tsv` + `tools/listc_v5b_manifest.tsv`
   machines; `regen_residue.py` drops them
   from `D_census` (zero walk cost).
4. `make census-verify` on stable hardware; `Print Assumptions
   census_decided` must stay `functional_extensionality_dep` only.

Expected `D_census` reduction from this track: **-36** (all in list-C
residue; 20 gap-1 + 16 gap-2), rising to **-45** once the last 9 land
(1 matrix-meta + 8 needing a `beng_stepS` variable-block hop).

## Reproduce (UNTRUSTED)

```
make -C ../BBB                                   # bin/irules, bin/verify
bin/irules --max-steps 200000 --cert-dir results/certs_v5gap tools/v5gap.txt
# emit the 20 boardable certs (those the v5 checker accepts):
python3 tools/gen_listc_v5_stage.py theories/Machines/ListCV5Stage \
        tools/listc_v5_manifest.tsv 5 <the-20-cert-paths>
coqc -Q theories BBB4 theories/Machines/ListCV5Stage/LCV5_00.v   # etc.
```

The v5 checker's per-machine cost is dominated by the `fuel` **nat
literal** in `vm_compute` (the staged boards use `fuel = 300000` and take
~2–3 min each; the corruption controls use `fuel = 3000`, ~1 s, and still
close the honest cycle — the meta cycle closes in ≪ 3000 replay
iterations).
