# v5 rule-replay gap — staging + hand-off

_Written 2026-07-23 (branch `claude/coq-bbb4-v5gap-<suffix>`), a
standalone parallel track to the wave-4 harvest.  Updated 2026-07-24
(branch `claude/coq-bbb4-v5zipper-crosss-<suffix>`): gap 3 landed --
8 of the last 9 boarded (v5c), superseding the engine-zipper hypothesis
with a smaller closure + multi-run end-match fix; see "Gap 3" below._

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
checker's sub-terms) found the 45 split across **three distinct corners**
(gap 1 end-match, gap 2 re-blocking, gap 3 block-hop closure + multi-run
end-match), all in the meta-cycle replay `breplayKP`, none of which the
landed Phase-2 engine covered.  Rule validation (`check_rulesBlkP`) and
the meta replay's *structure* are fine; the anchor re-simulation and
coverage are fine.  The gaps are downstream.  **Status: 44/45 boarded**
(20 + 16 + 8); the last is the matrix-meta cert (orthogonal).

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

### Gap 3 -- the engine crossing (LANDED, 8 boarded)

The remaining 9 split into 8 scalar machines and 1 matrix-meta cert.
**The 8 scalar machines are now boarded** by the v5c checker
(`irulesblkpfx_check_neverqh_v5c`), and the fix is NOT the engine "zipper"
the earlier hand-off (below) hypothesised.  Deep config-by-config
measurement this session (instrumenting the C `iv_step` / `iv_absorb` and
`Eval vm_compute`ing the Coq engine side by side) established the real
cause and a much smaller, cleaner, sound fix.

**What was actually measured (donor `1RB0LC_0LB1RC_1RD1LA_1LA0RC`):**

- The C meta replay runs at `lo = kmin` (verify.c: `g->lo[0] = c->ir_kmin`),
  the SAME `lo` the Coq replay uses.  So `(c)` k0-flooring below is a red
  herring -- worse, running at `lo = k0` fabricates counts like `k-117`
  that are 0 at the bound, which is what made the earlier probe "stall".
- Both engines PEEL a bouncing block only when its count min `>= 2`
  (C's `iv_need(e,2)` == Coq's `expr_ge lo e 2`).  Neither ever peels a
  count-1-at-`lo` run in the passing traces, so `(b)` peel-with-count>=1
  is also unnecessary.
- With ONE change -- closing the block table under block-hop outputs so
  `bhop_result`'s `blk_find` resolves the rotation blocks (piece `(a)`) --
  the UNCHANGED engine `EngineKS.beng_stepS` tracks the C `iv_step`
  **byte-for-byte for the entire 137-iteration meta cycle** (verified by
  normalising both config sequences and `diff`-ing: identical through the
  last iteration).  So there is no engine gap at all.
- The ONLY real gap is the END-MATCH.  The cycle closes on a configuration
  CELL-equal to the shifted template but whose two sides each carry TWO
  variable-count runs (e.g.
  `b1^3 . b10^(k+1) . b1^7 . b0 . b1^(1+3k) . b0 . b1^3` vs
  `b1^7 . b6^(k+1) . b1^3 . b0 . b1^(1+3k) . b0 . b1^3`).
  `StreamEq.cseq` (`exp1`) handles only ONE variable run, so `bend_eqb2`
  refuses and the Coq replay runs PAST the cycle end into the next
  (unrecognised) iteration -- which is where the earlier probe observed
  `beng_stepS = None`.  The C verifier's `iv_streams_eq` walks the cells
  symbolically and accepts.

**The v5c fix (two changes, both leave the soundness chain intact):**

- `(a)` BLOCK-HOP CLOSURE -- `BlkClosure.blk_closure` augments the block
  table with the primitive-root words block hops can produce (e.g.
  crossing `b10=[S1;S1;S1;S1;S0]` in `StC` yields `[S0;S1;S1;S0;S1]`, the
  reverse of declared `b9`, which `blk_find` missed).  UNTRUSTED
  preprocessing: `bhop_result` re-verifies every hop against
  `mk_tbl blks` (`bhop_result_spec`: `nreps (tbl nsym) factor = hout`),
  the whole chain is parametric in `blks`, and `mk_tbl_raw` gives
  `raw_ok` for ANY block list -- so closing the table can only accept
  MORE crossings, never an unsound one.  Zero new soundness; measured to
  add ~+1 block and terminate.
- MULTI-RUN END-MATCH -- `StreamEq2.cseq2` strips the maximal common
  (syntactically-equal) run prefix and suffix, then applies the proven
  one-pump `cseq` to the residues.  Stripping identical runs is
  denotation-preserving, so `cseq2_sound` reduces to `cseq_sound` with two
  `bdside_app` rewrites (**zero axioms**).  `bend_eqb3 = bend_eqb2 || cseq2`
  with `bend_eqb3_bsem` (`functional_extensionality_dep` only).

`MetaBlkPfxV5c.irulesblkpfx_check_neverqh_v5c` is a mechanical fork of
v5b: `blks := blk_closure tm (cp_blks cert) 16`, end-match `bend_eqb3`.
The engine (`beng_stepS`), the re-blocking replay (`breplayRB`), rule
validation (`check_rulesRB`) and the anchor/coverage check are all reused
verbatim.  `Print Assumptions irulesblkpfx_check_neverqh_v5c_sound` =
`functional_extensionality_dep` only; the checker accepts all 8 at
`cfuel/fuel = 200000/3000` (the meta cycles are short, so the boards use
`fuel = 3000`, ~1s each).  Boards: `theories/Machines/ListCV5Stage/
LCV5C_00..01.v`, manifest `tools/listc_v5c_manifest.tsv`, emitter
`tools/gen_listc_v5c_stage.py`, corruption `theories/Tests/IRulesV5c_Corruption.v`.

### The last 1 (`tools/listc_v5_uncaught.txt`) -- the matrix meta-map

- 1 matrix-meta cert (`0RB0LA_1LC1LD_1RD0RD_1LA0RC`, v7, `meta_a=0
  meta_b=0`, a `rulerunm` lattice run): the scalar `a*k+b` meta layer that
  `MetaBlkPfx`/`...V5`/`...V5b`/`...V5c` all reuse does not cover the
  matrix meta-map ("0 of the Phase-2 certs use the matrix meta-map").
  Closing it needs the matrix meta layer ported -- a separate feature,
  orthogonal to the v5 gap.  Left documented as out of scope.

> **Superseded hypothesis (kept for the record).**  The earlier hand-off
> concluded the 8 needed a general symbolic-zipper rewrite of
> `beng_crossS` (head crosses AND bounces back), composed with pieces
> `(a)` block-hop closure, `(b)` peel-with-count>=1, and `(c)`
> k0-flooring, "each necessary but jointly still insufficient".  The
> deeper measurement above shows `(b)` and `(c)` are unnecessary (and
> `(c)` actively harmful), the engine needs NO change, and the "still
> stalls" observation was the replay running past an unrecognised
> cell-equal cycle end.  Closure `(a)` + the multi-run end-match is
> sufficient and sound.

## Files (this branch)

| file | role | axioms |
|---|---|---|
| `theories/Checkers/IRules/StreamEq.v` | `cseq` + `cseq_sound`, `bend_eqb2` + `bend_eqb2_bsem` (new trust surface) | `cseq_sound`: none; `bend_eqb2_bsem`: `functional_extensionality_dep` |
| `theories/Checkers/IRules/MetaBlkPfxV5.v` | `irulesblkpfx_check_neverqh_v5` + `_sound` | `functional_extensionality_dep` |
| `theories/Machines/ListCV5Stage/LCV5_00..03.v` | the 20 gap-1 boards (`lcv5_NN` + `Forall NeverQuasiHaltsSt`) | `functional_extensionality_dep` |
| `theories/Checkers/IRules/Reblock.v` | `reblock_side` (untrusted) + verified `breblock_side` + `breblock_cfg_bsemX` (gap-2 trust surface) | `breblock_cfg_bsemX`: none |
| `theories/Checkers/IRules/MetaBlkPfxV5b.v` | `irulesblkpfx_check_neverqh_v5b` + `_sound` (re-blocking replay) | `functional_extensionality_dep` |
| `theories/Machines/ListCV5Stage/LCV5B_00..03.v` | the 16 gap-2 boards (`lcv5b_NN` + `Forall NeverQuasiHaltsSt`) | `functional_extensionality_dep` |
| `theories/Checkers/IRules/BlkClosure.v` | `blk_closure` (untrusted; re-verified by `bhop_result`) | — (no soundness claim) |
| `theories/Checkers/IRules/StreamEq2.v` | `cseq2` + `cseq2_sound`, `bend_eqb3` + `bend_eqb3_bsem` (gap-3 trust surface) | `cseq2_sound`: none; `bend_eqb3_bsem`: `functional_extensionality_dep` |
| `theories/Checkers/IRules/MetaBlkPfxV5c.v` | `irulesblkpfx_check_neverqh_v5c` + `_sound` (closed table + multi-run end-match) | `functional_extensionality_dep` |
| `theories/Machines/ListCV5Stage/LCV5C_00..01.v` | the 8 gap-3 boards (`lcv5c_NN` + `Forall NeverQuasiHaltsSt`) | `functional_extensionality_dep` |
| `theories/Tests/IRulesV5_Corruption.v`, `IRulesV5b_Corruption.v`, `IRulesV5c_Corruption.v` | MUST-fail negative controls | (Examples) |
| `tools/gen_listc_v5_stage.py`, `gen_listc_v5b_stage.py`, `gen_listc_v5c_stage.py` | emitters (v5 / v5b / v5c) | — |
| `tools/listc_v5_manifest.tsv`, `listc_v5b_manifest.tsv`, `listc_v5c_manifest.tsv` | the 20 + 16 + 8 boarded | — |
| `tools/listc_v5_uncaught.txt` | the 1 still-uncaught (matrix-meta cert) | — |
| `tools/v5gap.txt` | the derived 45-machine set | — |

The checker files (`StreamEq.v`, `MetaBlkPfxV5.v`, `Reblock.v`,
`MetaBlkPfxV5b.v`, `BlkClosure.v`, `StreamEq2.v`, `MetaBlkPfxV5c.v`) + the
corruption tests are wired into `_CoqProject` (base build);
the staged `ListCV5Stage/**` are self-contained and outside the census
target closure (validate each with `coqc -Q theories BBB4 <file>`), exactly
like wave-3's `ListCStage2/**`.

## Wire-in (box follow-up, when the census is next re-certified)

The 44 boards join the **proven (R_NeverQH) tier**, same conveyor belt as
wave-2/3 (`docs/IRULESQH_WAVE3.md`, `tools/wire_wave3.py`):

1. Append `lcv5_00..03` + `lcv5b_00..03` + `lcv5c_00..01` to `proven_list`
   (`Census/Proven_Data.v`).
2. Add `theories/Machines/ListCV5Stage/*` to `_CoqProject`.
3. Extend the drop list (`proven_listc_dropped.txt`) with
   `tools/listc_v5_manifest.tsv` + `tools/listc_v5b_manifest.tsv` +
   `tools/listc_v5c_manifest.tsv` machines; `regen_residue.py` drops them
   from `D_census` (zero walk cost).
4. `make census-verify` on stable hardware; `Print Assumptions
   census_decided` must stay `functional_extensionality_dep` only.

Expected `D_census` reduction from this track: **-44** (all in list-C
residue; 20 gap-1 + 16 gap-2 + 8 gap-3), rising to **-45** once the last
machine lands (the matrix-meta cert, needing the orthogonal matrix
meta-map layer).

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
