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

### Gap 2 — the engine re-blocking / hop (NOT yet closed, 25 remaining)

The other 25 (`tools/listc_v5_uncaught.txt`) get stuck **before** the
end-match: the Coq replay's engine step `EngineKS.beng_stepS` returns
`None` (verified structural — it still returns `None` at cfuel 5·10⁶).

Root cause (machine `1RB0LC_0RC0RD_1LC1LA_0RB0LA`, C trace vs Coq):
the C replay's `iv_absorb` re-blocks a run of single-cell runs back into
a multi-cell block — e.g. `b0^1 b1^4 b0^4 b1^4 b0^2 b1^1 → b2^2` (block 2
= `00111100`) at op 36→37 — and **that** re-blocked shape is what lets
the rule fire (`iv_rule_try`).  Coq's `bcanon` has no reverse re-blocking
(only `bexpand_const` in the forward direction), so its config accumulates
single-cell runs, the rule never matches, and a few steps later the head
oscillates at the boundary of a variable block that `beng_stepS` cannot
summarise into a block step → `None`.

The C operation to formalise is `iv_absorb_side` (src/verify.c ~2720):
absorb preceding length-1 runs into a following ≥2-cell block run, growing
its count by one, when the consumed cells spell that block's leading
window.  It is **denotation-preserving**, so it can be added soundly.
Sketch:

1. `breblock : list Z → BTbl → list BRun → list BRun` (port of
   `iv_absorb_side`), with `breblock_den : bsemX (breblock …) = bsemX …`
   (mirror `bcanon_side_den`).
2. Fork `breplayKP → breplayKP2` applying `breblock` after `bcanon` in the
   engine-step branch; re-prove `breplayKP2_sound` (a copy of
   `breplayKP_sound` with one extra `breblock_den` rewrite — the proof is
   otherwise identical because it only uses denotation preservation).
3. Fork the checker `→ …_v5b` using `breplayKP2` + `bend_eqb2`; the
   soundness proof is the `MetaBlkPfxV5` proof with `breplayKP2_sound`.
4. Board the 25 with `…_v5b`; corruption controls: a re-blocked mutant
   whose cells DON'T spell the block must be rejected.

Open risk: whether `breblock` alone is enough, or whether some machines
also need `iv_reblock_side` (the near-head concrete re-blocking, ver≥3)
or a genuine `beng_stepS` extension for the variable-block hop.  The
`beng_stepS = None` was confirmed structural, but re-blocking may keep
the config in a hop-able form so the rule fires first (as it does in C).
Validate computationally (define `breblock` as an oracle, fork the replay,
`Eval vm_compute` the checker over the 25) BEFORE investing in the proof —
exactly as gap 1 was validated (20/45 via the real forked checker) before
`cseq_sound` was written.

## Files (this branch)

| file | role | axioms |
|---|---|---|
| `theories/Checkers/IRules/StreamEq.v` | `cseq` + `cseq_sound`, `bend_eqb2` + `bend_eqb2_bsem` (new trust surface) | `cseq_sound`: none; `bend_eqb2_bsem`: `functional_extensionality_dep` |
| `theories/Checkers/IRules/MetaBlkPfxV5.v` | `irulesblkpfx_check_neverqh_v5` + `_sound` | `functional_extensionality_dep` |
| `theories/Machines/ListCV5Stage/LCV5_00..03.v` | the 20 boards (`lcv5_NN` + `Forall NeverQuasiHaltsSt`) | `functional_extensionality_dep` |
| `theories/Tests/IRulesV5_Corruption.v` | MUST-fail negative controls | (Examples) |
| `tools/gen_listc_v5_stage.py` | emitter (fork of `gen_irulesnqh_stage.py`) | — |
| `tools/listc_v5_manifest.tsv` | the 20 boarded (machine, theorem, file, anchor, cert_ver) | — |
| `tools/listc_v5_uncaught.txt` | the 25 gap-2 machines | — |
| `tools/v5gap.txt` | the derived 45-machine set | — |

`StreamEq.v` + `MetaBlkPfxV5.v` are wired into `_CoqProject` (base build);
the staged `ListCV5Stage/**` are self-contained and outside the census
target closure (validate each with `coqc -Q theories BBB4 <file>`), exactly
like wave-3's `ListCStage2/**`.

## Wire-in (box follow-up, when the census is next re-certified)

The 20 boards join the **proven (R_NeverQH) tier**, same conveyor belt as
wave-2/3 (`docs/IRULESQH_WAVE3.md`, `tools/wire_wave3.py`):

1. Append `lcv5_00..03` to `proven_list` (`Census/Proven_Data.v`).
2. Add `theories/Machines/ListCV5Stage/*` to `_CoqProject`.
3. Extend the drop list (`proven_listc_dropped.txt`) with
   `tools/listc_v5_manifest.tsv`'s machines; `regen_residue.py` drops them
   from `D_census` (zero walk cost).
4. `make census-verify` on stable hardware; `Print Assumptions
   census_decided` must stay `functional_extensionality_dep` only.

Expected `D_census` reduction from this track: **−20** (all in list-C
residue), rising to **−45** once gap 2 lands.

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
