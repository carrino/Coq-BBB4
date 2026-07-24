# Wave-7 — the NGramHist oracle-drive

_Written 2026-07-24 (branch `claude/ngramhist-oracle-wave-7-yo7hub`).  Continues
the history-augmented n-gram work of wave-6 (PR #25).  This wave reconstructs
mxdys' TNF so the per-machine oracle can drive the sweep, re-sweeps the residue
with per-machine params, adds pattern measures to the checker, and scaffolds
the Assembly `Forall`._

## 0. The TNF finding — the wave-6 hand-off hypothesis was WRONG (measured)

The wave-6 hand-off assumed the 3,594 residue machines that do NOT string-match
`BB4_verified_enumeration.csv` are "the same machines under a different TNF
relabeling", and that reconstructing mxdys' state relabeling would map them.
**That is false, and this wave measured why.**

`tools/nghist/tnf_canon.py` (first-visit state relabelling) and
`tools/nghist/oracle_lookup.py` (`reached_canon` = relabel + blank every
UNREACHED transition to `---`, then look up the CSV) establish:

- **mxdys' CSV contains ZERO full machines.**  Every one of the 858,908 rows
  has ≥1 undefined transition (distribution: 728,048 with exactly 1 dash,
  114,336 with 2, … 1 with 8).  This is bbchallenge's cnt≥1 pruning: the
  enumeration never fills the *last-reached* transition, so its space is
  exactly the machines that use at most `2n-1 = 7` of the 8 transitions from
  the blank tape.
- A machine that uses **all 8** transitions is therefore OUTSIDE mxdys'
  enumeration.  Its TNF ancestor (last-reached transition blanked) *halts* at
  the step it would use that transition, so mxdys records the ancestor as a
  HALT node — there is no oracle row for the (nonhalt) 8-transition completion,
  under any of the 48 state-permutation × mirror symmetries (checked
  exhaustively).
- Our census enumerates FULL machines ("no cnt=1 pruning", `TNF_QH.v`), so it
  produces exactly these extra 8-transition completions.  They are genuine
  nonhalt machines our tiers could not board; the oracle simply does not
  cover them.

**Measured split** (`reached_canon` + CSV lookup):

| population | uses ≤7 (in CSV, nonhalt) | uses all 8 (outside enum) |
|---|---|---|
| residue (5,129) | **1,535** (1,486 NGRAM-targetable) | 3,594 |
| holdouts (3,713) | 114 (all NGRAM nonhalt) | 3,599 |

Every ≤7-transition machine maps to a `nonhalt` CSV row; every all-8 machine
is absent.  The mapping is exact and behaviour-defined (relabel-invariant), so
`oracle_lookup.oracle_of` / `params_for` give mxdys' decider + params
(history, gram, gas) for the 1,486 targetable residue machines.

## 1. What the oracle IS good for (and what it is not)

- **Good for:** the 1,486 ≤7-transition residue machines.  Their oracle params
  (`tools/nghist/oracle_params.csv`) drive the sweep with the *minimal* params
  mxdys used.  wave-6's fixed `k=2→4, n=2` sweep OVER-parameterized the plain
  ones (833 want `gram=1`, 117 `gram=2`; only ~487 genuinely need history),
  blowing past the closure-size/fuel caps — 1,062 of the targetable machines
  were left unboarded.  Oracle-driving with per-machine `(history, gram, gas)`
  recovers them at small closures.
- **Not available for:** the 3,594 all-8 residue machines.  No oracle row
  exists.  These are swept blindly with escalating params + the rank fallback
  (wave-6 already boarded 540 of them this way, so they ARE closeable).

`params_for` map: `IMPL1_params_h_g_x_gas → history=h, gram=g, gas`;
`IMPL2_params_g_x_gas → history=1, gram=g, gas`.

## 2. Tooling (all UNTRUSTED, `tools/nghist/`)

- `tnf_canon.py` — first-visit state relabelling to TNF form.
- `oracle_lookup.py` — `reached_canon`, `oracle_of`, `params_for`; the CSV
  finding above; `BB4_CSV` env override for the 45 MB CSV kept out of git.
- `oracle_params.csv` — the 1,486 targetable residue machines with
  `(family, history, gram, gas)`.

The Coq kernel re-checks every emitted certificate via `vm_compute`; these
tools only pick which params to try.

## 3. Move 3 -- HPatt pattern measures + lex-tuple synthesis (LANDED)

The unboarded targetable machines all CLOSE at oracle params but FAIL the
single count/rank liveness measures (a state recurs but no 1-count measure
strictly decreases on its q-avoiding subgraph).  Two additions fix this, both
kernel-checked, `functional_extensionality_dep` only:

- `theories/Checkers/NGramHist.v`: `HPatt (p rg K phi gate)` on `hcomp` -- a
  pattern measure over `hsym` (the `NgPattE` fork).  `pm_val`/`pm_delta`/
  `pm_ok` are reused verbatim from `NGram`; the sole new obligation
  `pm_start_exact` (the `ng_start` form of `NGram.pm_exact`) is proved by
  self-seeding `ng_start_covers` with the config's own windows.
  `hcomp_denote` gains the `n` param for the `pm_ok` guard.
- `theories/Tests/NGramHist_Corruption.v`: `ctl_hpatt_boards` (a pattern-ONLY
  cert boards never-QH) + `hpatt_mut_rejected` (MUST-fail: `[S1;S1]->[S0;S0]`,
  no S1 => `pm_ok` false => sound no-op => the lex check rejects).  Axiom-free.
- `tools/nghist/nghist_prove.py`: `pm_delta` over the bit projection + a greedy
  **lexicographic ranking** (`lex_synth`) combining count and pattern measures.
  The wave-6 single-measure path is preserved (no regression); lex TUPLES are
  the real unlock -- one state discharged by several measures in lex order.

## 4. Move 2 -- the oracle-driven re-sweep (LANDED)

`tools/nghist/oracle_sweep.py` sweeps the 4,129 unboarded residue machines
(per-machine oracle params for the <=7-transition targetable ones, escalation
for the full-8).  With the lex-tuple prover it boards **242 new never-QH
machines** that wave-6's single-measure sweep could not
(`theories/Machines/NGHStage/NGH_05..07.v`, `Forall NeverQuasiHaltsSt`,
100/file, every file `coqc`-validated, `functional_extensionality_dep` only;
`tools/nghstage_manifest.tsv` extended to 676).  The yield is concentrated in
the full-8 machines (the targetable <=7 ones close at oracle params but are the
genuinely-hard never-QH tail).  The R_QH re-sweep on the never-QH failures
yields ~0 (1 in 1,800): those failures are not quasihalters -- their states all
recur, so they need richer liveness, not the wrap variant.

## 5. Stretch -- `theories/Census/Assembly.v` (LANDED)

Route A composition (no census walk): app-chains the NGHStage
`Forall NeverQuasiHaltsSt` (676) and NGHWStage `Forall iqh` (530) per-file
`Forall`s into one `Forall boarded boarded_all` over 1,206 machines, via a
common `boarded tm := NeverQuasiHaltsSt tm \/ (NonHalt /\ QHBound 2000 /\
QuasiHaltsSt)`.  `Print Assumptions boarded_all_boarded` =
`functional_extensionality_dep` only.  A closeout extends it with the wave-7
R_QH files (none this wave) and the wave-2/3/4 stage `Forall`s (their branch),
then relates `boarded_all` to the frozen `D_census` list.

## 6. The residual open core

After wave-7, ~3,650 residue machines remain unboarded by NGramHist.  These
are the machines where even the lex-tuple of count+pattern measures over the
augmented closure does not discharge liveness -- the genuine never-QH tail.
The `1RB0RB_1LC1RC_0RA1LD_1RC0LD`-class (mxdys' exact-model claim fails: no
finite model at any params) sits here.  Next levers: richer `HPatt` patterns in
`lex_synth`, higher history (`k=6,8` from the oracle's small tail), and a
per-state lex search that mixes gates (not just the whole q-avoiding set).
