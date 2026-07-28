# Next-session prompt — tower #20 is CLOSED; the (4,2) holdout list is DONE

_Rewritten 2026-07-28 at the end of wave-21 (branch
`claude/next-session-prompt-review-r8wdkq`), which proved tower #20's open
invariant and boarded it.  Full write-up: `NEXT_SESSION.md` section 2l; the
descriptor mirror is `tools/counters/desc20.py`, the earlier reconnaissance
`tools/counters/inv20.py`._

**Status, precisely.**  `theories/Machines/Counters/Tower_20.v` carries
`nqh_tower20 : NeverQuasiHaltsSt tm_20` with `Print Assumptions` =
`functional_extensionality_dep` only.  `tools/counters_manifest.tsv` has its
row, `tools/closeout/frozen_map.tsv` has its board, and #20 is OFF
`tools/closeout/frozen_unproven.txt` (`D_remaining` 622 -> 621).
`tools/closeout/audit.py` = OK (exact partition), `census_cache --check` =
MATCH.  **The (4,2) holdout list is closed** -- every wave/counter/holdout
machine is boarded.

The invariant that eluded waves 18-20 is a finite **descent descriptor**
(`Vd`/`Ud` in `Tower_20.v`), not a closure predicate: the level boots GROW
rather than cycle, and that growth is the `UDD` nesting, well-founded on the
descriptor.  See `NEXT_SESSION.md` 2l for the shape and the lap glue.

---

## What is left (all disjoint from #20)

1. **The residue track** -- the other 621 rows of `frozen_unproven.txt`.
   Its prompt is the wave-18/20 revisions of this file:
   `git show 02fd80b:docs/NEXT_SESSION_PROMPT.md`.  Everything in it about
   the residue still stands; only its holdout-status lines (which said the
   list had "exactly one machine left") are now history -- that one machine,
   #20, is boarded.

2. **The full `Closeout.vo` kernel re-check.**  Wave-21 verified #20's own
   pieces in-container (`Tower_20.vo` clean; the generated `cov_12_0094`
   cover lemma re-checks against `CloseoutKit`; `audit.py` OK).  It did NOT
   run `make -f Makefile.coq -j2 theories/Closeout/Closeout.vo`, which
   recompiles the whole 4,535-board tree and belongs on stable hardware
   (`-j2`, NOT `-j4` -- see the CI note below).  Do that on the box to
   re-certify the closeout end to end.

3. **CI is red on `main`** and has been since 2026-07-26: `ci.yml` runs
   `make -j4` over the whole tree and the runner is killed ~9 min in (no Coq
   error -- "The runner has received a shutdown signal").  PR #47 added ~300
   heavy files and this repo's playbook says `-j2`.  Diagnosed in
   carrino/Coq-BBB4#48; fixing it (split the build, or `-j2`, or a
   census-only fast job) is a real concern but not a proof failure.

## Ground rules that still hold

- ENV: apt coq 8.18.0 (`apt-get install -y coq`), then
  `coqc -native-compiler no -Q theories BBB4 <file>`.  No opam bootstrap.
  Tower_20 builds in ~3 s over five deps: `BBB4_Statement`, `CTape`,
  `Counters/WTape`, `Counters/WaveCounter`, `Machines/Counters/Tower_20`.
- NEVER touch `theories/Census/`; `python3 tools/census_cache.py --check`
  must stay MATCH.  Everything under `tools/` is UNTRUSTED; the kernel
  re-checks every board.
- Boarding a residue machine: prove its theorem, then
  `python3 tools/closeout/inventory.py` (regenerates `frozen_map.tsv` and
  `frozen_unproven.txt` by scanning `theories/Machines/**`),
  `python3 tools/closeout/gen_stages.py` (regenerates the `CB_*.v` stages +
  `Closeout.v`), `python3 tools/closeout/audit.py` (must print OK), then the
  `Closeout.vo` build on the box.  Add a corruption control in
  `theories/Tests/` in the tradition of
  `CountersTower20_Corruption.v` / `CountersW15_Corruption.v`.
- Name new files so they cannot clash with a concurrent residue session's
  (waves 10-18 used `ILS1_*`/`ILS4_*`/`ILS4F_*`, `IXP_*`, `WLS_*`, `WLJ_*`,
  `LAPC_*`, `LAPG_*`, `NLAP_*`, `Alph_*`).

Commit + push per validated batch.
