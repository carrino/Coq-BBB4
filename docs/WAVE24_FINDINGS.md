# Wave-24: the CASCADE, built

_Branch `claude/residue-reduction-cascade-yhqvj4`, 2026-07-28.  The task was
the exp-counter bucket — 72 of the 87 `no exit chain`/`no boot chain` rows —
whose design brief is `docs/CASCADE_EXIT.md`.  That brief ended with a
part-run gate: the A→B level transition derived as a single-index chain, and
B→A and the base close were OPEN because their endpoint framing was delicate
and two ad-hoc trace scripts had disagreed on blank-head numbering._

## 1. The one-line result

**The gate is closed and the route is built.**  B→A and the closing sweep
both derive as ordinary single-index chains; the level induction is
`theories/Counters/NestedLapCascade.v` (funext-only); the emitter renders the
whole overflow branch per machine; and one machine's branch is committed and
kernel-checked, proving the `LapStep` obligation for an overflow phase that
runs `2j+1` inner counts.

Nothing in `Checkers/LapDecider.v` was touched, and no new checker language
was needed — §4b's prediction held.

## 2. What actually blocked B→A

Not the mechanics, which §4b had traced correctly, and not the count
language.  The framing, in two independent knobs, and it needs both:

* **the peel** — how many unit copies sit in the sside's `post` rather than
  in its count.  B→A's turnaround walks back out over cells it has just
  written, and at peel 0 it runs one short: the window is blocked and NO
  chain exists, at any split.  One peeled unit is exactly the room it needs.
  A→B does not need this, which is why A→B derived at the first framing tried
  and B→A did not.
* **the split** — how many cells stay concrete before the opaque tail.  B→A's
  eat reads ONE cell into the growing region: the unit misreads there, and
  that misread is what ENDS the eat.  §4b said the turnaround was a
  fixed-size window at the tail head; it reaches one cell further.

Both are now searched rather than guessed (`nestcert._frame_pair`), which is
what a per-machine emitter needs anyway.  **The lesson generalises:** when a
transition is known to exist by trace and does not derive, the framing search
space is (peel, split) before it is anything else.

## 3. Two corrections to the brief's structure

* **The cascade descends to level 0, not to level 2.**  Levels 1 and 0 are
  invisible to the segment scan only because their runs are 2 and 1 values
  long, under `CASC_MINLEN`.  `cascade_check` predicts all four words of every
  level from the law and finds each one among `phase_mid`'s own
  configurations, down to level 0, at K = 6, 7 and 8 — a real extrapolation
  test, since the two lowest levels are not in the input.
* **The main count IS the level-j second count**: `tail_main = extraB ++ rep
  unit (M - j)` exactly.  The phase is uniform from level j down, the boot
  lands on B(j), and the induction needs no separate entry step.  The ENTRY
  chain the extractor derives independently comes out equal to B→A, same
  framing and same chain — which is the cross-check that the reading is right.

A third, smaller one: **no reindex is needed anywhere.**  The offset route had
to run the whole overflow branch at `j = S j'`; the cascade does not, because
the peel absorbs the shift.  `gso_`/`geo_` keep their standard form and the
closing sweep lands on the standard `B1`.

## 4. What was built

| piece | where |
|---|---|
| run/segment scan, tail law, per-level word check | `nestcert.cascade_segments/_runs/_law/_check` |
| framing search (peel × split) | `nestcert._frame_pair` |
| endpoints + chain gate | `nestcert.cascade_endpoints` |
| differential validation | `nestcert.cascade_validate` |
| drivers | `cascade_probe.py --endpoints`, `--gate` |
| level induction | `theories/Counters/NestedLapCascade.v` |
| emitter | `tools/counters/cascade_emit.py` |
| pinned exemplar | `theories/Tests/CASC_0RB1LA_0LC1RD_1LA1LD_1RB0LA.v` |

The extractor lives inside `nestcert.py` on purpose: §4c had measured two
ad-hoc probes disagreeing on blank-head numbering, so `phase_mid`'s
configurations and its `rstrip0` convention are single-sourced there, and
`cascade_probe.py` now delegates its own scan to them (its published
`--classify` numbers, 72/15, did not move).

## 5. The numbers

`cascade_probe.py --gate` per machine: read the law, check it at every level
down to 0, derive boot + inner lap + all three transition chains, then replay
the WHOLE cascade against the raw simulator at j = 2..8 — exact step counts
and exact configurations, 77 counts and 1433 inner laps each.

* **57 of the 87** gate end-to-end.
* And **57 of those 57** emit a Coq overflow branch that the kernel accepts:
  `cascade_emit.py --proto` over the whole gated set, `coqc` on each, 57
  compile and none fails.  The emitter is not exemplar-shaped.
* The 30 that do not gate, at K = 7: **12** report a main count at
  `2^(j-1)..2^j-1` — an octave-shifted top level, which `families()` already
  carries an `oct` for, so emitter work and not new theory; **17** report one
  or two counts in the phase (the `no boot chain` mirror half plus the 15
  odd-shaped rows §2 of the brief set aside); **1** a main count at 4..7.

The validation bites: adding one step to any transition's cost is caught at
j = 2 (checked for all three).

## 6. What this does NOT do

`D_remaining` is unchanged at **496**.  The committed module proves an
overflow branch, not a machine: a board needs the interior branch, the
bootstrap, the visit witnesses and the closer around it.  That wiring — a
third route in `emit_lapcert.derive`/`render` beside `nested` and `offset` —
is wave-25's build, and the one piece with a genuinely new shape is the visit
witnesses: `cascade_vis_at` is stated at an arbitrary level, but only level 0
is available at EVERY outer index, so a state that fires nowhere in the boot
has to fire in the closing sweep.

## 7. Do-not-retry, unchanged and extended

Everything in `CASCADE_EXIT.md` §5 stands.  Add:

* Framing B→A with the opaque split where A→B's sits — measured, no chain at
  any peel.
* Framing B→A at peel 0 — measured, no chain at any split.
* Reindexing the cascade's overflow branch at `j = S j'` the way the offset
  route does — unnecessary; the peel already absorbs the shift, and the
  reindex costs a whole extra concrete `j = 0` case for nothing.
