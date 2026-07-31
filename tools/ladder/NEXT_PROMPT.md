BUILD `(gray, 2)`.  It is four rows, the arms are MEASURED to derive, and the
build is specified to the lemma — in `carrino/Coq-BBB4`, on branch
`claude/ladder-gray-<yourid>` cut from `main`.  **Diff `origin/main` first**
(§4l's own lesson: `git show origin/main:tools/closeout/core_rows.txt` is one
diff and costs nothing — the wave route has taken rows out from under two
sessions now).  §4n merged: the phase cycle in `Inv`, three rows, core
undecided 43 → 40.

Read first, in this order: `docs/LADDER_PLAN.md` **§4n in full** — it is what
the last session did, its probe is why you are not measuring again, and its
last table is where the 40 stop; then §4i's "The gate, answered", whose four
`(gray, 2)` classes are listed VERBATIM and were independently re-derived by
§4n's probe from the machines themselves; then `theories/Checkers/LadderCheck.v`
§3 (`Class`, `ClassSucc`, `pos1_class_succ`) and §5 (`Section Iter`), which is
where every one of your edits goes; then `tools/ladder/armprobe.py`, which
already builds the gray class arms and is the emitter you are about to teach
`emit_ladder.py`.

**STATE.** 40 core undecided and 15 `0RB` shadows (`tools/closeout/core_rows.txt`;
`make closeout-status`).  5,101 frozen rows settled by a board.  Per §4n's last
table: 17 families-found-none-closed, 6 gray (**4 with both arms**), 5 fibonacci
(§4m, `live = BCD`), 5 no-family, 3 time cap, 4 arms-blocked.

**THE TASK.**  §4n measured the gray six and found **four** of them have both
class arms under the two knobs — and it found them by fitting the classes from
`fam_next` and recovering §4i's four verbatim.  So the measurement 4k's guard
asks for is DONE; do not re-run it.  Build the thing it selected:

* **`cls_side` gains a fixed word before the run.**  `(Binary, 1)`'s classes
  have `cs_u = []` so `cls_side` never carried one; three of `(gray, 2)`'s four
  do.  `run_side` already has `w1` — copy that shape, and `fam_cells_class`
  takes the same one-line change.
* **Four `ClassSucc` instances and one parity invariant.**  `P` is already in
  the file for exactly this and `(Binary, 1)` instantiates it at `fun _ => True`.
  The discriminator is the value's low bit, `+2` preserves it, and it is GLOBAL
  — it cannot be pushed into `cs_u`/`cs_w` (§4i measured that: with the parities
  mixed the four classes contradict each other).
* **The case split.**  `board_arm` runs on `digs_decomp`; `(gray, 2)` needs the
  four-way analogue — every member of a width is one of the four classes or the
  top.  §4n's probe checks exactly this by enumeration and reports coverage, so
  use it as the oracle while you state the lemma.
* **The top of a width is `[1] ++ 0^(k-2) ++ [1]`, not the all-max run** — the
  largest MEMBER, because `b^k - 1` is odd and not a member at all.  So
  `pos1_is_top` / `pos1_top_shape` get gray twins, and the fill arm's left-hand
  side has a fixed word each side of the run.
* **`Section Iter` at `Gray`/step 2.**  `Hcode`/`Hstep` gate it, and
  `fam_value` at `Gray` is a fold from the most significant digit down, so no
  lemma about `val_pos` transfers.  `inv_value_lt`, `fam_succ_total` and
  `top_reached_aux` each need their gray statement; the measure `b^k - value`
  falls by 2 rather than 1 and that is the whole difference.

**DO ONE ROW END-TO-END FIRST.**  `1RB0RB_0LC0LD_1LC1LD_1RA0RA` is the one §4g
and §4i both read; drive it to `NeverQuasiHaltsSt tm_*`, `make closeout`, and
confirm "core undecided" moves.  **A board that does not move a number is not a
board.**

**GATE.**  If a `ClassSucc` instance will not go through, STOP and write §4o
with which class and why — do not weaken `ClassSucc` to fit it, and do not add
a second class record.  §4i's result that the record does not widen is worth
more than any one row.

**DO NOT** re-run the arm probe over the gray six (§4n did it: 4 of 6, and the
two that fail do NOT fail on the class law — see below), do not add the
Fibonacci-rank or terminator-template constructor (that is §4m's five rows and
its own session), do not do the outer parameter (§4j), do not touch the count
language or `RU`.

**The two gray rows that are NOT in the four, and it is a FAMILY question.**
`1RB0RD_1LC0LB_1LD0LB_1RD0RA` and `1RB0RD_1LC0LC_1LD0LB_1RD0RA` have two-cell
digit words ending in `0`, so `fam_cells` spells one cell more than the
machine's `cconf` carries at the anchor — the trailing blank is never
materialised.  Measured: strip that one cell and the fill arm derives in 24
steps at every index and copy split.  Their class law is fine.  Either re-read
them at an anchor whose digit words do not end in a blank, or give `fam_cells`
a trimming the denotation can state.  Two rows, and it is not a `ClassSucc`.

**CONSTRAINTS.**  May touch `theories/Checkers/`, `theories/Machines/Ladder/`,
`tools/ladder/`, `docs/`, `NEXT_SESSION.md`.  **Never edit `theories/Census/`.**
Do not touch tailcert/nestcert/regcert or wave-session files.  Commit
incrementally; push and open a PR when the first row moves the core count.

**Facts worth not rediscovering.**

* Coq is not in the image — `apt-get install -y coq` gives 8.18.0, which is what
  CI expects.  It takes about a minute.
* **`make closeout` only needs `theories/Closeout/Closeout.vo`, and its
  dependency closure is 2188 files that do NOT include the nine
  `IRules_Batch`** (`coqdep` says so; ask it, not the plan file).  So the audit
  never pays their 8.2 GB each.  `make -f Makefile.coq -j3
  theories/Closeout/Closeout.vo` from cold is about 45 minutes on the 4-core
  box; `make -j3 closeout` after a kernel edit is about 30 (31 boards + 51
  `CB_*` + `Closeout`).  `.vo` are gitignored: a fresh container pays it, a
  branch reset does not.
* **Editing `theories/Checkers/LadderCheck.v` under a running `make` makes
  every already-built board fail** with `inconsistent assumptions over library
  BBB4.Checkers.LadderCheck`, and the build stops there.  Same trap as
  rewriting `_CoqProject` mid-build, same fix: finish the edit, then build.
  Nothing is lost but the wall clock.
* **`RuleSound` is an equation on `cconf` and `CTape.ctape_move` does not
  normalise.**  A blank the head materialises by stepping back over it is
  `S0 :: r` and not `r`, and `valfam`'s `other_side_cells` drops exactly those
  cells — the same TAPE under `lift` (so `Hboot` does not notice) and a
  different `cconf` (so every arm does).  `armprobe.py` reads the far side off
  the boot for this reason and the emitter's gray path will have to.  Without
  it, zero of six gray rows have an interior arm; with it, six.
* **The top of a width is the largest MEMBER.**  At step 2 the all-max string is
  not a member, and an arm built on it has no chain because the machine is never
  in that configuration.  Read the tops off the orbit.
* `board_neverqh`/`board_iqh` are now WRAPPERS at `NPH = 1` over the
  phase-indexed `boardph_neverqh`/`boardph_iqh` (§4n).  Their argument order is
  unchanged and the thirty-four boards use it; if you change `Section BoardPh`'s
  variables, `Section BoardOne` is where the old interface is kept alive, and
  every existing board depends on that.
* **A fill arm's anchor does not have to witness every recurring state.**
  `tops_cofinal_at` gives the tops of one chosen phase `pv`, and the emitter
  picks `pv` by trying each phase.  If a gray row's fill anchor cannot reach
  some state, that mechanism is already there at `NPH = 1` (`pv = 0`) and what
  it needs is a `pv` to choose from — which a one-phase family does not have.
  Widening the visit search is the other half: `emit_ladder.visits` now walks
  out from the anchor breadth-first over the engine's own candidate steps after
  the prefix search fails.
* **`stride = 0` needs the whole side concrete in `s_pre`** (`blk`/`blk_den`);
  the failure reads like "the carry ripple is not affine" and is an instant
  `None` at every stride.
* `emit_ladder.py` writes its refusal reason **into the `.v` file**.  Read the
  file, not the driver's last line.
* Keep `board_ladder.py`'s `wanted()` in step with `closure_data`'s refusals.
* **Never run `valfam.py` and a full `make -jN` at the same time.**  One row is
  fine; a sweep is not.
* The time-cap bucket is three rows, not four.  All four re-run at `--cap 900`
  (six times the sweep's budget): the three `1RB---` rows still cap, each with
  26 families found and four tried -- so raising the budget is not the lever,
  and the question is which families the searcher spends it ON.
  `1RB1RC_1LA1RA_0RC1LD_1LB0LD` finishes in 723 s and stops on
  `interior-not-covered` with 5 of 12 families tried: it is a coverage row that
  was wearing the budget's label.
* The arm-soundness, class and avoidance lemmas are Closed under the global
  context — zero axioms — because they are on `csteps`/`cden` and never go
  through `lift`.  `board_arm`, `board_lap_avoid`, `arm_index`, `blk_den`,
  `top_after` and `tops_cofinal_at` are too.  Keep it that way; funext enters
  only in the final assembly.
