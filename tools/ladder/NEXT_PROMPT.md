MEASURE THE THREE REMAINING BLOCKED BUCKETS BEFORE BUILDING ANY OF THEM, in `carrino/Coq-BBB4`, on branch `claude/ladder-gray-<yourid>` cut from main (§4l merged: both knobs on both arms, the quasihalt closer, nineteen rows boarded, core undecided 59 → 46).

Read first, in this order: `docs/LADDER_PLAN.md` **§4l in full** — it is what the last session did and its last table is where the 46 stop; then §4k's "The lesson, which is 4g's again with the sign flipped", because **that lesson is now the method and this prompt is an instance of it**; then §4i's "The gate, answered", whose four `(gray, 2)` classes are already measured VERBATIM and are the thing you are most likely to build; then `theories/Checkers/LadderCheck.v` §3 (`ClassSucc`, `pos1_class_succ`) and §7/§8 (`board_neverqh`, `board_iqh`) — the interface did not change this session and will not need to; then `tools/ladder/emit_ladder.py`'s `closure_data`, which is the arm builder you are about to run over rows it currently refuses.

**STATE.** 46 core undecided (`tools/closeout/core_rows.txt`; `make closeout-status`). 5,095 frozen rows settled by a board. Of the binary/step-1/one-phase rows in the live core there are **none left that the closure can state** — all 15 that had both arms are boarded and the 6 that do not are `RULE_LADDER` 5's table row. The remaining 46 are, per §4l's last table:

    15  no value family PROBED AT ALL      LADDER_NOFAM; PR #90 reads 13 of 15
    12  families found, none closed        mechanical: coverage or differential
     6  closed, gray                       needs the (gray, 2) ClassSucc
     6  closed, binary/step-1, ARMS BLOCKED   the count language; not this session
     4  time cap
     3  closed, two phases                 needs the phase cycle in Inv

**THE TASK — measurement first, and the build it selects. In that order, and the second is not chosen until the first is done.**

* **Run the arm builder over the three buckets and COUNT.** §4k's guard, and it reversed the order of two sessions' work when it was run: before building the thing that consumes the arms, run the arm builder over the rows. `closure_data` refuses gray at its first line and two-phase at its third; **relax those two refusals in a PROBE (not in the emitter) and see how many of the 6 + 3 have both class arms under the two knobs.** They may all have them, in which case the theorem work is the whole cost; they may have none, in which case building `(gray, 2)` is worth zero rows and the last session's mistake is repeated one bucket over. The 4 time-cap rows are a separate and cheaper question: re-run `valfam --cap` higher on those four alone (~25 s/row) and see whether the cap was the whole story. That is under an hour for all three answers.

* **Then build whichever the count says is biggest.** The likeliest is `(gray, 2)`, and it is the best-specified thing left: §4i measured that the `Class` record does not have to widen at all and listed the four classes verbatim, `ClassSucc`'s predicate `P` is already in the file for exactly this reason, and `(binary, 1)` instantiates it at `fun _ => True`. What you add is one `ClassSucc` instance per class, one parity invariant (the value's low bit, which `+2` preserves — it is GLOBAL and cannot be pushed into `cs_u`/`cs_w`), and the emitter's gray digit words. `board_neverqh` and `board_iqh` do not change. The two-phase three want the phase cycle in `Inv`, which is a change to that predicate and to nothing above it (§4i says so and §4l did not test it).

**DO ONE ROW END-TO-END FIRST**, whichever bucket wins. Drive it to a `NeverQuasiHaltsSt tm_*` (or `iqh tm_*`) theorem, `make closeout`, and confirm the audit's "core undecided" moves. **A board that does not move a number is not a board.**

**GATE.** If the `(gray, 2)` arm probe comes back at zero of six, STOP and write §4m with the count, and do the two-phase three or the time-cap four instead — do not build a `ClassSucc` instance for rows whose arms do not derive. Same for two phases. If `make closeout` will not take a board, fix `inventory.py`/`gen_stages.py` first.

**DO NOT** add the Fibonacci-rank or terminator-template constructor (that is the 15-row bucket and it is a bigger build than everything else on the list combined — it wants its own session and its own measurement), do not do the outer parameter (§4j), do not touch the count language or `RU`, and do not re-run the 61-row sweep.

**Still open from §4j and #90, and nobody has checked it.** `docs/LADDER_NOFAM.md`: PR #90 reads John's two bouncer rows at a different anchor with a terminator SET, which would make them PHASE work rather than outer-parameter work. §4j's fix is still unbuilt and should not be built until someone checks that. Two rows.

**CONSTRAINTS.** May touch `theories/Checkers/`, `theories/Machines/Ladder/`, `tools/ladder/`, `docs/`, `NEXT_SESSION.md`. **Never edit `theories/Census/`.** Do not touch tailcert/nestcert/regcert or wave-session files. Commit incrementally; push and open a PR when the first row moves the core count.

**Facts worth not rediscovering.**

* Coq is not in the image — `apt-get install -y coq` gives 8.18.0, which is what CI expects.
* **The full tree is ~2 h at `-j3`** and `theories/Machines/IRules_Batch_00.v` and `_01.v` are ~16 CPU-minutes EACH at the end of it, so the last quarter looks stalled and is not. `make closeout` is ~10 min once the tree is built. `.vo` are gitignored: a fresh container pays the 2 h, a branch reset does not.
* **Never run `valfam.py` and a full `make -jN` at the same time.** One row is fine (~25 s) and that is how the six promoted rows got certified; the 61-row sweep is not.
* **`board_ladder.py` rewrites `_CoqProject`, and doing that under a running `make` makes the build LIE.** `Makefile.coq` is generated from `_CoqProject`; changing it mid-build invalidates the generated makefile and `make` can exit **0** with several hundred files unbuilt. It cost nothing here because `make closeout` rebuilds whatever `Closeout.vo` needs — serially, which is the slow way round. Board first, then build.
* **§4k's lesson is the method now:** before building anything that consumes the arms, run the arm builder over the rows and count. It has now been right twice.
* **`stride = 0` needs the whole side concrete in `s_pre`.** `SWin` moves inside `s_pre` and NO chain step carries a cell from `s_post` across the block boundary into it (`srot 0` is the identity), so a flat arm stated as `mkS pre [] 1 0 post` has no chain at any depth. `LadderCheck.blk` is the normalisation and `blk_den` says the denotation is unchanged. The failure mode reads like "the carry ripple is not affine" and is not — it is an instant `None` at every stride.
* `board_iqh`'s `qa`, `sq`, `visq` are POSITIONAL after `t0`; Coq's `(name := v)` application does not reach past the anonymous hypotheses in between.
* **"core undecided" is a bucket, not a count of machines.** Boarding a core row can PROMOTE a `0RB` shadow into the core: 13 rows boarded took it 59 → 52, not 59 → 46. Quote `settled by a board` when the claim is about rows decided. (The six promoted rows were then boarded too, which is where the 46 comes from.)
* The fill arm's guaranteed block copies must be materialised into `s_pre`. Measured: the canonical `rep u (1*j+1)` form finds **no chain at all**; `u ++ rep u j` finds one in six steps. Do not "clean up" that normalisation.
* `vis_of_run` wants a chain from the anchor, **not a prefix of the arm's own chain** — a state can sit inside a macro step no prefix ends on. `emit_closure` searches from every prefix of each fill arm's derivation for this reason, and it now does it PER ARM INDEX because the tops the liveness lands on are whatever widths the counter reaches.
* `emit_ladder.py` writes its refusal reason **into the `.v` file**. Read the file, not the driver's last line — `board_ladder.py` reports the last stdout line and that is often a bad-arm note, not the refusal.
* Keep `board_ladder.py`'s `wanted()` in step with `closure_data`'s refusals. It drifted once and silently refused 18 rows on a condition that had already been removed.
* The arm shapes in `core61_armshapes.txt` are from `lapcert.derive_chain` at `maxdepth 40 / nmax 400`. Raising those did not help any row that failed. The emitter searches thresholds 0..3 and strides 1..4, cheapest (fewest arms) first.
* `tools/ladder/bounce.py --selftest` exists because two versions of that probe silently missed both of the machines it was written to find. Any probe whose miss you intend to report needs a known-positive case.
* The arm-soundness, class and avoidance lemmas are Closed under the global context — zero axioms — because they are on `csteps`/`cden` and never go through `lift`. `board_arm` and `board_lap_avoid` are too. Keep it that way; funext enters only in the final assembly.
