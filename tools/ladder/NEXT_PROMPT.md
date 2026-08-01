> # DONE — AND THE DIAGNOSIS BELOW WAS WRONG
>
> **The six rows boarded on 2026-08-01 (#118).**  Do not run this prompt.
> It is kept because what it got wrong is worth more than what it got right.
>
> This prompt's central claim is **"what blocks them is `Class`, not
> `Code`"**, and it specifies the fix as widening `Class.cs_t, cs_t'` and
> `Fill.f_mid` from `nat` to `list nat`.  **That widening was never built.**
> `cs_t : nat` is still `nat` (`LadderCheck.v` §3c) and `f_mid` still returns
> a scalar.
>
> What boarded the six was a fourth **CODE** — exactly the thing this prompt
> rules out.  The diagnosis in "What differs is the REPRESENTATIVE" below is
> correct and is the whole answer: `fibdec`/`fibokb` pick the GREEDY
> representative, these six stand on the LAZY one.  #118 added `FibL` to
> `LadderFam` with the decoder `fiblaz` (`fibdec`'s two-state automaton with
> the transitions swapped) and `lazfill`, plus `fam_lo` — because what a
> weighted numeration actually costs the interface is a FLOOR: width `k`
> spells exactly `[fibw k .. fibsum k]`.  The prompt had the measurement
> right and drew the wrong structural conclusion from it.
>
> The rows below are all boarded (`theories/Machines/Ladder/LDR_*.v`); the
> `1RB---` three-state population is closed entirely.  For live work read
> `docs/RESIDUE_MAP.md` and `tools/closeout/core_rows.txt`.

GIVE `LadderCheck`'s `Class` AND `Fill` A WORD-VALUED RUN UNIT, AND SIX ROWS
BOARD.  Wave 4v measured the fibonacci six against the kernel and the gap is
one field, not a numeration.  In `carrino/Coq-BBB4`, on branch
`claude/wordrun-<yourid>` cut from `main`.

**Diff `origin/main` first**: `git show origin/main:tools/closeout/core_rows.txt`
is one command, and the wave route has now taken rows out from under seven
sessions.  §4l, §4n, §4o, §4p, §4r and §4s each say this; §4o said it and then
had its OWN next-session prompt invalidated eight hours later by §4p, §4t had
its Route B invalidated by §4v, and §4u and §4v are two sessions that boarded
the SAME row in parallel — the third such collision in six waves.  **Re-read
the plan's last section before acting on a prompt, because the prompt is older
than the plan, and check `origin/main` again before you emit.**  This one was
written at the end of §4v.

Read first, in this order: `docs/LADDER_PLAN.md` **§4v in full** — it is the
measurement that selected this task and it RETIRES the previous prompt's
Route B; then **§3c and §11 of `theories/Checkers/LadderCheck.v`**, the
`(Fib, 1)` instance you are writing a sibling of; then §4r, which priced the
last instance and is the closest thing to a cost model.

**STATE.**  **15** core undecided and **5** `0RB` shadows
(`tools/closeout/core_rows.txt`, `tools/closeout/shadow_rows.tsv`;
`make closeout-status`).  **5,136** frozen rows settled by a board, 99.6%.
**20** rows remain, and the six below are **more than a third of the core**.
(Two 2026-08-01 waves ran in parallel on nickdrozd's nineteen and their board
sets are DISJOINT: `drozd-easy-puzzles` took five core rows and three shadows,
`drozd-easy-proofs` took `1RB1LB_1LC0RD_0LB1LA_0LA1RA` and
`1RB1LA_0LA0LC_1LC1RD_0RB0RD` with three more.  None of the eight is one of
the six below, which are untouched.)

**THE TASK.**

The six rows are

    1RB---_0LC1RD_1LB1RC_1LB0RD      1RB---_1LC0RB_0LD1RB_1LC1RD
    1RB---_0LC1RD_1LB1RD_1LB0RD      1RB---_1LC1RB_0LB1RD_1LC0RD
    1RB---_1LC0RB_0LD1RB_1LC1RB      1RB---_1LC1RD_0LB1RD_1LC0RD

and they are ONE sub-machine's worth of behaviour: at their own anchors all
six produce the identical value-to-string table (`docs/CORE_3STATE.md` §1's
grouping, showing up in the counter reading).  So one instance boards all six.
None of them carries a shadow.

**They count in the kernel's own numeration.**  `fibw` = 1,1,2,3,5,8,
`fam_lim F k = S (fibsum k)`, widths spanning `[fibw k .. fibsum k]` with
`fibonacci k` strings each, top of a width `1^k` at value `fibsum k`, value =
anchor visit index.  All of that is measured against the raw simulator in
`tools/counters/fibform.py` and all of it is what `LadderFam` already states.
**Do not build a numeration.**  §4s's `1,2,3,5,8,13` was `1,1,2,3,5,8` with a
constant marker cell dropped — `fit_weights` cannot pin a column that never
varies, so it drops the fit instead of completing it.

**What differs is the REPRESENTATIVE.**  `fibw 0 = fibw 1 = 1`, so a value
does not determine a string; `LadderFam.fibdec` / `LadderCheck.fibokb` pick
the greedy member and these six stand on the lazy one —

    LSB-first: the top digit is 1 and NO TWO ZEROS ARE ADJACENT

on all 23,614 measured values, at every anchor with a run above 50.  So what
to build is a second representative of the code that is already there:
`fiblaz` (the decoder), `fiblazb` (membership), their round trip, and the
classes below.  `fibw`, `fibsum`, `fibval`, `fam_lim`, `fam_top`, `fibsum_S`
are all untouched.

**The class laws, already validated against the orbit** — run
`python3 tools/ladder/fiblazy.py` (six rows, ~23,593 interior + 20 fill +
23,614 membership checks each, zero failures) and `--selftest` before you
believe them, and do not state a lemma the oracle has not checked:

    INTERIOR, split on the PARITY of the low run of ones
      E   (1,1)^m ++ [0]        ++ rest  ->  (1,0)^m ++ [1] ++ rest
      O   [1] ++ (1,1)^m ++ [0] ++ rest  ->  [1] ++ (1,0)^m ++ [1] ++ rest

    FILL, the top of a width, and the width's parity is the PHASE
      E   (1,1)^m         ->  (1,0)^m ++ [1]              k = 2m
      O   [1] ++ (1,1)^m  ->  [1] ++ (1,0)^m ++ [1]       k = 2m + 1

**The widening is two fields and it is a strict generalisation:**

    LadderCheck.Class.cs_t, cs_t' : nat  ->  list nat
    LadderFam.Fill.f_mid          : nat  ->  list nat

with `cls_lhs`/`cls_rhs`/`fill_apply` using `concat (repeat w n)` in place of
`repeat d n`.  There is NO stride — the LHS run `1^n` is `(1,1)^m` at the same
exponent the RHS run `(1,0)^m` uses, and both sides keep their length.  The
CELL side already speaks word runs (`flat_map_repeat` lands on
`rep (dig F t) n` and `rep` takes a word), so the change is on the DIGIT-string
side only.  The three existing instances (`pos1_class`, `g2c`, `f1c`) should
re-state as `[t]` for `t` and re-prove; **if any of them needs more than that,
stop and write down which, because that is the real cost of this task and
nobody has measured it.**

**WHAT NOT TO DO.**

* **Do not build `(Fib, 2)`/Zeckendorf.**  The previous prompt asked for it
  and §4v retires the request: it would build a `fam_lim`, a weight ladder and
  a round trip that already exist, and it would still not spell these
  machines' strings, because the difference was never the weights.  Two of
  that prompt's details were also the wrong way round — membership is no two
  adjacent ZEROS, and the top of a width IS `1^k` (the alternating `1010…` is
  what the fill lands ON).
* **Do not re-run Route A.**  `tools/ladder/fibread.py` ran it exhaustively:
  840 raw weight fits over all six rows, every anchor, both digit widths,
  every prefix, terminator and permutation — zero at `1,1,2,3,5,8`.  There is
  no tie to break.  And no anchor spells the greedy representative
  (`tools/counters/fibform.py`).
* **Do not re-probe the four base-2 quadratic rows** (`1RB0LD_0LC0RB_...` and
  the three `1RB1LA` rows).  §4p measured a second difference of exactly 2 on
  the arm itself, `QUAD_TERMINAL_MEASUREMENT.md` corroborates it independently
  and §4t re-ran the emitter over them for a third measurement of one blocker.
  No widening of `ARM_GRID` reaches a quadratic.
* **Do not count `1RB0RB_0LC1RD_1LC1LA_0LA1RB` with the six.**  §4s measured
  that it finds no family at any anchor — `digit_words(rules)` names nothing.
  It is a `no anchor` row.
* **Do not do the outer parameter (§4j), and it now has NO CONSUMER at all.**
  §4t measured it necessary and not sufficient for the only two rows it
  existed for — one lap of `0RB0RD_1LC1RB_1RA0LC_1LB0LC` moves two
  independent unbounded quantities and `cden` has one index — and #114 then
  boarded both of those rows off `Counters/Sep2Counter.v`, by hand and
  outside the ladder entirely.  So the field would be carried everywhere and
  used nowhere, which is 4j's own complaint about the `p` already there.
* **Never edit `theories/Census/`.**

**Also open and cheap.**

* **Re-run §4t's query whenever the emitter changes**: which core rows carry a
  `closed: true` certificate in a committed sweep and are still unproven?
  That is how `1RB1LA_0LA1RC_0RD0RB_1RA---` was found, and §4u boarded it (and
  §4v boarded it again, in parallel) for one command — its refusal was a stale
  certificate schema, not mathematics.  §4u also names what the emitter hits
  first on such a certificate: the missing `code` stamp, not `lands_in_phase`.
* Nick's list included three rows the ladder does not read at all, and the
  `drozd-easy-proofs` wave BOARDED one of them and re-read the other two.
  **`1RB1LB_1LC0RD_0LB1LA_0LA1RA` is settled** (a two-block bouncer, hand
  board off `WTape.cycR`/`cycL`/`cycLW`), and the standing lesson is that
  **"no value family" and "not a counter" are statements about the READER**:
  `LADDER_NOFAM.md`'s own fingerprint for that row is `1 1 1 1 2 2 2 2 3 3 3 3`
  strings per width — LINEAR, which is a bouncer's signature — and a linear
  shape-count routes a row to the WAVE track, whose hand boards want no
  grammar at all.  Of the other two:
  - `1RB1RC_1LA0LB_1LD0RD_1LB0RC` is a **base-3 wall counter** and its anchor
    is located (`tools/counters/ter3_probe.py`): 2-cell digits over
    `{00,10,11}` LSB-first with a truncated top, 75,006 consecutive anchor
    visits and zero failures, lap AFFINE in the carry length at `6c+4` /
    `6c+6`.  That alphabet is `Counters/Ter3WallB.v`'s digit for digit and
    the branches are `TernCounter`'s `tsucc`/`tsuccT`; the only new piece is
    the closer, since this row's theorem is `NeverQuasiHaltsSt`.  **Cheapest
    unbuilt row in the residue.**
  - `1RB0RB_1LC0RC_1RA0LD_0LB0LC` is a unary counter whose left wall moves
    exactly 3 cells per bounce (sixty consecutive events, no exception) with
    the right end frozen at cell 13 — `LADDER_NOFAM.md`'s
    `E(p) = 0^(24p+96) [head] φ (101)^p 0011111` re-indexed by the bounce.
* **`1RB0RB_0LC1RD_1LC1LA_0LA1RB` needs one reusable kernel piece.**  Its
  once-per-increment anchor IS located — `StB`, head `S0`, counter on the
  LEFT with one cell dropped, read at `F(1,1)`, DECREASING by one for 987
  consecutive visits (987 = `F(16)`, one whole epoch).  The index is not
  monotone across epochs, so it wants `LapGlueIx`'s arbitrary index over a
  fibonacci numeral type — and **`LapGlueIx` exports only the quasihalter
  closer** (`glue_qh_quiet_ix`), while this row's four states all recur.  So
  it needs a never-QH twin: a ~25-line copy of `LapGlue.glue_neverqh` with
  `I`/`nxt` for `positive`/`Pos.succ` and no `AvoidRun`.  Write that first —
  it is reusable and it is the only piece that is not this row's own
  arithmetic.  Cheap thing to try before any of it: the epoch length obeys
  `lap(w) = lap(w-1) + lap(w-2) + 3` EXACTLY to `w = 13`, so the epoch
  contains two smaller epochs; the sub-epoch is NOT at
  `(StA, (L, S0, rep [S1] k ++ R))` (zero occurrences at `w = 6, 7, 8`), so
  the copy sits at some other, probably mirrored, shape.
* **Validate every unit rule against its WHOLE unknown context in the oracle
  before writing Coq.**  Run each candidate over all instantiations of its
  unknown left and right context (every word up to length 6); the ones that
  come back context-independent become `cycR`/`cycL`/`cycLW` premises and the
  ones that do not become one-sided `wsteps_frame_l`/`_r` joints.  **That
  split IS the proof structure** — minutes in Python, hours if guessed in
  Coq.  Corollary: a `csteps` lemma over a symbolic left list reduces by
  `reflexivity` only while the head stays right of its start, because
  `ctape_move DL` blocks on a variable `l`.
* **A quadratic lap is not a blocker for a hand board.**  `LapGlue`'s lap
  premise existentially quantifies the step count; only the LADDER needs its
  arms affine.  4p's constant second difference and 4t's "the carry ripple is
  not affine in the run length" on `1RB1LA_0LA0LC_1LC1RD_0RB0RD` were both
  measuring the tool, and that row boarded with a `j^2 + 5j + 8` lap.

**Facts worth not rediscovering.**

* Coq is not in the image — `apt-get install -y coq` gives 8.18.0, which is
  what CI expects.  It takes about a minute.
* **`make closeout` only needs `theories/Closeout/Closeout.vo`, whose
  dependency closure does NOT include the nine `IRules_Batch`** (`coqdep`
  says so; ask it, not the plan file).  **Timed in §4t at ~2h20m on 4 cores at
  `-j3` from cold, ~2350 `.vo`; §4v measured ~2h05m at `-j3` on the same
  shape.**  `.vo` are gitignored, so a fresh container pays it and a branch
  reset does not — start it EARLY in the background and read while it runs.
  A ladder board itself compiles in seconds once `LadderCheck.vo` exists.
* **`tools/closeout/audit.py` is the live scoreboard and needs no Coq.**
  `inventory.py` → `gen_stages.py` → `audit.py` moves the numbers in seconds;
  the `Closeout.vo` build is what turns the audit's number into the kernel's.
  Say which one you have.  **`make closeout` gives you BOTH** and is a
  ~5-minute target on a warm tree; `make closeout-status` is the seconds one.
* **A new board must be added to `_CoqProject` by hand.**  `gen_stages.py`
  rewrites only the Closeout section; `check_coqproject.py` (CI) fails on any
  `.v` under `theories/` that is neither listed nor in
  `tools/coqproject_exempt.txt`.  If the row had a PARTIAL board on the exempt
  list, delete that line in the same commit — CI fails on a file that is in
  both.
* **A `cconf` carries no trailing blanks** (`lpad_eqb`), so a family all of
  whose digit words end in a blank with no terminator behind them spells one
  cell more than its own boot at EVERY width and no boot check can pass.
  §4s made that a term in `find_families`' sort key.  If an emitter refuses a
  boot with `boot cells ... are not the family at ...`, look for the rotated
  anchor in the same output before touching `fam_cells`.
* **Anything that touches the champion's score stays in HORNER form.**
  32,779,478 as a decimal literal is left as `Nat.of_num_uint` (opaque to
  `lia`), and forcing it under `vm_compute` builds 32.8M constructors.
  `CloseoutKit.covers_iqh_champ_at`'s gate is the proposition `B <= B_champ`
  under `lia` for exactly this reason — do not "simplify" it to a `<=?`.
* **Editing a file under `theories/Checkers/` under a running `make` makes
  every already-built board fail** with `inconsistent assumptions over
  library BBB4.Checkers.LadderCheck`.  **This task edits `LadderCheck.v` and
  `LadderFam.v`, so it is the trap you will actually hit**: let the background
  `Closeout.vo` build FINISH before the first kernel edit, or accept that the
  whole ladder subtree rebuilds after it.  (Adding an UNREGISTERED `.v` under
  `theories/` is safe — `make` has no rule for it — which is how §4o, §4s and
  §4v compiled boards while a build ran.)
* **`stride = 0` needs the whole side concrete in `s_pre`** (`blk`/`blk_den`);
  the failure reads like "the carry ripple is not affine" and is an instant
  `None` at every stride.
* **`RuleSound` is an equation on `cconf` and `CTape.ctape_move` does not
  normalise.**  A blank the head materialises by stepping back over it is
  `S0 :: r` and not `r`.
* `emit_ladder.py` writes its refusal reason **into the `.v` file**, and it
  is the real exception text.  Read the file, not the driver's last line.
* Keep `board_ladder.py`'s `wanted()`/`wanted_gray()` in step with
  `closure_data`/`closure_data_gray`'s refusals.  **Neither knows about the
  Fib path** — §4r, §4s and §4v all drove `emit_ladder.py` on a cert JSON by
  hand, because `wanted()` refuses `weights is not None` outright.
* **Never run `valfam.py` and a full `make -jN` at the same time.**  One row
  is fine; a sweep is not.
* CI builds `CloseoutKit.vo`, two example files and a `make all` dry run — it
  does NOT build the ladder boards or the `CB_*` stages.  Green CI is not
  evidence your board compiles.  Build it locally.  CI DOES check that every
  `.v` under `theories/` is registered or exempt.
* The arm-soundness, class and avoidance lemmas are closed under the global
  context — zero axioms — because they are on `csteps`/`cden` and never go
  through `lift`.  Keep it that way; funext enters only in the final
  assembly.

**CONSTRAINTS.**  May touch `theories/Checkers/`, `theories/Machines/`,
`tools/`, `docs/`, `NEXT_SESSION.md`.  **Never edit `theories/Census/`.**
Commit incrementally; push and open a PR when the first row moves the count.

**MERGE DISCIPLINE.**  These files are ALL GENERATED and must never be
hand-resolved on a conflict:

    theories/Closeout/CB_*.v, SH_*.v, Closeout.v, CoreRows.v, CloseoutFinal.v,
    BBB4_Theorem.v, the Closeout section of _CoqProject,
    tools/closeout/{core_rows.txt,frozen_map.tsv,frozen_unproven.txt,
                    shadow_rows.tsv}

Resolving one by hand silently reverts whichever side's boards you did not
notice.  Instead: `git checkout --theirs` to get a tree, then re-derive —

    python3 tools/closeout/inventory.py
    python3 tools/closeout/gen_shadow.py --harvest   # boards any freed shadow
    python3 tools/closeout/inventory.py              # ...and picks it up
    python3 tools/closeout/gen_stages.py
    python3 tools/closeout/audit.py     # must print CLOSEOUT AUDIT: OK

`make closeout` runs exactly that sequence.  Driving it by hand and skipping
the `--harvest` line is the one way a freed shadow still ends up sitting in
`core_rows.txt`; `audit.py` prints it if it does.  §4u is the first wave where
the harvest pass actually fired — the row it boarded carried a mirror shadow —
and it also records the count arithmetic that surprises: boarding a partner
promotes its shadow INTO `core_rows.txt`, so core went 27 -> 27 -> 26 across
the two steps, not 27 -> 26 -> 25.

The board `.v` files are the source of truth and never conflict, because they
are different files.
