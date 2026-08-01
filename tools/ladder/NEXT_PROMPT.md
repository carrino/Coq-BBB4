BUILD THE ZECKENDORF-COMPLEMENT NUMERATION.  Six core rows, the numeration is
MEASURED and script-checked against the machines, the split fits the EXISTING
`Class` record, and the build is specified to the lemma.  In
`carrino/Coq-BBB4`, on branch `claude/zeckendorf-<yourid>` cut from `main`.

**Diff `origin/main` first**: `git show origin/main:tools/closeout/core_rows.txt`
is one command, and the wave route has now taken rows out from under six
sessions.  §4l, §4n, §4o, §4p and §4r each say this; §4o said it and then had
its OWN next-session prompt invalidated eight hours later by §4p.  **Re-read
the plan's last section before acting on a prompt, because the prompt is older
than the plan.**  This one was written at the end of §4s.

Read first, in this order: `docs/LADDER_PLAN.md` **§4s in full** — it is the
measurement that selected this task; then **§4r in full**, the `(Fib, 1)`
build you would be copying; then `theories/Checkers/LadderCheck.v` §3c, §5c
and §11, which are the three pieces a numeration costs.

**STATE.**  **27** core undecided and **12** `0RB` shadows
(`tools/closeout/core_rows.txt`, `tools/closeout/shadow_rows.tsv`;
`make closeout-status`).  **5,117** frozen rows settled by a board, 99.2%.
**39** rows remain.

**THE TASK: BUILD THE ZECKENDORF-COMPLEMENT INSTANCE.**

The six rows are

    1RB---_0LC1RD_1LB1RC_1LB0RD      1RB---_1LC0RB_0LD1RB_1LC1RD
    1RB---_0LC1RD_1LB1RD_1LB0RD      1RB---_1LC1RB_0LB1RD_1LC0RD
    1RB---_1LC0RB_0LD1RB_1LC1RB      1RB---_1LC1RD_0LB1RD_1LC0RD

and `python3 valfam.py --spec <row> --numeration --cap 400` reads every one of
them as a Fibonacci counter at an anchor chain of 232–376.  **The
`--numeration` flag is required and it is new** (§4s): without it
`find_families` returns 26-odd junk positional families at chain 8 and its
`if not found` gate switches the numeration pass off entirely, which is why
these rows had never been read at all.

Where they stop: the weights come back `1, 2, 3, 5, 8, 13` — **Zeckendorf**,
not the `1, 1, 2, 3, 5, 8` that `LadderCheck` §11 states — so
`closure_data_fib` refuses on the weights.  Under the shifted reading the
INTERIOR covers cleanly and the failure is `overflow leaves the family`, with
the uncovered set

    (k=2, v=3), (k=3, v=6), (k=4, v=11), (k=5, v=19), (k=6, v=32), (k=7, v=53)

which is `sum(weights[:k])` at each width — the string `1^k`, the top of the
width.  With one repair round the wrong successors are a `1` followed by
zeros at values 5, 8, 13, 21, the weights themselves.  **The whole residue of
these six is the FILL arm.**

**THE SPEC IS WRITTEN AND CHECKED.  `python3 tools/ladder/zeckmem.py` prints
`ZECKMEM: OK`, and `--rows` re-reads the blocks off the six machines.**  §4s's
addendum states all four facts; the oracle enumerates every one of them
against the orbit, in the `fibmem.py` / `gray2check.py` tradition.  **Do not
state a lemma `zeckmem.py` has not checked** — it already caught one
off-by-one in the fill's parity that would have cost hours in Coq.

* **`Class` does NOT widen.**  Both interior classes fit the existing
  `(u, t, w, u', t', w')` record: the increment is `[0] ++ rest -> [1] ++
  rest`, and the carry is `u=[1], t=[1;1], w=[0] -> u'=[0;1], t'=[0;1],
  w'=[]` at run length `m`, both firing at offset 0 or 1.  Over widths 1..10:
  88 increments, 133 carries, 10 widenings, **0 unexplained**.  §4i's gate
  has now held through a fourth code — check that before budgeting.
* **The round trip should be EASIER than §4r's**, which is where §4r put all
  its risk.  This numeration is not redundant (no `w0 = w1`), so
  `fam_of_value` ought to invert outright rather than only on members.
* **The fill is where the work is**, and it is the one new shape: `1^k` goes
  to the ALTERNATING string of width `k+1` whose low digit is `(k+1) mod 2`.
  `(Fib, 1)`'s fill target was a bare run of `0`; `(01)^m` is a run of a
  two-cell BLOCK, which `Fill`'s prefix/`digit^n`/suffix cannot spell.
  The obvious dodge — re-read at digit width 2, where `(01)^m` is a bare run
  of ONE digit and `Fill` needs nothing — is **MEASURED DEAD**: `_weights_pass`
  at `lens=[2]`, `[3]`, `[4]` returns **zero** weighted families on these rows
  (42 at `lens=[1]`), so the counter does not decode at any wider digit.  Do
  not retry it; `Fill` is where the widening has to go.  The parity itself is
  not new — §4o made exactly that a parameter for `(Gray, 2)`.
* **DO NOT go looking for the `1,1,2,3,5` reading.**  §4s checked: `fibokb`
  and this membership are not the same language under identity, reversal,
  complement, or reversal-and-complement (`zeckmem.py --compare` prints the
  table).  `fibokb` restricts runs of `1`s, this restricts runs of `0`s.
  `FIB_ELEVEN.txt` reading these rows at `F(1,1)` is not a contradiction: a
  consecutive-VALUE test passes under either ladder, because pinning
  `(Fib, 1)`'s low digit to `0` gives exactly these weights.  What separates
  them is which representative of a value the machine WRITES — which is what
  a `ClassSucc` needs and a value test never sees.  And `fit_weights` solves
  the weights exactly from the enumeration order, so there is no freedom in
  the reading to go hunting for.
* **Before anything else, if a weighted family fails only at the overflow:
  check the class against the WALK.**  `all_strings`' docstring warns that
  enumerating `b^k` would demand members the machine never reaches.  §4s
  ruled that out here — at widths 1..8 the class is 1, 2, 3, 5, 8, 13, 21, 34
  strings and the machine visits exactly those, zero ghosts — which is what
  made the fill a real target rather than a reading error.

**WHAT NOT TO DO.**

* **Do not re-probe the four base-2 quadratic rows** (`1RB0LD_0LC0RB_...` and
  the three `1RB1LA` rows).  §4p measured a second difference of exactly 2 on
  the arm itself and `QUAD_TERMINAL_MEASUREMENT.md` corroborates it
  independently.  No widening of `ARM_GRID` reaches a quadratic.
* **Do not count `1RB0RB_0LC1RD_1LC1LA_0LA1RB` with the six.**  It has been
  filed with them since `docs/CORE_3STATE.md` §3 read it as a φ row by radix
  sweep, and §4s measured that it finds **no family at any anchor** —
  `digit_words(rules)` names nothing.  It is a `no anchor` row.
* Do not do the outer parameter (§4j).  **Never edit `theories/Census/`.**

**Also open and cheap.**  Nick's list included three rows the ladder does not
read at all — `1RB0RB_1LC0RC_1RA0LD_0LB0LC`, `1RB1LB_1LC0RD_0LB1LA_0LA1RA`,
`1RB1RC_1LA0LB_1LD0RD_1LB0RC` — all three now measured as `no value family`
under `--numeration` too, so they want `alphabet_infer.py` or a non-ladder
route (ReachSt), not a numeration.

**Facts worth not rediscovering.**

* Coq is not in the image — `apt-get install -y coq` gives 8.18.0, which is
  what CI expects.  It takes about a minute.
* **`make closeout` only needs `theories/Closeout/Closeout.vo`, whose
  dependency closure does NOT include the nine `IRules_Batch`** (`coqdep`
  says so; ask it, not the plan file).  Measured on 4 cores at `-j2` from
  cold: roughly **4–10 files a minute**, so the closure is HOURS.  `.vo` are
  gitignored, so a fresh container pays it and a branch reset does not —
  start it EARLY in the background and read while it runs.
* **`tools/closeout/audit.py` is the live scoreboard and needs no Coq.**
  `inventory.py` → `gen_stages.py` → `audit.py` moves the numbers in seconds;
  the `Closeout.vo` build is what turns the audit's number into the kernel's.
  Say which one you have.
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
  library BBB4.Checkers.LadderCheck`.  Same trap as rewriting `_CoqProject`
  mid-build.  Finish the edit, then build.  (Adding an UNREGISTERED `.v`
  under `theories/` is safe — `make` has no rule for it — which is how §4o
  and §4s compiled boards while a build ran.)
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
  Fib path** — §4r and §4s both drove `emit_ladder.py` on a cert JSON by
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
`core_rows.txt`; `audit.py` prints it if it does.

The board `.v` files are the source of truth and never conflict, because they
are different files.
