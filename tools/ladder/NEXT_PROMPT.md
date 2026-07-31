BUILD THE RE-ROOT CLOSER.  Twelve `0RB` shadows sit on ten core rows, the
general half of the argument is already merged (#98), and one worked example
is on disk.  Each shadow is a row the closeout still lists and nobody has to
find a family for.  In `carrino/Coq-BBB4`, on branch
`claude/reroot-<yourid>` cut from `main`.

**Diff `origin/main` first**: `git show origin/main:tools/closeout/core_rows.txt`
is one command, and the wave route has now taken rows out from under four
sessions.  §4l, §4n and §4o each say this and each said it after paying.

Read first, in this order: `docs/LADDER_PLAN.md` **§4o in full** — what the
last session built and, more to the point, its closing finding that boarding a
core row does NOT settle its shadow; then `tools/closeout/shadow_rows.tsv`
(column 4 is the partner and column 5 the re-rooting); then the merged general
half of the re-root argument and the one worked example on main
(`RRNQ_0RB0RD_1RC____1RD1LC_0LC1RA`, from #95/#98); then
`tools/closeout/gen_shadow.py`, which is the generator that has to learn to
emit the rest.

**STATE.**  **37** core undecided and **12** `0RB` shadows
(`tools/closeout/core_rows.txt`, `tools/closeout/shadow_rows.tsv`;
`make closeout-status`).  **5,107** frozen rows settled by a board, 99.0%.
**49** rows remain.

**THE TASK.**  §4o boarded four `(Gray, 2)` core rows and two of them carried
a shadow — and the shadows did not go away, they became core rows.  That is
the bookkeeping fact worth acting on: **a shadow is worth a row only if
someone builds its re-root, and until then boarding its partner just moves it
between two buckets.**  Twelve of the forty-nine remaining rows are of that
kind, and they are the only rows in the list for which the mathematics is
already done.

* The general lemma is merged and the one worked example compiles.  What is
  missing is the GENERATOR: `gen_shadow.py` emits one `RRNQ_*` today and the
  twelve want twelve, each with its own re-rooting (column 5 of
  `shadow_rows.tsv` — `mirror`, `swap:B:C`, and combinations).
* Every re-rooting is a permutation of states and/or a mirror of the tape, so
  the obligation is an equation between two concrete tables that `vm_compute`
  decides.  **If one of them is not, STOP and write §4p with which shadow and
  why** — do not weaken the general lemma to fit it.
* `audit.py` already re-verifies every shadow re-root in the core orbit
  independently, so a wrong re-rooting is caught by the audit and not by a
  wrong theorem.  Keep it that way.

**DO ONE ROW END-TO-END FIRST.**  `0RB0LA_1LA1RC_0RD1RD_1LB0LB` — it is one of
the two §4o promoted, its partner `1RB1LC_0LA0RB_0LD1LD_1RA0RA` is boarded on
this branch's base, and the re-rooting is a plain `mirror`.  Drive it to
`NeverQuasiHaltsSt tm_*`, run `make closeout`, and confirm "settled by a
board" moves.  **A board that does not move a number is not a board.**

**WHAT NOT TO DO.**  Do not build another `ClassSucc` instance — `(Gray, 2)`
is done (§4o) and the next `(code, step)` pair is worth less than twelve rows.
Do not do the outer parameter (§4j).  Do not touch the count language or `RU`.
**Never edit `theories/Census/`.**

**The two gray rows that are still open are a FAMILY question and are cheap.**
`1RB0RD_1LC0LB_1LD0LB_1RD0RA` and `1RB0RD_1LC0LC_1LD0LB_1RD0RA` have two-cell
digit words ending in `0`, so `fam_cells` spells one cell more than the
machine's `cconf` carries at the anchor.  The gray emitter now REFUSES them at
the boot check with exactly that reason in the `.v` file, and
`gray2check.py` confirms their class law is fine.  Either re-read them at an
anchor whose digit words do not end in a blank, or give `fam_cells` a trimming
the denotation can state.  Two rows, and no kernel lemma is involved.

**Facts worth not rediscovering.**

* Coq is not in the image — `apt-get install -y coq` gives 8.18.0, which is
  what CI expects.  It takes about a minute.
* **`make closeout` only needs `theories/Closeout/Closeout.vo`, whose
  dependency closure is ~2,094 files and does NOT include the nine
  `IRules_Batch`** (`coqdep` says so; ask it, not the plan file).  Measured on
  4 cores at `-j3` from cold: about **4 files a minute**, so a cold closure is
  hours and not the 45 minutes §4n estimated.  `.vo` are gitignored, so a
  fresh container pays it and a branch reset does not — start it EARLY and in
  the background, and do the reading while it runs.
* **`tools/closeout/audit.py` is the live scoreboard and needs no Coq at
  all.**  `inventory.py` → `gen_stages.py` → `audit.py` moves the numbers in
  seconds; the `Closeout.vo` build is what turns the audit's number into the
  kernel's.  Report which one you have.
* **Editing a file under `theories/Checkers/` under a running `make` makes
  every already-built board fail** with `inconsistent assumptions over library
  BBB4.Checkers.LadderCheck`.  Same trap as rewriting `_CoqProject`
  mid-build.  Finish the edit, then build.
* **`RuleSound` is an equation on `cconf` and `CTape.ctape_move` does not
  normalise.**  A blank the head materialises by stepping back over it is
  `S0 :: r` and not `r`; `valfam`'s `other_side_cells` drops exactly those
  cells — the same TAPE under `lift` (so the boot premise does not notice) and
  a different `cconf` (so every arm does).  The gray path in `emit_ladder.py`
  reads the far side off the BOOT for this reason and then writes the `Fam`
  record from what the arm search chose.
* **The top of a width is the largest MEMBER.**  At `(Gray, 2)` it is
  `[1-p] ++ 0^(k-2) ++ [1]` with value `2^k - 2 + p`, and at even parity that
  is NOT the string `of_value` computes for `b^k - 1`.
* `emit_ladder.py` writes its refusal reason **into the `.v` file**, and it is
  the real exception text.  Read the file, not the driver's last line.
* Keep `board_ladder.py`'s `wanted()`/`wanted_gray()` in step with
  `closure_data`/`closure_data_gray`'s refusals.
* **Never run `valfam.py` and a full `make -jN` at the same time.**  One row
  is fine; a sweep is not.
* CI builds `CloseoutKit.vo`, two example files and a `make all` dry run — it
  does NOT build the ladder boards or the `CB_*` stages.  Green CI is not
  evidence your board compiles.  Build it locally.
* The arm-soundness, class and avoidance lemmas are Closed under the global
  context — zero axioms — because they are on `csteps`/`cden` and never go
  through `lift`.  `board_arm`, `board_armG`, `gray_split`,
  `gray2_class_succ`, `blk_den`, `arm_index` and `tops_cofinal_at` are too.
  Keep it that way; funext enters only in the final assembly.
* The time-cap bucket is three rows, not four.  All four re-run at
  `--cap 900`: the three `1RB---` rows still cap with 26 families found and
  four tried, so raising the budget is not the lever — the question is which
  families the searcher spends it ON.  `1RB1RC_1LA1RA_0RC1LD_1LB0LD` finishes
  in 723 s on `interior-not-covered` with 5 of 12 families tried: it is a
  coverage row that was wearing the budget's label.

**CONSTRAINTS.**  May touch `theories/Checkers/`, `theories/Machines/`,
`tools/`, `docs/`, `NEXT_SESSION.md`.  **Never edit `theories/Census/`.**
Commit incrementally; push and open a PR when the first row moves the count.

**MERGE DISCIPLINE.**  These files are ALL GENERATED and must never be
hand-resolved on a conflict:

    theories/Closeout/CB_*.v, Closeout.v, CoreRows.v, CloseoutFinal.v,
    BBB4_Theorem.v, the Closeout section of _CoqProject,
    tools/closeout/{core_rows.txt,frozen_map.tsv,frozen_unproven.txt,
                    shadow_rows.tsv}

Resolving one by hand silently reverts whichever side's boards you did not
notice.  Instead: `git checkout --theirs` to get a tree, then re-derive —

    python3 tools/closeout/inventory.py
    python3 tools/closeout/gen_stages.py
    python3 tools/closeout/audit.py     # must print CLOSEOUT AUDIT: OK

The board `.v` files are the source of truth and never conflict, because they
are different files.
