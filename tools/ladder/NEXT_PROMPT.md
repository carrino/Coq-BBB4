BUILD THE FIBONACCI NUMERATION.  Five core rows, the arms are MEASURED to
derive, the numeration is MEASURED and checked against the machines, and the
build is specified to the lemma.  In `carrino/Coq-BBB4`, on branch
`claude/fib-numeration-<yourid>` cut from `main`.

**Diff `origin/main` first**: `git show origin/main:tools/closeout/core_rows.txt`
is one command, and the wave route has now taken rows out from under five
sessions.  §4l, §4n, §4o and §4p each say this; §4o said it and then had its
OWN next-session prompt invalidated eight hours later by §4p, which is the
sharper lesson: **re-read the plan's last section before acting on a prompt,
because the prompt is older than the plan.**

Read first, in this order: `docs/LADDER_PLAN.md` **§4p in full** — it is the
measurement that selected this task, and its last third ("The numeration,
CRACKED") is the specification you are implementing; then **§4o in full**,
which is the same build one numeration over and is the template you are
copying; then `tools/ladder/fibmem.py` (`FIBMEM: OK`), the oracle that already
checks every line of the spec against the orbit read off the machines; then
`theories/Checkers/LadderCheck.v` §3b, §5b and §10 — the `(Gray, 2)` instance,
which is the shape of every file you are about to add.

**STATE.**  **35** core undecided and **12** `0RB` shadows
(`tools/closeout/core_rows.txt`, `tools/closeout/shadow_rows.tsv`;
`make closeout-status`).  **5,109** frozen rows settled by a board, 99.1%.
**47** rows remain.

**THE TASK.**  §4p measured the five fibonacci rows and found the ARM RISK IS
ZERO: all five fit the same two classes, both arms derive at threshold 0..1
and **stride 1**, and the costs are affine (first differences a constant 2 and
a constant 0).  What blocks them is the NUMERATION and nothing else — `Fam`
has no weight field, `fam_value` is `val_pos`, and the five boards on disk
declare `Binary 1`, which is not what their machines do.  §4p then cracked the
numeration and checked all four facts:

* **Membership.**  LSB-first: an optional leading `1`, then a concatenation of
  the blocks `[0]` and `[1;1]`.  Counts come out 2, 3, 5, 8, 13, 21, 34, 55,
  89, 144 and agree with the orbit at every width 0..11.
* **The top of a width is `1^k`** — simpler than `(Gray, 2)`'s
  `[1] ++ 0^(k-2) ++ [1]`, and no `of_value` is needed to compute it.
* **The split is TWO-WAY and splits on the LOW DIGIT** — a `destruct`, where
  §4o had to do four-way:

      low digit 0    [0] ++ 0^n ++ rest    ->   [1] ++ 0^n ++ rest
      low digit 1    1^n ++ [1;0] ++ rest  ->   0^n ++ [1;1] ++ rest

  Measured over all 2,284 interior members of the five rows: overlap 0,
  uncovered 0, wrong successor 0.
* **Each rewrite adds exactly 1 to the value**, so the successor never has to
  be inverted pointwise.

So the build is: a `Fib` constructor on `Code` (every existing section is
gated by `Hypothesis Hcode : fm_code F = Binary` / `= Gray` and stays inert),
`fam_value` at `Fib` as the weighted fold, the membership predicate as
`ClassSucc`'s `P`, and the round-trip
`fam_of_value F (fam_value F ds) (length ds) = Some ds` over it.

**THE ONE PLACE THE RISK IS.**  The numeration is **REDUNDANT** — `w0 = w1 = 1`,
so `10000` and `01000` are both value 1 — and the membership rule is which
representative the machine picks.  So the round-trip lemma is NOT free the way
`(Gray, 2)`'s `gray_inj` was (there, one value and one width determined one
string outright).  Here it holds only ON MEMBERS, and the proof has to use the
membership predicate.  **Do that lemma first**: if it will not go through,
STOP and write §4q with the counterexample, because everything else rests on
it.

**THE CLOSER IS THE QUASIHALTING ONE, NOT `boardG_neverqh`.**  These five are
`live = BCD`: `A` is entered once, at step 0, and nothing targets it.  So they
QUASIHALT in `A` and want `LadderCheck` §8's shape (`boardph_iqh`) — every arm
additionally `RuleAvoid`, a visit chain per state other than the quiet one,
and the quiet state's last visit with the window to the anchor.  §4o's
`Section BoardG` is never-QH only and does NOT serve them; budget for the iqh
twin.  `sq = 0` here, which makes the window obligations small.

**RE-ROOT DOES NOT SERVE THESE FIVE** and §4p says why: `Census/Reroot.v`'s
precondition is a prefix writing only `S0` so the tape stays all-blank, and
these rows write a `1` on step 0 — the very event re-root stops at.  Do not
try it.

**STATE THE LEMMAS AGAINST THE ORACLE BEFORE PROVING THEM.**  `fibmem.py`
already checks the membership predicate, the top, the split and the successor
against the orbit.  §4o's `gray2check.py` is the same discipline and it caught
a wrong case split in seconds that would have cost hours in Coq.  Extend
`fibmem.py` to whatever you state; do not state anything it has not checked.

**DO ONE ROW END-TO-END FIRST**, drive it to its `iqh` triple, run
`make closeout`, and confirm "settled by a board" moves.  **A board that does
not move a number is not a board.**

**WHAT NOT TO DO.**

* **Do not re-probe the four base-2 quadratic rows.**  §4p measured their
  interior arm at `(r+1)(r+2)` and `r^2 + 5r + 12` — second difference exactly
  2 in every case — and `QUAD_TERMINAL_MEASUREMENT.md` corroborates it by an
  independent route on the terminal.  A strided arm is one chain repeated, so
  its cost is affine along the stride; no widening of `ARM_GRID` reaches a
  quadratic.  They are done as ladder rows.  **§4o's prompt pointed at exactly
  these four and was wrong** — it read §4i's "the next widening is known and
  small" as still live, and §4p had measured it dead.
* Do not build another `ClassSucc` instance for a code that has no rows.
* Do not do the outer parameter (§4j).  **Never edit `theories/Census/`.**

**Still open, and cheap, if you finish early.**  The two gray rows §4n and
§4o left alone — `1RB0RD_1LC0LB_1LD0LB_1RD0RA` and
`1RB0RD_1LC0LC_1LD0LB_1RD0RA` — have two-cell digit words ending in `0`, so
`fam_cells` spells one cell more than the machine's `cconf` carries at the
anchor.  The gray emitter REFUSES them at the boot check with exactly that
reason in the `.v` file, and `tools/ladder/gray2check.py` confirms their class
law is fine.  Either re-read them at an anchor whose digit words do not end in
a blank, or give `fam_cells` a trimming the denotation can state.  Two rows,
and no kernel lemma is involved.

**THE SHADOWS ARE NOT READY WORK, AND HERE IS WHY.**  Twelve `0RB` shadows sit
on ten core rows.  A shadow satisfies the `skipped` disjunct only while its
core row is DEFERRED; it needs a board of its own exactly when its core row
boards, and not before.  **Five of the twelve sit on three of the four
QUADRATIC rows** (§4p), so they are not coming back either.  Two things §4o
paid for, when you do free one:

* **`shadowlib.classify` drops a shadow from `shadow_rows.tsv` the moment its
  partner leaves the unproven set** — which is exactly when it becomes
  actionable.  So `gen_shadow.py --all`, whose input is that file, cannot see
  the row you just freed.  Drive it with the explicit form and read its
  `qstar`/`prefix`/`partner`/`ops` out of the previous revision of the table:

      git show HEAD~1:tools/closeout/shadow_rows.tsv
      python3 tools/closeout/gen_shadow.py --spec SHADOW --partner CORE \
              --qs B --t 1 --ops mirror --out theories/Machines/Counters --check

  §4o boarded `0RB0LA_1LA1RC_0RD1RD_1LB0LB` and
  `0RB0LA_1RC1LA_1RD0RD_1LB0LB` exactly this way.  Fixing `classify` so a
  freed row survives one generation is a real improvement and worth doing.
* The generator reads the partner's PACKAGE off `frozen_map.tsv` rather than
  hard-coding `BBB4.Machines.Counters` (§4o: ladder boards live under
  `BBB4.Machines.Ladder`).  `gen_shadow.py --regress` is `OK, 4 of 4` on a
  built tree and `INCONCLUSIVE` on an unbuilt one (§4p) — build the fixture
  first or it tells you nothing.

**Facts worth not rediscovering.**

* Coq is not in the image — `apt-get install -y coq` gives 8.18.0, which is
  what CI expects.  It takes about a minute.
* **`make closeout` only needs `theories/Closeout/Closeout.vo`, whose
  dependency closure does NOT include the nine `IRules_Batch`** (`coqdep` says
  so; ask it, not the plan file).  Measured on 4 cores at `-j3` from cold:
  roughly **4–10 files a minute**, so the closure is HOURS and not the 45
  minutes §4n estimated.  `.vo` are gitignored, so a fresh container pays it
  and a branch reset does not — start it EARLY in the background and read
  while it runs.
* **`tools/closeout/audit.py` is the live scoreboard and needs no Coq.**
  `inventory.py` → `gen_stages.py` → `audit.py` moves the numbers in seconds;
  the `Closeout.vo` build is what turns the audit's number into the kernel's.
  Say which one you have.
* **Editing a file under `theories/Checkers/` under a running `make` makes
  every already-built board fail** with `inconsistent assumptions over library
  BBB4.Checkers.LadderCheck`.  Same trap as rewriting `_CoqProject`
  mid-build.  Finish the edit, then build.  (Adding an UNREGISTERED `.v` under
  `theories/` is safe — `make` has no rule for it — which is how §4o compiled
  boards while a build ran.)
* **`stride = 0` needs the whole side concrete in `s_pre`** (`blk`/`blk_den`);
  the failure reads like "the carry ripple is not affine" and is an instant
  `None` at every stride.  You are about to work next door to this — do not
  re-derive it.
* **`RuleSound` is an equation on `cconf` and `CTape.ctape_move` does not
  normalise.**  A blank the head materialises by stepping back over it is
  `S0 :: r` and not `r`; `valfam`'s `other_side_cells` drops exactly those
  cells — the same TAPE under `lift` (so the boot premise does not notice) and
  a different `cconf` (so every arm does).  The gray path reads the far side
  off the BOOT for this reason; if an interior arm lands one cell off, this is
  why.
* `emit_ladder.py` writes its refusal reason **into the `.v` file**, and it is
  the real exception text.  Read the file, not the driver's last line.
* Keep `board_ladder.py`'s `wanted()`/`wanted_gray()` in step with
  `closure_data`/`closure_data_gray`'s refusals.
* **Never run `valfam.py` and a full `make -jN` at the same time.**  One row
  is fine; a sweep is not.
* CI builds `CloseoutKit.vo`, two example files and a `make all` dry run — it
  does NOT build the ladder boards or the `CB_*` stages.  Green CI is not
  evidence your board compiles.  Build it locally.  CI DOES check that every
  `.v` under `theories/` is registered or exempt, so a board left unregistered
  fails CI even though nothing builds it.
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

    theories/Closeout/CB_*.v, SH_*.v, Closeout.v, CoreRows.v, CloseoutFinal.v,
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
