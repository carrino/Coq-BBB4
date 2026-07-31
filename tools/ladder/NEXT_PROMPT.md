BUILD THE INTERIOR ARM'S OFFSET.  Four core rows stop on ONE refusal, the
widening is specified to the lemma in §4i, and three of the four carry five
`0RB` shadows between them — so it is **nine rows**, the largest single
bucket left.  In `carrino/Coq-BBB4`, on branch `claude/interior-offset-<yourid>`
cut from `main`.

**Diff `origin/main` first**: `git show origin/main:tools/closeout/core_rows.txt`
is one command, and the wave route has now taken rows out from under four
sessions.  §4l, §4n and §4o each say this and each said it after paying.

Read first, in this order: `docs/LADDER_PLAN.md` **§4i's "The live core,
swept"** — it names these four rows and specifies the fix in one sentence;
then **§4o in full**, which is the last session and whose closing findings are
about the SHADOWS and not about gray; then
`theories/Checkers/LadderCheck.v` §2b (`astride`/`aoff`/`acnt`/`arm_index`,
`blk`, `blk_den`) and `Section Cells` (`cls_side`, `run_side`) — where the
edit goes; then `tools/ladder/emit_ladder.py`'s `closure_data`, whose
`interior_at` is what has to learn the offset.

**STATE.**  **35** core undecided and **12** `0RB` shadows
(`tools/closeout/core_rows.txt`, `tools/closeout/shadow_rows.tsv`;
`make closeout-status`).  **5,109** frozen rows settled by a board, 99.1%.
**47** rows remain.

**THE TASK.**  These four core rows have a partial board already on disk and
tracked (`theories/Machines/Ladder/LDR_*.v`, not registered in `_CoqProject`,
carrying every arm the certificate has and no closure).  All four record the
SAME refusal in the `.v` file:

    interior arm: no chain at any threshold 0..3 and stride 1..4 --
    the carry ripple is not affine in the run length

    1RB0LD_0LC0RB_1LA1RC_0RC1LD   0 shadows
    1RB1LA_0LA0LC_1LC1RD_0RB0RD   2 shadows
    1RB1LA_0LA1RC_0LD0RC_1LD0RB   1 shadow
    1RB1LA_1LC0RD_0RA0LC_0LA1RD   2 shadows

and §4i already measured why and what the fix is, in its own words:

> at `s = 2` the odd residue derives (`4m+4`, as predicted) and the even one
> does not, because its arm needs a guaranteed block copy materialised into
> `s_pre` the way the fill arm's does, and then `m = 0` is no longer covered
> by it.  **So the next widening is known and small: the interior arm needs
> the same `[m1]` offset the fill arm already has, plus a separate arm for
> the residue's own `m = 0`.**

So: give `cls_side` the offset `run_side` has (it already gained the fixed
word `u` in §4o — this is the other half, the guaranteed copies materialised
about the block), and give the arm scheme a flat arm at the residue's own
`m = 0`.  `fam_cells_class` takes the matching change, exactly as it did in
§4o.

**MEASURE BEFORE YOU BUILD.**  `tools/ladder/fillcost.py` and
`core61_armshapes.txt` are the existing readings; walk the run from `t^n ++ d`
to `0^n ++ (d+1)` for `n = 1..10` on all four rows and check the cost is
`4m + c` per residue with a materialisation offset, and NOT quadratic.  §4i
measured two of the live core as genuinely `(n+1)(n+2)` — no stride and no
offset makes that affine, and those want `RU` or a count language, which is
`RULE_LADDER` 5's table row and NOT this task.  **If one of the four turns out
quadratic, STOP and write §4p with which row and the measured costs.**

**DO ONE ROW END-TO-END FIRST.**  `1RB1LA_1LC0RD_0RA0LC_0LA1RD` — it carries
two shadows, so it is worth three rows on its own.  Drive it to
`NeverQuasiHaltsSt tm_*`, run `make closeout`, and confirm "settled by a
board" moves.  **A board that does not move a number is not a board.**

**THEN COLLECT THE SHADOWS, AND MIND THE TRAP §4o FOUND.**
`tools/closeout/gen_shadow.py` already exists and does the whole job
(`--all`, `--check`, `--regress`); you do not have to write a generator.  But:

* **`shadowlib.classify` drops a shadow from `shadow_rows.tsv` the moment its
  partner leaves the unproven set** — which is exactly when the shadow becomes
  actionable.  So `gen_shadow.py --all`, whose input is that file, cannot see
  the rows you just freed.  Board the core row, then drive each freed shadow
  with the EXPLICIT form and read its `qstar`/`prefix`/`partner`/`ops` out of
  the previous revision of the table:

      git show HEAD~1:tools/closeout/shadow_rows.tsv
      python3 tools/closeout/gen_shadow.py --spec SHADOW --partner CORE \
              --qs B --t 1 --ops mirror --out theories/Machines/Counters --check

  §4o boarded `0RB0LA_1LA1RC_0RD1RD_1LB0LB` and
  `0RB0LA_1RC1LA_1RD0RD_1LB0LB` exactly this way.  **Fixing `classify` so the
  freed rows survive one generation is a real improvement and worth doing
  first** — but it is a change to a file another wave owns, so check
  `origin/main` before editing it.
* The generator now reads the partner's PACKAGE off `frozen_map.tsv` rather
  than hard-coding `BBB4.Machines.Counters` (§4o: ladder boards live under
  `BBB4.Machines.Ladder`, and a shadow off one imported the wrong module).
* SCOPE: never-quasihalting core rows only.  A core row boarded as `iqh`
  transports through `Reroot.qhbound_reroot`, which shifts the bound by the
  prefix length and carries a `B + t <= B_board` side condition — the
  generator refuses it rather than guessing, and that refusal is correct.

**WHAT NOT TO DO.**  Do not build another `ClassSucc` instance — `(Gray, 2)`
is done (§4o) and the next `(code, step)` pair is worth less than these nine
rows.  Do not do the outer parameter (§4j).  Do not touch the count language
or `RU`.  **Never edit `theories/Census/`.**

**Still open, and cheap, if you finish early.**  The two gray rows §4n and
§4o left alone — `1RB0RD_1LC0LB_1LD0LB_1RD0RA` and
`1RB0RD_1LC0LC_1LD0LB_1RD0RA` — have two-cell digit words ending in `0`, so
`fam_cells` spells one cell more than the machine's `cconf` carries at the
anchor.  The gray emitter REFUSES them at the boot check with exactly that
reason in the `.v` file, and `tools/ladder/gray2check.py` confirms their class
law is fine.  Either re-read them at an anchor whose digit words do not end in
a blank, or give `fam_cells` a trimming the denotation can state.  Two rows,
and no kernel lemma is involved.

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
