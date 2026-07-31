BUILD THE OUTER PARAMETER.  It is §4g's lesson for the SIXTH time — a
hard-coded assumption about the counter that gets reported as the machine's
failure — the field is already carried by the kernel and used nowhere, and
§4q measured the constants.  Two rows, and it is the last of the six.
In `carrino/Coq-BBB4`, on branch `claude/outer-parameter-<yourid>` cut from
`main`.

**Diff `origin/main` first**: `git show origin/main:tools/closeout/core_rows.txt`
is one command, and the wave route has taken rows out from under six sessions
now.  §4o's prompt was invalidated eight hours after it shipped, by a §4p that
had measured its task dead.  **Re-read the plan's last section before acting
on this one, because the prompt is older than the plan.**

Read first, in this order: `docs/LADDER_PLAN.md` **§4j in full** — it is the
diagnosis, and its "The fix is a shape both halves already have" is the
specification; then **§4q in full**, which re-reads the same two machines at a
better anchor and supplies the constants, and whose RETRACTION block is the
one thing in it that a careless reader will get backwards; then
`theories/Checkers/LadderFam.v` (`Fam`, `fam_cfg`, `CtrSt`) and
`theories/Checkers/LadderCheck.v` `Section Cells` (`cls_side`, `run_side`,
`cls_conf`, `cden_cls_conf`) — where the edit goes; then `valfam.py`'s
`Fam.read`, which is the other half of the same assumption.

**STATE.**  **30** core undecided and **12** `0RB` shadows
(`tools/closeout/core_rows.txt`, `tools/closeout/shadow_rows.tsv`;
`make closeout-status`).  **5,114** frozen rows settled by a board, 99.2%.
**42** rows remain.

**THE TASK.**  `0RB0RD_1LC1RB_1RA0LC_1LB0LC` and its twin `..._1LD0LC` are
ONE-PARAMETER families and nothing about them is unknown.  §4q sampled them
once per bounce, 704 bounces to step 3,000,000, zero failures, and at the
anchor that carries the constant `11` frame — `(StB, head 0, head at offset
3)` — the far side is a solid run of ones whose length is

    2v + 5   exactly, at every visit from 2 to 255

against the counter's own value `v`.  Both things that vary are functions of
the same `v`.  What blocks them is that `Fam` can name exactly one varying
thing, the digit string: `fm_other : list Sym` and `fm_pre : list Sym` are
FIXED words and neither can say "a run whose length is affine in the
parameter".

The fix is a shape both halves already have — the engine's own `sside`,
`pre ++ rep u (a*j + b) ++ post ++ X`, which §4i notes the class
decomposition already coincides with.  At §4q's anchor the instance is

    side = FAR (fm_other)     u = [S1]     a = 2     b = 5

**and the kernel field is already there.**  `fam_cfg` is
`let '(ds, _, ph) := s in ...` — that `_` is the outer parameter.  It is a
field of `CtrSt`, it is carried through `fam_succ`, the certificate reports an
`outer_p_law` and a `fill_moves_outer_p` for it, there is a merged branch
named for it — **and it does not appear in the denotation at all.**  This
change is what makes it appear.

**THE GATE, and it is the whole risk.**  Putting `p` into the denotation
changes `fam_cfg`, which every board's `Hboot` and every `cden_cls_conf` is
stated against.  **The 40-odd boards already on disk must compile unchanged.**
Do what §4o did for `cls_side`'s fixed word: keep the existing shape as the
instance at `a = 0, b = |fixed word|` so the old statements are the new ones
at a trivial parameter, and check two existing boards BEFORE building anything
on top.  If they cannot be recovered as an instance, **STOP and write §4s with
what does not factor** — do not fork `fam_cfg` into two denotations, and do
not weaken `RuleSound`.  §4i's "the record does not widen" has now survived
three instances (`(Gray,2)`, `(Fib,1)`, `cls_side`'s `u`) and is worth more
than two rows.

**Both halves, not just the kernel.**  `valfam.py`'s `Fam.read` has the same
assumption on the other side of the trust boundary —
`if tuple(base[:len(self.pre)]) != self.pre: return None` matches the
near-head prefix as a fixed tuple, so `read()` returns `None` at every anchor
and the row is filed *no anchor whose counter side decodes*.  §4q measured the
searcher's current behaviour precisely: **8 families, none closed, 0 arms**,
identically at 40k, 150k and 600k steps, and every family it tries is the
receding WALL (`side: L`, step 2) rather than the counter — it reads the
window the wall opens and then correctly refuses it.  §4q also tried two
patches to the search (`_grams`'s prefix cap, splitting the pooled `(B,0)`
anchor by frame) and **reverted both, neither helped**.  Its conclusion is the
instruction: **build the field, not the search.**

**DO ONE ROW END-TO-END.**  `0RB0RD_1LC1RB_1RA0LC_1LB0LC`, at §4q's anchor and
not §4j's.  Drive it to `NeverQuasiHaltsSt tm_*`, run `make closeout`, and
confirm "settled by a board" moves.  **A board that does not move a number is
not a board.**

**THE CHEAP TWO, if the gate holds early.**  `1RB0RD_1LC0LB_1LD0LB_1RD0RA` and
`1RB0RD_1LC0LC_1LD0LB_1RD0RA` — two-cell digit words ending in `0`, so
`fam_cells` spells one cell more than the machine's `cconf` carries at the
anchor.  The gray emitter REFUSES them at the boot check with exactly that
reason in the `.v` file (`boot cells [1, 0, 1] are not the family at [1, 1]`),
and `tools/ladder/gray2check.py` confirms their class law is fine.  Either
re-read them at an anchor whose digit words do not end in a blank, or give
`fam_cells` a trimming the denotation can state.  No kernel lemma is involved,
and four rows in one session is what the last three sessions each delivered.

**WHAT NOT TO DO.**

* **Do not add another axis to a probe over the no-family bucket.**  §4j ran
  `bounce.py` over the fifteen and matched exactly John's two; §4j's own
  sentence is *"the thirteen are not blocked by the near-head spacer alone.
  Whatever they are, fixing the outer parameter will not reach them, and one
  more human READ is worth more than another axis on the probe."*  PR #90 came
  at the same fifteen on the numeration axis and got a different 13.  Each
  probe found what its own axis could see.  **The remaining no-family rows want
  a human at a tape, not a wider search** — and the three that paid this month
  (gray, fibonacci, this bouncer) were all read by John, not found by a sweep.
* **Do not re-probe the four base-2 quadratic rows.**  §4p measured their
  interior arm at `(r+1)(r+2)` and `r^2 + 5r + 12`, second difference exactly
  2, corroborated on the terminal by `QUAD_TERMINAL_MEASUREMENT.md`.  A strided
  arm is one chain repeated, so its cost is affine along the stride; no
  widening of `ARM_GRID` reaches a quadratic.  Nine rows with their shadows,
  and they want `RU` or a count language with a product — **scope that
  deliberately, in its own session; it is the long pole to zero and the only
  bucket with no technique.**
* Do not build another `ClassSucc` instance: `(Binary,1)`, `(Gray,2)` and
  `(Fib,1)` cover every closed row that is left.
* **Never edit `theories/Census/`.**

**THE SHADOWS ARE NOT READY WORK, AND HERE IS WHY.**  Twelve `0RB` shadows sit
on ten core rows.  A shadow satisfies the `skipped` disjunct only while its
core row is DEFERRED; it needs a board of its own exactly when its core row
boards, and not before.  **Five of the twelve sit on three of the four
QUADRATIC rows** (§4p), so they are not coming back either.  Two things §4o
paid for, when you do free one:

* **You do not have to do anything.  A freed shadow now boards itself.**
  §4o hit this the hard way: `shadowlib.classify` used to drop a shadow from
  `shadow_rows.tsv` the moment its partner left the unproven set — exactly
  when it became actionable — so `gen_shadow.py --all`, whose input is that
  file, was blind to the rows that were ready, and §4o drove both of them by
  hand off `git show HEAD~1:tools/closeout/shadow_rows.tsv`.  **Fixed:**
  `classify` searches partners over the boarded set too and reports a third
  category, `freed`; `gen_shadow.py --harvest` boards every one; and
  `make closeout` runs it between two `inventory.py` passes.  So board a core
  row, run `make closeout`, and its shadows come with it.  `audit.py` prints a
  freed row that somehow survives, because it is the cheapest row on the list.
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
    python3 tools/closeout/gen_shadow.py --harvest   # boards any freed shadow
    python3 tools/closeout/inventory.py              # ...and picks it up
    python3 tools/closeout/gen_stages.py
    python3 tools/closeout/audit.py     # must print CLOSEOUT AUDIT: OK

`make closeout` runs exactly that sequence.  Driving it by hand and skipping
the `--harvest` line is the one way a freed shadow still ends up sitting in
`core_rows.txt`; `audit.py` prints it if it does.

The board `.v` files are the source of truth and never conflict, because they
are different files.
