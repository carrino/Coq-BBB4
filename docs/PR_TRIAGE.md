# PR triage, and the two prompts that follow from it

_Written against `main` at `3ffa761` with four PRs open (#92, #98, #99, #100).
Every count below is one a script in this tree printed, not an estimate._

## 1. The verdicts

| PR | what it is | verdict |
|---|---|---|
| **#100** the probe, the phase cycle, three rows | boards 3 core rows, 42 → 39 | **MERGE, first** |
| **#92** counts + `check_coqproject.py` CI guard | docs and tooling, **no `.v`** | **MERGE**, counts re-swept to 39 + 14 |
| **#98** `RerootSwap.v` + `gen_shadow.py` | fills a real general gap; the shadow harvester | **MERGE** |
| **#99** five partial ladder boards | boards nothing — but see §4 | **MERGE**, with an exempt block |

**#100 is the only open PR that moves the number**, and it was the only one
with a conflict.  It is now merged with `main`, regenerated, and green.

**Order: #100 → #92 → #98 → #99.**  It is forced, not stylistic:

* **#92's counts are correct only until #100 lands.**  #92 sweeps the docs to
  42 + 14; #100 makes that 39 + 14.  Since #92 *is* the count-sweep PR it
  should carry the final number, so it goes second and re-sweeps.
* **#99 cannot go before #92**, because the exempt block it needs lives in
  `tools/coqproject_exempt.txt`, a file #92 creates.  And it cannot go
  without that block: merging all four into one tree and running #92's new
  guard gives, verified rather than predicted —

  ```
  UNWIRED: 5 .v file(s) under theories/ are neither in _CoqProject nor exempt:
     theories/Machines/Ladder/LDR_1RB____0LB1RC_1LB0RD_1LC0RD.v
     ... (all five)
  exit=1
  ```

  which is the guard doing exactly the job #92 built it for.

Everything else merges cleanly onto `main` + #100 — checked with
`git merge-tree`, all `CLEAN`.

## 2. The trap that caused the only conflict, and the rule that removes it

#100 conflicted in **29 files and every one of them is generated**:

```
theories/Closeout/CB_28.v … CB_50.v, Closeout.v, CoreRows.v,
CloseoutFinal.v, BBB4_Theorem.v          <- gen_stages.py
tools/closeout/core_rows.txt, frozen_unproven.txt,
frozen_map.tsv, shadow_rows.tsv          <- inventory.py + gen_stages.py
the Closeout section of _CoqProject       <- gen_stages.py
```

Resolved by hand, this silently reverts whichever side's boards the resolver
did not notice — #100's regeneration was cut before #95, so taking its side
would have un-boarded main's two.  The rule, and it belongs in every ladder
prompt from here:

> **Never hand-resolve a generated file.**  Take either side to get a tree
> (`git checkout --theirs`), then re-derive from the board `.v` files, which
> are the source of truth and never conflict because they are different
> files:
>
> ```
> python3 tools/closeout/inventory.py    # rebuilds frozen_map / core_rows
> python3 tools/closeout/gen_stages.py   # rebuilds CB_*, Closeout, _CoqProject
> python3 tools/closeout/audit.py        # must print CLOSEOUT AUDIT: OK
> ```

Done that way the merge is the *union* of the two board sets, which is what
it was: 42 − 3 = **39 core, 14 shadows, 5,103 settled, 99.0%**, audit OK.

## 3. Shadows are not spread evenly, and it changes what a row is worth

`tools/closeout/shadow_rows.tsv` column 4 is each shadow's core partner.
Counting it:

> **All 14 shadows sit on 12 of the 39 core rows.**  Those 12 rows therefore
> account for **26 of the 53** rows left.  The other 27 core rows are worth
> one row each.

Bucketing the live 39 by the sweep's own `reason` field
(`tools/ladder/core143_ph.jsonl`) and adding the shadow load:

| bucket | core | shadows | **rows** |
|---|---:|---:|---:|
| no value family at the probed anchor | 21 | 4 | 25 |
| families found, none closed | 10 | 4 | 14 |
| families CLOSED, arms blocked | 5 | 6 | 11 |
| time cap | 3 | 0 | 3 |

That sweep is stale in one direction — §4m found families for five of the
first bucket's rows and §4n found gray classes for six more — and §4 below
shows how much that matters.

## 4. The finding that reshaped both prompts

`emit_ladder.py` writes its refusal reason **into the `.v` file**, and it is
the text of the `NoClosure` exception, not a template.  There are two:

```
line 381   interior arm: no chain at any threshold 0..3 and stride 1..4
           -- the carry ripple is not affine in the run length
line 431   fill arm: no chain at any threshold 1..3, stride 1..4 or copy split
```

Reading that line out of every unregistered partial board on disk — the four
`main` carries plus the five #99 adds:

| row | certificate arms | closure stops at | shadows |
|---|---|---|---:|
| `1RB1LA_0LA0LC_1LC1RD_0RB0RD` | 25 of 25 | **interior (381)** | 2 |
| `1RB1LA_1LC0RD_0RA0LC_0LA1RD` | 14 of 15 | **interior (381)** | 2 |
| `1RB1LA_0LA1RC_0LD0RC_1LD0RB` | 9 of 11 | **interior (381)** | 1 |
| `1RB0LD_0LC0RB_1LA1RC_0RC1LD` | 14 of 15 | **interior (381)** | 0 |
| `1RB---_0LB1RC_1LB0RD_1LC0RD` | 5 of 5 | **interior (381)** | 0 |
| `1RB---_0LB1RC_1LD0RC_1LB1RC` | 4 of 4 | **interior (381)** | 0 |
| `1RB---_1LC0RB_1LD1RB_0LD1RB` | 4 of 4 | **interior (381)** | 0 |
| `1RB---_1LC0RD_0LC1RB_1LB0RD` | 5 of 5 | **interior (381)** | 0 |
| `1RB---_1LC1RD_0LC1RD_1LB0RD` | 4 of 4 | **interior (381)** | 0 |

> **Nine core rows, carrying five shadows — 14 of the 53 — stop at the same
> line of the same function, and every one of those boards was emitted
> before §4n's fix.**

Two corrections fall out of that table.

**#99's PR body misdescribes its own artifact.**  It says the five *"die at
the closure"* and that this is *"already a different failure from the six
older ladder partials, which die **on an arm**."*  The files say otherwise:
all five die on the closure's **interior class arm**, at line 381, the same
line as the four older ones.  The body's "ZERO arms without a chain" is true
but is about the **certificate's** arms — the ones emitted as `sound_arm*`.
The closure's class arms are a different set, built fresh from the family by
`closure_data` (`conf(blk(...))` over digit words), and they are what fails.
This is not a Fibonacci-canonical-form story; it is the arms-blocked story
with five more rows in it.

**That is why #99 is worth merging.**  Not as a record — as five more
instances of the bucket Prompt B attacks, needed on disk for the
re-measurement.  Its exempt block should state the real reason, not the
body's.

## 5. Why the re-measurement is the right bet

§4n proved this exact signature is **not always a refusal**.  On the gray six
the identical "no chain at any threshold and stride" was one cell:

> *"`RuleSound` is an equation on `cconf` and `ctape_move` does not normalise.
> A blank the head materialises by stepping back over it is `S0 :: r` and not
> `r`.  `valfam` reads the far side through a run-length view that has already
> dropped a trailing blank run… Read the far side off the boot instead and the
> interior arms of **all six** gray rows derive; with the certificate's value,
> **none** does."*

`closure_data`'s failing `derive(el, er, c0, c1, …)` runs on exactly the
configurations that finding is about.  `tools/ladder/armprobe.py` already
implements the corrected reading and already has `--selftest`.  Nobody has
pointed it at these nine rows.

It may still be a genuine refusal — `LADDER_PLAN` §5 claims a non-affine cost
has no chain at any stride, and the two QUAD rows measured `(k+2)^2` exactly.
But that claim has now been wrong once, in the same words, on six rows.
Testing it costs one probe run.

## 6. The two prompts

Parallel-safe because they own **disjoint files**.  A owns the kernel; B is
forbidden it.

| | Prompt A | Prompt B |
|---|---|---|
| target | the gray four | the nine interior-arm rows |
| worth | 4 rows | **14 rows** (9 core + 5 shadows) |
| owns | `theories/Checkers/LadderCheck.v`, `emit_ladder.py` **gray path** | `armprobe.py`, `valfam.py`, `emit_ladder.py` **far-side reader**, `gen_shadow.py` |
| must not touch | `armprobe.py`, `gen_shadow.py` | **`theories/Checkers/` at all** |
| confidence | high — arms measured to derive, build specified to the lemma | medium — one cheap, falsifiable probe run decides it |

Both obey §2's regeneration rule, both run
`git show origin/main:tools/closeout/core_rows.txt` before choosing and again
before pushing, and for both: **a board that does not move a number is not a
board.**

---

# PROMPT A — build `(gray, 2)`.  Four rows, and the arms are already measured

Branch `claude/ladder-gray-<yourid>`, cut from `main`, in `carrino/Coq-BBB4`.

`tools/ladder/NEXT_PROMPT.md` is the long form — **read it in full first**; it
names every lemma you will touch.  What follows is the scope and the
ownership.

**STATE.** 39 core undecided, 14 `0RB` shadows, 5,103 settled (99.0%).

**THE TASK.**  §4n's probe measured the gray six and found **four** have both
class arms, by fitting the classes from the family's own successor and
recovering §4i's four verbatim.  The measurement is done; do not re-run it.
Build what it selected: `cls_side` gaining a fixed word before the run, four
`ClassSucc` instances, the parity invariant `P` (the value's low bit, which
`+2` preserves, and it is GLOBAL — §4i measured that it cannot be pushed into
`cs_u`/`cs_w`), a four-way case split to replace `digs_decomp`, and
`Section Iter` at `Gray`/step 2, where the measure `b^k − value` falls by 2
rather than 1 and that is the whole difference.  **The top of a width is the
largest MEMBER**, so `pos1_is_top` / `pos1_top_shape` get gray twins.

**DO ONE ROW END-TO-END FIRST.**  `1RB0RB_0LC0LD_1LC1LD_1RA0RA`, the row §4g
and §4i both read.  Drive it to `NeverQuasiHaltsSt tm_*`, `make closeout`, and
confirm "core undecided" moves.

**GATE.**  If a `ClassSucc` instance will not go through, STOP and write §4o
with which class and why.  Do not weaken `ClassSucc` to fit it and do not add
a second class record — §4i's result that the record does not widen is worth
more than any one row.

**PARALLELISM.**  A second session is re-measuring the interior-arm rows at
the same time and owns `tools/ladder/armprobe.py`, `valfam.py`,
`tools/closeout/gen_shadow.py`, and the far-side/boot reading helper in
`emit_ladder.py`.  **Confine your `emit_ladder.py` edits to the gray code
path**; do not restructure the shared arm-reading helpers.  You own
`theories/Checkers/` outright — B is forbidden it, so you will not be raced
there.

**DO NOT** re-run the arm probe over the gray six, do not do the outer
parameter (§4j), do not touch the count language or `RU`.  **Never edit
`theories/Census/`.**

**The two gray rows that are NOT in the four are a FAMILY question, not a
`ClassSucc` one.**  `1RB0RD_1LC0LB_1LD0LB_1RD0RA` and
`1RB0RD_1LC0LC_1LD0LB_1RD0RA` have two-cell digit words ending in `0`, so
`fam_cells` spells one cell more than the machine's `cconf` carries at the
anchor.  Measured: strip that cell and the fill arm derives in 24 steps at
every index and copy split.  Leave them.

**MERGE DISCIPLINE.**  §2 above — the generated closeout files are
re-derived, never hand-resolved.

---

# PROMPT B — re-measure the nine interior-arm rows.  Fourteen rows, and the hypothesis is one cell

Branch `claude/ladder-interior-arm-<yourid>`, cut from `main`, in
`carrino/Coq-BBB4`.

**THE CLAIM YOU ARE TESTING, AND ONE PROBE RUN DECIDES IT.**

Nine core rows have an unregistered partial board on disk, and every one of
them stops at the **same line of the same function** — `emit_ladder.py:381`,
`closure_data`'s interior class arm:

> `interior arm: no chain at any threshold 0..3 and stride 1..4 -- the carry`
> `ripple is not affine in the run length`

They carry five shadows between them, so the bucket is **14 of the 53 rows
left** — the densest in the residue:

```
1RB1LA_0LA0LC_1LC1RD_0RB0RD   +2 shadows   25 of 25 certificate arms sound
1RB1LA_1LC0RD_0RA0LC_0LA1RD   +2 shadows   14 of 15
1RB1LA_0LA1RC_0LD0RC_1LD0RB   +1 shadow     9 of 11
1RB0LD_0LC0RB_1LA1RC_0RC1LD    0            14 of 15
1RB---_0LB1RC_1LB0RD_1LC0RD    0             5 of 5
1RB---_0LB1RC_1LD0RC_1LB1RC    0             4 of 4
1RB---_1LC0RB_1LD1RB_0LD1RB    0             4 of 4
1RB---_1LC0RD_0LC1RB_1LB0RD    0             5 of 5
1RB---_1LC1RD_0LC1RD_1LB0RD    0             4 of 4
```

(The last five arrive with #99.  Its PR body says they *"die at the closure"*
and calls that *"a different failure from the ones that die on an arm"* — the
files say they die on the closure's interior class arm, line 381, same as the
first four.  Its "zero arms without a chain" is about the **certificate's**
arms; `closure_data` builds the class arms separately.  Trust the files.)

**§4n proved this signature is not always a refusal.**  On the gray six the
identical "no chain at any threshold and stride" turned out to be one cell:

> *"`valfam` reads the far side through a run-length view that has already
> dropped a trailing blank run… Read the far side off the boot instead and the
> interior arms of **all six** gray rows derive; with the certificate's value,
> **none** does."*

`closure_data`'s failing `derive(el, er, c0, c1, …)` runs on exactly those
configurations.  **All nine boards were emitted before that fix and nobody has
re-measured them.**  `armprobe.py` already implements the corrected reading.

**THE TASK, in this order.**

1. **`armprobe.py --selftest` first**, so you know the probe is honest, then
   run it over the nine rows.  Most are `(Binary, 1)` step-1, so the probe
   needs no relaxation for them — this is the probe doing its job on the
   bucket it was never pointed at.
2. **Print the count before building anything.**  How many of the nine have
   the interior class arm derive under the corrected far-side reading?  §4k's
   guard: report it either way.
3. **If arms derive: board them.**  The families already close, so nothing new
   is needed in the kernel.  Re-emit through `emit_ladder.py` /
   `board_ladder.py`, **delete that row's line from
   `tools/coqproject_exempt.txt`** as that file instructs (a path that is both
   exempt and listed fails `check_coqproject.py`), and `make closeout`.
4. **Then harvest the shadows.**  `tools/closeout/gen_shadow.py` turns a
   boarded `nqh` core row into its shadows' boards; it refuses a partner whose
   `frozen_map.tsv` kind is not `nqh`, and ladder boards are `nqh`.  Run
   `--regress`, then `--all`.  **Five shadows are waiting on the first three
   rows** and they are why this bucket is 14 and not 9.
5. **If the arms still do not derive, that is the deliverable.**  Write §4o
   with the count and say which it is: the same one-cell story, or genuinely
   the non-affine carry ripple `LADDER_PLAN` §5 claims.  Nobody knows today.
   At minimum, correct the boards' stop-note, which still cites §4h(a)'s
   `ClassSucc` reason that §4l removed.

**Two rows stop at line 431 instead** (`fill arm: no chain …`):
`1RB---_0LB1RC_1LB0RD_1LC0RC` and `1RB---_1LC0RD_0LC1RB_1LB0RB`.  Neither is a
core row any more, so they are worth zero — read them only if the interior
nine come back clean and you want the fill twin of the same question.

**PARALLELISM — the hard constraint.**  A second session is building
`(gray, 2)` in `theories/Checkers/LadderCheck.v` right now.  **Do not edit
anything under `theories/Checkers/`.**  If you conclude the kernel must
change, that is a finding to write up, not a change to make — say so in §4o
and stop.  You own `armprobe.py`, `valfam.py`, `gen_shadow.py`, and the
far-side/boot reading helper in `emit_ladder.py`; keep your `emit_ladder.py`
edits out of the gray code path.

**MERGE DISCIPLINE.**  §2 above.  You and the gray session will both add board
`.v` files and both run `make closeout`, so you *will* collide in the
generated closeout files.  That is not a merge problem — take either side and
re-run `inventory.py`, `gen_stages.py`, `audit.py`.  Never resolve one by
hand.

**Facts worth not rediscovering** (each cost a session):

* Coq is not in the image: `apt-get install -y coq` gives 8.18.0, ~1 minute.
* `make closeout` needs only `theories/Closeout/Closeout.vo`, whose closure is
  2,188 files and **does not include the nine `IRules_Batch`** (ask `coqdep`,
  not the plan file), so you never pay their 8.2 GB each.  Cold build at `-j3`
  is about 45 minutes.
* **Editing a file under `theories/Checkers/` during a running `make` makes
  every already-built board fail** with "inconsistent assumptions over library
  BBB4.Checkers.LadderCheck".  Another reason your constraint is cheap to
  keep.  The same trap applies to switching git branches mid-build.
* `emit_ladder.py` writes its refusal reason **into the `.v` file** — and it
  is the real exception text.  Read the file, not the driver's last line.
* **Never run `valfam.py` and a full `make -jN` at the same time.**
* CI builds `CloseoutKit.vo`, two example files, and a `make all` dry run — it
  does **not** build the ladder boards or the `CB_*` stages.  A green CI is
  not evidence your board compiles.  Build it locally.
