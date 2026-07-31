# PR triage, and the two prompts that follow from it

_Written against `main` at `3ffa761` with four PRs open (#92, #98, #99, #100).
Every count below is one a script in this tree printed, not an estimate._

## 1. The verdicts

| PR | what it is | verdict |
|---|---|---|
| **#100** the probe, the phase cycle, three rows | boards 3 core rows, 42 → 39 | **MERGE FIRST** |
| **#92** counts + `check_coqproject.py` CI guard | docs and tooling, **no `.v`** | **MERGE**, after #100, with its counts re-swept |
| **#98** `RerootSwap.v` + `gen_shadow.py` | fills a real general gap; the shadow harvester | **MERGE** |
| **#99** the five Fibonacci partial boards | boards nothing, 677 lines, 0 shadows | **CLOSE** |

**#100 is the only open PR that moves the number**, and it was the only one
with a conflict.  It is now merged with `main`, regenerated, and green.

### Why #99 is the one to close

It is the "exploration that is not clearly helpful".  Its own PR body offers:
*"Close it without merging if you would rather the finding live only in #61
and `docs/CORE_3STATE.md`."*  Four things say take that offer:

1. **It boards nothing and its bucket is the lowest-leverage one left.**  The
   five Fibonacci rows carry **zero** shadows (§3), so the bucket is worth 5
   rows where the arms-blocked bucket is worth 11.
2. **It would be the first thing #92's new CI guard fails on.**  Verified, not
   predicted — merging all four into one tree and running the guard gives:

   ```
   UNWIRED: 5 .v file(s) under theories/ are neither in _CoqProject nor exempt:
      theories/Machines/Ladder/LDR_1RB____0LB1RC_1LB0RD_1LC0RD.v
      ... (all five)
   exit=1
   ```

   So merging it costs a second exempt block with its own reason — carrying
   cost on a guard that was introduced one PR ago.
3. **Its blocker is in the file the next session rewrites.**  The closure is
   blocked because `LadderFam` counts positionally (`val_pos`), and Prompt A
   below rewrites exactly that region for `(gray, 2)`.  The five boards would
   be regenerated against a different kernel anyway.
4. **The finding survives the close.**  It is already stated in
   `LADDER_PLAN` §4n's table ("closed (fibonacci) | 5 | 4m's five: the
   canonical form wants a Coq lemma"), in the PR body, and on the branch,
   which stays on the remote.

Closing it is a judgement call and merging it with an exempt block is
defensible; the leverage argument is what tips it.

## 2. The merge order, and why it is not free

**#100 → #92 → #98 → #99(close).**  Two ordering facts, both measured:

* **#92's counts are correct only until #100 lands.**  #92 sweeps the docs to
  42 + 14.  #100 makes that 39 + 14.  Since #92 *is* the count-sweep PR, it
  should be the one that carries the final number — so it goes second, with
  `42 + 14 / 5,100 / 98.9%` re-swept to `39 + 14 / 5,103 / 99.0%`.
* **All three remaining PRs merge cleanly onto `main` + #100** — checked with
  `git merge-tree`, all `CLEAN`.  The only thing that does not survive the
  integration is the guard result above.

## 3. The number nobody had written down: shadows are not spread evenly

`tools/closeout/shadow_rows.tsv` column 4 is each shadow's core partner.
Counting it:

> **All 14 shadows sit on 12 of the 39 core rows.**  Those 12 rows therefore
> account for **26 of the 53** rows left.  The other 27 core rows are worth
> one row each.

That changes which bucket is worth working.  Bucketing the live 39 by the
sweep's own `reason` field (`tools/ladder/core143_ph.jsonl`) and adding the
shadow load:

| bucket | core | shadows | **rows** |
|---|---:|---:|---:|
| no value family at the probed anchor | 21 | 4 | 25 |
| families found, none closed | 10 | 4 | 14 |
| **families CLOSED, arms blocked** | **5** | **6** | **11** |
| time cap | 3 | 0 | 3 |

(The first bucket is stale in one direction: §4m found families for five of
its rows and §4n found gray classes for six more, so it is smaller than 21 in
truth.  The `CLOSED` bucket is the one that matters here.)

**Five rows whose ladder family already closes carry six shadows between
them — 11 of the 53, on machines that stop only on an arm chain.**  Four of
the five already have partial boards on disk with 9 to 25 arms each proved
sound.  That is Prompt B.

## 4. The trap that caused the only conflict, and the rule that removes it

#100 conflicted in **29 files and every one of them is generated**:

```
theories/Closeout/CB_28.v … CB_50.v, Closeout.v, CoreRows.v,
CloseoutFinal.v, BBB4_Theorem.v          <- gen_stages.py
tools/closeout/core_rows.txt, frozen_unproven.txt,
frozen_map.tsv, shadow_rows.tsv          <- inventory.py + gen_stages.py
the Closeout section of _CoqProject       <- gen_stages.py
```

Resolved by hand, this silently reverts whichever side's boards the resolver
did not notice — #100's stale regeneration would have un-boarded main's two.
The rule, and it belongs in every ladder prompt from here:

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

## 5. The two prompts

They are parallel-safe because they own **disjoint files**.  A owns the
kernel; B is forbidden from touching it.

| | Prompt A | Prompt B |
|---|---|---|
| target | the gray four | the arms-blocked five |
| worth | 4 rows | **11 rows** (5 core + 6 shadows) |
| owns | `theories/Checkers/LadderCheck.v`, `emit_ladder.py` **gray path** | `tools/ladder/armprobe.py`, `valfam.py`, `emit_ladder.py` **far-side reader**, `tools/closeout/gen_shadow.py` |
| must not touch | `armprobe.py`, `gen_shadow.py` | **`theories/Checkers/` at all** |
| confidence | high — arms measured to derive, build specified to the lemma | medium — a precise, cheap-to-falsify hypothesis |

Both must obey §4's regeneration rule, both must
`git show origin/main:tools/closeout/core_rows.txt` before choosing and again
before pushing, and for both: **a board that does not move a number is not a
board.**

---

# PROMPT A — build `(gray, 2)`.  Four rows, and the arms are already measured

Branch `claude/ladder-gray-<yourid>`, cut from `main`, in `carrino/Coq-BBB4`.

This is `tools/ladder/NEXT_PROMPT.md` as §4n left it, and that file is the
long form — **read it in full first**; it names every lemma you will touch.
What follows is the scope, the ownership, and the two things that file does
not say.

**STATE.** 39 core undecided, 14 `0RB` shadows, 5,103 settled (99.0%).

**THE TASK.**  §4n's probe measured the gray six and found **four** have both
class arms, by fitting the classes from the family's own successor and
recovering §4i's four verbatim.  The measurement is done; do not re-run it.
Build what it selected: `cls_side` gaining a fixed word before the run, four
`ClassSucc` instances, the parity invariant `P` (the value's low bit, which
`+2` preserves, and it is GLOBAL), a four-way case split to replace
`digs_decomp`, and `Section Iter` at `Gray`/step 2 — where the measure
`b^k − value` falls by 2 rather than 1, and that is the whole difference.
**The top of a width is the largest MEMBER**, so `pos1_is_top` /
`pos1_top_shape` get gray twins.

**DO ONE ROW END-TO-END FIRST.**  `1RB0RB_0LC0LD_1LC1LD_1RA0RA`, the row §4g
and §4i both read.  Drive it to `NeverQuasiHaltsSt tm_*`, `make closeout`, and
confirm "core undecided" moves.

**GATE.**  If a `ClassSucc` instance will not go through, STOP and write §4o
with which class and why.  Do not weaken `ClassSucc` to fit it and do not add
a second class record — §4i's result that the record does not widen is worth
more than any one row.

**PARALLELISM.**  A second session is working the arms-blocked five at the
same time and it owns `tools/ladder/armprobe.py`, `valfam.py`,
`tools/closeout/gen_shadow.py`, and the far-side/boot reading helper in
`emit_ladder.py`.  **Confine your `emit_ladder.py` edits to the gray code
path** and do not restructure the shared arm-reading helpers.  You own
`theories/Checkers/` — the other session is forbidden from touching it, so
you will not be raced there.

**DO NOT** re-run the arm probe over the gray six, do not touch the Fibonacci
five (their closure wants a `LadderFam` canonical-form lemma and that is a
third session), do not do the outer parameter (§4j), do not touch the count
language or `RU`.  **Never edit `theories/Census/`.**

**The two gray rows that are NOT in the four are a FAMILY question, not a
`ClassSucc` one.**  `1RB0RD_1LC0LB_1LD0LB_1RD0RA` and
`1RB0RD_1LC0LC_1LD0LB_1RD0RA` have two-cell digit words ending in `0`, so
`fam_cells` spells one cell more than the machine's `cconf` carries at the
anchor.  Measured: strip that cell and the fill arm derives in 24 steps at
every index and copy split.  Leave them.

**MERGE DISCIPLINE.**  See §4 above — the generated closeout files are
re-derived, never hand-resolved.

---

# PROMPT B — re-measure the arms-blocked five.  Eleven rows, and the hypothesis is one cell

Branch `claude/ladder-armsblocked-<yourid>`, cut from `main`, in
`carrino/Coq-BBB4`.

**THE CLAIM YOU ARE TESTING, AND IT IS CHEAP TO FALSIFY.**

Five core rows have a ladder family that **closes** and stop only on an arm.
They carry six shadows between them — **11 of the 53 rows left**, the densest
bucket in the residue:

```
1RB1LA_0LA0LC_1LC1RD_0RB0RD   +2 shadows   partial board on disk, 25 arms sound
1RB1LA_1LC0RD_0RA0LC_0LA1RD   +2 shadows   partial board on disk, 14 of 15 sound
1RB1LA_0LA1RC_0LD0RC_1LD0RB   +1 shadow    partial board on disk,  9 of 11 sound
1RB1LA_0LA1RC_0RD0RB_1RA---   +1 shadow    no partial board yet
1RB0LD_0LC0RB_1LA1RC_0RC1LD    0 shadows   partial board on disk, 14 of 15 sound
```

All four partial boards stop with the **same sentence**, written into the
`.v` file by the emitter:

> `The closure: NOT BUILT for this row -- interior arm: no chain at any`
> `threshold 0..3 and stride 1..4 -- the carry ripple is not affine in the`
> `run length`

**§4n proved that exact signature is not always a refusal.**  On the gray six
the same "no chain at any threshold and stride" was a one-cell configuration
artifact:

> *"`RuleSound` is an equation on `cconf` and `ctape_move` does not normalise.
> A blank the head materialises by stepping back over it is `S0 :: r` and not
> `r`.  `valfam` reads the far side through a run-length view that has already
> dropped a trailing blank run… Read the far side off the boot instead and the
> interior arms of **all six** gray rows derive; with the certificate's value,
> **none** does."*

**These four boards were emitted before that fix, and nobody has re-measured
them.**  `tools/ladder/armprobe.py` already implements the corrected reading
(far side off the boot; tops read off the orbit) and already has `--selftest`
against an already-boarded row.

**THE TASK, in this order.**

1. **Run `armprobe.py` over the five rows.**  Run `--selftest` first so you
   know the probe is honest.  These are `(Binary, 1)` step-1 rows, so the
   probe needs no relaxation for them at all — this is the probe doing the
   job it was built for, on the bucket it was not pointed at.
2. **Report the count before building anything.**  How many of the five have
   every arm derive under the corrected far-side reading?  That number
   decides the rest, and §4k's guard says print it either way.
3. **If arms derive: board them.**  The families already close, so the
   closure needs nothing new in the kernel — re-emit through
   `emit_ladder.py` / `board_ladder.py`, delete the row's line from
   `tools/coqproject_exempt.txt` as that file instructs (a path that is both
   exempt and listed fails `check_coqproject.py`), and `make closeout`.
4. **Then harvest the shadows.**  `tools/closeout/gen_shadow.py` (#98) turns a
   boarded `nqh` core row into its shadows' boards; it refuses any partner
   whose `frozen_map.tsv` kind is not `nqh`, and ladder boards are `nqh`.
   Run `--regress` first, then `--all`.  **Six shadows are waiting on these
   five rows** and they are the reason the bucket is worth 11 and not 5.
5. **If the arms still do not derive, that is the deliverable.**  Write
   §4o with the count and the failure mode, and say whether it is the same
   one-cell story or genuinely the non-affine carry ripple that
   `LADDER_PLAN` §5 claims.  Right now nobody knows which, and the file's own
   stop-note cites §4h(a)'s `ClassSucc` reason that §4l already removed — so
   at minimum, correct the note.

**PARALLELISM — the hard constraint.**  A second session is building
`(gray, 2)` in `theories/Checkers/LadderCheck.v` at the same time.
**Do not edit anything under `theories/Checkers/`.**  If you conclude the
kernel must change, that is a finding to write up, not a change to make —
say so in §4o and stop.  You own `tools/ladder/armprobe.py`, `valfam.py`,
`tools/closeout/gen_shadow.py`, and the far-side/boot reading helper in
`emit_ladder.py`; keep your `emit_ladder.py` edits out of the gray code path.

**MERGE DISCIPLINE.**  See §4 above.  You and the gray session will both add
board `.v` files and both run `make closeout`, so you *will* collide in the
generated closeout files.  That collision is not a merge problem — take
either side and re-run `inventory.py`, `gen_stages.py`, `audit.py`.  Never
resolve one of those files by hand.

**Facts worth not rediscovering** (from §4n, and they cost a session each):

* Coq is not in the image: `apt-get install -y coq` gives 8.18.0, ~1 minute.
* `make closeout` needs only `theories/Closeout/Closeout.vo`, whose closure is
  2,188 files and **does not include the nine `IRules_Batch`** (ask `coqdep`,
  not the plan file), so you never pay their 8.2 GB each.  Cold build at
  `-j3` is about 45 minutes.
* **Editing a file under `theories/Checkers/` during a running `make` makes
  every already-built board fail** with "inconsistent assumptions over library
  BBB4.Checkers.LadderCheck".  Another reason the constraint above is cheap
  for you to keep.
* `emit_ladder.py` writes its refusal reason **into the `.v` file**.  Read the
  file, not the driver's last line.
* **Never run `valfam.py` and a full `make -jN` at the same time.**
* CI builds `CloseoutKit.vo` and two example files — it does **not** build the
  ladder boards or the `CB_*` stages.  A green CI is not evidence your board
  compiles; build it locally.
