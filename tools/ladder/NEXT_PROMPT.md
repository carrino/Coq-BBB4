COVER THE TOP OF A WIDTH.  It is the SHARED blocker, measured from two
numerations independently, and it is now the majority obstruction in the core.
In `carrino/Coq-BBB4`, on branch `claude/width-top-<yourid>` cut from `main`.

**Diff `origin/main` first**: `git show origin/main:tools/closeout/core_rows.txt`
is one command, and the wave route has now taken rows out from under seven
sessions.  §4l, §4n, §4o, §4p, §4r and §4s each say this; §4o had its own
next-session prompt invalidated eight hours later by §4p, and the prompt §4u
was handed named a core count two waves stale, a "highest section" two
sections stale, and a step-1 premise that had already been implemented.
**Re-read the plan's LAST section before acting on a prompt.**  This one was
written at the end of §4u; §4t and §4u landed within hours of each other.

Read first, in this order: `docs/LADDER_PLAN.md` **§4u** — it is the
measurement that selected this task, and its `rejection` histogram is the
selection criterion; then **§4s's "The FIBONACCI seven"**, which found the
same blocker from the other numeration; then `theories/Checkers/LadderCheck.v`
§3c and §5c, where a fill arm's class lives.

**STATE.**  **26** core undecided and **11** `0RB` shadows on **9** partners
(`tools/closeout/core_rows.txt`, `tools/closeout/shadow_rows.tsv`;
`make closeout-status`).  **5,119** frozen rows settled by a board, **99.3%**.
**37** rows remain.

**THE FINDING THAT SELECTS THIS.**  §4u instrumented `valfam.py` to record the
pool and split the one opaque `families found but none closed` verdict.  Over
the fourteen rows still carrying it:

     19  family not covered
     13  overflow leaves the family
     13  the fill DECREASES the outer parameter (a reading of the window)
      5  reachable set too short to check
      5  no arm replayed to anchor

`overflow leaves the family` means the interior covers and the FILL arm at the
top of a width does not.  §4s measured exactly that on the six `1RB---`
fibonacci rows — uncovered set `sum(weights[:k])`, the string `1^k` — and
read it as a Zeckendorf problem.  It is not: §4u finds the same failure on
four **base-2** rows, two of them `all_failures_at_overflow` (fails at the top
of a width and nowhere else):

    1RB0RD_1LB1LC_1RC0RA_0LB1RD   pool 39   4/4 at overflow
    1RB0RD_1LC1RA_0RB0LC_1LD0LA   pool 40   4/4 at overflow
    1RB1LC_0LC0RB_1LA1RD_0LA0RD   pool 55   3/4 at overflow   <- shadow partner
    1RB1LD_1LC1RA_0RB0LC_0RA0LD   pool 31   2/4 at overflow   <- shadow partner

**Two numerations, one blocker, ten rows.**  That is the pattern §4s and §4t
both name as the one worth trusting: a thing measured twice from different
directions.  Anything that covers `1^k` generically is worth more than a
fourth `(code, step)` pair, and §4r's own advice — "do not go looking for a
fifth code before someone measures a row that wants it" — now cuts against
building `(Fib, 2)` first.

**THE ORDER.**

1. **Read the four base-2 overflow rows' fill arms before building anything.**
   These are NOT the quadratic four; their interiors cover.  Start with
   `1RB0RD_1LB1LC_1RC0RA_0LB1RD` and `1RB0RD_1LC1RA_0RB0LC_1LD0LA`, the two
   that fail ONLY at overflow — they are the cleanest statement of the
   problem in the tree, and they are base 2, where the kernel already speaks
   the numeration and nothing but the arm is in question.  `armprobe.py` is
   the tool and §4p is the template for using it.
2. **Then decide between a generic `1^k` fill arm and Zeckendorf.**  If the
   base-2 tops and the fibonacci tops want the same arm shape, build it once.
   If they do not, that is a real finding and it retires the "one blocker"
   reading above — say so.
3. **Route A on the six fibonacci rows is still unexplored and still cheap**
   (it was Route A in §4s's prompt and no session has run it):
   `tools/counters/FIB_ELEVEN.txt` records all six at `F(1,1) off=0` under
   `fib_anchor.py`, a different reading convention from `valfam`'s.  If some
   anchor admits `1,1,2,3,5` inside `Fam`'s denotation, the kernel already
   speaks it and there is nothing to build.  **This is what freed the two
   gray rows in §4s** — the buildable reading was already in the searcher's
   output and had only lost a tie.

**THE SHADOW ARITHMETIC, corrected.**  Eleven shadows on nine partners, and
two partners carry TWO shadows each — `1RB1LA_1LC0RD_0RA0LC_0LA1RD` and
`1RB1LA_0LA0LC_1LC1RD_0RB0RD` are worth **three rows apiece**.  Both are §4p
quadratic rows, so the biggest prize sits behind the hardest blocker; do not
read "worth three" as "do this one".

**Boarding a partner does NOT drop the core count by one.**  `inventory.py`
PROMOTES the freed shadow out of `shadow_rows.tsv` into `core_rows.txt` — a
shadow is a shadow only while its partner is deferred.  §4u went 27 → 27 → 26
across board-then-harvest.  `python3 tools/closeout/gen_shadow.py --harvest`
(no arguments) does the second half and `audit.py` prints the exact command
when a shadow is waiting.  A session that boards a partner and stops has moved
the settled count by one and the core count by zero.

**WHAT NOT TO DO.**

* **Do not select a row by `n_families`.**  §4u measured it meaningless: the
  candidate list is `fams[:4]` plus at most two fallbacks, and over all
  fifteen rows in the bucket **every one tried exactly four**, pool sizes
  3..74.  `n_families: 74` is four rejections and seventy never looked at.
  Select on the `rejection` histogram, which now exists in every record.
* **Do not re-run the "none closed" sweep.**  §4u did, instrumented, at the
  stock cap: `tools/ladder/residue14_4t.{jsonl,log}`, all fourteen still fail.
  The stale certificate that boarded `1RB1LA_0LA1RC_0RD0RB_1RA---` was stale
  on its own account and the bucket is not hiding another.
* **Do not raise the prover's clock.**  §4r measured `--cap 420 --kmax 8`
  against 240 on the six `1RB---` rows and it lands in the same place.
* **Do not re-probe the four base-2 QUADRATIC rows** (`1RB0LD_0LC0RB_...` and
  the three `1RB1LA_...`).  §4p measured a second difference of exactly 2 on
  the arm, `QUAD_TERMINAL_MEASUREMENT.md` corroborates it, and §4t re-probed
  them from the emitter's side and got `the carry ripple is not affine in the
  run length`.  Three measurements, one blocker.  **These are a different set
  from the four overflow rows in the table above** — do not merge the two
  lists.
* **Do not count `1RB0RB_0LC1RD_1LC1LA_0LA1RB` with the fibonacci rows.**  §4s
  measured that it finds no family at any anchor.  It is a `no anchor` row.
* **Do not do the outer parameter (§4j).**  §4t measured it necessary and NOT
  sufficient: one lap moves two independent unbounded quantities and `cden`
  has one index.  Scope the anchor and the parameter together, or leave both.
* **Never edit `theories/Census/`.**

**FACTS WORTH NOT REDISCOVERING.**

* Coq is not in the image — `apt-get install -y coq` gives 8.18.0, ~1 min.
* **`family_pool` is new (§4u) and reads the floor for you.**  The three
  `1RB---` rows in the bucket are the only rows whose ENTIRE pool sits at
  chain 8 — `min_chain`, the floor — 24 families each; every other row reads
  at 32..200.  That is the condition §4s's `--numeration` comparison exists
  for, visible without running the pass.
* **`emit_ladder.py` writes its refusal INTO the `.v` file** and that is the
  real exception text.  Read the file, not the driver's last line.  §4u's row
  refused with `code None: LadderCheck states (Binary, 1) only` — a
  certificate written before the `code`/`step`/`numeration` stamps existed.
  **A committed JSONL verdict is a record of what the tooling did that day,
  not a property of the machine.**  Four instances now: §4p's HIGHER label,
  §4s's gray tie-break, §4t's stale schema, §4u's row.
* **`make closeout` only needs `theories/Closeout/Closeout.vo`**, whose
  closure does NOT include the nine `IRules_Batch` (`coqdep` says so).
  ~2h20m cold on 4 cores at `-j3`, ~2350 `.vo`.  Start it EARLY in the
  background.  **Two `IRules_Batch_*` at 8.2 GB will not fit in this image's
  15 GB together** — do not raise `-j` past 3.
* **`pkill -f "<pattern>"` matches the killing shell's own command line.**
  §4u's `pkill -f "Makefile.coq -j1"` killed the shell that was about to
  start the replacement build.  Use a pattern that cannot self-match.
* **`audit.py` is the live scoreboard and needs no Coq**; `inventory.py` →
  `gen_stages.py` → `audit.py` moves the numbers in seconds.  Say which one
  you have — the audit's number or the kernel's.
* **A `cconf` carries no trailing blanks** (`lpad_eqb`), so a family whose
  digit words all end in a blank spells one cell more than its own boot at
  every width.  §4s made that a term in `find_families`' sort key.
* **Anything touching the champion's score stays in HORNER form.**
  `CloseoutKit.covers_iqh_champ_at`'s gate is the proposition `B <= B_champ`
  under `lia` — do not "simplify" it to a `<=?`.
* **Editing a file under `theories/Checkers/` under a running `make`** makes
  every already-built board fail with `inconsistent assumptions over library
  BBB4.Checkers.LadderCheck`.  Same for rewriting `_CoqProject` mid-build.
  Adding an UNREGISTERED `.v` is safe — `make` has no rule for it.
* **`stride = 0` needs the whole side concrete in `s_pre`**; the failure reads
  like "the carry ripple is not affine".
* **`RuleSound` is an equation on `cconf` and `ctape_move` does not
  normalise.**  A blank the head materialises by stepping back is `S0 :: r`.
* Keep `board_ladder.py`'s `wanted()`/`wanted_gray()` in step with
  `closure_data`'s refusals.  **Neither knows about the Fib path** — §4r, §4s
  and §4u all drove `emit_ladder.py` on a cert JSON by hand.
* **Never run `valfam.py` and a full `make -jN` at the same time.**  One row
  is fine; a sweep is not.  §4u ran a 14-row sweep against a `-j1` build and
  paid for it in wall clock.
* CI does NOT build the ladder boards or the `CB_*` stages.  **Green CI is not
  evidence your board compiles.  Build it locally**, and `Print Assumptions`
  it: every ladder board should be `functional_extensionality_dep` alone.
* **Read `liveness.states_infinitely_often` BEFORE choosing a board section.**
  `ABCD` wants `NeverQuasiHaltsSt`; a row whose live set is a proper subset
  quasihalts and wants §11's closer instead.  §4r was handed a prompt naming
  the wrong one for five rows.

**CONSTRAINTS.**  May touch `theories/Checkers/`, `theories/Machines/`,
`tools/`, `docs/`, `NEXT_SESSION.md`.  **Never edit `theories/Census/`.**
Commit incrementally; push and open a PR when the first row moves the count.

**MERGE DISCIPLINE.**  These are ALL GENERATED and must never be hand-resolved:

    theories/Closeout/CB_*.v, SH_*.v, Closeout.v, CoreRows.v, CloseoutFinal.v,
    BBB4_Theorem.v, the Closeout section of _CoqProject,
    tools/closeout/{core_rows.txt,frozen_map.tsv,frozen_unproven.txt,
                    shadow_rows.tsv}

Note that git will happily AUTO-merge the closeout tables textually, which is
the same failure as hand-resolving them.  Take ONE TREE and re-derive:

    python3 tools/closeout/inventory.py
    python3 tools/closeout/gen_shadow.py --harvest   # boards any freed shadow
    python3 tools/closeout/inventory.py              # ...and picks it up
    python3 tools/closeout/gen_stages.py
    python3 tools/closeout/audit.py     # must print CLOSEOUT AUDIT: OK

`make closeout` runs exactly that sequence.  Skipping the `--harvest` line is
the one way a freed shadow still ends up sitting in `core_rows.txt`;
`audit.py` prints it if it does.

The board `.v` files are the source of truth and never conflict.
