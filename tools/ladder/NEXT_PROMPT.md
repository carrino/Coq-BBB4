WIDEN `Class` TO A WORD RUN, THEN BUILD `FibL` — THE LAZY FIBONACCI CODE.
Wave 4v measured the six fibonacci rows for the first time AT THE LEVEL OF
THE CANONICAL FORM and **refuted both routes the previous prompt offered**.
In `carrino/Coq-BBB4`, on branch `claude/lazyfib-<yourid>` cut from `main`.

**Diff `origin/main` first**: `git show origin/main:tools/closeout/core_rows.txt`
is one command, and the wave route has now taken rows out from under seven
sessions.  **Re-read `docs/LADDER_PLAN.md`'s LAST section before acting on
this prompt, because the prompt is older than the plan.**  This one was
written at the end of §4v.

Read first, in this order: `docs/LADDER_PLAN.md` **§4v in full** — it is the
measurement that selected this task and it contradicts §4s; then **§4r in
full**, the `(Fib, 1)` build you would be copying; then
`theories/Checkers/LadderCheck.v` §3 (the `Class` record and `ClassSucc`),
§3c and §11.

**STATE.**  **21** core undecided and **10** `0RB` shadows
(`tools/closeout/core_rows.txt`, `tools/closeout/shadow_rows.tsv`;
`make closeout-status`).  **5,125** frozen rows settled by a board, 99.4%.
**31** rows remain.

**WHAT 4v MEASURED, SO YOU DO NOT REMEASURE IT.**

The six rows are

    1RB---_0LC1RD_1LB1RC_1LB0RD      1RB---_1LC0RB_0LD1RB_1LC1RD
    1RB---_0LC1RD_1LB1RD_1LB0RD      1RB---_1LC1RB_0LB1RD_1LC0RD
    1RB---_1LC0RB_0LD1RB_1LC1RB      1RB---_1LC1RD_0LB1RD_1LC0RD

* **The anchor and the ladder are SETTLED.**  All six decode to
  `0, 1, 2, 3, …` with zero failures over 4,000 consecutive anchor visits, at
  a flat one-cell-per-digit anchor, under `fibw = 1, 1, 2, 3, 5, 8` — the
  kernel's own weights.  Do not run `fib_anchor.py`, `radix_clock.py` or
  `valfam --numeration` on these rows again.
* **Route A (the kernel already speaks it) is DEAD.**  `fam_of_value` at
  `Fib` is `fibdec`, which picks ONE representative of a redundant
  numeration, and it is not the machine's: `fibokb` accepts **324 of 4000**
  of these rows' anchor words (the control — §4r's five boarded rows —
  scores 4000).  The complement is exact: the six score **4000 of 4000** on
  "no two adjacent ZEROS, `d0 = 1`", which is the **lazy** (dual) fibonacci
  form, and §4r's five score 243 on it.
* **Route B (`(Fib, 2)` / Zeckendorf) is DEAD and would have built the wrong
  code.**  §4s inferred Zeckendorf from the weights `1, 2, 3, 5, 8` alone.
  Those are the same tape with the forced low digit split off as `fm_pre`;
  the members contain adjacent 1s (`0101, 1101, 0111, 1011, 1111` at width
  4) and are not Zeckendorf's.  **The top of a width here is `1^k`**, the
  same bare run `(Fib, 1)` has — not `1010…`.

**THE TASK.**

1. **Widen `Class` to a WORD run.**  The increment is exact and
   single-valued (0 mismatches over 3,982 interior transitions) and it is

       1^(2m)   0 rest  ->  (1 0)^m    1 rest
       1 1^(2m) 0 rest  ->  1 (1 0)^m  1 rest

   — an ALTERNATING run of half the length, in two parity classes.
   `cs_t : nat` cannot spell `(1 0)^m` and no regrouping rescues it (the
   four values of a 2-cell digit at index `j` are `0, fibw (2j+1),
   fibw (2j), fibw (2j+2)`, not multiples of a common weight).  So
   `cs_t, cs_t' : list nat` with `cls_lhs c n rest = cs_u ++ concat (repeat
   (cs_t c) n) ++ cs_w ++ rest`.  **All three existing instances use
   singleton runs**, so they change by `cbn` and nothing about their
   arithmetic moves.  The arm side already speaks a word run —
   `LadderKernel`'s `sside` is `rep (s_u s) (s_a s * j + s_b s)` — so
   `fam_cells` of a word-run class is exactly the `rep` the arms state.
2. **Add `FibL` to `Code`.**  `fam_lim` at `FibL` is `S (fibsum k)` and
   `fam_value` is `fibval` — *both unchanged from `Fib`*, so §3c's `fib_ub`,
   `fibsum_S` and the weight algebra are reusable verbatim.  What is new is
   `fam_of_value`: a ONE-state decode (the automaton is "the previous digit
   was a 0, so this one is forced"), simpler than `fibdec`'s two states, and
   the round trip is `gray_inj`-easy rather than §4r's risky lemma because
   the lazy form is NOT redundant at a fixed width.
3. **Then the §11 board copy**, with two interior classes (the two
   parities) and the same `1^k` fill arm §11 already has.

**Write the oracle first** (`tools/ladder/fibmem.py` is the template, and
§4o's `gray2check.py` before it): do not state a lemma the Python has not
checked against the orbit read off all six machines.

**WHAT NOT TO DO.**

* **Do not build Zeckendorf.**  See above; §4s's guess was from the weights,
  not from the members.
* **Do not re-probe the four base-2 quadratic rows** (`1RB0LD_0LC0RB_...`
  and the three `1RB1LA` rows).  §4p measured a second difference of exactly
  2 on the arm itself; no widening of `ARM_GRID` reaches a quadratic.
* **Do not do the outer parameter (§4j/§4t).**  Necessary and not sufficient
  for its own two rows; scope the per-phase anchor with it or leave both.
* **Do not read "not a counter" as a residue verdict.**  §4v boarded
  `1RB1LB_1LC0RD_0LB1LA_0LA1RA`, which `LADDER_NOFAM.md` files exactly that
  way — and whose own fingerprint (`1 1 1 1 2 2 2 2 3 3 3 3` strings per
  width, i.e. LINEAR) is a bouncer's signature and says so two paragraphs
  later.  A linear shape-count routes a row to the WAVE track, and the wave
  track's hand boards want no grammar at all: `WTape.cycR` / `cycL` /
  `cycLW` cross one repeated block each and a lap is a chain of them.  The
  sibling `1RB0RB_1LC0RC_1RA0LD_0LB0LC` is the same call and is still open
  (`LADDER_NOFAM.md` reads it as `E(p) = 0^(24p+96) [head] φ (101)^p
  0011111` with `φ` in a finite set of 22 — a one-parameter family with a
  bounded control state, i.e. a phase cycle, not a numeration).
* **Never edit `theories/Census/`.**

**Facts worth not rediscovering.**

* Coq is not in the image — `apt-get install -y coq` gives 8.18.0, which is
  what CI expects.  It takes about a minute.
* **Validate every unit rule against its WHOLE unknown context in Python
  before writing Coq.**  §4v ran each candidate rule over all instantiations
  of the unknown left and right context (every word up to length 6); the
  ones that came back context-independent became `cycR`/`cycL`/`cycLW`
  premises and the ones that did not became one-sided `wsteps_frame_l`/`_r`
  joints.  **That split IS the proof structure** — reading it off the oracle
  costs minutes and guessing it in Coq costs hours.
* A `csteps` lemma over a SYMBOLIC left list reduces by `reflexivity` only
  while the head stays right of its start (`ctape_move DL` blocks on a
  variable `l`).  Check `mindepth = 0` in the oracle; it is the same fact as
  the `wsteps true true` premise.
* `rewrite` on `rep`/`app` identities picks the wrong occurrence constantly.
  Give the lemma its arguments (`rewrite (zsum 3 (4*j+6) [S1])`), and avoid
  `cbn [rep]` where an index is `4 * j` — `cbn` will unfold the `Nat.mul`
  and the term stops matching.
* **`make closeout` gives you both the bookkeeping and the kernel.**
  `inventory.py` → `gen_shadow.py --harvest` → `inventory.py` →
  `gen_stages.py` → `audit.py` is ~2 min and needs no Coq;
  `theories/Closeout/Closeout.vo` behind it is ~2h20m on 4 cores at `-j3`
  from cold.  Start it EARLY in the background and read while it runs.
  `make closeout-status` is the seconds one.
* **Skipping `gen_shadow.py --harvest` is how a freed shadow ends up still
  sitting in `core_rows.txt`.**  §4v's row freed one the moment it landed;
  `audit.py` prints it if you miss it.
* **Never run `valfam.py` and a full `make -jN` at the same time.**
* CI builds `CloseoutKit.vo`, two example files and a `make all` dry run —
  it does NOT build the ladder boards or the `CB_*` stages.  Green CI is not
  evidence your board compiles.  Build it locally.

**CONSTRAINTS.**  May touch `theories/Checkers/`, `theories/Counters/`,
`theories/Machines/`, `tools/`, `docs/`, `NEXT_SESSION.md`.  **Never edit
`theories/Census/`.**  Commit incrementally; push and open a PR when the
first row moves the count.

**MERGE DISCIPLINE.**  These files are ALL GENERATED and must never be
hand-resolved on a conflict:

    theories/Closeout/CB_*.v, SH_*.v, Closeout.v, CoreRows.v, CloseoutFinal.v,
    BBB4_Theorem.v, the Closeout section of _CoqProject,
    tools/closeout/{core_rows.txt,frozen_map.tsv,frozen_unproven.txt,
                    shadow_rows.tsv}

Instead: `git checkout --theirs` to get a tree, then re-derive with the
five-command sequence above (`make closeout` runs exactly that).  The board
`.v` files are the source of truth and never conflict, because they are
different files.
