# Closing out the counters — findings, and the route to done

_Written 2026-07-25.  The consolidated record of the big-block-RepWL / residue
session: what the counter population actually is, what boards it onto the board
today, what the remaining wall is (measured, not guessed), and the ranked path
through it.  Read this before touching the counter route again.  Companions:
`COUNTER_EMITTER_WAVE8.md` (the emitter's design), `COUNTER_CODEGEN_BLOCKERS.md`
(the emitter measurement), `RESIDUE_708_DIAGNOSIS.md` (the residue taxonomy),
`REPWL_BIGBLOCK_WAVE8.md` (the RepWL track), `MACHINE_NOTES_WAVE8.md` (the
hand-inspection log)._

## 0. The one-sentence reason counters resist everything generic

A binary counter's tape word **is** the base-2 expansion of `n`, so it differs
on *every single increment*: no finite block set, n-gram set, or window ever
closes, and every closure method instead manufactures a spurious carry-free
cycle.  mxdys states the complementary condition exactly — *"my inductive
decider can only decide a TM when it can model the forward behavior exactly"* —
and that is why an exact per-lap model decides this whole population while every
lossy abstraction bounces off.

**Measured confirmation.** A wider-parameter RepWL probe over all 708 residue
machines (`L ≤ 40`, `T ≤ 4`, warmup, 12 000-node cap) returned
**NOCLOSE 706 / CAUGHT 2 / CLOSED-BUT-NO-CERTIFICATE 0**.  Zero of the third
kind is the load-bearing number: the measure/rank vocabulary is *never* the
bottleneck — finitization itself is.  A richer measure set cannot help.

## 1. Scoreboard

| population | count | status |
|---|---|---|
| counter core (`wave8_fingerprints_v2.jsonl`) | 2,480 | |
| ├ recognized `cls=COUNTER` | 1,738 | growth **L 658** / **R 1,080** |
| └ `cls=NOFIT` | 742 | = the residue of `RESIDUE_708_DIAGNOSIS.md` |
| boarded `ILC_*.v` (L, Jp route) | 61 | kernel-verified |
| boarded `ILCM_*.v` (mirror/R route) | 99 | kernel-verified |
| **growth=L still to board** | **597** | 1 derives today (§4) |
| boarded this session (RepWL + TCycler) | **44** | 36 `RWL8_*` + 8 `TCyc8_*` |
| genuinely open in the 708 | **0** | every machine has a known route |

Boards landed this session, all `coqc -native-compiler no -Q theories BBB4`
compiled with `Print Assumptions` = `functional_extensionality_dep` only, and
all through **existing** checkers (zero new soundness surface):

* **36 `RWL8_*.v`** — periodic bouncers via `rw_check_neverqh_sound`, block size
  matched to the tape period, `L` 9…30, `T=2` (heaviest closure 12 029 nodes,
  160 s).  These existed because `COUNTER_EMITTER_WAVE8.md` §4b declared "RepWL
  DEAD" from a sweep capped at `L ≤ 4`.
* **8 `TCyc8_*.v`** — genuine translated cyclers via `tcycler_check_neverqh_sound`
  (+ `_sound_L` through `Mirror`), periods 67…2215.  They sat in the residue
  because no TCycler pass was ever run over it and their periods exceed the
  census light tier's cycle-search budget.

## 2. What the route actually needs: the anchor

Everything hinges on one object.  An **anchor** is a recurring configuration
whose tape *is* the counter's value, identified by a fixed predicate.  Worked
example, `0RB---_0LC1RB_1LA1LD_1LC0RB` (the one machine of the 597 that derives
today; predicate = *state B, blank head, far side entirely blank*):

```
t=  5   left = 1          head=0  right=blank   ->  p=1
t= 13   left = 111        head=0  right=blank   ->  p=2
t= 17   left = 101        head=0  right=blank   ->  p=3
t= 29   left = 11111      head=0  right=blank   ->  p=4
t= 61   left = 1111111    head=0  right=blank   ->  p=8
```

In Coq that is one line — `Cc p := (StB, (Jp p ++ [S0], S0, []))` — and
`glue_neverqh` then needs only three ingredients, all keyed off it:

1. **lap**: `Cc p → Cc (p+1)`,
2. **boot**: blank tape → `Cc p0`,
3. **visit**: every state fires within one lap (so none goes quiet).

Induction on `p` covers the rest forever.  Note the step gaps above —
4, 8, 4, 12, 4, 8, 4, 16: the carry ripple, longest at the 7→8 overflow.  That
variability is why the lap lemma splits on `cview` into an interior-carry branch
and an overflow branch.

## 3. The encoding zoo (measured)

A residue counter is a binary counter in one of a small family of encodings.
`tools/kcopy_classify.py` measures which, per machine, by decoding anchored tape
snapshots and requiring the decoded integers to be **consecutive** — then
re-confirming in a **late window at large values** (a decode that works at
value 6 but breaks at 10³ is not a decode).  Output for 1,280 machines is
committed as `tools/counter_encodings.tsv` (stride, offset, data position,
inversion, wall side, anchor state).

| family | meaning |
|---|---|
| `KCOPY<k>` | each bit stored in `k` **identical copies** (`k=3` ⇒ "3× wider counter") |
| `SEP<k>` | one data cell per `k`-cell block, the rest a **constant separator** (value 0 **or** 1) |
| `…i` | data bit **inverted** (0 = set) ⇒ the decoded value **DESCENDS**; this is `JpCounter.v`'s complement encoding |

Sweep over 1,323 open/unboarded machines: **1,280 (96 %) decode as counters**,
1,224 of them late-confirmed.

```
  685 SEP2      375 KCOPY1     126 SEP2i      42 MIXED      20 KCOPY2
   15 SEP2i*     14 KCOPY1*     10 SEP2*      10 SEP3        9 SEP4*
    6 KCOPY2i     5 KCOPY1i*     2 KCOPY2*     1 SEP4          (* = early-only)
```

stride distribution `k`: **1 → 394, 2 → 864, 3 → 12, 4 → 10**;
**153 machines are in an inverted encoding.**

So stride ≥ 2 is ~55 % of the population and inversion ~12 % — not the "~2 %
exotic tail" the emitter design assumed.

**Two structural refinements found by hand-inspection, both load-bearing for a
lap proof:**

* **Packed frontier group.** `1RB0LB_1LC1RD_0RD0LC_1RA1LD` (and its sibling) is
  stride-3 in the body but its **two most significant bits are adjacent, with no
  separator**: the field is `[b0 0 0][b1 0 0] … [b_{n-2} b_{n-1}]`.  A decoder
  that stops at the first broken separator reads the body correctly and
  **silently drops the top two bits** — harmless for routing, fatal for a lap
  proof, where the anchor word must carry the packed pair as its own case.
* **Slot-advancing field.** `0RB1LC_1LC0LC_0RD1LA_1RD1RB` is a counter (inverted,
  1-separators, no 1-block wall, left boundary pinned at the origin) whose field
  **advances by one cell as it counts**, so no fixed `(stride, offset)` read
  works.  Reading each 2-cell slot as a three-state digit (`11`→0, `01`/`10`→1,
  `00`→2) gives a clean arithmetic progression 2,4,6,8,10,12,14.  Open question:
  base-3 digit, or binary digit whose read position shifts per carry?  That
  decides whether the emitter needs a new digit type or just an advancing anchor
  offset.  **This is the only machine of the 708 still unread.**

## 4. Emitter status, measured

`emit_interleave.py --list` over all 597 unboarded growth=L counters
(derive+validate only): **1 / 597 derive.**

| count | share | failure |
|---|---|---|
| 378 | 63 % | `no fixed anchor tail up to length 6` |
| 133 | 22 % | `only N anchor snapshots` |
| 80 | 13 % | `no interior skeleton fits the raw lap` |
| 3 | — | `no overflow stop fits the raw lap` |
| 2 | — | `no lap closure` |

**85 % fail before the lap is ever considered.**  The anchor predicate is
hardcoded as *blank head + blank far side*, and the field must be literally a
`Jp` word.

Adding the `Ip` encoding (already present in `ENC`; only `process()` hardcoded
`'Jp'` — now landed as `enc_table`) shifts the profile without moving the pass
count:

| stage | Jp only | Jp + Ip |
|---|---|---|
| no fixed anchor tail | 378 | **306** (−72) |
| only N anchor snapshots | 133 | 133 |
| no interior skeleton fits | 80 | 109 (+29) |
| no overflow stop fits | 3 | **40** (+37) |
| no lap closure | 2 | 8 (+6) |
| **derives** | **1** | **1** |

**72 machines have a perfectly good `Ip` anchor and die in the lap skeleton.**
Verified by hand on `0RB---_1LA1RC_0LD0RB_1RB1LD`: state C, head blank, far side
blank, left list exactly `Ip(p) ++ [S1]` for consecutive p = 64, 65, 66, …
(`enc=Ip, tail=[1,0], p0=1`); its real blocker is `no overflow stop fits`.

Emission stays **gated to `Jp`**, because the Coq template hardcodes
`Jp`/`cview_*_J`: an `Ip`-anchored machine would otherwise get windows derived
under `Ip` written against a `Jp` anchor.  The kernel would reject it, but
emitting a known-broken board is pointless noise.

**Independently confirmed:** the sibling session's `tools/counters/emit_qh.py`
reaches the same wall and hard-codes
`"encoding %s unsupported (this emitter is Jp-only)"` (line 475).  Two sessions,
same conclusion.

## 5. Dead ends — measured, do NOT retry

| lever | grid measured | result |
|---|---|---|
| RepWL on the counter core | `(L,T) ∈ {2,3,4}²`, `t=0` (§4b) | 0/60 — **but this is `L ≤ 4`**; at `L` 9…30 it boards 36 machines. A "dead" verdict must record its grid. |
| widen the emitter's anchor search | tail cap 6→24, scan 200k→3M steps, `nmax` 60→240, snapshot floor 12→8 | **0 gain**, identical profile |
| add the `Ip` encoding alone | all 597 | anchors +72, **0 new derives** |
| RepWL measure vocabulary | `L ≤ 40`, `T ≤ 4` over 708 | 0 finitize-but-no-cert ⇒ vocabulary is never the bottleneck |
| wide-vocabulary NGramHist | counter core | 0/572 (pre-existing) |
| determinism "hammer" | `k ≤ 12` | 0/300 refuted (pre-existing) |

## 5b. Why every parameter widening failed: the template has MORE structure than the laps

Three independent widenings each gained **exactly zero** derives (anchor caps,
the `Ip` encoding, the ripple unit length `ulen (2,) -> (2,1,3,4)`).  The reason
is structural and is now measured.  `tools/counters/lapshape.py` traces one
interior lap from each machine's derived anchor and segments it into monotone
head-direction phases, signing each phase `(dir, state_in, state_out)`:

| | |
|---|---|
| machines with a derivable anchor **and** traceable lap | **243** of 597 |
| distinct lap shapes | **52** |
| phase-count distribution | 2 → 47, **3 → 83, 4 → 88**, 5 → 7, 6 → 11, 7 → 4, 8 → 3 |

**Most laps have only 2-4 phases, while the emitted template is a fixed
six-window chain** (P1, RIP, STPI/STPO, RET, FIN).  A 3-phase lap cannot be
matched to a 6-window skeleton at *any* setting of its constants, which is
exactly why widening constants returns 0 every time.

The shapes are strongly concentrated (`tools/counter_lapshapes.tsv`):

```
  31  -CC|+CD|-DC|+CD        9  -BB|+BD|-DB|+BD
  29  +AB|-BA|+AB            9  -CA|+AB
  28  -DD|+DC|-CD|+DC        8  +CD|-DA|+AB
  25  -DA|+AB                6  +DC|-CD|+DC
  14  +BC|-CB|+BC            6  +CD|-DC|+CD
  13  -CC|+CB|-BC|+CB       ...  (52 shapes total)
  12  +CB|-BC|+CB
```

**Top 4 shapes = 113 machines; top 12 = 190.**  So the unit of work is *one
template per lap shape*, and the population is small enough to enumerate.

Nothing in the kernel forces six windows: the Coq side composes an arbitrary
chain of `wsteps` unit lemmas via `csteps_chain`, framed by `wsteps_frame` /
`wsteps_frame_l` / `cycL` / `cycR`, and `glue_neverqh` takes the assembled lap as
a black box.  The six-window count lives **only** in the emitter's template
string and its skeleton search.

## 6. The ranked path to done

1. **Make the window chain phase-generic** (§5b).  Replace the fixed six-window
   skeleton with the phase list `lapshape.py` already extracts: emit one
   `wsteps` unit lemma per discovered phase and frame it by that phase's shape
   (plain run ⇒ `wsteps_frame`; repeated cycle ⇒ `cycL`/`cycR`).  This is the
   single change that unlocks all 243 traceable machines instead of one shape at
   a time, and it needs no new Coq theory — only the emitter's template string
   and skeleton search, since `csteps_chain` already composes arbitrary chains.
   Validate against the existing `Interleave_TGT.v` shape first (it must
   reproduce that board unchanged), then the 31-machine shape 1.
   *Fallback if that proves hard:* hand-author one template for shape 1
   (31 machines), clone, then shapes 2-4 (another 82).
2. **`Ip` template variant — substitutions only, no new theory.** `cview` is
   defined once in `MonoCounter.v` (encoding-independent); `tovf` is a fixpoint
   on `positive` alone; `pair_rot : forall (x y : Sym) j, rep [x;y] j ++ [x] =
   x :: rep [y;x] j` is **generic in its symbols**; `ILCounter.v` already
   supplies `Ip`, `Ip_head`, `cview_some_I`, `cview_none_I`, `pair_fold`.  So the
   emitted template's deltas are `Jp`→`Ip` and `cview_*_J`→`cview_*_I` at the
   three `lap_exact` rewrite sites.  Build it *after* step 1, so it has
   something to emit; then lift the `enc != 'Jp'` gate.
3. **Widen the anchor family to a non-blank far side.** 133 machines report
   `only N anchor snapshots` because they hold their counter against a **wall**
   — hand-confirmed, and `kcopy_classify.py` finds their anchors fine (e.g.
   `1RB0LB_1LA0LC_0LB0RD_1RD0RC`: `001` wall, anchor state C, values
   3009…3014).  `glue_neverqh` already accepts an arbitrary `Cc p`, so this is
   emitter + template work with **zero new soundness surface**.
4. **Widen the encoding table.** 306 machines decode under neither `Jp` nor
   `Ip`.  `tools/counter_encodings.tsv` already names each one's stride, offset,
   data position and inversion — that table is the input.  Add the packed
   frontier group (§3) as a template parameter while here.
5. **The 1,080 growth=R machines** ride the mirror route (`emit_mirror.py`,
   99 boarded) around the same lap; every fix above transfers.
6. **Tail work, already scoped elsewhere:** 15 √-growth wave/bounce counters
   (`WaveCounter`/`BounceCounter` templates, per-machine); the champion
   `1RB1LD_1RC1RB_1LC1LA_0RC0RD` (blanks at step 32,779,478 then spins out —
   needs `exists B, QHBound B` plus a heavy prefix on stable hardware); the
   slot-advancing machine (§3).

## 7. Non-negotiables (unchanged, restated because they held all session)

* Everything under `tools/` is **UNTRUSTED**; the kernel re-checks every board.
  A wrong certificate, window, or constant fails to **typecheck** — it can never
  mis-prove.
* `Print Assumptions` = `functional_extensionality_dep` only on every new board.
* **Never** touch `theories/Census/`; `python3 tools/census_cache.py --check`
  stays `MATCH` (verified before and after every commit this session).
* `coqc -native-compiler no` is sufficient and is the blessed container path;
  apt Coq 8.18.0 works — no opam bootstrap is needed for board work.
* A "lever is dead" claim must record the **parameter grid** it was measured on.

## 8. Process finding: hand-inspection beat the automation 6 times

Every class that looked hard was a tooling or parameter gap, and each was
exposed by a human reading **one** machine on bbchallenge:

| # | machine | human read | what it overturned |
|---|---|---|---|
| 1 | `1RB0LB_0RC1RD_1LC0LA_0RA0RB` | "like a game of life doing `1110110110`" | RepWL "dead" ⇒ 36 boards at `L` 9…30 |
| 2 | `1RB1RC_1LA1RA_0RC1LD_1LB0LD` | "each bit has 3 copies, 3× wider" | stride ≠ 1 is common (`KCOPY3`; +9 cells/8× measured) |
| 3 | `1RB0LD_1LC0RD_0LC1LD_0RB1RA` | "counter with 0 between bits" | killed a fabricated "value lives in gap lengths" subclass (~120 machines) |
| 4 | `1RB1RC_0LB1LA_0RD1RC_1LB0RC` | "just a counter, same structure" | confirmed the separator axis |
| 5 | `1RB0LB_1LA0LC_0LB0RD_1RD0RC` | "wall at 1, counts leftwards inverted, 1 between bits" | the **inverted** family ⇒ cracked 6 of 7 stragglers |
| 6 | `1RB0LB_1LC1RD_0RB0LC_1RA1LD` | "2 zeros between bits, no space between the 2 MSBs" | the **packed frontier group** (a lap-proof requirement) |

The corrections landed on *my* analysis each time, and two of my own errors are
worth recording because they are reusable:

* **popcount oscillates on a counter** (7 = `111` → 3 ones, 8 = `1000` → 1), so
  "ones frozen while a 0-gap grows" is exactly what a counter looks like — it is
  **not** evidence the value lives in the gaps.  I built a whole subclass on it.
* `kcopy_classify`'s `SEP2` records stride and inversion, **not the separator
  value** (which it infers).  I read `SEP2` as "0-separator", concluded a new
  0-separator Coq encoding was needed, and was wrong: those machines separate
  with 1s, i.e. they are `Ip`, which the repo already had.

Practical consequence: **when a class looks hard, print a few machine strings and
ask a human before building anything.**

## 9. Reproduce

```sh
# environment: apt coq 8.18.0 suffices; native off. Census untouched.
python3 tools/counters/repwl_bigblock.py \
    tools/counters/wave8_unrecognized.txt /tmp/hits.tsv      # 34 of 742
python3 tools/gen_rwl8_certs.py /tmp/hits.tsv                # -> RWL8_*.v
python3 tools/kcopy_classify.py < machines.txt                # encoding per machine
python3 tools/counters/emit_interleave.py \
    --fp tools/counters/wave8_fingerprints_v2.jsonl --list L.txt   # 1/597 derives
for f in theories/Machines/RWL8_*.v theories/Machines/TCyc8_*.v; do
  coqc -native-compiler no -Q theories BBB4 "$f"
done
python3 tools/census_cache.py --check                         # must print MATCH
```

Manifests: `tools/rwl8_manifest.tsv` (36 RepWL boards, with `L`/`T`/contexts),
`tools/tcyc8_manifest.tsv` (8 TCycler boards, with side/anchor/period/reach),
`tools/counter_encodings.tsv` (1,280 machines' measured encodings/anchors).

## 10. Next session — ordered plan

**Step 0 — merge PR #29.** Clean, `main` already merged in, 11 commits, nothing
pending.  (CI on this repo does not run — GitHub billing — so every board here
was verified locally: `coqc -native-compiler no` + `Print Assumptions`, and
`census_cache.py --check` = MATCH before and after each commit.)

**Accounting note that governs the order.** The 44 boards from this session are
Class-1 work only: they are standalone `NeverQuasiHaltsSt` theorems and are
**not** in `proven_map.tsv` / `Proven_*.v`, so **`D_census` has not dropped by
44**.  Folding them in means regenerating `Proven_*`/`Deferred_*` under
`theories/Census/`, which invalidates `CENSUS_VO_HASH` on purpose and forces
`make census-verify` on stable hardware (PLAYBOOK Class 2).  So do **not** pay
the re-walk for 44 machines — batch the counter boards first and pay it once.

**Step 1 — the milestone: hand-author ONE board for lap shape 1.**
Shape `-CC|+CD|-DC|+CD`, 4 phases, **31 machines**
(`tools/counter_lapshapes.tsv`, `shape_rank = 1`).  Clone
`theories/Machines/Counters/Interleave_TGT.v` structurally but with a **4**-window
chain instead of 6: one `wsteps … = Some …` unit lemma per phase, each framed by
its shape (plain run ⇒ `wsteps_frame` / `wsteps_frame_l`; repeated cycle ⇒
`cycL` / `cycR`), chained by `csteps_chain` across the two `cview` branches, then
`glue_neverqh tm Cc p0 boot lap vis`.
*Checkpoint:* one new counter board compiles with
`Print Assumptions` = `functional_extensionality_dep` only.
*Why this first:* it is the same "template by example" move that produced
`Interleave_TGT` in the first place, it produces a board immediately, and it
learns the rep-algebra junction for a non-6-window chain empirically instead of
guessing it inside a generic emitter.

**Step 2 — clone shape 1 across its 31 machines.**  Fork `emit_interleave.py`,
substituting the shape-1 window chain; the per-machine anchor parameters are
already derived (`enc`, `edge`, `tail`, `p0`) and `tools/counter_encodings.tsv`
carries the encoding.  *Checkpoint:* 31 boards, each kernel-verified.

**Step 3 — shapes 2-4 (+82 machines):** `+AB|-BA|+AB` (29), `-DD|+DC|-CD|+DC`
(28), `-DA|+AB` (25).  Three and two phases respectively — after step 2 the
pattern "phase list ⇒ window chain" should be concrete enough to make the
emitter **phase-generic** (§5b) rather than one template per shape, which then
covers all 243 traceable machines.

**Step 4 — the two remaining populations,** in this order because both are moot
until a lap can be fitted: the anchor family with a **non-blank far side**
(133 machines held against a wall; `glue_neverqh` already accepts an arbitrary
`Cc p`, so zero new soundness surface), then **more encodings** (306 machines;
`counter_encodings.tsv` is the input).  The 1,080 growth=R machines ride the
mirror route around the same lap, so every fix transfers.

**Step 5 — Class 2, on stable hardware, paid ONCE:** add every new board to
`proven_map.tsv` (`gen_proven.py`), regen `Deferred_*`
(`gen_deferred.py` / `regen_residue.py`), `make census-verify`,
confirm `Print Assumptions census_decided` is
`functional_extensionality_dep` only, then `census_cache.py --update` and commit
the new `.vo` + hash.  Only this step lowers `D_census`.

**Queued, independent of the above**

* **Resume the paused classifier sweep** — `tools/kcopy_classify.py` covered
  1,323 of 2,713 open machines before it was stopped to free CPU; it is
  resumable and worth ~15 min if a complete encoding table is wanted.  Purely
  diagnostic.
* **One machine still unread:** `0RB1LC_1LC0LC_0RD1LA_1RD1RB` (§3, slot-advancing
  field).  The question for a human is whether the slot is a **base-3 digit** or
  a **binary digit whose read position shifts per carry** — that decides whether
  the emitter needs a new digit type or just an advancing anchor offset.
* **The champion** `1RB1LD_1RC1RB_1LC1LA_0RC0RD`: blanks at step 32,779,478 then
  spins out.  Needs `boarded` generalized to `exists B, QHBound B` (structural,
  already identified) plus a 32.8M-step prefix — one long `native_compute`, i.e.
  stable hardware, not this container.
* **Do not re-run** the levers in §5: three parameter widenings and two
  existing-decider screens over the recognized counters all returned exactly
  zero, each with its grid recorded.
