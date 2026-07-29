# Wave-30 prompt: close the counters — three PEELS, not three theories

Continue the (4,2) residue reduction in carrino/Coq-BBB4, on branch
`claude/counter-peels-4-2-<yourid>`, cut from `main` (wave-29 and the
wall-bouncer wave are both merged; `main` is current).

## STATE

`make closeout-status`, or `python3 tools/closeout/audit.py`:

    4,901 of the frozen 5,156 settled (95.1%)
    172 core undecided + 83 0RB shadows (the shadows resolve with their cores)

The 172, by blocker:

|   n | blocker | who |
|----:|---|---|
|  70 | `no overflow phase at K=6` | wave-29's bucket, §3 below |
|  51 | `no interior chain` | §1 and §2 below |
|  24 | `no inner family at pow2 j` | §4 |
|  12 | `no boot chain` | — |
|  11 | `no anchor` | the wall-bouncer route just opened this |
|   4 | `no second exit chain` / `no inner interior chain` | — |

**YOUR TASK IS THE 121 IN THE FIRST TWO ROWS.**  They are counters — plain,
legible, John-confirmed counters — and every one of them is blocked by a
framing gap in OUR step language, not by anything the machine does.  Three
gaps, measured and sized.  Nothing below needs new mathematics; two of the
three need no new Coq at all.

## READ FIRST, in this order

* `docs/WAVE29_REGISTER_FINDINGS.md` — **§10 is your task list** (§10a the
  `cycR` gap, §10b the `lift` gap), and §5c/§5d/§5e are §3 below.  §7 is
  do-not-retry.
* `docs/LAPDECIDER.md` — §2 (the step language) and §5 (the search).  You are
  going to add a step, so read §2 twice.
* `theories/Counters/WTape.v` lines 190–260 — `cycR`, `cycLW`, `cycL`.  The
  gap is visible in three lemma statements side by side.
* `theories/Checkers/LapDecider.v` — the `lstep` inductive (l. 169), the
  `sstep` arms for `SCycL n m` (l. 326) and `SCycR n` (l. 349), and the
  soundness cases (l. 541, l. 559).
* `docs/WAVE28_FINDINGS.md` §2 (the PEEL, and why it is always the answer).
* `docs/WAVE16_FINDINGS.md` §§5–6 and `docs/WAVE12_FINDINGS.md` §8 —
  do-not-retry.

Provenance worth knowing: nickdrozd posted 64 machines he was "pretty sure
are all solvable", read off this repo's own published residue map.  52 were in
the 172; the other 12 were already boarded.  43 of the 52 are the
`no interior chain` bucket.  He is right, and §§1–2 say why they were stuck.

## (1) THE `cycR` GAP — the step language is ASYMMETRIC.  17 rows.

`tools/counters/intgap.py` closes the interior branch's symbolic reachable set
under the whole step language.  Over all 51 `no interior chain` core rows
(`tools/counters/intgap51.json`):

    17  cycR-gap      a MISSING PRIMITIVE
     8  lift          §2
    26  unreachable   §5

Look at the three `WTape` lemmas together:

    cycL  : wsteps .. (q, (u,       h, rw)) = Some (q, ([],      h, rw ++ w))
    cycLW : wsteps .. (q, (lw ++ u, h, rw)) = Some (q, (lw,      h, rw ++ w))
    cycR  : wsteps .. (q, ([],      h, u )) = Some (q, (w,       h, []))
                                                   ^^ NO lw, NO rw

`cycL` deposits **past a concrete right window** `rw` — that `rw` is exactly
`SCycL n m`'s `m` — and `cycLW` generalises it on both sides.  `cycR` demands
the left window be EMPTY on entry and `SCycR n` has **no offset parameter at
all**.  There is no `cycRW`.  So a lap that walks the block back RIGHTWARD
past a concrete left prefix cannot be written down, and that is exactly where
these 17 dead-end.  On `1RB---_0LC1RD_0LB1RD_1LB0RD` (`Kp@D`, tail `[S0]`,
far `[S1]` — 200 of 200 anchors, no gaps, interior AND overflow both exactly
`2j + 4`) the search reaches 15 states and stops at

    (StC, left = [S0;S1] concrete, head = S0, right = rep [S0] j ++ [S1])

with the target `(StD, [S0] ++ rep [S0] j ++ [S1], S0, [S1])` — **one `SCycR`
away, past two concrete left cells.**

### Build

1. `theories/Counters/WTape.v`: **`cycRW`**, the mirror of `cycLW`, by the
   same induction.  Get the deposit orientation off `cycLW`'s proof, do not
   guess it: the sides are adjacent-first, so the left deposit prepends.
2. `theories/Checkers/LapDecider.v`: a **NEW constructor** `SCycR2 (n m : nat)`
   — one `sstep` arm mirroring the `SCycL n m` arm, one soundness case
   discharged by `cycRW`.
   **DO NOT change `SCycR`'s arity.**  Every committed board's chain is a
   literal list of `lstep`s closed by `vm_compute`; adding a parameter to an
   existing constructor invalidates all of them.  Adding a constructor does
   not — no existing chain mentions it.
3. `tools/counters/lapcert.py`: mirror the `sstep` arm and offer `SCycR2` from
   `_cyc_candidates` (the mirror of the `SCycL` offer, including the `m`
   enumeration).
4. `emit_lapcert.py --list` over the 51, then over the WHOLE residue.

### Acceptance

* `Print Assumptions` on the new `WTape`/`LapDecider` lemmas: **closed under
  the global context**.  `LapDecider` is the trusted checker; it does not get
  an axiom.
* **Every committed board re-renders BYTE-IDENTICAL** and recompiles.  This is
  the non-negotiable regression for a checker change: emit into a scratch dir
  and `diff` against `theories/Machines/`.  A single changed byte means the
  candidate ordering shifted and you must make the new step the LAST candidate
  offered.
* Expect ~17 boards.  If you get 0, the deposit orientation in `cycRW` is
  mirrored wrong — check it against the dead-end state above before touching
  the search.

## (2) THE `lift` GAP — split × lift is not wired.  8 rows.  No new Coq.

`emit_lapcert.derive` derives the SPLIT interior chains (`Z0 -> Z1` at
`j = 0`, `P0 -> P1` at `j = S j'`) **exactly only**: the `lift=True` last
resort is reached solely on the ONE-chain path, and `GLUE_SPLIT` proves exact
`cden` equalities.  Measured on 8 rows, both split chains derive up to `lift`
— e.g. `1RB0RB_1LC1RA_0LC0LD_0RA0RD` under `Alph_000_100_1@A`, tail `[S0]`,
far `[]`: `j = 0` cost 4, `j = S j'` cost `10j' + 14`, both landing one
written blank past the anchor.

Everything downstream exists.  Wave-16 wired the lift route for the ONE-chain
mode: `islack`, `GLUE_ONE_LIFT`, `NQH_CLOSE_LIFT`, `@VISCONC@`, `@VISHI@`,
`@LAPICASE@`, and `LapCertGlueLift`'s `glue_neverqh_lift` / `vis_via_ovf_lift`.
The job is to make `islack` legal when `mode == 'split'`: a `GLUE_SPLIT_LIFT`
whose two halves are `lift` equalities, `lapi_` returning `exists n c'`, and
the lift closer.

Expect ~8 boards, and re-check that no `mode == 'one'` board changes route.

## (3) THE DOUBLE PEEL — the 70 `no overflow phase` rows.  66 stop at ONE gate.

Wave-29 §5c established what these are, and John confirmed it: **plain
counters** whose anchor family alternates its FRAME (state, tail, far) by
octave parity.  `tools/counters/tailcert.py` reads a gap-free two-form family
on **95 of the 113** rows in the original bucket, and derives three of the
four branches on the exemplar.  Then 66 of them stop at one gate:

    no interior j=0 chain

and it is NOT §1's gap.  On `0RB1LA_0LC1RD_1LD0RB_1RB0LA` (`Ip@A`, tail
`[S0;S1;S0]`) the `j = 0` frame is

    Z0 = (StA, left = [S1;S0] CONCRETE, head = S0, right = [])
    reachable = 2 states, 1 dead end, target in no form

The lap leaves the two concrete cells of `sS` immediately and runs into the
OPAQUE left tail `XL = E q0 ++ tail`.  The `j = 0` frame is simply **too
SHORT**: the lap needs cells of `E q0`, which the frame does not name.

So peel **one more digit**.  Split the interior branch three ways instead of
two — `j = 0` with `q0`'s low digit `0`, `j = 0` with it `1`, and `j = S j'` —
giving concrete prefixes `sS ++ uD` and `sS ++ uS`.  That is the existing
split device one level deeper, and it is the seventh consecutive wave in which
one more peeled unit copy was the whole difference.  Do this in `tailcert.py`
first (it has the reader and the differential validation already), then check
whether the same double peel also moves any of §5's 26.

Expect the largest single batch of the wave if it lands.  MEASURE FIRST: run
the three-way split's chains through `derive_chain` on ten rows before writing
one line of template.

## (4) The 24 `no inner family at pow2 j` — a BOUNDED inner carrier

Wave-29 §5d: on the exponential arm of the two-form family the inner counter
runs a **PARTIAL octave**, e.g. `2^(K+1)+4 .. 2^(K+1)+2^K-1`, not to the
all-ones fill.  `nestcert.families` wants a full `2^(K-1)..2^K-1`,
`derive_offset` wants `2^(K+1)+c..2^(K+2)-1`, and
`NestedLapLift.inner_to_fill_lift` runs to `fill v0`.  None covers "from `v0`
to `v0 + 2^k - 1`".

The missing piece is one lemma beside `inner_to_fill_lift`: the same
well-founded induction on `JpCounter.tovf`, stopped at a measured endpoint
instead of at the fill.  Take it only if §§1–3 land early.

## (5) The 26 `unreachable` — MEASURE, do not build

`intgap.py` probes only the FIRST anchor family `emit_lapcert.anchors` offers.
Before designing anything for these, extend it to probe EVERY anchor family
(both mirrors), plus `restscan`'s tolerant keys and `tailcert.two_form`'s
parity-split keys, and report whether the target is reachable at ANY of them.
Four of wave-29's seven sub-classes dissolved on exactly this move.

## NON-NEGOTIABLE

* Never edit `theories/Census/`.  `python3 tools/census_cache.py --check` must
  stay **MATCH**.
* A board counts only when its file compiles AND
  `Print Assumptions nqh_<ID>` shows `functional_extensionality_dep` only.
* `SkipGlue`, `NestedLapLift`, `LapDecider`, `LapCertGlue`, `LapGlue*`,
  `RegGlue`, `WTape` are axiom-free or funext-only — **keep them that way**.
  §1 touches two of them; prove, do not assume.
* Everything under `tools/` is UNTRUSTED; the kernel re-checks every board.
* **Do not add a row to `alphabets_gen.ENCROWS`/`ENCS`** without checking that
  `reg113.json`, `quad35.json` and `jexc80.json` still reproduce — `ENCS` is
  the search space of every scan.  Wave-29 nearly broke this; register a
  private `ENCDATA` row instead (see `tailcert.py`'s `Alph_01_11_11`).

## ENV

`apt-get install -y coq` (8.18.0), then
`coq_makefile -f _CoqProject -o Makefile.coq`.  Build only what you need —
`make -f Makefile.coq theories/Checkers/LapDecider.vo theories/Counters/WTape.vo
theories/Counters/LapCertGlueLift.vo theories/Census/TNF_QH.vo theories/Mirror.vo`
is ~40 s.  **DO NOT run `make all`.**  Compile a board with
`coqc -native-compiler no -Q theories BBB4 <file>`.

Note for §1: a `LapDecider` change means every board that imports it must
recompile.  Do that ONCE, at the end, over the boards you touched plus a
sample of 30 committed ones — not `make all`.

## DO NOT RETRY (measured)

* **Widening `derive_chain`'s `maxdepth`/`nmax` on the `no interior chain`
  bucket.**  Measured: the reachable set is CLOSED at 7–89 states.  The search
  is not truncating; the language is missing a step.
* **Changing `SCycR`'s arity** rather than adding a constructor — invalidates
  every committed chain literal.
* **Any reading of the wave-29 register bucket that has a WALL in it.**  Two
  were measured (wall in the tail, wall on the far side) and both are
  artifacts: the machine is a plain counter and the "wall" is its own leading
  zero-pairs.  A reading whose laps come out exponential on a bucket whose
  neighbours are affine is a reading to distrust.
* **Decoding the whole tape as one word** (`rev(r) ++ [h] ++ l`, both
  orientations, all alphabets, every tail split, 0..6-cell drops) — tops out
  at 168/255 coverage, WAVE28 §4.
* **Fitting a virtual anchor's laps with one affine law when the frame has
  period P** — WAVE29 §7.
* **`nestcert.families` on a phase whose inner rests DESCEND** — the 4 `Jp`
  gray-code rows; needs a descending carrier, not a wider search.
* Standing: WAVE29 §7, WAVE28 §4, WAVE27 §5, WAVE26 §6, WAVE25 §6, WAVE24 §7,
  WAVE18 §5, WAVE16 §5.

## STANDING MOVES

* **PEEL BEFORE ANYTHING ELSE.**  Seven waves.  §§1 and 3 are both peels; §1
  is a peel the step language cannot express and §3 is one it can.
* **READ THE LANDING OFF THE MACHINE instead of assuming its padding.**  Dump
  the configuration when a structural gate fires, before widening any search.
* **MEASURE THE BUCKET — AND THE READER — BEFORE DESIGNING FOR IT.**  Four of
  wave-29's seven sub-classes were reader caps (`FARMAX = 8`, `TAILMAX = 2`,
  an exceptional lowest octave, a misplaced wall), not machine behaviour.
* **After ANY change to `derive` or to the step language, re-run
  `restscan.py --emit`, `regcert.py` and `tailcert.py` over the open buckets.**
  Each is a DIFFERENT gate and it costs nothing but the run.
* **WHEN STUCK ON A CLASS, ask John with an ABSOLUTE-COORDINATE TAPE DUMP**
  (`tools/counters/spacetime.py --rests --mark --lo/--hi` FIXED — without
  fixed columns the frame shifts row to row and the dump is unreadable).
  Hand-inspection is **35-for-35** across waves 8–29; his read of
  `0RB0RC_1LC1RB_0LD1RA_1RC1LD` in wave-29 retired a 99-row class in one
  sentence.  Ask EARLY, ask with a TAPE, ask about a CLASS not a machine.

## PER BATCH

    python3 tools/closeout/inventory.py && python3 tools/closeout/gen_stages.py \
      && python3 tools/closeout/audit.py && python3 tools/census_cache.py --check
    git push -u origin <branch>          # retry on network error

Merge conflicts with `main` are routine and always in GENERATED tables
(`_CoqProject`, `theories/Closeout/*`, `tools/closeout/frozen_unproven.txt`):
take main's side on every one, then re-run the four commands above.

Write `docs/WAVE30_FINDINGS.md`.

## DEFERRED TO STABLE HARDWARE

Census fold-in, `CloseoutFinal.v`, the champion
`1RB1LD_1RC1RB_1LC1LA_0RC0RD`, and `0RB1LC_1LC0LC_0RD1LA_1RD1RB`.
