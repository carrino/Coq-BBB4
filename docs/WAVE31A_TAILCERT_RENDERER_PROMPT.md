# Wave-31a prompt: BOARD THE TWELVE — build `tailcert`'s missing renderer

Continue the (4,2) residue reduction in `carrino/Coq-BBB4`, on branch
`claude/tailcert-renderer-4-2-<yourid>`, cut from `main`.

**This prompt supersedes item (0) of `docs/WAVE31_PROMPT.md` and is ahead of
everything else in that document.**  Take this first.  It needs no new
mathematics, no new lemma, and no new measurement.

## STATE

    4,916 of the frozen 5,156 settled (95.3%)
    162 core undecided + 78 0RB shadows (the shadows resolve with their cores)

## THE ONE-LINE JOB

`tools/counters/tailcert.py` derives a complete, differentially-validated
certificate for **12 of the 162 open core rows** and cannot write a single one of
them down, because it has no renderer.

    python3 tools/counters/tailcert.py --list tools/closeout/core_rows.txt
    => 12 / 162 fully derived

The 12 are committed as `tools/counters/tailcert_derived12.txt`:

| n | alphabet | overflow arms | validation |
|--:|---|---|---|
| **6** | `Alph_00_01_1` | **FLAT** (`kind == 'flat'`, 0 nested overflows) | 192 anchors |
| 6 | `Alph_10_11_11` | nested (4 nested overflows, 56 inner laps) | 192 anchors |

`tailcert`'s docstring advertises `--emit`; `main()` never implemented it.
`PREFIX = 'REG'`, `OUTDIR`, and the imports of `coqc` and `mirrorize` are all in
the file, unused.  The route's last mile was never built.

**Take the 6 FLAT rows first.**  They have no nesting anywhere.

## READ FIRST, in this order

* `tools/counters/regcert.py` — `render` (l. 1100), `process` (l. 1209),
  `_arm_reps` (l. 1061), `_fill` (l. 1088), and the templates `INT_DEFS`,
  `INT_GLUE`, `INT_DISPATCH`, `OVF_GLUE`.  **This is the renderer you are
  adapting.**  Read `render` twice before writing anything.
* Any committed `REG_*` board in `theories/Machines/Counters/` — the target
  shape, already compiling and funext-only.
* `tools/counters/tailcert.py` — `_derive` (l. 256), `validate` (l. 351),
  `visits` (l. 400), `boot` (l. 417).  These produce everything the renderer
  consumes; do not change them except as §4 allows.
* `theories/Counters/RegGlue.v` — `podd` and its three lemmas.  Axiom-free,
  already in the tree, and it is what makes an octave-parity board statable.
* `docs/WAVE29_REGISTER_FINDINGS.md` §2 — why the piecewise `Cc` works and what
  each branch has to prove.
* `docs/WAVE30_FINDINGS.md` §6b–§6d — the reader fix these 12 rows depend on,
  and why the interior gate is now empty.

## THE BOARD, SPECIFIED

The two-form board is **`regcert`'s board MINUS the register arms, PLUS a split
interior**.  That is the whole difference, and it is worth stating precisely
because it makes the job smaller than it looks.

    Cc p = if podd p then (q1, E p ++ t1, S0, f1)
                     else (q0, E p ++ t0, S0, f0)

with `RegGlue.podd` the octave parity.

### What you DELETE from `regcert`'s renderer

**All of it.**  `VIRT_HEAD`, `VIRT_FLAT_DEFS`, `VIRT_FLAT_GLUE`,
`VIRT_NEST_CIN`, `VIRT_NEST_DEFS`, `VIRT_NEST_GLUE`, `IEPOW`, `lapvcases`,
`virt_@ID@`, `frmv`, and every `SkipGlue` import.

A `two_form` family is **gap-free by construction** — that is the acceptance
test in `two_form`, and it is why `tailcert` exists — so there are no virtual
anchors to fence and no register mark to move.  Confirmed on the exemplar:
`D` has no `vlap` key at all.  `SkipGlue` is not needed by this route.

### What you ADD

The interior branch is a **SPLIT per octave parity** — four chains, where
`regcert` has one per parity:

    D['ints'][b] = {Z0, Z1, chz, cz,      # j = 0,      concrete
                    P0, P1, chp, cp}      # j = S j',   one unit peeled

`emit_lapcert.GLUE_SPLIT` is the proof shape for each half (`gz_` at
`cview p = (0, Some q0)`, `gp_` at `cview p = (S j, Some q0)`, then `lapi_`
dispatching on `destruct j`).  What is new is that there are TWO of those, one
per parity, and the outer dispatch is on `podd p` — so the structure is

    gz0_ gp0_ lapi0_        (parity 0)
    gz1_ gp1_ lapi1_        (parity 1)
    lapi_  := destruct (podd p) -> lapi1_ | lapi0_

Copy `regcert`'s `INT_DISPATCH` for that outer step; it already does exactly this
dispatch for its one-chain interior.

### What you KEEP unchanged

The overflow arm.  `regcert`'s `OVF_GLUE` already handles an overflow that
**crosses parities** — that is what `RegGlue.podd_succ_fill` is for ("an overflow
increment crosses into the next octave, so the frame flips").  `tailcert` states
it the same way:

    B0 = (st[b],  (uS, uS, 1, 0, soS ++ tl[b]),  S0, far[b])
    B1 = (st[nb], ((), uD, 1, 2, soD ++ tl[nb]), S0, far[nb])

destination state `st[nb]`, count `1*j+2`, source PEELED.  **Do not "fix" this
framing.**  It is exactly why these 12 rows derive here and not through
`emit_lapcert.derive`, which was tried on the exemplar's own family key
(`Alph_00_01_1@D`, tail and far both empty, `p0 = 8`) and fails at
`no overflow chain` on BOTH parities.  The framing is the point.

For the 6 nested rows, `D['ovf'][b]` carries the boot/inner/exit triple instead
of `ch`/`c`; `regcert`'s `VIRT_NEST_*` templates are the shape to borrow for
that arm, applied to the OVERFLOW rather than to a register step.  Do the flat
6 first and land them before touching this.

### `D`, in full

    spec orig mirror enc         the (already mirrored) machine and alphabet
    st tl fr                     {parity: state}, {parity: tail}, {parity: far}
    ks p0 boot                   octaves covered, the boot anchor, boot length
    ints[b]                      Z0 Z1 chz cz P0 P1 chp cp
    ovf[b]                       kind B0 B1, then ch c (flat)
    vis[q]                       a chain reaching state q, per state
    val                          the differential-validation summary string

`validate` has already replayed every branch against the raw simulator — exact
step counts, exact configurations, `lift`-equal landings — on 192 anchors per
row, BEFORE you render anything.  If a board fails to compile, suspect the
template, not the certificate.

## ACCEPTANCE

* Every board compiles, and `Print Assumptions nqh_<ID>` shows
  `functional_extensionality_dep` **only**.
* `python3 tools/census_cache.py --check` stays **MATCH**.
* Nothing under `theories/` should need to change for the 6 flat rows.  If a
  board wants a new library lemma, **check the census closure first** (see
  NON-NEGOTIABLE) — wave-30 lost a build cycle putting a one-line lemma in
  `WTape.v`.
* Run the byte-identical A/B afterwards (`tools/counters/rerender_check.py`,
  patched vs a pristine worktree at your merge base, then `diff -rq`).  Adding a
  renderer cannot re-route `emit_lapcert`, but `tailcert` shares `regcert`'s
  `_chain`, so **prove it rather than assuming it**.
* **Expect 6 boards from the flat arms, then 6 more.**  If you get 0 on the flat
  6, the fault is the template: re-read `regcert`'s `INT_GLUE` against
  `emit_lapcert.GLUE_SPLIT` before touching `_derive`.

## THEN, AND ONLY THEN

Re-run `tailcert.py --list` over the whole open residue (`core_rows.txt` plus
`frozen_unproven.txt`).  Wave-30's reader fix moved 67 rows and only the 162 core
rows were checked for end-to-end derivation; the shadows were not, and a shadow
whose core boards may still need its own board.  Also re-run `restscan.py
--emit`, `regcert.py` and `emit_lapcert.py --list` — each is a DIFFERENT gate and
it costs nothing but the run.

## NON-NEGOTIABLE

* Never edit `theories/Census/`.  `census_cache --check` must stay **MATCH**.
* **Check the census closure before adding a lemma to a library file:**

      python3 -c "import sys;sys.path.insert(0,'tools');import census_cache as C;\
        print('theories/Counters/X.v' in set(C.closure_v_files()))"

  INSIDE, do not edit: `WTape.v`, `LapGlue.v`.  OUTSIDE, fine:
  `LapCertGlue.v`, `LapCertGlueLift.v`, `NestedLapLift.v`, `NestedLap.v`,
  `LapDecider.v`, `RegGlue.v`, `JpCounter.v`.
* `SkipGlue`, `NestedLapLift`, `LapDecider`, `LapCertGlue`, `LapCertGlueLift`,
  `LapGlue*`, `RegGlue`, `WTape` are axiom-free or funext-only — keep them so.
* Everything under `tools/` is UNTRUSTED; the kernel re-checks every board.
* **Do not add a row to `alphabets_gen.ENCROWS`/`ENCS`** without checking that
  `reg113.json`, `quad35.json` and `jexc80.json` still reproduce.  Register a
  private `ENCDATA` row instead — `tailcert.INVERTED` is the pattern, and it
  asserts `ENCS` is unchanged after import.
* Do not edit `nestcert.py`'s cascade section, `cascade_probe.py`,
  `cascade_emit.py`, `NestedLapCascade.v`, or any `CASB_*`/`CASC_*` board.

## ENV

`apt-get install -y coq` (8.18.0), then
`coq_makefile -f _CoqProject -o Makefile.coq`.

**Build the Counters/Checkers closure ONCE, up front:**

    make -f Makefile.coq $(ls theories/Counters/*.v theories/Checkers/*.v \
      | sed 's/\.v$/.vo/' | tr '\n' ' ')

Wave-30 lost real time to this.  `--emit` runs `coqc`, and a board whose
alphabet `.vo` is missing fails with "Cannot find a physical path bound to
logical path", which `process` reports as an ordinary derivation failure and then
DELETES the file.  It looks exactly like "the row does not board".  Build first.
**DO NOT run `make all`.**

After changing any library file, rebuild BOTH `theories/Counters` and
`theories/Checkers`: a stale `LapDecider.vo` gives "makes inconsistent
assumptions over library BBB4.Counters.WTape", which also looks like a proof
failure and is not.

A new board file must be added to `_CoqProject` — `gen_stages.py` does it for
boards it can see, but check, because a dangling `_CoqProject` entry breaks
`make` with "No rule to make target".

## DO NOT RETRY (measured)

* **Routing these 12 through `emit_lapcert.derive`.**  Tried on the exemplar's
  own family key; fails at `no overflow chain` on both parities.  The two-form
  overflow framing (destination state `st[nb]`, count `1*j+2`, peeled source) is
  what makes them derive.
* **A deeper peel on the two-form interior branch**, or widening
  `derive_chain`'s depth.  The interior gate is already EMPTY (wave-30 §6d).
* **`two_form`'s "gap-free union" as evidence of an ascending counter** — it is a
  condition on the value SET; `two_form` now also requires the arrival order to
  ascend (wave-30 §6c).  If you touch the reader, carry that check.
* **A descending carrier for a family that reads downward** — it is a
  bit-polarity inversion; try the swapped digit words (`tailcert.INVERTED`,
  `gen_alphabet.py --abc dig0,dig1,term`).
* **`WTape.cycRW` / an `SCycR` with a left-prefix offset** — 0 chains on all 17
  rows, and the variant that fires is unsound at `k = 2` (wave-30 §2).
* Standing: WAVE30 §8, WAVE29 §7, WAVE28 §4, WAVE16 §5.

## STANDING MOVES

* **The certificate already exists.**  This is the rare wave where the
  measurement is done: `validate` has replayed all 192 anchors of every branch.
  Any failure is in the RENDERER.  Do not re-derive, do not re-measure, and do
  not widen a search.
* **MEASURE THE BUCKET — AND THE READER — BEFORE DESIGNING FOR IT.**  Wave-30
  killed two of its own three builds this way; both diagnostics had selected a
  necessary condition and been read as a sufficient one.
* **A SOUNDNESS ARGUMENT IS A MEASUREMENT.**  Before writing an induction, test
  its STEP against the raw simulator at `k = 0, 1, 2`.
* **WHEN STUCK, ask John with an ABSOLUTE-COORDINATE TAPE DUMP**
  (`spacetime.py --rests --mark --lo/--hi` FIXED).  Hand-inspection is
  **39-for-39** across waves 8–30.

## PER BATCH

    python3 tools/closeout/inventory.py && python3 tools/closeout/gen_stages.py \
      && python3 tools/closeout/audit.py && python3 tools/census_cache.py --check
    git push -u origin <branch>          # retry on network error

Merge conflicts with `main` are routine and always in GENERATED tables
(`_CoqProject`, `theories/Closeout/*`, `tools/closeout/*`): take main's side on
every one, then re-run the four commands above.

Write `docs/WAVE31A_FINDINGS.md`.
