# Wave-22 — the nested route grows two ends: N counts, and the OFFSET family

_Branch `claude/skipped-machines-residue-lyfjw6`, off main at `D_remaining`
621 (the wave-21 merge).  This wave took the residue prompt's ranked leads in
order and landed **110 boards**: the whole "no shift chain" bucket (8) and
102 of "no inner family at `pow2 j`" (22 + the 80-machine Mp-outer cluster).
`D_remaining` **621 → 511** — the project's first crossing of **90% settled**
(4,645 of the frozen 5,156).  All 110 are `NLAP_*` through the one checker;
`Print Assumptions` = `functional_extensionality_dep` only on every one
(checked individually).  `census_cache --check` MATCH at every commit;
`theories/Census/` untouched; `audit.py` OK (exact partition)._

## 1. Scoreboard

| | |
|---|---:|
| boards | **110** (8 multi-count + 22 offset-family + 80 offset/split/refill) |
| `D_remaining` | 621 → **511** |
| frozen rows settled | 4,535 → **4,645 / 5,156 (90.1%)** |
| new Coq | **none** — every front closes through `NestedLapLift` / `NestedLap2` / `WTape.rep_rot` unchanged |
| board axiom footprint | `functional_extensionality_dep` only, on all 110 |
| census | MATCH throughout |

Both fronts are pure EMITTER work, and that is the wave's headline: the
composition theorems shipped in wave-18 were already general enough for
counts the emitter could not yet identify or land on.

## 2. Front one — the shift chain generalizes to N counts (8 boards)

The 13 machines filed under `no shift chain` / `no second exit chain` had
both inner families identified and "only a chain missing".  The truth is
better: **they carry a THIRD (and sometimes a FOURTH) count per overflow
phase**, in yet another shifted frame — the sync-bouncer
`count → shift → count` with more shifts.

`NestedLap2.boot_via_fill` is generic in `(Cc, Cin1, Cin2)`, so **it composes
with itself**: each extra count is one more application, folding the finished
count into the next one's boot.  No new Coq.  The emitter's `_second_count`
became `_more_counts` — a recursive, backtracking search over candidate
families at every level (`nestcert.MAXCOUNTS` = 4) — and the Coq emission
generalized to a LIST of families: an assert-style boot stack
(`HB1 … HBn`, one `boot_via_fill` application per shift), per-shift
definitions (`chm_`, `chm3_`, …), and a multi-count `visx_` that reuses the
same boot stack.  Validation replays every count of every phase against the
raw simulator.

**8 of the 13 board** (all `Jp`, six via mirror).  A typical board is
`NLAP_1RB1RD_1LC0RD_1LA1LB_0LB1RD.v`: three `Jp@B` families with tails
`()` → `(1,0,1)` → `(0,0,1)`, i.e. boot → count → shift → count → shift →
count → exit.

### 2b. The 5 survivors are a CHECKER gap, measured precisely

The remaining 5 (`0RB1LA_0LC1RD_0RD1LD_1RB0LA`, `0RB1LB_1RC0LD_0LA1RB_0RC1LD`,
`0RB1LC_0LC1RC_1LA0RD_0LA1RD`, `1RB0LD_0LC1RA_0RA1LA_0RB1LD`,
`1RB0LD_0LC1RA_0RC1LA_0RB1LD`) all fail the same way, one level down: after
the LAST count's fill the exit is not another count but a plain double sweep
(left over the `(1,0)`-rep converting it to `(1,1)`s, then right re-laying
it), and the RETURN sweep enters its rightward cycle in a state it only
reaches after consuming ONE unit of the rep — with the two cells it needs
not matching the rep's post, so no rotation lstep can expose them
(`SRotR` requires `post` agreement, and `SCycR`, unlike `SCycL`, has no
entry-offset parameter `m`).  The instrumented search visits 13 configs and
is exhausted.

So these 5 need either a new lstep — `SCycR` with an entry offset, i.e. a
`LapDecider.v` extension with its own soundness case and corruption tests —
or hand-written boards.  Recorded in `docs/RESIDUE_MAP.md`; not attempted
this wave.

## 3. Front two — the OFFSET family, and the reindex that finally works (22 boards)

`no inner family at pow2 j` was the largest chain-search bucket (162 rows).
A range scan over the decoded value streams (the wave's most useful
measurement; reproduce with the `hits`-gathering in `nestcert._gather`)
splits it exactly:

| best consecutive run in one overflow phase | n | reading |
|---|---:|---|
| `2^(K+1)+2 .. 2^(K+2)-1` (and +1/+3/+4 variants) | **95** | octave-up count with an OFFSET start; fill IS reached |
| `2^(K+2)+2 .. 2^(K+2)+2^(K+1)-1` (`Ip`, ends at `10111111b`) | 24 | an ANCHOR ARTIFACT of the scan -- the same machines seen from a different anchor; the boarded 22 come from this set |
| no run ≥ 8 under any obS=0 key | 41 | genuinely no decodable family |

### 3a. What boards: the reindex, done right this time

For the 95: the inner count starts at `2^(j+1)+c` (c = 2 on every machine
that validates) and runs to the all-ones fill, so the EXIT side is the
ordinary one.  The blocker was always the START:

    E (2^(j+1)+2) = uD ++ uS ++ rep uD (j-1) ++ soD

— block count `j-1`, the exact index-shift `NESTED_LAP_PLAN.md` measured at
0/12 in wave-15 and marked "do not treat as a fix".  What was wrong then was
the *sside construction*, and the working one is:

* **reindex the whole overflow branch at `j = S j'`**: boot source `b=1`,
  inner start `pre = digit blocks of c`, fill `b=2`, outer successor `b=2` —
  every side an ordinary sside in `j'`;
* `v0 = xO (xI (pow2 j'))` — a plain positive term, so
  `NestedLapLift.nested_overflow_lift` (stated at arbitrary `v0`) applies
  unchanged, and `fill (xO (xI (pow2 j'))) = fill (pow2 (S (S j')))` holds
  by `cbn`, so `cview_fill_pow2` still names the exit word;
* **the `j = 0` case (`p = 1`) is one CONCRETE run** (17–23 steps on the
  22), stated with the same `ceqb`/`ceqb_lift` pattern as the bootstrap
  lemma (`lapo0_`), and `cview_none_shape p 0` funnels `lapo_`'s `j = 0`
  branch into it;
* the VISIT lemmas destruct the outer index the same way: `j = S j'` goes
  through `viso_`/`visx_` (restated at `cview p = (S (S j), None)`), and
  `j = 0` falls back to per-state CONCRETE witnesses from `Cc 1` (`visz_*`,
  `eexists; vm_compute`).

Two emitter subtleties that cost iterations, recorded so they are not
re-paid:

* **the boot landing inherits `b` from the boot SOURCE** (`SCycL` transfers
  the count), so it arrives with an extra unit folded into its count and a
  shortened post.  No chain surgery can undo this (nothing unfolds a count
  into a post), and none is needed: `gbo_`'s `cden` normalization goes
  through `replace (1*j+b) with (j+b); rewrite rep_add`, which lands both
  sides on `pre ++ rep uD j ++ flat`.
* **positive constructors wrap LSB-outermost**: `2^(j+2)+2` is
  `xO (xI (pow2 j))`, not `xI (xO (pow2 j))`.  The kernel caught the wrong
  order immediately (`epre_` failed to compile) — the untrusted-emitter
  design working as intended.

**22 of the 95 board** (all with outer `Alph_10_11_11`, inner `Ip`, `c=2`,
boot `4j'+23`, exit `4j'+12`).  The other 73 fail earlier (no boot chain to
the offset anchor, or no interior lap for the inner key) — their runs start
at `+1/+3/+4` or their chains genuinely do not derive; nothing was measured
to say they are close.

### 3b. Measured negatives (do-not-retry additions)

* **Octave-only families** (`pow2 (j+oct)`, `oct` = 1, 2 — representable as
  `b = oct` with NO reindex) measure **ZERO** on this bucket.  The
  generalization is kept because it subsumes the `oct = 0` search and costs
  nothing, but no machine's inner count starts at a clean octave power.
* **The multi-count route buys ZERO of the 65 `no exit chain` / 22 `no boot
  chain` machines** — re-measured over all 87 after the N-count
  generalization landed.  WAVE18 §4b stands: their blocker is family
  identification, not chains.
* The "24 `Ip` top-bit riders" segmentation was an ANCHOR ARTIFACT: re-run
  after the 22 boards, the residual 140 have NO such runs.  A partial-span
  lemma is NOT the next build.
* ~~The residual `Mp`-outer cluster needs the inner-lap split~~ — **BUILT
  the same wave, section 3c below, and it boarded 80.**

### 3c. The Mp-outer cluster: the split inner lap, and two frame bridges (80 boards)

The residual "no inner family" cluster (`Mp`-outer, inner `Alph_01_11_011`,
`run 66..127`) was measured to one blocker and then built, all in-wave:

* **the inner interior lap is affine (`4i+2`) but its chain only derives in
  SPLIT form**: the carry sweep's period sits one cell INTO the `[1;1]`
  unit, so `SCycL` fires only from the phase-shifted sconf — an exact `Z`
  chain at `i = 0` plus peeled `P` chains at `i = S i'` (count `i-1`, one
  unit in the prefix), the interior-lap mirror of wave-13's `j = 0` split
  (`nestcert._inner_lap_split`, templates `FAM_{DEFS,GLUE}_LAP_SPLIT`);
* **the boot lands in a SHIFT1 frame** (unit rotated one cell against the
  block frame, `pre = preb[:-1]`, `u = x :: uD[:-1]`) — bridged in the glue
  by ONE pinned application of a board-local `rrc_` lemma
  (`rep (x::u) k ++ x :: Y = x :: rep (u++[x]) k ++ Y`, two lines over
  `WTape.rep_rot`);
* **the exit chain only derives from the REPHASED fill** (one unit cell
  rotated out front: `uS^(j+2) ++ soS = a :: (b,a)^(j+1) ++ b :: soS`) —
  same `rrc_` bridge, other direction (`nestcert._refill`,
  `OFF_GXI_RF`).

The outer alphabet is `Mp` (`obS = 1`), so the reindexed boot source is the
PEELED form — the same `gso_`/`geo_` holes as `obS = 0` serve it unchanged.
80 of the 140 sampled derive, all fully validated (7 overflow phases each,
every inner lap replayed, plus the concrete `j = 0` lap), and all 80 board.

The 60 that remain: 32 still "no inner family" under any route, and the
others fail one of the offset chains; nothing measured says they are close.

## 4. Template hygiene

The shared board template gained holes (`@CVSJ@`, `@NNJ@`, `@B1B@`,
`@B1SJ@`) whose defaults reproduce the previous text BYTE-IDENTICALLY —
verified by re-rendering a committed nested board and diffing.  Flat and
nested boards are unaffected.

## 5. What is next, in measured order

1. **The 24 `Ip` top-bit riders** — one new lemma (`NestedLap3`, the
   partial span), then the offset machinery as-is; the detector and range
   data already exist.
2. **The 15 no-visit-witness** (unchanged; WAVE16 §6b analysis stands).
3. **The 41 `QUAD`/`QUAD`** (unchanged; never had a design pass).
4. **The 235 no-anchor** (unchanged; `alphabet_infer.py` first).
5. The 73 offset-family machines that did not board and the 5 `SCycR`-gap
   machines — both have precise, recorded blockers.
