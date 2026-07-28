# Wave-22 — the nested route grows two ends: N counts, and the OFFSET family

_Branch `claude/skipped-machines-residue-lyfjw6`, off main at `D_remaining`
621 (the wave-21 merge).  This wave took the residue prompt's ranked leads in
order and landed **30 boards**: the whole "no shift chain" bucket (8) and 22
of "no inner family at `pow2 j`".  `D_remaining` **621 → 591** (4,565 of the
frozen 5,156 settled, **88.5%**).  All 30 are `NLAP_*` through the one
checker; `Print Assumptions` = `functional_extensionality_dep` only on every
one (checked individually).  `census_cache --check` MATCH at every commit;
`theories/Census/` untouched; `audit.py` OK (exact partition)._

## 1. Scoreboard

| | |
|---|---:|
| boards | **30** (8 multi-count + 22 offset-family) |
| `D_remaining` | 621 → **591** |
| frozen rows settled | 4,535 → **4,565 / 5,156 (88.5%)** |
| new Coq | **none** — both fronts close through `NestedLapLift` / `NestedLap2` unchanged |
| board axiom footprint | `functional_extensionality_dep` only, on all 30 |
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
* **The residual 74-machine `Mp`-outer cluster (`run 66..127`, inner
  `Alph_01_11_011`) is measured one level further**: the reindexed BOOT
  CHAIN DERIVES (obS=1 outer handled, `c = 2`), and the inner interior lap
  is perfectly AFFINE (`4i+2`, measured over the whole octave) — but its
  chain does not derive at the plain `AI0/AI1` endpoints, and the exit
  fails too.  The reason is a UNIT-BOUNDARY ALIGNMENT: the leftward carry
  sweep's period sits one cell INTO the `[1;1]` rep (`11^i 01 =
  1 (11)^(i-1) 101`), so `SCycL` only fires from the phase-shifted form
  with count `i-1` — the interior-lap mirror of wave-13's `j = 0` SPLIT
  (`Z`-chain at `i = 0`, peeled `P`-chains at `i = S i'`), which the OUTER
  interior branch already has (`INT_SPLIT`) and the inner-family glue does
  not.  That port (split-mode `lapin@S@` + peeled `gsn/gen`) is the next
  build, worth up to 74 machines.

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
