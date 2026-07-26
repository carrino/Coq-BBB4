# Wave 14 (2026-07-26) — the 27 holdouts, decomposed; the wave family CLOSED

_First session pointed at the **holdouts** rather than the residue.  Read
`docs/TERMINOLOGY.md` first for what "holdout" vs "residue" means; this file
is the holdout-front scoreboard, what landed, and where the next lever is._

---

## 1. The 27, decomposed (this is the map the front was missing)

`tools/census_holdouts_kept.txt` is the live list.  Cross-referencing it
against `theories/` (and against `tools/closeout/frozen_unproven.txt`, which
is the authority on what is actually *boarded*) splits it as:

| status | count | machines |
|---|---|---|
| **boarded** | **16** | Wave_7, Wave_17, Wave_24, Wave_27, Wave_36, Wave_6, Double_9, NGHHold_00..08 |
| unproven | 11 | below |

The 11 unproven, by BBB `results/counterN.cert` family:

| family | n | machines (cert #) |
|---|---|---|
| tower | ~~4~~ 1 | #20 `1RB0RD_1LC1LB_1RA0LB_1LC1RA` (#21/#34/#40 boarded, §3b) |
| double | ~~3~~ 1 | #32 `1RB1LD_1RC0RB_1LA0RC_0LD0LA` (#30/#37 boarded, §3b) |
| blockdbl | 3 | #11 `1RB0LD_1RC0RC_1LA1RB_0LC0LD`, #13 `1RB0RB_1LC1RA_1RA0LD_0LB0LD`, #28 `1RB1LC_1LC1RD_1LA0LC_0RD0RB` |
| ~~xd~~ | ~~3~~ 0 | **all three BOARDED this session** (§3a) |
| fractal | 2 | #3 `1RB0LA_1LC0RD_0LB1LA_0RB1LA`, #5 `1RB0LA_1LC1RD_0LC1LA_0RD0RB` |
| wave4 | 1 | #15 `1RB0RC_0LC1LB_0LD1LC_1RD0RA` |
| wrap-QH | 2 | `1RB---_1LC0LB_0RC0LD_1RD1RB`, `1RB---_1RC0RB_0LC0RD_1LD1LB` |
| v4-irules | 1 | `1RB1RA_0RC0RB_1LC1LD_0RA0LA` |
| ~~open~~ | ~~1~~ 0 | **BOARDED this session** (§3a) |

**The wave family is now COMPLETE** — all six BBB `wave_counter` certs
(#6, #7, #17, #24, #27, #36) carry kernel-checked `NeverQuasiHaltsSt`
theorems off the single `theories/Counters/WaveCounter.v` closer.

---

## 2. What landed: #6 and #24

`theories/Machines/Counters/Wave_6.v`, `Wave_24.v` — both axiom-clean
(`Print Assumptions` = `functional_extensionality_dep` only), negative
controls in `theories/Tests/CountersWave_Corruption.v`, wired into
`_CoqProject`, `tools/counters_manifest.tsv` and the route-A closeout
(`CB_07.v`, recompiled green; `D_remaining` 1,266 → 1,264).

These were the pair the wave hand-off flagged as "#6/#24 have 4-step
0-writing cross cycles (harder `cross_run`)".  `WaveCounter.v` needed **no
change** — `nextf 1` / `WInv 1` / `WInv_no_leadstop` / `wglue_neverqh` are
reused verbatim; `tools/counters/trace_wave.py` already confirmed both run
the #27 orbit exactly.

### The gadget table (from `tools/counters/probe6.py`, validated by `lap6.py`)

```
FT     5  (StC,(S1::L,S0,[]))          -> (StA,(L,S1,[S1;S1]))
XC     4  (StA,(S1::c::L,S1,R))        -> (StA,(L,c,S1::S1::R))       cross, 2 cells
BT     5  (StA,(S0::S1::c::L,S1,R))    -> (StA,(L,c,S1::S1::S0::R))   block transition
BTe    5  (StA,([S0;S1],S1,R))         -> (StA,([],S0,S1::S1::S0::R)) at the lead = SPAWN
DEP    1  (StA,(L,S0,R))               -> (StB,(S1::L,chd R,ctl R))
RS     1  (StB,(L,S1,R))               -> (StC,(S0::L,chd R,ctl R))
RSW    1  (StC,(L,S1,R))               -> (StC,(S1::L,chd R,ctl R))
RSEP   3  (StC,(S1::L,S0,R))           -> (StC,(S0::S1::L,chd R,ctl R))
```

Every one is a **plain `csteps` reflexivity** — `CTape.cstep` already
materialises blanks via `chd`/`ctl`, so no `wsteps` windowed transport is
needed anywhere in this file (#17/#27 needed `wsteps_frame_r`).

### Three things that made #6 *easier* than #27, not harder

1. **The return changes nothing.** `C1/1R>C` rewrites a one as a one, and the
   3-step separator gadget writes 1 at x, 1 at x−1, then 0 back at x.  So the
   tape after the leftward wave *already is* `wbody (nextf 1 front)` and the
   return is a pure traversal to the frontier blank.  **No `relaid` /
   `relaid_b` / `bridge_l` borrow algebra at all** — that is most of
   `Wave_27.v` deleted.
2. **The cross is uniform over the whole word,** not per-block: `XC` when the
   cell below the head is a one, `BT` when it is a separator, stop the moment
   the head itself lands on a separator.  Concretely that *is*
   `WaveCounter.carry`: a run entered at offset 0 deposits iff it is even, at
   offset 1 iff it is odd, and a non-depositing run always hands the next one
   over at offset 1.
3. **The parity lives in the stopping position,** not in an exit state, so
   there is no `stC`-style exit-state function; the two cases fall out of
   `destruct (Nat.even d)` inside `wave_L6`.

### The one piece of real design: `decp`

`bridge6` is the identity "the wave's own bookkeeping IS `carry`".  It only
closes if the deposit's decrement is applied to the **newest** laid run —
which is `base[0]` *only* when the carry stopped immediately.  Hence

```coq
Definition decp (po : bool) (cs : list nat) := if po then dec1 cs else cs.
```

and the statement

```coq
retl (dec1 (wcs po blocks base)) (S0 :: S1 :: dsufL po blocks)
  = retl (decp po base) (S0 :: wbody (carry po blocks)).
```

With `decp`, the deposit case, the interior-continue case and the SPAWN all
close in a single induction; at the top level
`decp po0 [mat po0 (S b0)] = [S b0]` for **both** parities, which is exactly
"the frontier ends at `b0+1`".  Getting this wrong is the trap: an
un-parameterised `dec1 base` works for the even frontier and silently fails
for the odd one.

### #24 was nearly free — remember this heuristic

`mirror_tm tm_24 = 1LB1RA_1LC1RD_1RD0LD_0LD0RA` is **exactly `tm_6` with the
states relabelled by `(StA StC)(StB StD)`**.  That bijection *moves the start
state*, so it is NOT a `TM_swap` transport (the machines really are
different: boots 71 vs 74, and #24 is none of the 12 mirror/relabel images of
#6 that fix `StA`) — but every lap lemma transcribes under the substitution.
`Wave_24.v` was produced by applying it mechanically to `Wave_6.v` and fixing
three things by hand:

- the machine table + `mirror_ok`;
- the boot count (71);
- the `vis` offsets (A,B,C,D ← #6's C,D,A,B = 0,1,5,2).

**It compiled on the first try.**  So: before writing any counter machine
from scratch, check whether it (or its mirror) is an already-boarded machine
under *any* state bijection — including ones that move `StA`, which the swap
lemmas cannot transport but a file-level `sed` can.

---

## 3. The relabel-sibling scan — a live lead for four holdouts

Running that heuristic over the 20 then-unproven holdouts against all 3,908
boarded machines (mirror × all 24 state permutations) found **four hits**:

| unproven holdout | is a relabel of | boarded in |
|---|---|---|
| #1 `1RB0LA_0RC0RD_1LD1RD_1LA1RB` | `0RB0RC_1LC1RC_1LD1RA_1RA0LD` | `NGHStage/NGH_01.v` |
| **`1RB0RB_1LC1RC_0RA1LD_1RC0LD`** (the "open" one) | `0RB1LD_1RC0RC_1LA1RA_1RA0LD` | `NGHStage/NGH_01.v` |
| #25 `1RB1LB_1RC1LD_1LD0RC_0LA0LB` | mirror of `0RB0RC_1LC1RC_1LD1RA_1RA0LD` | `NGHStage/NGH_01.v` |
| #28 `1RB1LC_1LC1RD_1LA0LC_0RD0RB` | mirror of `1RB1LD_1RC0RB_1LA1RB_0LD0LA` | `Counters/Bounce_33.v` |

All four relabelings move `StA`, so **this is not a proof transport** — the
boarded theorem is about the same transition table started in a *different*
state, and `NeverQuasiHaltsSt` is a statement about the blank-tape run from
`StA`.  What it *is*: direct evidence that these machines' dynamics are
inside the reach of engines we already have in Coq (NGramHist for three of
them, the bounce-counter machinery for #28).

This is worth taking seriously **against** `TERMINOLOGY.md`'s standing
discipline ("point the porting machinery at the residue; keep it away from
the 27").  That discipline rests on "mxdys' deciders failed on these", which
is an argument about *his* method at *his* parameters, not about ours at
ours.  Note especially that the machine documented for a year as having **no
known proof anywhere** has an NGramHist-boarded relabel sibling.

## 3a. …and running the engines on the 20 boarded FOUR of them, including the "open" machine

The sweep predicted by §3 was run (`tools/nghist/holdout_sweep.py sweep`,
results in `tools/nghist/holdout_results.tsv`).  At the **cheapest**
parameters — `k=2, n=2, t=40, fuel=20000`, the same rung the residue harvest
starts at — NGramHist's never-QH tier closes **4 of the 20**:

| holdout | family | contexts | predicted by the sibling scan? |
|---|---|---|---|
| `1RB0LA_0RC0RD_1LD1RD_1LA1RB` | xd #1 | 116 | yes |
| **`1RB0RB_1LC1RC_0RA1LD_1RC0LD`** | **the "open" one** | 239 | yes |
| `1RB1LB_1RC1LD_1LD0RC_0LA0LB` | xd #25 | 116 | yes |
| `1RB1LD_0LC0RB_1RA1LA_0LD0LA` | xd #29 | 67 | no — a bonus |

Boards: `theories/Machines/NGHHold/NGHHold_{00,01,02,03}.v`, each a
`ngramhist_check_neverqh_lex_sound` call closed by `vm_compute`, each
`Print Assumptions` = `functional_extensionality_dep` only.  Regenerate with
`holdout_sweep.py emit`.

**`1RB0RB_1LC1RC_0RA1LD_1RC0LD` is the machine `NEXT_SESSION.md` has recorded
for a year as "the only one with no known proof anywhere".**  It now has a
kernel-checked `NeverQuasiHaltsSt` theorem.  The whole `xd_counter` family is
gone too, so BBB's hand-built transducer certs (`xd_arc`/`xd_dfa`, the
~1,100-line `verify_xd_counter`) never need porting.

**So `TERMINOLOGY.md`'s "keep the machinery away from the 27" discipline is
retired.**  It rested on "mxdys' deciders failed on these" — a statement
about *his* method at *his* parameters.  Ours is his NGramCPS extended to
quasihalting with a lex liveness gate; it is a different tool, and the
holdout list is an inference rather than a record (that file's own CAVEAT).
The rule going forward: **sweep the holdouts with every engine at every
escalation rung BEFORE hand-writing a parametric proof for any of them.**

The 16 survivors resisted `(2,2)`, `(4,2)` and `(6,2)`, and none of them is
an R_QH/wrap board either (0 hits on that tier).  Still untried on them:
higher rungs (`n=3`, `k=8`, bigger `MAXCTX`/fuel), `RepWL`, `irules`-QH, and
`LapDecider`.  Do that first next session — it is hours of untrusted compute,
not weeks of Coq.

---

## 3b. The escalation sweep: FIVE more, and n=3 was the axis

`tools/nghist/holdout_escalate.py` over the 16 survivors, rungs
`(4,3) (6,3) (8,2) (8,3) (12,2)`.  **5 hits / 16**, every one of them at
**gram order n = 3** — the axis the first pass never touched:

| holdout | family | k, n | contexts |
|---|---|---|---|
| `1RB1LD_1RC0LA_1RD0RD_1LB1RB` | **double #30** | 4, 3 | 178 |
| `1RB1RB_1RC1LC_1LD0RA_1LB0LB` | **double #37** | 4, 3 | 169 |
| `1RB0RD_1LC1LB_1RD0LB_1RD1RA` | tower #21 | 6, 3 | 246 |
| `1RB1RA_0LC0RA_1LC1LD_1LA0LC` | tower #34 | 6, 3 | 261 |
| `1RB1RD_1LC1LB_1RA0LB_1RD0RC` | tower #40 | 6, 3 | 176 |

Boards `NGHHold_04..08`, all `functional_extensionality_dep` only.

**I predicted this would come back empty and was wrong**, on the reasoning
that "everything so far closed at the cheapest rung, so survivors need a
different engine, not bigger parameters."  The flaw: the first pass only ever
varied `k` (history) at `n = 2`.  History and gram order are not
interchangeable — `n` is how much of the *neighbourhood* each context sees,
`k` is how far *back* it remembers, and these machines needed width, not
depth.  Record the lesson as: **sweep the axes independently before
concluding an engine is exhausted.**

This takes #30 off the board — the machine the recon called "a genuinely hard
parametric proof, larger than any landed counter machine," with a full
session of banked reconnaissance — without writing any of it.  Same for the
tower family, whose alternative was porting a 1,500-line table interpreter.

## 3c. The n=3 lever does NOT transfer to the residue (measured)

Having found that gram order n=3 boarded 5 holdouts that n=2 could not, the
obvious move was to re-sweep the 1,244 unboarded residue machines the same
way -- `harvest_sweep.py` has the identical n=2 blind spot.  Measured on a
SHUFFLED (representative) sample at the cheapest n=3 rung:

    0 hits / 100.

That bounds the true rate under ~3%, against 5/16 on the holdouts.  The lever
does not transfer, and the reason is a conflation in the justification worth
recording so nobody repeats it:

**The argument was "fail_diag.py puts ~85% of residue failures at NOMEAS --
closure fine, liveness measure search fails -- and that is a vocabulary
problem, which n addresses."  Both halves are true and the inference is
still wrong.**  `n` widens the CONTEXT vocabulary (how much tape
neighbourhood a node sees).  NOMEAS is a failure of the MEASURE vocabulary
(which lexicographic components are available to rank the closure).  Those
are different vocabularies, and this file's own completion plan already said
so: step 4 of "Eliminating the residue" calls for `NgPattE` PATTERN MEASURES
and states "this is the residual the blind sweep leaves."

The holdouts that fell to n=3 were counter machines whose closures were
genuinely context-starved; the residue's blocker is downstream of closure.
So the residue needs either the pattern-measure vocabulary (TERMINOLOGY step
4) or a different engine whose liveness argument is not lex-measure-based at
all -- RepWL, irules-QH, LapDecider, none of which has been run over the
residue at any parameters.  That is the next lever, not more `n`.

The ladder was left running anyway (k=4 and k=6 at n=3 are already queued and
cost nothing to finish), but it should be read as confirmation, not hope.

## 4. blockdbl recon (#11/#13/#28) — the next hand-written family

`tools/counters/probe_bd.py` rebuilds `verify.c`'s model and confirms it for
j = 2..7:

```
side R:  D(j) = 1^m 0 1^t,   head on the RIGHTMOST 1, state edge
side L:  D(j) = 1 0^z 1^m,   head on the LEFTMOST  1, state edge
m(j) = ma*2^(j-1) + mb,  m -> 2m + mdbl        t(j) = ta*j + tb,  t -> t + ta
```

| # | machine | edge | side | ma | mb | mdbl | ta | tb |
|---|---|---|---|---|---|---|---|---|
| 11 | `1RB0LD_1RC0RC_1LA1RB_0LC0LD` | C | R | 3 | 1 | −1 | 2 | −1 |
| 13 | `1RB0RB_1LC1RA_1RA0LD_0LB0LD` | B | R | 3 | 0 | 0 | 2 | −1 |
| 28 | `1RB1LC_1LC1RD_1LA0LC_0RD0RB` | C | L | 4 | −1 | 1 | 2 | 0 |

`probe_bd.py 13 2 7` → all six j exact, all 8 transitions fire, step ratio
→ 4 (so one lap is Θ(m²)).

**The warning the C verifier hides:** it only re-simulates j ∈ [jmin,jmax]
raw.  A Coq proof needs the general induction, and the lap is **not** a
single parametric run — the turnaround count also grows like m², i.e. one lap
is an *outer* loop of Θ(m) sweeps, each a Θ(m) `cycR`/`cycL` crossing.  So
blockdbl needs `MeasureGlue`-style nesting like `Bounce_8.v`, not the flat
`LapGlue` shape.  Budget it as a full family session, and do **#13 first**
(mdbl = 0, mb = 0 — the cleanest parameters).

Also note #28 already appears in the relabel-sibling table above, so try the
cheap route on it first.

**ANCHOR TRAP (measured 2026-07-26).**  `verify.c`'s `bd_build_D` puts the
head ON the rightmost 1 (`pos = x-1`).  The event actually reachable from the
blank tape has it on the **blank one cell further right**.  Both anchors
"work" for the C verifier's finite check, but only the second is the orbit,
and building the first one in Coq sends the run off into a non-recurring
trajectory.  The orbit for #13, confirmed exact for i = 0..3:

    D(i) = 1^(3*2^i) 0 1^(2i+2),  head on the BLANK past the last 1, StB
    lap step counts: 34, 106, 358, 1294

Note also the accumulator is `2i+2`, not `verify.c`'s `t = 2j-1` -- same
`t -> t+2` recurrence, different offset, because the cert's j-indexing starts
at 2 and its anchor is the shifted one.  Take the anchor from the blank-tape
run, not from the cert.

**#11 and #13 are siblings of each other** (`perm=(2,0,1,3)`, no mirror; the
relabelling moves `StA`, so it is a transcription rather than a transport --
the `Wave_6` -> `Wave_24` route).  So blockdbl is really ONE hand proof plus
one mechanical transcription plus #28, not three jobs.  Checked the same way
across {double, blockdbl, fractal, tower}: this is the ONLY internal sibling
pair -- in particular #30/#32/#37 are three genuinely separate proofs, and
none of them is a relabelling of the boarded `Double_9`.  So "reuses the
DblCounter gray algebra verbatim" in NEXT_SESSION.md means the ALGEBRA is
shared, not the file.

### #32 reconnoitred (`tools/counters/probe32.py`)

MEASURED anchor, exact for j = 1..6 (again NOT the certificate's -- the
anchor trap above applies here too):

```coq
Cf(j) = (StB, (rep [S0] z ++ rep [S1;S1;S0] k ++ [S1;S1;S1], S0, []))
        k = 2^j - 1,   z = 2j + 5
```

tape order `1^3 (011)^k 0^z`, head on the blank past the last 0.  Laps
210 / 710 / 2574 / 9758 / 37950 / 149630, ratio -> 4, so Theta(len^2).

Sweep decomposition (maximal same-direction runs):

```
B+1:1  A-1:LONG | B+1:3 A-1:1 (B+1:4 A-1:1)^k B+1:3 | A-1:LONG | ...
```

The inner repeat count is **exactly k** -- a `cycR` unit, 5 steps, net +3 --
bracketed by entry/exit `B+1:3` gadgets.  But a later group in the SAME lap
shows `B+1:5` where the first had `B+1:4`: that is the `0^z` accumulator's
carry firing.  So #32 is a comb ratchet nested inside an odometer, exactly
#30's shape, and it is in **#30's difficulty class, not #6's** -- flat
`LapGlue` will not close it.

Do the same measurement for #37 before committing to a shared family lemma;
and read the carry rule off the executor rather than deriving it (the #30
recon's digit transitions change LENGTH, and there is no reason to expect
#32's to be gentler).

That is an argument for doing **blockdbl before double** despite blockdbl
needing new nesting machinery: 3 machines for ~2 units of work, versus 3
machines for 3.

---

## 5. Two leads that were closed off (do not re-chase)

- **The `1RB---` pair is not free.** Both already carry
  `NonHalt /\ QuietAfter tm StA 0 /\ QuasiHaltsSt` in
  `theories/Machines/Bulk/Wrap_01.v` (`tm_wrap_007` and its sibling), so they
  look like pure wiring.  They are not: boarding needs `QHBound`, and
  `tools/provenqh_stay.txt` records that the QHBound tier was
  probe-confirmed to FAIL on both (plain + lex liveness, n ≤ 6, t ≤ 1024, and
  the t = 4096 extension in `qhbound_lex2_t4096_overbound.tsv`).  The
  remaining content is a liveness proof that B/C/D never go quiet — i.e. a
  never-QH argument on the 3-state core `{B,C,D}` that `A0` hands off to
  (no transition anywhere targets `StA`, which is why A is quiet at index 0).
  The re-root route (`tools/gen_reroot.py`, `docs/REROOT_LISTC_STAGE.md`) is
  the right shape for it, not the wrap tier.
- **tower and xd are not a session.** `verify_tower_counter2` is ~1,500 lines
  of table interpreter (`tpat`/`shape`/`uphase` rows in the certs) and
  `verify_xd_counter` ~1,100 (transducer arcs + a DFA).  Porting either as a
  verified Coq checker boards 4 resp. 3 machines at once and is the right
  *eventual* lever, but it is a multi-session checker build in the
  `LapDecider`/`RepWL` shape — not something to start mid-session.

---

## 6. Environment notes (this container)

- **Coq comes from apt**: `apt-get install -y coq` gives exactly 8.18.0
  (matching `.github/workflows`), no opam switch needed.  It has **no**
  `native_compute`, which is fine — everything on the holdout front is
  `vm_compute`/`reflexivity`.  The committed census `.vo` are not loaded by
  `Closeout.v`, only by `CloseoutFinal.v`.
- Before building, `git ls-files | grep -E '\.vo$|\.glob$' | xargs touch` so
  `make` skips the census (`python3 tools/census_cache.py --check` must say
  MATCH — it did).
- **`make -j4` OOMs** on the heavy batches (`IRules_Batch_02` alone peaked at
  ~6.3 GB of the 15 GB box, alongside `TCyc_05` at ~2 GB).  Use `-j2`.
  Targeted builds are much better anyway:
  `make -f Makefile.coq theories/Closeout/CB_07.vo -j2`.

---

## 7. Scoreboard

- Holdouts: **27 total, 11 boarded, 16 unproven** (was 5 / 22).
  Gone this session: the whole wave family (#6, #24), the whole xd family
  (#1, #25, #29), and the one machine that had no known proof anywhere.
- Route-A closeout: `proven_rows` 3,890 → **3,896**, `D_remaining` 1,266 →
  **1,260** (`tools/closeout/inventory.py` then `gen_stages.py`; `CB_07.vo`
  and `CB_26.vo` rebuilt and kernel-green).
- `D_census` = 5,156, frozen and unchanged, as always.
