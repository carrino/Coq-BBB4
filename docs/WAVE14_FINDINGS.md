# Wave-14 — the overflow wall is EXPONENTIAL, and 46 boards were sitting behind three bugs

_Branch `claude/residue-reduction-4-2-5syxph`, off merged wave-13.  This wave
tested `WAVE13_FINDINGS.md` §10b (the alternating-frame hypothesis), found the
real mechanism behind the ~523-machine overflow wall, built the Gray-code
family, and boarded 57.  **Read §2 and §3 before starting anything** — §3
retires the build §10c proposed, and it would have produced zero boards._

## 1. Scoreboard

| | |
|---|---:|
| boards this wave | **90** (79 `LAPC_*` + 11 `LAPG_*`) |
| `D_remaining` | 1,266 → **1,176** |
| frozen rows settled | 3,890 → **3,980 / 5,156 (77.2%)** |
| new Coq | `Counters/GpCounter.v`, `Counters/BpCounter.v`, 18 generated `Counters/Alph_*.v` — all axiom-free |
| board axiom footprint | `functional_extensionality_dep` only |
| closeout | `audit.py` OK — tables partition the frozen list exactly |
| census | `census_cache --check` = MATCH at every commit; `theories/Census/` untouched |

`LapDecider.v` and `LapCertGlue.v` are **untouched and still axiom-free**.

## 2. The alternating frame: John was right, and the first measurement was the wrong test

§10b recorded John's reading of `0RB---_0RC0LD_1LD1RC_0LA1LB` — *"1's to the
LEFT of the bits when the msb is even and 1's to the RIGHT when the msb is
odd"* — as unverified, and asked for a decode at consecutive bit lengths.

**Attempt 1 (wrong test, recorded so it is not repeated).**  Decoding the
anchor word HEAD-RELATIVE at each state gave a clean, confident, and
misleading answer: state B reads marker-BEFORE for all 4,083 firm readings
across bit lengths 2..12; state D reads marker-AFTER for all of them.  Both
constant, no flip.  That looks like a refutation and is not one, because

    MB(m) ++ [S1]  =  [S1] ++ MA(m)      identically, for every m

— moving the head one cell re-parses the same tape from one frame into the
other.  A per-state verdict therefore measures where the head is, not where
the markers are.  **A frame claim is a claim about ABSOLUTE COLUMN PARITY**
and has to be measured in absolute tape coordinates.  `frame_probe.py`
carries both modes and `spacetime.py` prints the absolute diagram.

**Attempt 2 (the right test).**  Sample one canonical phase (state A, head at
absolute column 0), group snapshots into epochs by the tape frontier, and ask
which columns VARY inside an epoch (the bits) and which stay 1 (the markers):

| epoch (frontier) | 6 | 8 | 10 | 12 | 14 | … | 30 |
|---|---|---|---|---|---|---|---|
| snapshots | 4 | 8 | 16 | 32 | 64 | … | 4744 |
| bit columns | 2,4 | 2,4,6 | 2,4,6,8 | 2,4,6,8,10 | … | … | … |
| bit parity | even | even | even | even | even | even | even |

Constant across 13 epochs.  And structurally it *must* be: the frontier grows
by exactly **2** at every msb bump (one bit cell + one marker cell), so the
parity of the bit lattice cannot change from epoch to epoch.

**Attempt 3 — where the flip actually is.**  John's own restatement located
it: *"do a round of counting 8->15, then shift over one with 1 in position 2
and then count 8->15 again, then shift back to lsb being in the 2 position",
"in this way of saying it, it always has a 1 to the right of each bit"*.
Measuring the two phases of one epoch separately:

    MAIN round     t = 228..332 : varying columns = [2, 4, 6, 8]   (even)
    OVERFLOW       t = 346..466 : varying columns = [3, 5, 7, 9]   (odd)

and the overflow phase's cells read 000, 100, 010, 110, 001, 101, 011, 111 —
**a second full counting round, in the shifted frame.**  The frame flips
exactly once per msb bump, exactly as John read it; it just never flips at
the ANCHOR, because the anchor phase does not occur during the overflow.  The
encoding stays `Mp` throughout ("a 1 to the right of each bit"), which is also
what `WAVE12_FINDINGS.md` §7 recorded for this same machine.

## 3. That second round is the overflow wall — and it is EXPONENTIAL

The overflow does a whole extra counting pass, so it costs work proportional
to the counter VALUE, not to the tape length.  Measured on the flagship at
its own anchor, on the raw simulator:

| `j` | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|---|---|
| interior | 4 | 8 | 12 | 16 | 20 | 24 | 28 | 32 | 36 |
| overflow | 20 | 40 | 76 | 144 | 276 | 536 | 1052 | 2080 | 4132 |

Interior `4j + 4` — affine.  Overflow `16·2^j + 4j + 4` — **exponential**; a
second, independent anchor family on the same machine measures
`8·2^j + 4j + 4`, same shape.

**This is why the overflow chain search fails, and it is not a search
weakness.**  `sside` carries its count as `a*j + b` and `srun` returns
`ca*j + cb`; both are affine in `j` by construction, so an exponential
overflow is **unrepresentable** — the same architectural limit as §9c's
quadratic interior, sitting on the branch that gates the most machines.

**§10c's proposed build would have boarded zero.**  `enc_src`/`enc_dst` from
two `ENCDATA` rows changes which WORD the overflow targets.  The wall is how
much WORK the overflow does.  Nothing about a second encoding row shortens a
`Θ(2^j)` lap into an affine one.

This is not new to the project — it is the family `WAVE10_SHAPES.md` §3 named
(*"measured 10·2^j'+4j+4, 8·2^j'+…"*, *"needs an INNER induction (a sweep
lemma), not a window chain"*) and that wave-12 boarded 163 of by hand with
`Counters/IXPGadgets.v`, whose own header says it: *"the overflow lap
2^K-1 -> 2^K runs an INNER interleaved counter from 2^(K-1) up to the
all-ones fill"*.  Wave-13 built an affine-only checker and then read the
resulting failures as a missing encoding.  **The measurement that would have
caught it is cost-vs-`j` on the OVERFLOW branch, which had never been run** —
the exact omission §9c called out for the interior branch, repeated one
branch over.  `tools/counters/ovfshape.py` now makes it.

### The residue, measured two ways

`wall_survey.py` buckets by WHICH part of the certificate fails, keeping the
best outcome across every (mirror, anchor) candidate — over all 1,266:

| bucket | count |
|---|---:|
| anchor + interior derive, **overflow fails** | 534 |
| anchor derives, interior fails | 344 |
| no anchor at all | 185 |
| no visit witness (quasi-halting) | 157 |
| derives completely | 46 |

which reproduces §10a's ~523.  `ovfshape.py` then asks what those overflows
COST (complete sweep, all 1,266):

| interior / overflow degree | count |
|---|---:|
| AFFINE / **EXP2** | **496** |
| — / no decodable anchor | 392 |
| AFFINE / AFFINE | 304 |
| HIGHER / HIGHER | 49 |
| QUAD / QUAD | 25 |

**The dominant class of the residue is an exponential overflow** — 496 of
1,266, and outside the certificate model.  The 304 `AFFINE/AFFINE` machines
are the ones the existing checker can still reach; they are a different
population, `Kp`-dominated where the `EXP2` bucket is `Jp`-dominated.

### The `HIGHER` bucket is three things, and one of them is in-model

Re-running `degree()` with parity and base-3/4 tests splits the 49 `HIGHER`
machines cleanly:

| refined class | count | status |
|---|---:|---|
| `EXP4` (cost ~`4^j`) | 19 | **11 are the Gray boards** — see below |
| `HIGHER` (mostly ~`3^j`) | 17 | never read; no hypothesis |
| `PARITY-AFFINE` | 13 | **IN model** — §9b's two-pass carry |

* **`PARITY-AFFINE`** is affine on each parity class of `j` separately (e.g.
  `2j+2` on even `j`, `4j+4` on odd).  That is exactly `WAVE13_FINDINGS.md`
  §9b's two-pass carry — the traversal period is 2 CELLS while the block unit
  is 1 — and §9b says the existing checker expresses it after re-indexing
  `j = 2i + r` with `u^2` as the block unit.  Its exemplar
  `0RB0LA_0LC1RD_0RD1LC_1LA1RB` is in this set, which confirms the reading.
  **These 13 need no new theory, only the `m = 2` re-index wired into the
  emitter.**
* **`EXP4` is a GRAY SIGNATURE, not a class.**  11 of the 19 are precisely the
  11 machines boarded through `GpCounter.v` this wave: a Gray word decoded at
  a BINARY anchor makes the apparent lap cost grow like `4^j`.  So `EXP4` at a
  binary anchor is a cheap detector for "try the Gray family here", and the 8
  leftovers are the natural next Gray targets.

### The 8 leftover `EXP4` machines — a localized, unfinished lead

`0RB0LA_1LA1RC_0RD1RD_1LB0LB` is §9d's *second* Gray exemplar ("counts up,
then down, then bumps the msb: 8->15->9").  Its `Gp p = gray(2p)` anchor
family **is present and does close, affinely**: at StB on the mirror, the lap
costs a flat `4j + 8` for every `j` measured, with no `j = 0` split needed.
`gray_anchors` finds the anchor; all five symbolic branches then fail in
`derive_chain`.

Diagnosed as far as: the lap immediately steps RIGHT off the anchor into blank
tape (the machine keeps scratch on the far side), so the chain must open with
`SWinR`; peeling a second high cell into `post` (a 4-way `x,y` split instead
of the 2-way `x` split) does **not** help, so it is not the tail depth.  The
search budget is not the problem either (depth 24, `nmax` 64, against a
12-step lap).  **Next step: instrument `_win_candidates` on this
configuration** — the anchor and the lap are both verified correct, so
whatever it is, it is in the candidate generator, and 8 machines are behind it.

## 4. Three bugs were holding 46 finished certificates

`wall_survey.py` found 46 machines that derive COMPLETELY — anchor, both
interior branches, overflow, visit witnesses, bootstrap, and differential
validation against the raw simulator — and had no board.  Three causes, all
in `tools/`, none in the theory:

1. **`emit_lapcert.process()` crashed the whole run.**  It formatted the
   interior cost as `'%d*j+%d' % D['ci']` OUTSIDE the `try`.  Wave-13's `j=0`
   split leaves `ci` at `None`, so the first split-mode machine in a list
   raised `TypeError` and **every machine after it in that run boarded
   nothing.**  This is the most expensive kind of bug in this project: it
   looks exactly like "the search found nothing".
2. **`mirrorize()` knew only the `NeverQuasiHalts` closing shape**, so every
   right-growing QUASI-HALTING machine failed with *"closing theorems not
   found"* — precisely the blocker `WAVE13_FINDINGS.md` §6 predicted.  It
   needed **no new Coq**: `mirror_nonhalt`/`mirror_qh` are in `Mirror.v` and
   `qhbound_mirror` is already in `Census/TNF_QH.v`, which every board imports.
3. **The anchor-glue tactics ended in `rewrite <- !app_assoc`**, which FAILS
   when the anchor tail is empty and there is nothing to reassociate.  Now
   wrapped in `first [ <old> | cbn [app]; rewrite <- ?app_assoc; cbn [app];
   rewrite ?app_nil_r ]`, so previously-working cases take the old path byte
   for byte.

Standing lesson: **a survey that reports only its LAST failure cannot
distinguish "nothing derives" from "everything derives and the writer
crashed".**  `wall_survey.py` keeps the best outcome per machine and exists
so this class of loss is visible.

## 5. The Gray-code family (WAVE13 §9d) — built, 11 boards

`theories/Counters/GpCounter.v` is the sixth counter word family and the
first that is not a digit alphabet: the tape word is the reflected-binary
code of the count, so `Ip/Jp/Kp/Dp/Mp`'s shape `E p = rep uS j ++ sS ++ E q0`
does not apply.  The measured anchor word is the Gray code of TWICE the lap
index (the machine's two anchor states catch the even and odd Gray words, so
a one-state family steps by two), which has a clean structural recursion:

    Gp xH = [S1; S1]     Gp (xO q) = S0 :: Gp q     Gp (xI q) = S1 :: flip0 (Gp q)

Three decomposition lemmas, all proved by induction on `p`, all **affine**, so
`LapDecider.v` is untouched — `srun_sound` never sees the encoding:

    cview p = (S j, Some q0), Gp q0 = x :: G
        Gp p        = S1 :: rep [S0] j ++ S1 :: x      :: G
        Gp (succ p) = S0 :: rep [S0] j ++ S1 :: negs x :: G
    cview p = (0, Some q0), Gp q0 = x :: G
        Gp p = S0 :: x :: G          Gp (succ p) = S1 :: negs x :: G
    cview p = (S j, None)
        Gp p = S1 :: rep [S0] j ++ [S1]
        Gp (succ p) = S0 :: rep [S0] j ++ [S1; S1]

Each was checked against the raw simulator for `p = 1..19999` before being
proved.  The flipped high cell `x` is a single CONCRETE cell, and splitting
the interior branch on it is what makes the opaque tail `G` identical on both
sides of the lap — which `srun_sound` requires.  Five chains per machine:
`(j=0, j>=1) × (x=S0, x=S1)` plus the overflow.

`tools/counters/emit_graycert.py` emits `LAPG_*`.  **Measured population: 11
of 1,266.**  §9d called 4 a floor and asked for a periodic-difference
detector; with a full Gray anchor scan the true figure is 11.  Worth having
and cheap, but it is not a large class — do not size future work off it.

## 5b. The alphabet does not have to be guessed

Six alphabets had been added one at a time, five of them off a human tape
reading.  All six have the same shape — a positive recursion with three fixed
words:

    E xH = C        E (xO q) = A ++ E q        E (xI q) = B ++ E q

and that triple determines an `ENCDATA` row completely:

    interior   E p = rep B j ++ A ++ E q0        ->  uS = B, sS = A
               E (succ p) = rep A j ++ B ++ E q0 ->  uD = A, sD = B
    overflow   E p = rep B j ++ C                ->  obS = 0, soS = C
               E (succ p) = rep A (S j) ++ C     ->  soD = C

`A=[S1;S0] B=[S1;S1] C=[S1]` reproduces the `Ip` row verbatim; `Bp` is
`A=[S0;S0] B=[S0;S1] C=[S0;S1]`.  So `alphabet_infer.py` reads `(A,B,C)` off
the machine's own snapshots (`C` is the first word, `A` and `B` the second and
third with `C` stripped) and verifies the recursion against every remaining
word; `gen_alphabet.py` turns a triple into a Coq module whose two lemmas are
the same induction as `ILCounter`'s — **proved, not asserted**, so a wrong
triple fails to compile.

Measured over the 392 no-anchor machines: **234 (60%) have an inferable
family, in 18 distinct alphabets, 12 of them new**; the largest covers 59
machines.  All 18 modules compile, and six of them reproduce
`Ip`/`Jp`/`Kp`/`Dp`/`Mp`/`Bp` exactly — which is the check that the inference
is sound rather than curve-fitting.

**This confirms the standing do-not-retry rather than overturning it.**  The
18 alphabets bought **9 boards**, not 234.  What they bought instead is
DIAGNOSIS — over the whole residue the failure profile is now

| failure | count |
|---|---:|
| no overflow chain (the exponential wall, §3) | 532 |
| no interior chain | 433 |
| no visit witness (quasi-halting) | 164 |
| **no anchor family at all** | **47** |

against 185 with no anchor before.  The residue is now almost entirely two
named, measured problems instead of one named problem and a dark bucket.

## 6. What to do next, in order

1. **The exponential overflow is the residue's main class (≈439+ machines)
   and it needs a DESIGN pass, not a search.**  Two routes, and this wave did
   not choose between them:
   * teach `LapDecider` a nested lap — an inner anchor family run `2^j` times,
     which is what the overflow physically does (§2's "count the range again
     in the shifted frame").  This is the "inner induction / sweep lemma"
     `WAVE10_SHAPES.md` §3 asked for, and `IXPGadgets.v` already carries the
     positive-arithmetic gadgets (`pow2`, `fill`, `cview_none_shape`) that a
     hand-built instance of it needed;
   * or route these machines to the existing `emit_ixp.py`/`IXPGadgets.v`
     path, which boarded 163 of exactly this family in wave-12, and treat the
     certificate checker as the affine-only tool it is.
   The first keeps the per-machine cost a `vm_compute`; the second is a
   known-good hand template.  **The cheap version of the second was tried and
   does not work as-is**: `emit_ixp.py --list <the EXP2 machines>` derives
   **0 of 12** sampled, all with *"no anchor family with a consecutive run
   >= 12"*.  Its template is hard-wired to `Ip` with the anchor tail exactly
   `[S1;S0]` (the wave-12 "flip shape"), and the EXP2 bucket is
   **224 `Jp` / 168 `Ip` / 104 `Mp`**, so most of it cannot present an `Ip`
   anchor at all.  Widening `emit_ixp`'s alphabet is the move
   `WAVE13_FINDINGS.md` §8 already put on do-not-retry, and it would also
   need the flip-shaped interior to match — so route (1), the nested lap, is
   the real work.  (For contrast the `AFFINE/AFFINE` bucket, which the
   existing checker can still reach, is **185 `Kp` / 43 `Jp` / 40 `Dp` /
   36 `Ip`** — a different population entirely.)
2. **The 157 quasi-halting machines** (WAVE13 §6) are unchanged and still the
   cleanest one-theorem win: the 96 with `StA` targeted need the
   states-visited variant of `wsteps_frame`/`cycL`/`cycR`.  The `mirrorize`
   half of that blocker is now closed (§4.2).
3. The `QUAD/QUAD` (22) and `HIGHER/HIGHER` (48) machines are the §9c family
   and are also out-of-model.  Same design question as (1) — a count that is
   not affine in `j`.
4. The **47** (was 185) with no anchor family at all, and the 27 genuine mxdys
   holdouts.

## 7. Do-not-retry, added this wave

* **A HEAD-RELATIVE frame decode as a test of a frame hypothesis.**
  `MB(m) ++ [S1] = [S1] ++ MA(m)`, so the answer is partly an artifact of
  head position.  Use absolute column parity (`frame_probe.py --abs`,
  `spacetime.py`).
* **`enc_src`/`enc_dst` from two `ENCDATA` rows to break the overflow wall**
  (`WAVE13_FINDINGS.md` §10c).  Measured: the wall is the overflow's COST,
  not its target word.  Zero boards.
* **Concluding "the search finds nothing" from an emitter run that raised.**
  §4.1 cost 46 finished certificates.  Survey with `wall_survey.py`, which
  records the best outcome per machine, before believing a negative.
* **Sizing the Gray class off the wave-13 estimate.**  Measured 11 of 1,266.

## 7b. mxdys' deciders are available, and they carry the missing count language

mxdys pointed John at `github.com/ccz181078/busycoq` branch `BB6`
(`verify/Inductive.v`, `verify/RRBA.v`).  This retires the standing
do-not-retry entry.  Their top-level theorem is `~halts` only -- there is no
quasi-halting layer anywhere in that tree -- but the model they build to
prove it is exposed as first-class rules `multistep_expr a b n` over symbolic
configurations that carry their state, and the count language `nat_expr`
includes `nat_mul` and `powsum k x = ((k+2)^x - 1)/(k+1)`, a geometric sum.
That is exactly §3's wall (`Θ(2^j)`, 496 machines) plus the quadratic (25)
and base-3/4 (36) families.  Full assessment and a staged plan, with a
measure-first decision gate, in `docs/MXDYS_DECIDERS_PLAN.md`.

## 8. Deferred, unchanged

* Census fold-in (route B) — batch once on stable hardware; the only step
  that lowers `D_census`.
* The champion `1RB1LD_1RC1RB_1LC1LA_0RC0RD` and the carry-shifted one-off
  `0RB1LC_1LC0LC_0RD1LA_1RD1RB`.
* The `Closeout.vo` COMPILE needs the ~719-file board `.vo` closure (~85 min
  in a fresh container).  `inventory.py`, `gen_stages.py` and `audit.py` all
  ran clean this wave and the numbers in §1 come from them.
