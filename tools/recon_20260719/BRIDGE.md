# Task F — the census↔upstream normal-form bridge: quantify + design

Recon over: /home/user/Coq-BBB4 (Census/TNF_QH.v, tools/census_ladder.c,
theories/Mirror.v, BBB4_Statement.v), /home/user/BBB (src/enumerate.c, results/certs_*,
BBB4_holdouts_3713.txt).  Residue: `tools/census_residue.txt` = 12,897 rows
(B 7,213 wrap-QH + C 5,655 never-QH survivors + 29 over-bound caught_t4096).
Deferred also holds 77 holdout rows (`tools/census_holdouts_kept.txt`).

All artifacts under scratchpad/recon_F/: `mapper.py` (normalizer), `intersect.py` /
`finalize.py` (classification), `mapping.tsv` (12,897 rows), `cert_matches.tsv` (113 rows).

## VERDICT UP FRONT

The recon_E "structural (0RB vs 1RB)" hypothesis is **confirmed but narrow**.  A
simulation normalizer that re-roots each first-write-0 census machine at its first
1-write reproduces the upstream (bbchallenge) TNF *exactly* (validated: **3708/3713
holdouts are byte fixed points**, the other 5 differ only by cosmetic dead-state
`_------` padding; **3705/3705 re-root runs are behaviourally identical to the
original from its first-1-write config**).  With that bridge:

- **113 of 12,897 residue machines** map to an upstream per-machine object
  (107 certs + 6 holdouts) — **and ALL 113 are 0RB re-roots.  ZERO of the 9,192
  first-write-1 (direct) residue machines match any cert or holdout.**
- So the structural gap explains only the 0RB tail.  The dominant reason recon_E saw
  a 0-intersection is **coverage, not structure**: the 9,192 direct-1RB residue
  machines are *valid upstream (4,2) TNF machines that upstream already DECIDED by
  mass deciders* (they are not in the 3,713 undecided holdout set), just with no
  per-machine cert.  The census residue is **entirely inside upstream's solved
  region** — 0 machines are new to upstream.

Therefore **per-machine cert-table boarding is NOT the big cheap lever** (yield 113).
The bridge's real levers are (i) an **0RB small-core reduction** worth ~1,295 machines
and (ii) **de-duplication**: the 12,897 rows are only **9,917 distinct** upstream
machines, so 2,980 rows are re-rootings/reductions of another deferred machine and ride
along for free.  Crucially, the bridge is **~90 % existing Coq machinery** — the
head-relative tape model makes a re-root a `TM_swap`-that-touches-`StA` plus a concrete
≤4-step quiet prefix; the only new content is one lemma family.

---

## 1. The two normal forms (exact)

Both use the standard bbchallenge text: 4 states A..D, symbols {0,1}, blank 0, start A,
head at origin; 6 chars/state = two 3-char transitions `<write><dir><next>` for read 0
then read 1; `---` = undefined.  Both label states in **first-visit order** and fix the
**first move to R by mirror symmetry** (Coq-BBB4 `theories/Mirror.v` `mirror_tm`;
census_ladder root keeps dir=R; BBB `enumerate.c` header).  The census tree
(`census_ladder.c:568`) roots A0 ∈ {0RA,1RA,0RB,1RB} (0RA/1RA die in the loop tier),
so its live roots are **both 0RB and 1RB**.  Upstream `enumerate.c` fixes **A0 = 1RB**
(default `--starts 1RB`).

That is the entire difference: **census enumerates first-write-0 (`0RB…`) machines;
upstream does not.**  Everything else (first-visit labelling, first-move-R, don't-care
`---` on unreached transitions, no cnt=1 pruning) coincides.  Proof that the conventions
coincide on the shared 1RB space: my normalizer is the **identity on 3708/3713
holdouts and 3824/3829 cert strings** (the 5+5 exceptions are 3-state machines upstream
pads to 4 with `_------`; behaviourally identical, and my canon drops the dead state).

The census's own symmetries — `TM_swap`/`St_swap` (state relabel, TNF_QH.v:214-352) and
`mirror_tm` (Mirror.v) — **preserve the A0 write bit**, so a 0RB machine can never
become 1RB inside the census's orbit.  There is **no symbol-swap lemma anywhere in
`theories/`** (grep confirms: only state-swap + mirror).  The 0/1 tape swap is not
behaviour-preserving from the blank tape (it changes the blank).  Hence the bridge for
0RB machines is a **re-rooting**, not a symbol swap.

## 2. The mapper (scratchpad/recon_F/mapper.py)

`upstream_tnf(m)`:
- `canon(m, start)` — behaviour-preserving: mirror if A0 moves L; simulate from blank;
  relabel visited states in first-visit order; **unreached slots → `---`** (matches
  upstream don't-care and the census Deferred completion orbit).  Early-stops when every
  *defined* slot has fired (correct + fast).
- If canonical A0 writes 1 → **mode `direct1`**, tnf = canon(m).
- If canonical A0 writes 0 → **mode `reroot`**: find the state q\* whose read-0
  transition performs the **first 1-write** from the blank tape (always within ≤4 steps
  on the read-0 prefix); return `canon(m, start=q*)`.

Validation (all in `intersect.py`/`finalize.py`):
| check | result |
|---|---|
| 3,713 upstream holdouts are fixed points | **3,708 exact; 5 = `_------` padding only** |
| 3,829 cert strings are fixed points | **3,824 exact; 5 = padding only** |
| canon idempotence (canon∘canon) | 0 bad |
| re-root behaviourally = original from t\* (0RB, 3,000 steps) | **3,705 / 3,705** |
| 77 census-holdout rows → upstream holdout set | **77 / 77** |
| every produced upstream_tnf starts `1RB` (no excluded 1RA) | 12,897 / 12,897 |

## 3. Intersection (mapping.tsv, 12,897 rows)

Canonical A0 / mode: **9,192 direct1 (1RB)**, **3,705 reroot (0RB)**.

**(a) upstream-certified: 107.  (b) upstream holdout: 6.  (c) nothing: 12,784.**
**All 113 hits are `reroot`; 0/9,192 direct1 machines match anything.**

Cert-family table (all matches; list B/C in parens):
| family | hits | list | example census → upstream_tnf |
|---|---|---|---|
| certs_rank | 51 | C | 0RB0LC_1RC1LD_1LA0RB_1RB1RD → 1RB1LD_1LC0RA_0RA0LB_1RA1RD |
| certs_irules | 18 | C | 0RB0LD_1LA1LC_0LD0LC_1RD1RB → 1RB1RC_0LA0RD_0RD0RC_1LD1LA |
| certs_modclass | 13 | C | 0RB0LC_1RC0LD_1LA0RB_1RD1RA → 1RB0LD_1LC0RA_0RA0LB_1RD1RC |
| certs_v6res90 | 8 | C | 0RB1LA_1RC1LD_0LA1RB_1RC0LB → 1RB1LD_0LC1RA_0RA1LC_1RB0LA |
| certs_rwlsilent | 6 | B | 0RB---_1LC0RD_1LD1LB_1RB0LC → 1RB0LC_1RC1RA_1LA0RB (ns=3) |
| (holdout) | 6 | C | 0RB0RC_1LC1RC_1LD1RA_1RA0LD → 1RB1LB_1RC1LD_1LD0RC_0LA0LB |
| certs_fuel | 4 | C | 0RB0LA_1RC1RB_0LD0RC_1LD1LA → 1RB1RA_0LC0RB_1LC1LD_0RA0LD |
| certs_drift | 4 | C | 0RB0LA_1LC1LD_1RD0RD_1LA0RC → 1RB1RC_1LC0LC_1RD0LB_0LA0RD |
| certs_v7res46 | 2 | C | 0RB1LA_1LA1LC_1RD0LC_1RC1RB → 1RB1RC_0LA1RB_1LD0RC_1LC1LA |
| certs_neverqh | 1 | C | 0RB0LB_1LC0LC_1RD0LA_1LB0RC → 1RB0RB_1LC0RD_1RA0LB_0LA0RA |

Reading: cert hits are almost entirely list-C (never-QH) machines that re-root **cleanly
to a 4-state 1RB machine** (drop 0 states) that upstream certified as never-QH (rank /
irules / modclass / fuel / drift / neverqh, plus the v6/v7 irules variants).  The 6 B
hits are quasihalters that **reduce to a 3-state** rwlsilent core.  The 6 holdout hits
are the census and upstream *both* being stuck on the same never-QH machine.

**(c) split — every "nothing" machine is still upstream-SOLVED:**
| bucket | rows | why it's decided upstream (but has no per-machine cert) |
|---|---|---|
| 4-state 1RB TNF, mass-decided | **11,489** | direct1(4) 9,177 + reroot(4) 2,312 — valid (4,2) TNF, not in the 3,713 holdouts ⇒ decided by upstream's at-scale deciders |
| reduces to ≤3-state 1RB | **1,295** | direct1(3) 15 + reroot(3) 1,264 + reroot(2) 16 — land in (3,2)/(2,2), fully solved |
| truly new to upstream | **0** | none |

Re-root loss (why B barely matches): drop-state distribution `{0: 2,421, 1: 1,272,
2: 12}` → `nstates_after {4: 2,419, 3: 1,270, 2: 16}`.  A dropped state is a **quiet
prefix state**, which forces the census machine to be a quasihalter.  Hence
- **list C (never-QH) re-roots: drop `{0: 1,623, 1: 50}`** — 97 % keep all 4 states
  (all states recur, consistent with never-QH); the 50 drop-1 are RepWL *survivors*
  that are actually prefix-quiet quasihalters (mis-binned, belong in the wrap tier).
- **list B (QH) re-roots: drop `{0: 798, 1: 1,214, 2: 12}`** — 61 % drop ≥1 state, i.e.
  reduce to a ≤3-state core (the archetypal 0RB prefix-quiet quasihalter).

**De-duplication:** the 12,897 rows are only **9,917 distinct** upstream machines
(4-state 9,404 / 3-state 511 / 2-state 2).  **2,138 of the 4-state re-roots (C 1,514,
B 624) land on a 1RB machine that is ITSELF a direct1 residue row** — the census defers
the same behaviour twice (once as 0RB, once as 1RB).

## 4. The Coq bridge — mostly existing lemmas

Let m be a census 0RB machine, t\* the first-1-write step, q\* the state firing it,
u = the upstream representative.  The transfer needs four moves; three already exist.

**The linchpin (why this is cheap): the tape is head-relative.**
`Tape = {t_left:nat→Sym; t_head:Sym; t_right:nat→Sym}`,
`InitES = (StA, mkTape blank_side S0 blank_side)` (BBB4_Statement.v:62-97).  Up to t\*
the machine writes only S0, so the config after the prefix is
`(q*, mkTape blank_side S0 blank_side)` = **`InitES` with state q\* instead of StA** —
head position is not in the representation, so there is nothing to translate away.  The
prefix identity `stepn m t* InitES = Some (q*, InitES_tape)` is a **concrete ≤4-step
`reflexivity`/`vm_compute`** per machine (or one generic read-0-path lemma).

- **(i) re-root = a `TM_swap` that touches `StA`.**  `TM_swap StA q* m` relabels q\*↔StA;
  its `InitES` is `(StA, InitES_tape)`, and by the general (already-proved, u/v-arbitrary)
  `stepn_swap`/`step_swap` (TNF_QH.v:264-285),
  `stepn (TM_swap StA q* m) n InitES = option_map (es_swap StA q*) (stepn m n (q*,InitES_tape))
   = option_map (es_swap StA q*) (stepn m (t*+n) InitES)`.
  The **existing** `visits_swap`/`quiet_swap`/`qhbound_swap`/`nonhalt_swap`
  (TNF_QH.v:287-333) assume u,v≠StA only to reuse `es_swap_init`; the **new** work is a
  variant that substitutes the prefix identity for `es_swap_init` — ~20-30 lines, plus
  the per-machine prefix reflexivity.  Call them `qhbound_reroot`, `neverqh_reroot`.
- **(ii) relabel the remaining states (first-visit order among B,C,D):** pure
  `TM_swap` with u,v≠StA — **existing** lemmas apply verbatim.
- **(iii) first-move-R mirror:** `mirror_tm` + `mirror_neverqh`/`mirror_nonhalt`/
  `mirror_quiet`/`mirror_quasihalts` (Mirror.v) — **existing**.
- **(iv) don't-care completion:** the census Deferred orbit already closes over
  completions via `qhbound_le`/`nonhalt_le` (TNF_QH.v header) — **existing**.

**What each census predicate needs:**
- **QHBound / R_QH (list B):** quiet states of m = the dropped prefix states
  (last visit ≤ t\* ≤ ~4, a concrete constant) ⊎ quiet states of u shifted by t\*.
  `QHBound (max(t*+1, Bu+t*)) m` follows from `qhbound_reroot` + a ≤4 constant. NonHalt
  and QuasiHaltsSt come from the prefix + the quiet prefix state. Clean.
- **NeverQuasiHaltsSt (list C):** never-QH ⇒ no quiet state ⇒ every prefix state is
  revisited i.o. ⇒ **drop 0** (matches the data: 1,623/1,673). Then
  `Visited m = π(Visited u)` and recurrence transfers directly by `neverqh_reroot`
  (= general `visits_swap` + t\* shift). The 50 drop-1 "C" machines are simply not
  never-QH; they route to the QHBound tier.

**Bottom line:** three of four moves are already proven; the re-root is one new
StA-swap variant whose only per-machine obligation is a ≤4-step reflexivity.  No new
trust surface — the engine and checkers are reused unchanged.

## 5. Recommendation + expected D_census yield

Cert-table boarding of the residue is **not** the promised cheap mega-lever — it is
worth **113** machines (107 certs whose families ALL have existing census checkers:
rank, irules, modclass≈irules, fuel, drift, neverqh, v6/v7≈irules; + 6 holdouts that
don't help).  Do it, but as a rider on the reroot lemma, not as the headline.

Ranked by yield-per-effort, all resting on the single `*_reroot` lemma family:

1. **0RB small-core reduction — immediate ~1,295 machines.**  1,295 residue rows reduce
   to ≤3-state 1RB machines (513 distinct). Every ≤3-state (4,2) machine is trivially
   decided (BB(2,2)/BB(3,2) closed). Board a 513-row small-decision table (all
   `vm_compute`) + `qhbound_reroot`/`neverqh_reroot`. These are exactly the list-B
   prefix-quiet quasihalters whose liveness the wrap tier couldn't reach — the reroot
   moves the liveness into a 2-3 state core where it is trivial. **Low effort.**

2. **De-duplication — 2,138 free riders, distinct work 12,897 → 9,917 (−23 %).**  Wire
   the reroot lemma so any tier that decides a 1RB rep auto-decides its 0RB twin. No new
   decider needed; it multiplies the value of every tier-strengthening item below.

3. **Cert-boarding — ~107 machines.**  Re-run the existing census checker (rank/irules/
   fuel/drift) on the clean 4-state reroot target, transfer via `neverqh_reroot`.

4. **The residual ~9,404 distinct 4-state 1RB machines have NO upstream per-machine
   cert** (upstream mass-decided them). The bridge does not shortcut these; it only
   proves they are decidable and de-dups them. Lever = strengthen the census's own tiers
   exactly per NEXT_SESSION.md: RepWL block 8-10 / fuel 32k (item 3), rank pattern
   vocabulary + n=4 (item 2), wrap-lex (item 1). The bridge makes each such kill count
   ~1.3× (dedup).

**Expected next-session D_census shrink from the bridge alone (items 1+3, ~one session):
≈ 1,300–1,400 machines** (1,295 small-core + ~107 cert, minimal overlap), plus the
structural payoff that the residue is now 9,917 distinct and provably ⊂ upstream-solved.
The big remainder (~9,400 distinct 4-state) stays a tier-strengthening problem, now
de-duplicated and with a certainty that every one of them is decidable.
