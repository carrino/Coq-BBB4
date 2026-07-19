# Task E — FAR tier for the quasihalting contract: design verdict + empirical ceiling

Recon over: /home/user/Coq-BBB4 (Closure.v engine, Checkers/Wrap.v, Census/TNF_QH.v,
Census/Run.v), /home/user/BBB (src/verify.c wrapfar/wrapctl verifiers, results/certs_*),
/home/user/Coq-BB5 (CoqBB5/BB5/Deciders/Verifier_FAR.v, Verifier_WFAR.v),
/home/user/bbchallenge-deciders/decider-finite-automata-reduction (built and run).
Survivor lists: measure_B/survivors2.txt (7,213 wrap-QH survivors),
measure_C/survivors2.txt (5,655 never-QH RepWL survivors).

## VERDICT UP FRONT

**Skip the FAR tier.** FAR's non-halt ceiling on both residue lists is 100% — and
irrelevant. FAR certificates are pure safety objects; the census contract's binding
constraint on BOTH lists is per-state RECURRENCE (liveness), and the measured liveness
transfer of the FAR product-graph route is 0/60 (list C) and 3/60 (list B). The right
next lever is a bouncer/irules-style checker (the upstream cert families with no Coq
checker yet), which proves periodic/segment STRUCTURE from which per-state recurrence
falls out.

---

## (a) Design analysis: can FAR carry NeverQuasiHaltsSt?

### The contract split (exact)

From theories/BBB4_Statement.v and Census/TNF_QH.v:

- `NeverQuasiHaltsSt tm := forall q, Visited q -> forall N, exists n>=N, VisitsAt q n`
  — genuine liveness, per state.
- `R_QH` needs `NonHalt /\ QHBound B /\ QuasiHaltsSt` with
  `QHBound B := forall q s, QuietAfter q s -> S s <= B` (B_census = 2000).
- Per-state trichotomy is unavoidable for both results: every TM state must be either
  (i) silent (never visited — safety), (ii) quiet with last visit <= t <= B-1
  (safety: wrap q to halt, prove the wrapped machine halt-free from the step-t config
  — Checkers/Wrap.v `tm_wrap` + `closure_invariant`), or (iii) visited i.o.
  (liveness: `rank_ok` / lex certificates). There is no safety-only route around
  (iii): a state whose recurrence is unproven could have a last visit beyond B,
  violating QHBound.

FAR (DFA + co-CTL NFA, bbchallenge decider-finite-automata-reduction) proves exactly:
"the regular set recognizing all halting configurations, closed under step-preimage,
excludes the start configuration". That discharges (i)/(ii)-shaped goals
(non-reachability) and NOTHING in class (iii). The certificate is compatible with both
recurrence and abandonment of any non-wrapped state — all 7,213 list-B machines are
believed quasihalters and all carry FAR non-halt certificates, which proves the point.

### The product-graph route (honest assessment: buildable, measured useless)

A FAR certificate CAN be turned into a forward covering abstraction that plugs into
Closure.v's engine contract. BBB's own `wrapfar` verifier
(/home/user/BBB/src/verify.c:14110–14238) already implements exactly this closure in C:

- Abstract node `A = (l, r, s, k)` : left-DFA state x right-DFA state x TM state x
  head symbol (both half-tapes read outside-in; leading-zero rule `dfa(0,0)=0`).
  `a_state = s`; `a_enc` = trivial injective packing (fits `positive`).
- `succs (l,r,s,k)`: `None` if `tm s k = None` (or `s = wrapped q`); on a right move
  writing w to state t: deterministic push `l' = dfa(l,w)`, nondeterministic pop
  `{ (l',r',t,k') | dfa(r',k') = r }`; mirrored for left moves. Total node space
  n^2 * 4 * 2 (<= 800 at n = 10; <= 32 at the n = 2 that covers ~96% of certs).
- `covers a c`: DFA folds over the two finite half-tape supports + state/head match;
  zero-padding invariance from `dfa(0,0)=0`. Seed from the anchor config by folding
  (verify.c:14174–14184 does the same).
- Obligations vs. Closure.v: `a_enc_inj` (trivial), `covers_state` (trivial),
  `succs_sound` (one case split per direction; the true preimage is enumerated — an
  order of magnitude simpler than RepWL's `rw_succs_sound`, no counting/capping),
  seed-covers. Everything downstream — `close`, `closed_b`, `live_ok`,
  `compute_ranks`, `rank_ok`, lex certificates, silent-state handling,
  `closure_check_neverqh_sound` — is generic in (A, enc, a_state, succs, covers)
  and is consumed UNCHANGED.

So no soundness gap blocks the construction: FAR-for-neverQH is formally viable.
The problem is empirical. Liveness on the product graph requires every q-avoiding
abstract cycle to be killed by rank or lex measures, and the DFAs that FAR actually
finds for these machines are tiny (2 states for 96%/87% of B/C): the product graph
is 16–72 nodes and cannot witness progress toward q. Direct measurement
(recon_E/liveprobe.py — single DFA both sides, sizes 1–3 with dfa(0,0)=0, product
closure per verify.c, per-state q-avoiding acyclicity = plain-rank feasibility):

- List C (unwrapped, anchor t=1000, sample 60): closure halt-free 52/60
  (mostly at DFA size 1) — but **0/60** pass per-state rank liveness.
- List B (wrapped at quiet candidate, anchor t = s+1, horizon 20k, sample 60):
  **56/60 get the full safety half** (QuietAfter q s + NonHalt + QuasiHaltsSt) at
  DFA size <= 3 — but only **3/60** also pass rank liveness for the remaining live
  states (= QHBound). 4/60 fail to close at n <= 3.
- Lex rescue is not plausible at scale: the abstract-edge-determined measure deltas
  (position drift, write-read counts) are the same vocabulary the census's much finer
  n-gram/RepWL abstractions already apply — these machines are the SURVIVORS of that.
  A coarser graph with the same measures cannot do better.

Note the census has already absorbed the FAR-shaped quietness reasoning upstream
invented: Checkers/Wrap.v header records that all 18 upstream `wrapfar` certificates
(results/certs_quietfar, type `wrapfar`) board via the existing n-gram wrap closure
at n = 2 from t = s + 1 — no DFA machinery was needed even for them.

### CoqBB5 port assessment (Verifier_FAR.v / Verifier_WFAR.v)

- `Verifier_FAR.v` (1,031 lines): fully verified DFA/NFA co-CTL checker
  (`dfa_nfa_verifier`): hypotheses nfa_h0/nfa_h/nfa_r/nfa_l + steady-state
  `nfa_acc` closed under 0, plus `(q0,A)` not accepted, conclusion
  `~HaltsFromInit`. It also reconstructs the NFA from the DFA alone (`nfa_rec`
  worklist, PositiveMap-backed) — i.e. the "direct" completion is verified. Porting
  it to Coq-BBB4 yields NonHalt ONLY. The NFA is a backward (preimage-closed)
  object; it cannot be "run forward", so no recurrence information is extractable
  from it, even in principle. As a census tier it cannot produce R_NeverQH or R_QH
  on its own, and R_Leaf still needs QHBound — same liveness wall.
- `Verifier_WFAR.v` (593 lines): the MITM weighted-DFA verifier is itself a forward
  covering abstraction — `MITM_WDFA_ES_step : ES -> option (list ES)` over nodes
  `(U_l, U_r, sym, state, Z, option Dir)` IS a `succs` function in Closure.v's exact
  sense. If a FAR-shaped instance were ever built, THIS is the template shape, not
  the DFA/NFA one.
- Tape-model impedance: CoqBB5 works over `ExecState Σ` with `make_tape'` /
  half-tape streams and ListES simulation; Coq-BBB4 over CTape/GTape `cconf` with
  its own `covers`/`lift` discipline and PosEnc tries. Statement-level ideas
  transfer 1:1; code does not. A FARProd instance would be a new
  theories/Checkers/FARProd.v of ~600–900 lines (succs ~80, covers + succs_sound
  ~250–350, anchor seed + seed_covers ~150, search-side plumbing and Decide.v tier
  wiring ~150), zero new trust surface beyond the instance lemmas (engine reused),
  1–2 sessions. Cost is modest — but the measured yield (0–5% where it matters)
  does not justify it.

## (b) Empirical ceiling (non-halt), both lists

Build: copied decider-finite-automata-reduction to scratch, set
`src/core/limits.rs TM_STATES := 4`, `cargo build --release --features
sink_heuristic` (network via preconfigured proxy; node_crunch git dep fetched fine;
25 s build, exit 0). Ad-hoc mode requires a DB file to exist even for text
machines — an empty file passed via `-d` suffices. Machines fed as bbchallenge
text via `-a` (400/batch).

Results (validated proofs; the decider re-checks every proof before reporting):

| list | n | FAR non-halt | params | runtime |
|---|---|---|---|---|
| B (wrap-QH) | 7,213 | **7,213 (100%)** | `-p direct -l 9` | 0.2 s total |
| C (never-QH RepWL) | 5,655 | **5,655 (100%)** | `-p direct -l 9` | 0.2 s total |

`mitm_dfa -l 12` was queued for residue; residue was empty. No sampling — full lists.

Minimal-depth stratification (cumulative solved at DFA-size limit d, from the
pre-restart Bstrat/Cstrat runs): B: d2 7,157 / d3 7,209 / d4 7,213;
C: d2 5,301 / d3 5,601 / d4 5,647 / d5 5,654 / d6 5,655.

Certificate sizes (fullB.json / fullC.json, all direction R):
B DFA sizes {2: 6,914; 3: 241; 4: 57; 5: 1}; C {2: 4,912; 3: 227; 4: 196; 5: 218;
6: 42; 7: 33; 8: 23; 10: 4}. NFA = 4n+1 <= 41 states. DVF record = 1 + 2n <= 21
bytes/machine. Verification cost is microseconds per machine in C/Rust and trivially
native_compute-able (the CoqBB5 verifier's NFA reconstruction is a tiny worklist).

Honesty caveats:
- 4,737/5,655 C machines (84%) and 3,253/7,213 B machines (45%) have NO undefined
  transition — NonHalt is vacuously true for them (step returns None only on
  undefined transitions), so the "100% FAR ceiling" is partly vacuous; for the
  machines with halt transitions FAR still solves 100%, at depth <= 6.
- For list B the census needs the QH triple; FAR-nonhalt is only conjunct one.
  The remaining need: QuasiHaltsSt (wrap safety — cheap, 93% measured even with
  toy single-DFA product closures) and QHBound's live half (liveness — 5%).

Quiet-point measurement (200-machine B sample, 50k-step horizon): every machine has
a quiet candidate with last visit <= 23 (median 0, p90 5). The B_census = 2000 score
bound is NOT the blocker for list B; these are prefix-quiet quasihalters. The blocker
is proving the OTHER states recur — the same liveness wall as list C.

## (c) Recommendation

1. **Skip FAR / wrapfar-DFA as a census tier.** Non-halt is not the bottleneck
   anywhere in the residue; safety-side quietness is already served by Wrap.v's
   n-gram engine (which boards all 18 upstream wrapfar certs at n=2); the liveness
   side measurably does not transfer (0–5%).

2. **Build the bouncer/segment ("irules"/geom) checker instead.** What the residue
   actually needs, on both lists, is recurrence for aperiodic live structures.
   Upstream's certificate families for exactly these machines are
   results/certs_bouncer (type `bouncer`: side, `period_records`, `segments` with
   repeat-counts — an eventually-affine tape decomposition) and
   results/certs_geom/certs_irules (type `irules`: block-encoded inductive rules
   with `rulerun` step templates), both verified in /home/user/BBB/src/verify.c and
   reproduced in /home/user/bbchallenge-deciders/decider-bouncers-reproduction.
   These certs prove structured infinite behavior — per-state recurrence is then a
   LINEAR consequence (every state firing inside the certified period/rule template
   recurs; states outside it are wrap-quiet with prefix-bounded last visits). This
   serves list B's QHBound (live part of prefix-quiet quasihalters is typically a
   bouncer) and list C's NeverQuasiHaltsSt in one engine. Realistic cost: 2–4
   sessions (cert semantics from verify.c + a new Checkers instance; the closure
   engine does NOT fit directly — bouncers need a step-template induction rather
   than a finite closed set, so this is a new checker shape, the first since
   Closure.v).

3. **Cheap parameter-lift probes first (hours, no new proofs).** (i) List C:
   RepWL rungs stop at block 7 / fuel 8,192, but upstream's hard
   `neverqh_rwl` certs use blocks 8–10 (6 machines among the 15 holdout-adjacent
   certs); sweep blocks 8–10, T=2, fuel 32k over the 5,655 before building anything.
   (ii) List B: the qhb ladder tops at n=6, t=1999 — given measured quiet points
   <= 23, sweep larger n at small t (the expensive large-t rungs are not where
   these machines live). Rungs are Section variables; extending them needs no
   soundness re-proof (Run.v comment).

4. Attribution note (orchestrator pointer): direct filename intersection of both
   survivor lists with all 3,829 upstream per-machine certs (19 cert dirs) is ZERO —
   structural, not just coverage: the census normal form includes first-write-0
   machines (`0RB...`, 2,024 in B / 1,000+ in C) while every BBB cert/holdout is
   `1RB` TNF; write-bits are preserved by mirror/relabel, so a simulation-based
   normalization bridge is required for any cert-level attribution. The residue
   mass has no per-machine certs upstream (mass deciders); cert dirs only cover
   holdout-adjacent machines.

## Artifacts (all under /tmp/claude-0/-home-user/2b01b1ad-6519-5466-986f-cbc04a643004/scratchpad/recon_E/)

- farbuild/ — TM_STATES=4 FAR decider build (release, sink_heuristic).
- far_run.py, fullB.json / fullC.json, B_far_solved.txt (7,213) /
  C_far_solved.txt (5,655), *_far_residue.txt (both empty) — full-list runs.
- Bstrat.d*.json / Cstrat.d*.json — minimal-depth stratification data.
- liveprobe.py — product-closure + per-state rank-acyclicity probe
  (C: 52/60 closed, 0/60 live; B: 56/60 safety, 3/60 QHBound).
- all_certs.tsv — 3,829 upstream cert filenames x family, for attribution.
- DESIGN.md — this report.
