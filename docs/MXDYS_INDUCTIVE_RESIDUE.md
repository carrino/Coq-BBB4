# mxdys' `Inductive` decider, run over the community's target list

_Measured 2026-07-30 on branch `claude/turing-machine-inductive-prover-9a1alg`,
at the commit that carries `tools/mxdys/sweep_inductive.sh` and
`tools/counters/champion_probe.py` — the two probes every number below comes
from.  Everything under `tools/` is UNTRUSTED; the one board this produced is
kernel-checked and depends on none of it._

Two community members put up a target list and said these are solvable via
mxdys' inductive prover.  This runs the prover at them and reports what it
actually says.  **They were right about the three headline rows, and the
prover's answer on one of them is a board.**

---

## 0. The result, in one table

| row | `Inductive` verdict | what it means here |
| --- | --- | --- |
| `1RB1LD_1RC1RB_1LC1LA_0RC0RD` | **NONHALT**, `default_config`, 3 layers | **BOARDED** — `theories/Machines/Counters/Champion_1RB1LD_1RC1RB_1LC1LA_0RC0RD.v`, `NonHalt /\ QHBound 32779478 /\ QuasiHaltsSt`, funext-only |
| `1RB1LB_1LC0RD_0LB1LA_0LA1RA` | **NONHALT**, `default_config`, 3 layers | anchor family + lap law extracted and differentially validated (§3); one grammar piece short of a board |
| `1RB1RD_1RC0LD_1LB0RA_1LC0LC` | **NONHALT**, `default_config`, 2 layers | already boarded in wave-32 (`QHBound 2401`) — the prover agrees |
| the 23 bonus rows | **FAIL**, 23 of 23 | see §4 — a real negative, with a control |

The headline row that mattered is the **BBB(4) champion itself**, which
`docs/CLAIMS.md` and `README.md` both single out as *the* reason the theorem is
not a proof that BBB(4) = 32,779,478.  It is now boarded, at its own score,
exactly.  **The board is NOT wired into the closeout in this branch** — that
changes `core_rows.txt`, `bbb4_target`'s own caveat and `docs/CLAIMS.md`, and
wants its own pass with `tools/closeout/{inventory,gen_stages,audit}.py` and a
census-cache check.  The theorem stands on its own meanwhile.

Positive control for the harness (`docs/MXDYS_INDUCTIVE_STAGE0.md` §0.2): 60
machines from mxdys' own `Indv1.v` reproduce 60/60 as `nonhalting` through the
same binary at the same settings, so a `NONHALT` here is his decider's verdict
and not ours.

Negative control for the *interesting* part: the production `bin/irules` engine
finds **zero anchors, zero rules, zero certs on all 150 core rows at both
2·10⁵ and 10⁶ steps** (`tools/ladder/baseline_irules_150.txt`,
`docs/LADDER_PLAN.md` §2).  So on these three rows `Inductive` is not doing a
little better than our stack — it is deciding rows on which our stack derives
nothing at all.

Reproduce:

    sh tools/mxdys/sweep_inductive.sh /tmp/mx docs/mxdys_target_rows.txt 100000 30
    /tmp/mx/busycoq/verify/dump 1RB1LD_1RC1RB_1LC1LA_0RC0RD default 200000 10000000

---

## 1. What the decider actually returns, and why it is not a proof for us

`Inductive_inf.hlin_layers_steps` returns a layer tower whose top rule is a
`multistep_lb_expr`, i.e.

    multistep_lb tm n s0 s1  :=  exists n0, n <= n0 /\ s0 -[tm]->> n0 / s1

with `n` a *free variable*.  "For every `n`, the blank tape reaches
configuration `C(n)` in at least `n` steps" is `check_nonhalt`'s whole
argument, and it is a **non-halting** statement.  Our target is
`NeverQuasiHaltsSt` (or `QHBound`), which is strictly stronger: it needs
liveness, per state.

`docs/MXDYS_INDUCTIVE_STAGE0.md` measured the obvious bridge dead — the states
appearing at rule *endpoints* carry no liveness information.  This wave has a
sharper counterexample than Stage 0's: `1RB1RD_1RC0LD_1LB0RA_1LC0LC` reports
`Sms=ABCD` (all four states at multistep endpoints) and is a **quasihalter**
that goes quiet on `StB` after 2,331 steps (wave-32 §3c).  Endpoint states are
not a witness, full stop.

**What IS load-bearing is the rule's config family.**  `C(n)` is a symbolic
tape, and reading it is what these three rows needed.  That is the whole
contribution below: `Inductive` is used as a *reader of last resort* — it hands
over the anchor family that eight waves of `anchors()` / `restscan` / `regscan`
enumeration could not find — and the proof is then built in our own
liveness-carrying machinery.

---

## 2. The champion: `1RB1LD_1RC1RB_1LC1LA_0RC0RD` — BOARDED

`dump` at `default_config` (his orientation; `TM'_from_str` may flip):

    LAYER 0
      w0: {0inf >[A] 0inf} -->lb[n1] {(1)^(n1+10242) 0inf <[C] 0inf}
    LAYER 1
      w1: {(1)^10241 0inf <[C] (0)^0 0inf} -->' {(1)^(n1+10242) 0inf <[C] 0inf}
    LAYER 2
      w1: {(0)^((n3*27)+23) (1)^2 0inf >[D] (1)^0 0inf}
          -->' {(0)^((n2*5)+14) (1)^n1 0inf >[D] (1)^0 0inf}
          where  (n3*125)+135 = n1+(n2*3)

Layer 2 is the machine's Collatz-like ×5/×3 register — the hard part, and the
reason this row sat in the residue.  **Layer 1 is the answer.**  `1^k <[C]`
with blank tape beyond it is not a counter and not a bouncer: `tm StC S0 = 1LC`
writes a one, steps left and stays in `StC`, so a head in `StC` with nothing
but blanks to its left **never leaves `StC` again**.  The layer-1 rule says the
machine reaches that state of affairs.

Read off the raw simulator (`tools/counters/champion_probe.py`), the landing is
cleaner still:

    stepn 32779478 InitES = (StC, entirely blank tape)     nonblank cells = 0

The machine erases its whole 10,239-cell working region and returns to a
**blank tape in state C** at step 32,779,478, then spins left in `C` forever.
Last visits over 40M steps:

    A  32,769,237     B  11,801,813     D  32,779,477     C  never quiet

`StD`'s last visit at 32,779,477 **is** the champion's score, 32,779,478.

So the board is one big `vm_compute` plus two three-line inductions:

* `prefix_run_N` — `cstepsN tm 32779478 c0` lands on `cEnd = (StC, ([], S0, []))`
  up to blank padding (`ceqb`).  **`TCyclerN.cstepsN` iterates `N.iter` on the
  binary numeral**, so the fuel is ~25 machine words instead of 32.8M
  constructors; `cstepsN_nat` is the bridge.  This is why the row was
  "deferred to stable hardware" (`WAVE33_PROMPT.md`) and why it does not need
  to be: the run is seconds, not hours.
* `tail_run` — `csteps k (StC, ([], S0, R)) = (StC, ([], S0, repeat S1 k ++ R))`
  by induction on `k`.  The C-loop.
* `qhbound_champion` / `quasihalts_champion` / `nonhalt_champion` follow.

The bound is also **tight** — `StD`'s last visit is at 32,779,477, measured by
`champion_probe.py --last` — but that is recorded in the file's comment rather
than proved in it: an in-file proof costs a SECOND 32.8M-step `vm_compute` for
a fact the closeout does not consume.  With the tightness lemma dropped the
whole file is **one `vm_compute`, ~17 s**, which is why it is safe to leave in
the default build.

**Trap paid, for the next reader.**  The `nat` index must never be evaluated.
A bare `32779478 : nat` is abstracted by Coq's large-numeral guard, and any
tactic that forces it (`reflexivity`, `cbn`, `vm_compute` on the `nat` side)
builds a 32.8M-constructor unary numeral and stack-overflows.  Horner digit
form plus `lia` is the whole workaround — the same guard
`tools/closeout/gen_stages.py` already works around for `champion_score`.
`lia`'s `zify` knows `N.to_nat`, so `N.to_nat champ_scoreN = champ_score` is
one `lia`; rewriting with `Nnat.N2Nat.inj_add`/`inj_mul` and then closing with
`reflexivity` does **not** work — it evaluates both sides.

---

## 3. `1RB1LB_1LC0RD_0LB1LA_0LA1RA` — the family, found; the grammar, one piece short

`dump` at `default_config`:

    {0inf >[A] 0inf} -->lb[n1]
      {1 (0 1)^((n1*2)+21) (0 (1)^4)^(n1+13) 0inf  <[C]  (0)^1 1 0inf}

Decoded into bbchallenge orientation and differentially validated against the
raw simulator, the anchor family is

    Cf m = (StC, ([S1], S0, [S1] ++ rep [S0;S1] (2*m-5) ++ rep [S0;S1;S1;S1;S1] m))

for `m >= 3`, and **all three `LapGlue.glue_neverqh` premises are in hand**:

| premise | measured |
| --- | --- |
| `Hboot` | `csteps 229 c0 = Cf 3` |
| `Hlap`  | `Cf m -->^(108*m - 49) Cf (m+1)`, **exact, verified m = 3..25** |
| `Hvis`  | all 8 transitions fire inside every lap, so every state recurs |

The lap splits in two, both exact for m = 3..12:

    Cf m -->^(72m-44) G m -->^(36m-5) Cf (m+1)
    G m = (StC, ([S1], S0, [S1] ++ rep [S0;S1] (2*m-2) ++ rep [S0;S1;S1;S1;S1] m))

and the second half decomposes into four *uniform* sweeps plus three constant
pieces (counted at m = 4, 139 steps):

    12  +  18*(m-1)  +  9*m  +  2  +  5*m  +  3  +  2*(2m-2)   =   36m - 5
    ^      ^ over the   ^ over    ^     ^ back over   ^   ^ back over
    turn   (01) region  (01111)   turn  (01111)       turn (01) region

Each sweep is one `csteps` induction over a `rep`-of-a-word list — the idiom
`theories/Machines/Counters/BNC_*.v` already uses.  `tools/ladder/drive.py`
independently mines and differentially validates **25 local rules** on this row
(`r14`: `D[1] L<0^u> R<01^v> => L<0^(u+4)> R<01^(v-2)>`; `r2`: the `01111`
block sweep; `r1`, `r13`: their leftward inverses) — again, on a row where
`bin/irules` derives nothing.

### Why eight waves of readers missed it, precisely

**The family has TWO repeated blocks on ONE side, with different indices**
(`2m-5` and `m`).  Every reader and every checker in this tree is
one-repeater-per-side:

* `LapDecider`'s symbolic side is `sside := (pre, u, (a,b), post)` — a single
  repeated block whose count is affine in the index, then an opaque tail the
  lap never reaches.  This lap sweeps to the far end of the *second* block, so
  the tail cannot hide it.
* `anchors()` / `restscan` look for `Cc p = (q, E p ++ tail, S0, far)` — one
  digit family.
* `WAVE29_BOUNCER_FINDINGS.md` §3 already named the shape on this exact row
  ("a genuine TWO-index side... which is why the plain single-insertion fit
  reports no family") and §7b recorded the clean negative that follows from
  it: no decode, no gray code, nothing.  That negative was correct and it was
  about the *reader*, not the machine.

So the remaining work on this row is **one grammar piece, not new
mathematics**: a two-block `sside` (or a hand board with the eight sweep
lemmas above).  It is the same diagnosis `docs/LADDER_PLAN.md` §0 makes for the
residue as a whole — per-module search vocabularies fail by omission — with a
row-level receipt.

---

## 4. The 23 bonus rows: FAIL, 23 of 23

`Inductive` decides none of them, at either budget, on any of the seven configs
`measure.ml` sweeps (`default`, `arithseq`, `exploop`, `arith_exploop`, `bsz2`,
`bsz3`, `bsz2_exploop`):

| budget | result |
| --- | --- |
| `maxT = 100000`, 30 s/config | **0 / 23**, all seven configs exhausted on every row |
| `maxT = 1000000`, 45 s/config | in progress at write time; 0 of the rows completed so far decide |

(The 10x budget matters less than it looks: `docs/LADDER_PLAN.md` §2 measured a
5x escalation changing nothing for `bin/irules` on the same population, because
the blocker is SHAPE, not budget.  Record the finished number when it lands.)

Seventeen of the 23 carry an undefined `A1` (`1RB---`), i.e. they are rows
whose non-halting argument must also show `A1` is never reached.  That is not
the obstruction on its own — `Inductive` handles `---` natively
(`dir_from_char '-' = None`) and decides plenty of such rows upstream.

**"FAIL" means this sweep found nothing, never "nonexistent"** (wave-14's
standing lesson).  What is NOT measured here, and is the obvious next probe:
mxdys' hinted configs — `config_SBC` (sync bouncer counter) and `config_BEC`
(bell eats counter) — which need a hand-supplied `ExtraRules` vocabulary and
are exactly where his own counter families live
(`MXDYS_INDUCTIVE_STAGE0.md` §0.4).  Our residue is counters; `default_config`
is not where counters get decided in his tree either.
`tools/counters/exrules_search.py` already derives candidate `ExtraRules`
hints from `alphabet_infer`, and never had a consumer.  **That is the wiring
this list is waiting on**, and it is the first thing to try before concluding
anything about these 23.

---

## 5. Standing conclusions

* **`Inductive` is a reader, not a decider, for this project.**  Its verdict is
  `~halts`, which moves `D_remaining` by zero; its *rule families* are what
  move rows.  Use it that way: `dump` a stuck row, decode the family, prove it
  in our own liveness-carrying closers.  Two of the three headline rows paid
  for themselves that way in one session.
* **Endpoint states are still not liveness** — now with a boarded
  counterexample, not just a structural argument (§1).
* **The champion's 32.8M-step prefix was never the obstacle.**  Binary-numeral
  fuel (`TCyclerN.cstepsN`) makes it a seconds-long `vm_compute`; the numeral
  guard on the `nat` side is the only trap, and §2 records it.
* **Do not re-run** `measure` on the 23 bonus rows at `default_config` family
  budgets.  Run `config_SBC`/`config_BEC` with derived `ExtraRules` instead.
