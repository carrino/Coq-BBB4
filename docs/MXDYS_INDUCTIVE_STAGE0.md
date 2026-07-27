# Stage 0 — mxdys' `Inductive` decider measured against the (4,2) residue

_Run 2026-07-26 on branch `claude/coq-bbb4-residue-removal-lt5yac`.  This is the
decision gate that `docs/MXDYS_DECIDERS_PLAN.md` §3 said not to skip.  It is
now run, and it changes the plan._

Everything below is measured, with the reproduction commands inline.  Nothing
here touches `theories/Census/`; no board is claimed.

---

## 0. Bottom line

1. **The build risk was imaginary.**  The dependency closure of
   `Inductive_inf.v` is **15 files and compiles in 35 seconds** — not the
   "~1 month" the README quotes for the whole repo.  It extracts to a native
   OCaml decider with stock `apt` Coq 8.18 + `libcoq-core-ocaml-dev`.

2. **The harness is faithful.**  60 machines taken from mxdys' own
   `Indv1.v` reproduce **60/60 as `nonhalting`** through our extracted binary
   at his exact settings (`default_config`, `T = 100000`).  So negatives are
   real negatives.

3. **Gate (ii) is zero, and it is zero *structurally*, not by tuning.**  On
   those same 60 machines — ones his decider *decides* — the rule chain's
   `config_expr` endpoints carry **1 or 2 distinct states, never more**, on
   *six-state* machines.  Reading per-state visit witnesses off the rule
   endpoints (`MXDYS_DECIDERS_PLAN.md` §1b, the `vis_via_ovf` mechanism)
   **does not work.**

4. **The counter families in his own tree are human-hinted, not searched.**
   `IndSBCv1.v` (sync bouncer counter): 106 of 107 lemmas pass a hand-built
   `config_SBC`.  `IndBECv1.v` (bell eats counter): 100 of 122 pass
   `config_BEC`.  The ~6,400 hint-free lemmas (`Indv1-7`, `IndBGAS`,
   `HLv1/2`) are *not* the counter shapes.  Our residue is counters.

5. **The real find is the `ExtraRules` hint interface** (§4).  It is a typed,
   seven-constructor vocabulary of counter increment/decrement rules stated as
   `-[tm]->+` progress facts over `(d0, d1, d1a, qL, qR, QL, QR)`.  That is our
   anchor family + lap certificate in his notation — and it is where the states
   actually live.

**Verdict on the plan's gate:** this is the middle branch —
*"(ii) near zero but (i) large ⇒ the work moves INSIDE a rule."*  Do **not**
start Stage 1 (the `Stream Sym ↔ nat -> Sym` bridge) expecting endpoint
liveness to fall out.  It will not.

---

## 1. What was built

```
apt-get install -y coq ocaml-findlib libcoq-core-ocaml-dev   # Coq 8.18.0, OCaml 4.14.1
cd busycoq/verify
for f in LibTactics Eqb HashTable Helper TM Compute Flip BBinf Permute \
         Pigeonhole Enumerate Individual Ternary Inductive Inductive_inf; do
  coqc -native-compiler no -Q . BusyCoq -Q ./BigInt BigInt $f.v
done                                                        # 35 s total
ocamlfind ocamlopt -thread -package coq-core.kernel -linkpkg \
  Inductive.mli Inductive.ml decider.ml -o decider
```

`Inductive_inf.v` instantiates the functor at **`BBinf`** — `Q = Sym = N`,
unbounded arity — so **no `BB42.v` / `Individual42.v` is needed for Stage 0**.
Its `TM'_from_str` parses bbchallenge notation directly, and `---` maps to
`None` (halt) because `dir_from_char '-' = None`.  Confirmed end to end:

| machine | verdict |
|---|---|
| `0RB---_0LA---` (trivial cycler) | `nonhalting` |
| `1RB1LC_1RC1RB_1RD0LE_1LA1LD_---0LA` (BB5 champion) | `halts at 4 0` = state E, symbol 0 ✓ |

**Caveat on provenance:** `BBinf.v` carries the tree's only two `Admitted`
lemmas — `all_qs_spec` and `all_syms_spec`, which cannot hold for an unbounded
alphabet.  Extraction warns about exactly these.  They are `Prop`-only and
irrelevant to a *search oracle*, but they mean **the extracted binary is an
oracle, never a proof**.  A real `BB42` context (45 lines, patterned on
`BB52.v`) would be needed for anything load-bearing.

### `theories`-free instrumentation

`Inductive.v`'s extracted `exec` prints only `nonhalting` / `halts at` /
`failed to decide`.  For us that verdict is worth nothing — `~halts` moves
`D_remaining` by zero.  So `busycoq/verify/InductiveDump.v` (new, this branch)
adds a printer and two collectors over the data `hlin_layers_steps` already
returns, and extracts a second binary `dumper`:

* `states=` / `nstates=` — every `Q` appearing in any `config_expr` in any
  `prop0_expr` of all four `prop_expr` slots of every `hlin_layer`.  A
  deliberate **over**-approximation of "states at rule endpoints", so a
  negative here is conclusive.
* `flags=` — bit 0 `nat_mul`, bit 1 `nat_powsum`, bit 2 `nat_powsum2`,
  bit 3 a `side_binary*` counter tape constructor; plus `powsum_k=` for the
  bases.
* `--dump` prints the whole layer hierarchy as readable rules.

It proves nothing and is UNTRUSTED reporting; it never enters a proof.
It also distinguishes a case `exec` hides: `inl` (step budget `T` exhausted)
versus a genuine failure — both print "failed to decide" in the stock binary.

---

## 2. Gate (ii), measured on mxdys' own successes

60 machines sampled from `Indv1.v`, run at his settings:

```
./dumper --maxT 100000 "<machine>"
```

| result | count |
|---|---:|
| `verdict=nonhalting` | **60 / 60** |
| `nstates=1` | 9 |
| `nstates=2` | 51 |
| `nstates≥3` | **0** |
| `flags=1` (needs `nat_mul`) | 58 |
| `flags=0` | 2 |

These are **six-state** machines and the chain never names more than two
states.

### Why this is structural, not a tuning failure

`Inductive.v`'s acceptance condition is

```coq
Definition check_nonhalt(x:prop_expr):bool :=
match x with
| ([],[multistep_lb_expr s1 s2 (nat_var v1)]) => s1 == (side_0inf,side_0inf,q0,R)
| _ => false
end.
```

The certificate it accepts is a **single** `prop0_expr` naming exactly **two**
configurations — the blank initial config at `q0`, and one other.  So the
top-level certificate *cannot* mention more than two states, by construction.
Our collector additionally swept every subordinate layer and still found ≤ 2,
which says the accelerated rules stay anchored at the same one or two
turnaround states.  Everything else the machine does happens *inside* an
accelerated rule, where the certificate does not record it.

This is the same fact from the other side: mxdys' remark that his decider
"can only decide a TM when it can model the forward behavior exactly" is
true, and the exact model *is* there — but the **non-halting certificate it
emits is a lossy projection of that model**, keeping only what `~halts`
needs.  The state-visit information exists during the search and is discarded
at certificate-emission time.

---

## 3. The black-box search on our residue

`tools/closeout/frozen_unproven.txt` (1,157 machines on this branch; the
prompt's 1,176 is the pre-wave-14 count).

* 30-machine head sample, `default_config`, `--maxT 100000`: **0 decided**.
* More budget is not the lever: `--maxT 5000000` (50×) on
  `0RB---_0RC0LD_1LD1RC_0LA1LB` finishes in **142.7 s** and still returns
  `verdict=timeout` — i.e. `hlin_layers_steps` returned `inl`, the step budget
  ran out without the search converging.
* A randomized 120-machine sample across five configurations (`default`,
  `--exploop`, `--arithseq`, `--block-size 2`, `--block-size 3`) is the
  larger measurement; numbers land in §6.

This is consistent with §4: the search half of `Inductive` is not what ate the
counter families in his own tree either.

---

## 4. `ExtraRules` — the part that is actually worth having

```coq
Inductive ExtraRules :=
| side_binary_inc_rule      (d1 qL qR:list Sym)             (QL QR:Q)
| side_binary_Pos_inc_rule  (d0 d1 d1a qL qR:list Sym)      (QL QR:Q)
| side_3ary_Pos_inc_rule    (d0 d1 d2 d1a d2a d2' qL qR:list Sym)(QL QR:Q)
| side_binary_dec_inc_rule  (d0 d1 d1a qL qR:list Sym)      (QL QR:Q)
| side_binary_dec_ov0_rule  (d0 d1 d1a d1b qL qR:list Sym)  (QL QR:Q)
| side_binary_dec_ov1_rule  (d0 d1 d1a d1b qL qR:list Sym)  (QL QR:Q)
| side_BL_inc_rule          (f0 d0 d1 d1a f0' d1' qL qR:list Sym)(QL QR:Q)
.
```

and its obligation, e.g. for `side_binary_Pos_inc_rule`:

```coq
(forall l r n,
   l <* d0 <* d1^^n <{{QL}} qL *> r  -[ tm ]->+
   l <* d1 <* d0^^n <* qR {{QR}}> r) /\
(forall r n,
   const s0 <* d1a <* d1^^n <{{QL}} qL *> r  -[ tm ]->+
   const s0 <* d1a <* d0 <* d0^^n <* qR {{QR}}> r)
```

Read that against our own vocabulary and it is the **same object**:

| mxdys | ours |
|---|---|
| `d0`, `d1`, `d1a` | the counter alphabet words — our `Ip`/`Jp`/`Kp`/`Dp`/`Mp`/`Bp`/`Gp` families, what `alphabet_infer.py` infers from the tape |
| `qL`, `qR` | the anchor HEAD/TAIL symbols (wave-9 had to make these parameters too) |
| `QL`, `QR` | the anchor states |
| the interior clause | our interior lap |
| the `const s0 <* d1a` clause | our **overflow** lap, at the blank far side |
| `ExtraRules_WF` discharged by `solve_rule`/`es` | our per-machine `vm_compute` board |

`config_SBC` supplies **two** of these (a `dec_inc` and a `dec_ov1`) plus a
block size, an `initial_steps` offset, `mnc 4` and `enable_exp_toplevel_loop`
— i.e. interior rule + overflow rule + framing, exactly the pair our
`emit_lapcert.py` searches for.

Three things follow.

* **The alphabet was never the binding constraint for him either.**  He hands
  it to the tool.  `WAVE14_FINDINGS.md` reached the same conclusion from the
  other direction (inferring 18 alphabets bought diagnosis, not boards) — that
  entry in the do-not-retry list is now *explained*, not just observed.
* **`side_binary_dec` / `side_binary_Pos` / `side_BL` are the tape
  constructors carrying the `powsum` count language**, i.e. our measured
  `Θ(2^j)` overflow wall.  This is the §1c payoff and it survives intact.
* **The states are present in the hint** (`QL`, `QR`) and the hint is proved
  by step evaluation, where every intermediate state is visible.  So the
  liveness information we need lives at the *rule* level, not the chain level
  — which is precisely "the work moves inside a rule".

### 4a. The hint path is now drivable from our side — validated

The stock CLI cannot express an `ExtraRules`, so the extracted binary can only
ever run in the hint-*free* mode, which is not the mode that ate the counter
families.  `InductiveDump.v` now adds `--bec / --becpos / --dec / --ov0 /
--ov1` (words as digit strings, `.` = empty; states as letters), plus
`--initial-steps` and `--mnc`.

Validated by reproducing mxdys' own `IndSBCv1.v` `nonhalt3`
(`config_SBC 5604 3 A B A B [0] [1] [0;1;0] [1] [0;0;1;1] [0;0;1;0] [0]`) on
`1LB---_0LC1RE_0RD1LF_1LC1RB_0RF0RA_0LA0RB`:

| mode | verdict | time |
|---|---|---|
| hint-free (stock black box) | `timeout` | 9.15 s |
| **hinted, same machine** | **`nonhalting`** | **0.067 s** |

```
./dumper --block-size 3 --initial-steps 5604 --exploop \
         --dec 0011 0010 0 0 1 A B \
         --ov1 0011 0010 0 0 010 1 A B \
         --maxT 200000 "1LB---_0LC1RE_0RD1LF_1LC1RB_0RF0RA_0LA0RB"
```

The hinted run reports `flags=11` — `nat_mul` **and `nat_powsum`** and a
counter-side tape constructor.  So the exponential count language we are
walled on is exercised, and observable, on a real cert.

It also reports `nstates=2` — **on a hinted counter cert, with the states
supplied in the hint itself.**  Gate (ii) fails here too.  That is the
cleanest possible statement of the finding: even when you hand the tool the
anchor states, the certificate it emits still names only two.

### 4b. Our inferred alphabets map onto his hints exactly

`tools/counters/alphabet_infer.py` infers a triple with

```
E xH = C        E (xO q) = A ++ E q        E (xI q) = B ++ E q
```

and `side_binary_Pos_inc_rule d0 d1 d1a qL qR QL QR` obliges

```
forall l r n, l <* d0 <* d1^^n <{{QL}} qL *> r -->+ l <* d1 <* d0^^n <* qR {{QR}}> r
forall r n,   const s0 <* d1a <* d1^^n <{{QL}} qL *> r -->+
              const s0 <* d1a <* d0 <* d0^^n <* qR {{QR}}> r
```

i.e. **`(A,B,C) ↔ (d0,d1,d1a)`**, with the second clause pinned to
`const s0` being precisely our overflow-at-the-blank-far-side lap.  Sanity run
over the first six residue machines: 6/6 infer a family at 160 words each
(5 × `Kp` `A=[0] B=[1] C=[1]`, 1 × NEW `A=[0,1] B=[1,1] C=[1]`), each with its
anchor state and side.  What inference does **not** give is `qL`/`qR` (anchor
head/tail words) and `QR`; those are a small search, and `anchor_profile.py` /
`emit_lapcert.py` already compute the same objects on our side.

---

## 5. What to do with this

The plan's Stage 1/2/3 as written assumed endpoint liveness.  Revised:

* **Do not** build `theories/Bridge/BusyCoqTM.v` yet.  Its one theorem
  (`multistep_csteps`) is still correct and still wanted, but on its own it
  buys nothing while gate (ii) is zero.
* **Do** treat `ExtraRules` as a *design specification* for extending
  `LapDecider`, which is the cheaper fallback `MXDYS_DECIDERS_PLAN.md` §5
  already identified — now with a verified reference implementation to copy
  rather than a design to invent.  Concretely: our lap model is affine
  (`docs/LAPDECIDER.md`); the extension needed is `powsum k` and one
  multiplication, on the **overflow** branch, with the far side pinned to
  `const s0` exactly as `side_binary_Pos_inc_rule`'s second clause does.
* **The liveness theorem is unchanged and is still ours.**  It is the same
  "the lap visits only states in `S`" fact that `NEXT_SESSION_PROMPT.md` item
  (1) wants for the 164 quasi-halters — a states-visited variant of
  `wsteps_frame` / `cycL` / `cycR`, which today state only their endpoints.
  One theorem, not one per machine.  **Both fronts now need the same theorem,
  which makes it the highest-value single piece of work on the board.**
* If we do want to use his search as an oracle for the counter families, the
  next experiment is to drive `config_SBC'` with **our** inferred alphabets
  (`alphabet_infer.py` → `(A,B,C)` triples → `d0/d1/d1a`), not to keep running
  the hint-free black box.  `InductiveDump.v` would need a CLI for
  `set_ex_rules`; the stock binary has no way to express a hint.

---

## 6. The three numbers, over the whole residue

All 1,157 machines of `tools/closeout/frozen_unproven.txt`, at mxdys' exact
hint-free `Indv1.v` recipe (`default_config`, `T = 100000`):

| outcome | count |
|---|---:|
| step budget exhausted (`inl`) | 1,145 |
| **`nonhalting`** | **12** |
| `halts` | 0 |

* **(i) 12 / 1,157 — 1.0 %.**  The hint-free search does essentially nothing
  on this residue.  (0 reported halting, which is the expected consistency
  check: these are non-halting machines.)

* **(ii) 0 / 1,157.**  The over-approximating collector reports state counts
  `2`×8, `3`×3, `4`×1 among the 12, i.e. one apparent full-coverage machine —
  `1RB1RD_1RC0LD_1LB0RA_1LC0LC`.  Dumping it shows the apparent coverage is an
  **artifact of the over-approximation**: the accepted certificate is

  ```
  STEPLB 0^inf {0}> 0^inf  -->(>=v1)  1.(0)^(+ v1 23)….0^inf {3}> 0^inf
  ```

  which names states **A and D only**.  The other two states come from
  scratch propositions in the `w1_`/`w0_` layer slots that `check_nonhalt`
  never inspects.  So the honest count of machines whose *certificate* covers
  all four states is **zero**, and the generous over-count still only produced
  one.  This is §2's structural argument confirmed on the residue itself.

* **(iii)** Among the 12: **11 need `nat_mul`**, 1 needs nothing, and **0 need
  `nat_powsum`**.  That is itself informative — the hint-free search only ever
  succeeds on residue machines whose cost is at most quadratic, and never
  reaches a `powsum` machine.  It gives up exactly at the EXP2 wall
  `ovfshape.py` measured (496 EXP2 of 1,176), rather than crossing it.
  The `powsum` capability is real, but it is reached through the **hints**
  (§4a's hinted cert reports `flags=11`, i.e. `nat_powsum` set), not through
  the black-box search.

### Feeding our own alphabets in as hints

27 of a random 40 residue machines yield a counter family from
`alphabet_infer.py` at 160 words each.  Mapping `(A,B,C) → (d0,d1,d1a)` and
gridding the parameters inference does not supply (`qL`, `qR`, `QR`; `QL`
pinned to the inferred anchor state; `--block-size |A|`; `--exploop`;
`maxT 30000`):

* one rule at a time (`--becpos` **or** `--dec`), 72 configs/machine: **0/27**.
* the interior+overflow **pair** (`--dec` **+** `--ov1`), as `config_SBC`
  actually supplies them: see §6a.

**This negative is bounded, and the bound matters.**  What it rules out is the
*naive* grid.  What it does **not** rule out, and what a follow-up should vary
before concluding anything, is:

1. **`initial_steps`.**  Every one of mxdys' SBC certs passes a per-machine
   offset in the 1,268–7,450 range.  We passed 0, so the search starts from a
   blank tape on which the counter structure has not yet formed.  This is the
   most likely single cause.
2. **`qL`/`qR` word length.**  His are up to `[0;1;0]`, `[0;1;1;0;1]`; we
   gridded only `{ε, 0, 1}`.
3. **The two anchor state *pairs*.**  `config_SBC` takes `QL QR QL' QR'` —
   the interior and overflow rules may be anchored at *different* states.  We
   forced them equal.

None of that changes the gate: even a hint that lands returns a certificate
naming two states (§4a, measured on his own machine).  It changes only
whether their engine is usable as a rule-discovery oracle for our checker.

---

## 7. Do-not-retry additions

* **RRBA is the wrong instrument for this project, twice over.**  Its verdict
  type is bare `bool` (`decide_loop2 : ... -> bool`, spec yields `~halts tm c0`)
  and its internal record structure is `loop1_t := int*int*int*int` — four
  machine words, no state, no symbolic configuration.  There is nothing to
  read liveness off of *even on a success*.  It also targets shift-recursive /
  sync bi-counter (Skelet10) shapes.  A previous session churned on RRBA and
  got nothing; that is expected, not bad luck.
* **`RWLAcc`** — same problem: `decide_nonhalt T : bool`.
* **`UBRRBA`** — halting only, per its own README entry.
* Of the whole suite, **`Inductive` is the only decider whose certificate
  carries a state at all** (`config_expr = side_expr*side_expr*Q*dir`), and it
  carries at most two of them.
* **RETIRED:** "run mxdys' decider over the residue and the boards fall out."
  Measured; they do not.
