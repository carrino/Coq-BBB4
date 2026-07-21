# Phase 2 design + differential validation (recon_G)

Goal of this recon: make the next session's Coq work start from certainty.
Everything below was **measured**, not assumed. Paths are absolute.

- Repo (Coq): `/home/user/Coq-BBB4`, branch `claude/d-census-shrinking-7amyyl`
- Repo (upstream C / certs): `/home/user/BBB`
- Scratch: `/tmp/claude-0/-home-user/2b01b1ad-6519-5466-986f-cbc04a643004/scratchpad/recon_G/`
- Extended mirror (scratch copy, **do not** overwrite `tools/irulesblk_prover.py` yet):
  `recon_G/prover_ext.py`

## 0. Bottom line

| set | n | upstream `bin/verify` | extended mirror | mechanisms needed |
|-----|---|-----------------------|-----------------|-------------------|
| v6 "needs blk,rulepfx" | 44 | **44/44 PASS** | **44/44 PASS** (full anchor+coverage) | block + `rulepfx` + `rmdok` |
| v7 "needs rulepfx,rulerunm" | 6 | **6/6 PASS** | **6/6 PASS** (full anchor+coverage) | block + `rulepfx` + `rmdok` + `rulerunm` |
| v4 "needs mmrow,nvar,tplrunmv" | 1 | **1/1 PASS** | not attempted — **recommend defer** | `nvar` + `mmrow` + `tplrunmv` (matrix meta-map) |

The Phase-2 mechanism split is **NOT** as the tags read. Measurement corrects it:

- **`rmdok` is mandatory for all 44 v6, not "possibly".** With the `rulepfx`
  parse fixed but exact-division kept, **0/44** close the meta cycle; adding
  `rmdok` → **44/44**. The v6res90 set is intrinsically remainder-bearing.
- **`rulerunm` is not separable for the 6 v7.** With the residue lattice
  collapsed to a plain variable, **0/6** self-validate their rules. None pass on
  `rulepfx` alone; the lattice is load-bearing inside the rule body.
- **v4 is one machine needing a whole orthogonal matrix-meta-map layer.** Defer.

No-regression: the extended mirror is byte-for-byte identical in verdict to the
landed `tools/irulesblk_prover.py` on the 428 v1 + 6 Phase-1 block certs
(**434/434, diff empty**) — all Phase-2 code is version/line-gated.

## 1. Ground truth — `bin/verify` cross-check

`make bin/verify` (up to date; `src/verify.c`, 15931 lines). Invocation
`bin/verify CERT...`, exit 0 iff all pass.

- 44 v6 in `/home/user/BBB/results/certs_v6res90/*.cert` → **44 PASS, exit 0**
- 6 v7 in `/home/user/BBB/results/certs_v7res46/*.cert` → **6 PASS, exit 0**
- 1 v4 `/home/user/BBB/results/certs_geom/1RB1RA_0RC0RB_1LC1LD_0RA0LA.cert` → **PASS**

The cert dirs partition the 51 exactly (diff of `tools/irules_deferred.tsv`
machine lists vs dir contents is empty for v6 and v7; the v4 machine's cert lives
in `certs_geom/`). Full matrix: `recon_G/validation_matrix.tsv`.

## 2. What the mirror needed (three edits, all gated)

The landed `irulesblk_prover.py` already carried *skeleton* `rulepfx` support
(sentinel `sent` in `eng_step`, `prefix=` splice in `appK_side`, `pfx` in
`ruleK_apply`, `rule_check` setting `sent=pfx`). It nonetheless scored **0/44**.
Two real bugs + one missing mechanism:

1. **`rulepfx` parse format bug.** Cert lines are `rulepfx IDX pl pr` (two
   numeric flags — verify.c:1057-1067), but the mirror parsed `rulepfx IDX L|R`.
   Every `rulepfx 0 1 1` was misread as R-only, dropping the L prefix. Fixed the
   parser to read `pl pr`. This alone flipped the 12 "rule validation failed"
   cases to "meta replay did not close" — isolating the remaining gap as `rmdok`.
2. **`rmdok` not implemented** in `find_binding` (see §3.2).
3. **`rulerunm` not parsed at all** (v7) — the run was silently dropped, so the
   rule shape was short by one run (see §3.3).

Toggle added: `g_latt` (default True) collapses refined runs to plain, used only
to *prove* rulerunm is non-separable (the 0/6 probe).

## 3. Per-mechanism semantics (with verify.c line refs)

### 3.1 `rulepfx` — prefix (near-head) rule matching  [v5+]
- **Cert:** `rulepfx IDX pl pr`, `pl,pr∈{0,1}`, not both 0 (verify.c:1057-1067).
  A set flag marks that side as a *near-head prefix*: the rule's runs match only
  the first `nl`/`nr` runs of the config; the untouched rest is spliced back.
- **Applier (verify.c `iv_rule_try`, 3206-3230):** a prefix side matches when
  `c->nl >= r->nl` (`>=`, not `==`); a **non-prefix** side must match exactly
  **and** must not be a sentinel side of the current replay
  (`c->nl != r->nl || g->sent[side]` ⇒ no match, 3215-3218). Symbols of the
  first `nl` runs must agree (3221-3229). Application modifies the first `nl`
  runs and leaves the rest; `iv_rebuild_side(..., sent)` keeps a trailing blank
  run as *content* (not background) when the side is a sentinel (3174-3196,
  3452-3453).
- **Sentinel self-validation:** a prefix rule's OWN body is validated with its
  prefix sides marked opaque (`g->sent[0/1]=r->pfx[0/1]`, 3025-3026). If the
  engine would read past the declared runs into the opaque rest, it must
  **hard-fail** (the app-exhausted branch). Mirror: `eng_step` `if not app:
  return None when sent[si]`. C: the app-run-out inside `beng_cross`.
- **Also (shape rule):** on a prefix side a trailing `sym==0` run is legal
  content next to the opaque rest, whereas on a whole side it is forbidden
  (background) — verify.c:2991-2996.
- Distribution across the 44 v6: per-rule flags `(0 1)`×30, `(1 0)`×14,
  `(1 1)`×110. All 6 v7 also use `rulepfx`.

### 3.2 `rmdok` — binding drain with a constant remainder  [v6+]
`g->rmdok = (c->ver >= 6)` (verify.c:3024, 15728). In the binding-drain
(verify.c:3299-3348, commit 3408-3456):
- Binding run count `e_j`, delta `-d_j`, lower bound `lb_j`. Let `R = e_j - lb_j`,
  `rmd = ((R.c0 mod d_j) + d_j) mod d_j`.
- Frozen versions require `rmd == 0`; **v6 allows `rmd != 0`** (3321-3323).
- **Every coefficient of `R` must be divisible by `d_j`** (3325-3329) — only the
  constant term carries the remainder.
- When `rmd != 0`, additionally require `min(e_j) >= lb_j + rmd` (R≥1 guard,
  3330-3331).
- `Rex = R.c0/d_j + 1` with coefficients `R.cf/d_j` (floor; 3348-3351).
- **Binding run ends at the constant `lb_j + rmd - d_j`**, dropping if it is 0
  (3425-3429).

**Key simplification, verified numerically and against the Coq shape:** because
the run's coefficients are all divisible by `d_j` and `Rex` uses floor division,
the *uniform* application `eaddmul e (-d_j) Rex` **already collapses to the
constant `lb_j + rmd - d_j`**. So neither the mirror's `appK_side` nor the Coq
`appBlk_side` needs a binding-run special case — **only `find_binding`/`bindsb`
changes.** Mirror diff (`find_binding`):
- old: `eeqb(dj*(Rex-1), e-lb)` (exact, both c0 and cf).
- new: `rmd = (e.c0-lb) mod dj`; reject if `rmd!=0 and not g_rmdok`; require
  `all(cf % dj == 0)`; keep `expr_ge(lo, Rex, 1)` (which is exactly
  `min(e) >= lb+rmd`). Survival of the other decs is unchanged (`surviveb`).

### 3.3 `rulerunm` — var run confined to a residue lattice  [v7 only]
- **Cert:** `rulerunm IDX side ri sym del lb mod res` (verify.c:1023-1056).
  Constraints: `mod>=2`, `0<=res<mod`, `del % mod == 0`, `lb >= mod+res`,
  `(lb-res) % mod == 0`. Each of the 6 v7 certs has **exactly one** such run.
- **Rule-body start/end (verify.c:3042-3048, 3085-3091):** the run's count is
  the fresh variable *scaled and offset*: start `mod*w + res`, end
  `mod*w + res + del`. The fresh-var lower bound is `lo_w = (lb-res)/mod`, and the
  recomputed bound must satisfy `mod*lo_w + res == lb` (3143-3146).
- **Apply-time residue precondition (verify.c:3245-3254):** to match a config
  run with count `e`, require `((e.c0 mod mod)+mod)%mod == res` **and** every
  coefficient `e.cf % mod == 0`. Since `del` is a multiple of `mod` and `e≡res`,
  the result stays on the lattice.
- Mirror: `BRRun` payload extended to `('V', del, lb, mod, res)`; `rc_start`/
  `rc_end`/`rc_lo` produce `mod*w+res`(+`del`) and `(lb-res)//mod`; `appK_side`
  adds the residue guard. Binding drain (`del,lb`) is **unchanged** — it operates
  on config counts exactly as `rulerun` does. `collect_decs` needs no change.
- **The scalar meta layer is untouched** for v7: the templates use plain
  `tplrun` + scalar `meta_a/meta_b`. `rulerunm` lives entirely in the rule
  applier / rule-body encoding.

### 3.4 `nvar` / `mmrow` / `tplrunmv` — multi-variable matrix meta-map  [v4]
The lone v4 machine (`1RB1RA_0RC0RB_1LC1LD_0RA0LA`). This is an **orthogonal**
mechanism layer; the rule bodies stay scalar, but the *meta* level becomes
vector-valued:
- **`nvar N`** (N∈{2,3}) growth variables — a count *vector* `x` (verify.c:911-915).
- **`mmrow r m0 m1 [m2] c`** — row `r` of the meta matrix `M` plus constant `c`
  (verify.c:916-928). The meta-cycle is `x -> M*x + cc` instead of scalar
  `k -> a*k + b`. Static soundness gates (verify.c:15570-15612): `M` nonnegative,
  not the identity, **inward** `M*xmin + cc >= xmin` componentwise, `xmin>=1`,
  `x0>=xmin`.
- **`xmin`, `x0`** — the lower-bound vector (seeds `g->lo`) and the anchor
  vector (verify.c:929-948, 15720-15723).
- **`tplrunmv side idx sym mv be`** — template run driven by variable `mv`
  (`mv<0` = constant `be`); denotation count `x[mv]` (or `be`)
  (verify.c:949-969). The meta target is `iv_tpl_want` = row `M[mv]` applied to
  the vector + `cc[mv]` (verify.c:2310-2321, 15769-15803).
- Anchor compares the concrete tape against the template with `x0` substituted
  (verify.c:15668-15704).

**Enumeration of the port cost** (why defer, see §7).

## 4. Coq fork map (concretized from the landed engine)

Read: `theories/Checkers/IRules/{EngineK,RulesBlk,RulesK,MetaBlk}.v`. The landed
block engine is the **v3 block** checker (Phase 1). Structure and where Phase 2
cuts:

### Stays unchanged (reused verbatim)
- **`EngineK.v`** block denotation `bdside`/`bsem`, `bpush`/`bmerge_adj`/
  `btrim_blanks`, block-hop `hop_sim`/`bhop_result`, re-blocking
  `breblock_side`, `bcanon`, `bstreams_eq`. Only the step's app-exhausted branch
  gets a sentinel (below).
- **`MetaBlk.v`** the **scalar** meta layer: `btpl_start`, `btpl_want a b`,
  `btpl_shift`/`bwant_shift`, `BIRCert`. v6 and v7 both use scalar
  `meta_a/meta_b` (0 of 50 use `mmrow`), so this file barely moves — a
  `MetaBlkPfx` fork only swaps in the pfx-aware rule check and threads the new
  `BRule` field. (The matrix meta-map is v4-only and out of scope.)
- **`RulesK.v`** `decs_side`, `surviveb`, `rexOf`/`ediv_expr`, `appK_side`
  inversion lemmas — shapes reused by the block fork.

### Forks (v6: `rulepfx` + `rmdok`) — `RulesBlkPfx.v` on top of `RulesBlk.v`
1. **`BRule` record** (`RulesBlk.v:30`): add `br_pfx : bool * bool`.
2. **`appBlk_side`** (`RulesBlk.v:128-148`): base case `[] , []  => Some []`
   forks to a prefix variant `appBlkPfx_side` with `[] , rest => Some rest`
   (splice the untouched tail). Its denotation lemmas
   (`appBlk_side_den0/denS/denR`, `_bge`, `_vlen`, 254-413) fork to carry the
   spliced `rest` through `bdside` (the rest denotes identically on both sides).
3. **`find_binding`/`bindsb`** (`RulesK.v:100-115`): the exact-division conjunct
   `eeqb (eaddmul (econst 0) (-d) (eaddc Rex (-1))) (eaddc e (-lb))` (line 105)
   splits into
   (a) a **coefficient-divisibility** predicate on `e - lb` (keep), and
   (b) a **c0-remainder** allowance gated by an `rmdok:bool` parameter, with the
   extra `expr_ge lo e (lb+rmd)` guard when `rmd<>0`.
   `rexOf` (floor `ediv_expr`) is **unchanged**; the binding-run terminal value
   is still produced by the existing `appBlk_side` `eaddmul` (proved constant).
4. **`ruleBlk_apply`** (`RulesBlk.v:159-180`): fork to `ruleBlkPfx_apply` —
   length checks become `pfx ? c.nl>=r.nl : c.nl==r.nl (and not sent)`; call the
   pfx `appBlkPfx_side`; pass `rmdok` into `find_binding`.
   **Theorem `ruleBlk_apply_sound`** (`RulesBlk.v:415`) forks to
   `ruleBlkPfx_apply_sound`: the Reach witness now covers the matched prefix
   only, with the spliced rest unchanged; the `rmdok` last round is valid because
   the pre-last count is `lb+rmd >= lb` (new sub-lemma; the surviving-runs part
   reuses `surviveb`).
5. **`breplayK` / `bruleBlk_check` / `check_rulesBlk`**
   (`RulesBlk.v:958/1045/1091`, sound lemmas 986/1055/1114): thread `sent` and
   `rmdok`; `bruleBlk_check` sets `sent := br_pfx r` for a rule's own validation.

### Forks (engine sentinel) — `EngineK.v` / `beng_cross`
- **`beng_step`/`beng_cross`** (`EngineK.v:299,949-972`): thread a
  `sent : bool*bool`. In the app-exhausted branch (the spin-out / read-blank
  case), **fail** when the exhausted side is a sentinel. `beng_step_sound`
  (974) extends: on a sentinel side the step is only taken when it did not read
  past declared runs. This is the "`beng_step`'s `[]` branch must fail when
  `sent[side]`" from NEXT_SESSION's sketch.

### Forks (v7: `rulerunm`) — on top of the v6 fork
- **`BRRun`** payload `(BSym * RCnt)`: `RCnt` gains a refined constructor
  `RVm (del lb mod res)` (or extend `RV`). `brstart`/`brend`/`brlbs`
  (`RulesBlk.v:37-56`) produce `mod*w+res`, `mod*w+res+del`, `(lb-res)/mod`.
- **`appBlkPfx_side`** `RV` arm gains the residue guard
  (`e.c0 ≡ res [mod]`, coeffs `≡0 [mod]`). Soundness: the refined start
  denotation equals the plain one on the lattice; the residue guard makes the
  match sound. `decs_side_blk` unchanged (uses `del,lb`).
- Scalar meta layer (`MetaBlk.v`) still unchanged.

## 5. Corruption tests to write (differential-sound)

Harness `recon_G/corrupt_test2.py` (verify vs mirror, matched fuel). All in
mirror scope reject in **both**; result table:

| corruption | verify | mirror | note |
|---|---|---|---|
| v6 rule delta `-2→-3` | reject | reject | ✓ |
| v6 rule lb `3→2` (too small) | reject | reject | ✓ (self-val fails) |
| v6 rule lb `3→5` (too large) | reject | **accept** | strictness gap, §6 |
| v6 `meta_a`/`meta_b` bump | reject | reject | ✓ (cycle can't close) |
| v6 `blk 01→00` | reject | reject | ✓ |
| v6 `tplrun be 1→2` | reject | reject | ✓ |
| v6 `k0 −1` | reject | reject | ✓ |
| v6 `kmin 8→9` | accept | accept | ✓ (larger kmin still sound) |
| v7 `rulerunm res 1→0` | reject | reject | ✓ |
| v7 `rulerunm mod 2→4` | reject | reject | ✓ |
| v7 `rulepfx 1 1 0→0 1` | reject | reject | ✓ |
| v7 `meta_a 2→1` | reject | reject | ✓ |
| v7 `tplrunL 1 0→1 1` | reject | reject | ✓ |

Recommended **Coq** corruption `.v` fixtures (one per mechanism), mirroring the
above so each `_sound` theorem is exercised on a rejected cert:
- prefix flag flip (both directions), so the `pfx ? >= : ==` branch is tested;
- `rmdok` remainder tamper (change `lb` so `rmd` shifts → binding run ends at a
  wrong constant → cycle fails to close);
- `rulerunm` `res`/`mod`/`del` tamper (residue guard rejects);
- sentinel: a prefix rule whose body reads into the opaque rest must fail
  self-validation;
- meta-map (`meta_a/meta_b`) tamper — non-closure by fuel exhaustion.

## 6. The one strictness gap (surface, don't hide)

`bin/verify` **recomputes the minimal rule bounds and requires the cert to state
them exactly** (verify.c:3130-3153, "recomputed bounds must equal the
certificate's exactly"). The mirror (and the landed Coq applier) **trust the
cert's `lb`** and use it as `lo` during self-validation. Consequence: a
**non-minimal (too-large) `lb`** is accepted by the mirror but rejected by
verify (`lb 3→5` above). This is **soundness-preserving** — a larger `lb`
restricts the rule's domain, and the never-quasihalts decision stays valid — but
non-canonical. A **too-small** `lb` is correctly rejected by both (self-val
fails). Recommendation: the Coq soundness proof does **not** need the exact-bound
check; either (a) replicate verify's bound-recomputation-equality for parity, or
(b) document the tightness relaxation. Soundness is unaffected either way.

Two second-order notes:
- **Fuel.** The mirror's flat `FUEL=300000` lets a broken meta map grind
  (diverging symbolic runs) before failing. It never false-accepts: with a fuel
  matched to verify's caps (`IVOPS=200000`, `IVRULEOPS=20000`, `IVAPPLYCAP=4096`,
  `IVHOPCAP=1024`; verify.c:2217-2219,2423) — or even `fuel=3000` — real certs
  still pass (<0.01 s) and every corruption fails (<0.1 s). The Coq checker uses
  an explicit `Nat` fuel, so this is a wall-clock note only. Set Phase-2 fuel to
  verify's `IVOPS`/`IVRULEOPS`.
- **Whole-rule-on-sentinel-side guard** (verify.c:3215-3218, the
  `|| g->sent[side]` disjunct) is **not** modeled in the mirror's `ruleK_apply`
  (it does not receive `sent`). It did not affect the 50, but the Coq
  `ruleBlkPfx_apply` **must** carry it (a whole-side rule can never soundly match
  a sentinel side of the current replay). Add it and its `_sound` obligation.

## 7. v4 recommendation — DEFER (disproportionate)

One machine, and a whole orthogonal layer:
- New `nvar` growth-*vector* state through the meta driver; `EngineK` `Expr`
  already carries a coefficient vector, so the value layer mostly exists, but
  every meta definition (`btpl_start/btpl_want/btpl_shift/bwant_shift`,
  `BIRCert`, `irulesblk_check_neverqh`) becomes vector-valued.
- **Matrix meta-map** `x -> M*x + cc` replacing scalar `a*k+b`. The soundness
  argument changes from scalar affine monotonicity (`a>=1`, not identity ⇒ growth)
  to **monotone-nonnegative-matrix growth** (M nonnegative, not identity, inward
  at `xmin` ⇒ the orbit is unbounded). That is a genuinely new
  Perron-Frobenius-flavored Coq proof, not a reuse of the scalar `btpl_shift`.
- `tplrunmv` vector template denotation + a multi-variable anchor comparison.

Cost is dominated by the matrix-growth soundness lemma and is shared by **zero**
of the other 50 holdouts. Recommend: **Phase 2 = the 50** (44 v6 + 6 v7); make
v4 its own later "multivar / matrix-meta" phase or leave it deferred. If ever
pursued, the mirror side is ~40 lines (Expr is already multi-var); the Coq side
is the real cost.

## 8. Session plan (Coq, next session)

1. **Engine sentinel first** (small, self-contained): thread `sent` through
   `beng_cross`/`beng_step`; fail the app-exhausted branch on a sentinel side;
   extend `beng_step_sound`. Gate everything else on this.
2. **`RulesBlkPfx.v`**: `BRule.br_pfx`; `appBlkPfx_side` (splice `rest`) + fork
   its denotation lemmas; `find_binding`/`bindsb` `rmdok` parameter (coeff-div +
   c0-remainder + `lb+rmd` guard); `ruleBlkPfx_apply` (pfx length checks,
   sentinel-side guard, `rmdok`) + `ruleBlkPfx_apply_sound`. Prove the new
   `rmdok`-last-round sub-lemma.
3. **`breplayK`/`bruleBlk_check`/`check_rulesBlk` forks** threading `sent`,
   `rmdok`; `MetaBlkPfx.v` swapping in the pfx rule check (scalar meta
   unchanged). Differential-validate against the mirror on the 44.
4. **Batch files** `IRulesBlkPfx_Batch_*.v` for the 44; corruption fixtures (§5).
5. **`rulerunm` on top**: `RCnt` refined constructor; `brstart/brend/brlbs`;
   residue guard in `appBlkPfx_side` + `_sound`. Batch the 6 v7. Differential
   against the mirror's lattice path.
6. Re-run `bin/verify` and the extended mirror as the two external oracles at
   each landing; keep the mirror's `--no-anchor` diff vs the original at 434/434.

## 9. Reproduction (commands)

```
S=/tmp/claude-0/-home-user/2b01b1ad-6519-5466-986f-cbc04a643004/scratchpad/recon_G
# upstream oracle
/home/user/BBB/bin/verify /home/user/BBB/results/certs_v6res90/*.cert   # 44 PASS
/home/user/BBB/bin/verify /home/user/BBB/results/certs_v7res46/*.cert   # 6 PASS
# extended mirror (full anchor+coverage)
python3 $S/prover_ext.py --dir /home/user/BBB/results/certs_v6res90     # 44/44
python3 $S/prover_ext.py --dir /home/user/BBB/results/certs_v7res46     # 6/6
# no-regression vs the landed mirror (434/434 identical)
python3 tools/irulesblk_prover.py --no-anchor --dir $S/phase1_corpus | sort > a
python3 $S/prover_ext.py          --no-anchor --dir $S/phase1_corpus | sort > b
diff a b   # empty
# corruption differential
S=$S python3 $S/corrupt_test2.py
```
