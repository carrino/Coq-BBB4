# Wave-26: the cascade bucket, closed out — and what the residue of it is

_Branch `claude/residue-reduction-4-2-dpb65q`, 2026-07-29.  Wave-25 boarded
the 57 gated cascade machines and 8 of the 12 octave-down rows, and named the
remaining 4 precisely (`docs/WAVE25_FINDINGS.md` §7): the same octave-down
shape except the closing count **enters one value in**.  This wave boards
those 4 and then re-measures the 17 one/two-count rows the bucket has left._

## 1. The one-line result

**All 4 board, first render, funext-only.**  `D_remaining` **431 → 427**
(4,729 of the frozen 5,156 settled, 91.7%).  The cascade route is now
**spent**: `cascade_probe.py --gate` over the whole 87-machine bucket reports
**69 GATED** — and all 69 are boarded (`CASB_*`) — against 17 one/two-count
rows and 1 main-count-at-4..7.  Nothing in `theories/` outside the four new
board files was touched; no new library Coq, no new checker surface, no new
axiom.

## 2. The 4: what "enters one value in" actually cost

Wave-25's §7 reading was exactly right, including the size of the fix.  At
outer index `S j'` the closing count runs `2^(j'+2)+1 .. 2^(j'+3)-1`, i.e.
it starts at `xI (pow2 (S j'))` and not at `pow2 (S (S j'))`.  Three
consequences, and only three:

* **the word.**  `E (xI (pow2 n)) = uS ++ rep uD n ++ soD` — the octave's own
  word with the odd digit peeled off the front and ONE FEWER unit copy behind
  it.  (`docs/WAVE25_FINDINGS.md` §7 wrote this as `sS ++ …`; the digit-1
  word is `uS` in `ENCDATA` terms — `sS` is the interior lap's start `post`
  and equals `uD` in every row of the table, inferred rows included, so it is
  the wrong name for this position.)  Proved by `rewrite <- epow2_; reflexivity`
  — it is the encoding fixpoint's own `xI` clause.
* **the fill twin.**  `E (fill (xI (pow2 n))) = rep uS (S n) ++ soS`, proved
  `exact (efill_ (S n))`: `fill (xI (pow2 n))` and `fill (pow2 (S n))` both
  reduce to `xI (fill (pow2 n))`, so the two are convertible and the existing
  `efill_` discharges it as-is.
* **nothing else.**  The way OUT is untouched — both values share a fill, so
  `CLOSEB`, `gclbx_` and `geo_` are byte-identical to the `big_in = 0` render.
  `fill_hop` needed no generalisation (`inner_to_fill_lift` is arbitrary-`v0`
  already), and `cascade_overflow` never sees the value.

Mechanically: `nestcert.cascade_law` reads the entry offset off the run
instead of demanding it be zero (`law['big_in']` ∈ {0, 1});
`cascade_transitions` gives `CLOSEA`'s destination the peeled prefix and one
fewer unit; `cascade_validate` replays the closing count from `2^(j+1)+big_in`;
and `cascade_emit.reps_low` swaps the landing-shape gate, the rendered word
and the index `replace`.  The `LOW_*` templates carry the count's value in
four holes (`@BIGV@`/`@BIGVP@`/`@BIGVE@`/`@BIGVF@`) plus an `@EXISEC@` block
that is EMPTY at `big_in = 0`.

**Regression:** all 65 previously committed `CASB_*` boards and the gated
`--proto` render come out **byte-identical** to the pre-change emitter
(checked mechanically, all 65 + proto).  The committed
`theories/Tests/CASC_*.v` differs from BOTH renders only in its doc header,
which was hand-edited when it was committed in wave-24 — pre-existing, not
this wave.

## 3. The 17 one/two-count rows, re-measured

Wave-25 §6 said "nothing about them is a cascade" and asked for a
re-measurement before any design.  Here it is.  **All 17 are `no boot chain`
rows**, and they fall into exactly three sub-families:

| n | shape | what the phase is |
|---|---|---|
| **10** | `2^(j-1)` count, then `2^j` count | TWO counts, one octave apart, **under two different alphabets** (`Alph_01_11_011` tail `11`, then `Alph_10_11_1` tail `1`) |
| **4** | one 5-value count `12..16` | a slow count spanning ~the whole phase with a GROWING far side (`far = 0…01`); profile `2^7:x6 2^6:x4` |
| **3** | one span, decoded at 5 octaves | every segment is a nested SHADOW of one span (`64..127`, `32..63`, … `4..7`, far growing by `11` per level) — one count, not five |

The 10 are the interesting ones and §4 is about them.  The 4 and the 3 are
each a distinct unsolved shape; note two of the 3 measure overflow **HIGHER**,
not `EXP2`, so they are not in the exponential-counter model at all.

## 4. The 10: measured, and the ONE thing still untried

The 10 are a two-count overflow whose **first count sits one octave DOWN**.
That is why they are `no boot chain` and not `no exit chain`:
`nestcert.families()` searches octaves `0 .. MAXOCT` only, so the
`2^(j-1) .. 2^j-1` count is never returned as a candidate; the boot is
searched into the `2^j` count instead, which begins ~130 configurations into
the phase behind a whole other count, and no chain reaches it.

Three things were measured this wave, in order, and the third is the one that
matters.

**(a) The octave floor is real but not the whole blocker.**  With `families()`
restricted to `oct = -1` the octave-down family is found on all 10 —
`Alph_01_11_011@…` tail `11`, unambiguous, top-scoring — and then the boot
chain into it **still does not derive** under the plain `_chain`
(`derive_chain`, no peel and no split).

**(b) Under the FRAMING search it derives on all 10.**  Wave-24's own lesson
had never been applied here — *"when a transition is known to exist by trace
and does not derive, the framing search space is (peel, split) before it is
anything else"* (`WAVE24_FINDINGS.md` §2), and B→A had NO chain at peel 0 at
any split.  Running `_frame_pair` on this boot: **10 of 10 derive**, all at
the identical framing —

    peel = (1, 0)   post = 6   cost = 4*i + 6   EXACT (no lift), 7 steps

One peeled unit copy, again.  So these rows are **not** an identification
failure and **not** a boot-chain failure; both pieces exist.

**(c) The remaining blocker is the SHIFT chain**, from the octave-down count's
fill to the octave-0 count's start — and it is NOT a bounds problem.  It does
not derive at `(peel ≤ CASC_PEEL = 3, split ≤ CASC_POST = 14)` on any of the
10, and widening to `(peel ≤ 8, split ≤ 30)` — **378 framings per machine** —
finds nothing either (checked on 3 of the 10; the 10 are structurally
identical everywhere else, all deriving at the same framing with the same
cost).  The second family is identified without ambiguity (`families()`
returns `Ip@…` tail `1`, the same three words as the `Alph_10_11_1` the
segment scan names — the known alphabet-aliasing that `cascade_runs`'
`prefer` exists for), so this is not a decode question either.

What the shift actually has to do is the thing no route here has: **re-encode
a `j`-length word from one digit alphabet into another** (`Alph_01_11_011`'s
`uD`/`uS` into `Ip`'s), across ~66 configurations.  That is a pass over the
whole word, not a turnaround at its head, and a single-index window chain is
the wrong shape for it however it is framed.  The exit chain is untested
behind it.

Note the other half of the cost if the shift lands: an octave-DOWN count is
`j - 1` blocks, which is not an sside count over `nat` without a reindex at
`j = S j'` plus a concrete `j = 0` case — exactly the reindex the octave-down
cascade route already builds (`cview_none_shape` + `lapz_`/`visz_`), so the
device exists and is not new theory.

## 5. Machines with a halt transition: a real effect, already spent

Worth recording because it is a natural thing to try next and the answer is
"no":

| | with a `---` halt | full 4×2 |
|---|---|---|
| in the frozen 5,156 | 1,537 (29.8%) | 3,619 |
| boarded | 1,492 | 3,237 |
| **settled** | **97.1%** | **89.4%** |
| still open | **45** | 382 |

One fewer reachable transition does make a machine easier for this
machinery — by 7.7 points — but that is why only **45** are left, 10.5% of
the residue against 29.8% of the frozen set.  The 45 sit in the same buckets
as everything else (26 `no interior chain`, 12 `no overflow phase`, 3 `no
inner family`, 3 `no anchor`, 1 `no boot chain`) and share no sub-route.
**They are not a batch.**

## 6. Do-not-retry, extended

Everything in `WAVE25_FINDINGS.md` §6 and `WAVE24_FINDINGS.md` §7 stands.
Add:

* Searching the 10 two-count rows' boot chain with the UNFRAMED `_chain` —
  measured, 0 of 10; with `_frame_pair` it is 10 of 10 at peel (1,0), post 6.
  This is the third bucket in a row where one peeled unit copy was the whole
  difference (B→A in wave-24, the octave-down boot in wave-25, this).  **Peel
  before anything else** is now the standing first move on any transition
  that traces but does not derive.
* WIDENING the 10's SHIFT-chain framing bounds — measured 0 at
  `(peel ≤ 3, split ≤ 14)` and 0 again at `(peel ≤ 8, split ≤ 30)`, 378
  framings per machine.  Do not widen further and do not go back to
  alphabets (the second family is identified unambiguously).  The shift
  re-encodes a `j`-length word between two different digit alphabets; that
  is a pass over the whole word and a single-index window chain cannot be
  it at any framing.  Whatever takes these 10 is a NEW piece, and naming it
  is the design question — not a search-budget question.
* Reading the 3 shadow-only rows as a one-count-per-level cascade — the five
  descending segments are nested re-decodings of ONE span, not five counts,
  and two of the three measure overflow `HIGHER`.
