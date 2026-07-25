# How much is left, and where it is — measured, wave-12

_Written after John's anchor correction (`UNCERTAIN_MACHINES.md` §1) turned
out to be systematic rather than a one-off.  This file replaces guesswork
about the residue with a measurement._

## The measurement

`tools/counters/reanchor_probe.py` takes each unproven machine, runs it from
the blank tape, and finds the anchor family `(state, encoding, tail)` with the
most decodable snapshots — **without** using `derive_tail`, whose synthetic
trailing blank is what mis-anchored the §1 bucket.  It then measures the
interior laps from that anchor.  `ovkind_probe.py` follows up on the affine
ones and classifies where the overflow lap actually lands.

Sample: the first **400** of the 1,388 unproven machines.

| | n | share |
|---|---:|---:|
| anchor found, interior laps **affine** | **279** | 70% |
| anchor found, laps not affine | 19 | 5% |
| no decodable anchor family | 102 | 25% |

Every one of the 279 has **slope 4**.  By encoding/tail:
`Ip` tail `[S1]` 153 · `Jp` tail `[]` 59 · `Jp` tail `[S0]` 34 ·
`Jp` tail `[S1]` 27 · rest 6.

## Where the overflow lands (the 279)

| overflow `2^K-1 -> ?` | n | route |
|---|---:|---|
| `2^K` — **standard** | **95** | existing templates; only the anchor was wrong |
| `2^K + 1` | 69 | one cell past the anchor — landing-detection detail, likely also existing templates |
| `2^(K+1)` — **widen** | 35 | the width-widening encoding scoped in `UNCERTAIN_MACHINES.md` §1 |
| `3·2^K` and other small multiples | 41 | same shape, different stride |
| no close found in budget | 39 | unprofiled |

## What this says

**The residue is dominated by ordinary counters, not exotic ones.**  70% of
the sample is affine at slope 4 the moment the anchor is read correctly.  The
bottleneck this whole session was `derive_tail`'s anchor choice, not the lap
templates — and every emitter (`emit_interleave`, `emit_shape1`,
`emit_shape4`, `emit_ixp`, `emit_wall`, `emit_wallj`) inherits it.

Extrapolated to the full 1,388 (sample rate × pool, so ±, but the direction is
not in doubt):

| bucket | est. machines | work |
|---|---:|---|
| standard overflow, affine | **~330** | fix the anchor search, re-run existing emitters |
| `2^K+1` landings | ~240 | probably the same fix |
| widen | ~120 | one new encoding file + template |
| other multiples | ~140 | likely small variations on the above |
| no anchor / not affine | ~560 | the genuinely hard residue |

## The one thing to do next

Replace `derive_tail` / `derive_tail_far`'s "append a synthetic blank and take
the first tail length that decodes" with the probe's rule: **enumerate
candidate `(state, encoding, tail)` families and pick the one with the longest
consecutive run, preferring the SHORTEST tail.**  Then re-run the existing
emitters over the residue before writing any new template.  On present
evidence that is worth several hundred boards and costs one function.

Do NOT write more lap templates until this is done — this session produced
three of them and the measurement says the templates were rarely the
limiting factor.
