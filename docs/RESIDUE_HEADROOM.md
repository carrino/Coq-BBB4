# How much is left, and where it is — measured, wave-12

_Superseded twice in one session; this is the corrected version.  Read the
"What I got wrong" section before trusting any earlier number._

## What I got wrong (first version of this file)

The first version reported "70% of the residue is affine once the anchor is
read correctly" and recommended fixing the anchor search as work "worth
several hundred boards".  Two defects:

1. **The sample was biased.**  I took "the first 400" of the unproven list,
   which is SORTED by spec string — every machine in it started `0RB…`.  That
   is not a random sample of the space.
2. **Affine interior ≠ boardable.**  I classified the overflow by where it
   LANDS and called a standard landing a template fit.  Landing and cost are
   independent: a machine can land on `2^K` with an overflow cost that
   doubles (that is the IXP inner-counter case, not a template fit).

## The corrected measurement (full residue, not a sample)

`tools/counters/reanchor_probe.py` over **all 1,389** unproven machines:

| | n | share |
|---|---:|---:|
| anchor found, interior laps affine | **678** | 49% |
| anchor found, laps not affine | 38 | 3% |
| no anchor family at all | **673** | 48% |

The affine 678 by encoding/tail: `Ip[S1]` 345 · `Jp[S1]` 110 · `Jp[]` 104 ·
`Jp[S0]` 88 · `Ip[S0]` 19 · rest 12.

## The anchor search WAS defective — and fixing it was not enough

`emit_interleave._tail_for_snaps` had three real defects (documented in the
`derive_tail_best` docstring): it read the candidate tail off the LAST
snapshot only, required the consecutive run to END there, and used a
FRACTION-of-all-snapshots threshold that no single family can meet when a
trace mixes several.  `derive_tail_best` / `derive_tail_best_far` replace it
with a grouped longest-run search and are wired as fallbacks into
`emit_shape1`, `emit_shape4`, `emit_ixp`, `emit_wall`, `emit_wallj`.

Measured effect: on the routed Jp-mirror subset the failure mode moved from
`no anchor family` (bailing before any template ran) to `shape:` and `laps
not affine` (the template genuinely not fitting).  **Boards produced by the
fix alone: 4.**  The anchor search was a real false-negative source, but it
was not the binding constraint.

## So where is the juice, honestly

The binding constraint is TEMPLATE COVERAGE, not anchor detection.  Of the
678 affine-interior machines the emitters now reach, essentially all fail on
window-shape checks, and the shape messages do **not** cluster — the largest
group in a 71-machine routed run was 2.

That means the remaining work is a long tail of small template variants, not
one or two big levers.  Concretely, and in the order I would take them:

1. **Ip tail `[S1]`, 345 machines** — the largest single anchor family, and
   the one the `emit_shape4` / `emit_ixp` templates are closest to.  Trace
   five, cluster their window shapes, and extend the closest template.
2. **Jp families, 302 machines** — same exercise against `emit_shape1`.
3. The 673 with no anchor family are NOT interleaved counters at a
   blank-head anchor and should not be attacked with these emitters at all.

## Rule for the next measurement

Sample randomly, never a prefix of a sorted list; and classify the overflow
by COST (affine / exponential / no-close), not by landing.  The two probes
that do this correctly are committed: `reanchor_probe.py` (anchor + interior)
and `ovkind_probe.py` (landing) — the cost classifier lives in the session
scratch and should be folded in next time it is needed.
