# Wave-9 — what actually blocks the counter residue (measured), and the `Ip` unblock

_Written 2026-07-25.  Supersedes the §0/§4 hand-off numbers in
`COUNTER_EMITTER_WAVE8.md`.  Everything below is measured and reproducible via
`tools/counters/anchor_profile.py`; the machine-facing claims are backed by
compiled boards._

## 0. The one-paragraph version

The wave-8 hand-off said the emitter was blocked on the ENCODING: thread `Ip`
through the template and 64 quasihalting counters fall out.  Half of that is
right and half is wrong, and the wrong half matters more.

- **Wrong half:** the 298 quasihalting counters are *not* encoding-blocked.
  **0 of 40 sampled** have a lap that the single-sweep template can model, at
  any encoding — their OVERFLOW lap grows like `2^j`, not `a + b·j`.
- **Right half:** the encoding *is* a real blocker — on the **never-QH counter
  core**, where **19% of an 80-machine sample** fits the template and **two
  thirds of those are `Ip`**.  Extrapolated over the 2,328 unboarded core
  machines that is **~440 boardable, ~290 of them `Ip`**.

So the encoding work was worth doing; it was just pointed at the wrong list.
It is now done and validated end to end: `tools/counters/emit_ip.py` emits
`Ip` boards, and the first one is compiled and axiom-clean.

## 1. The test wave-8 was missing: BOTH lap branches must be affine

`Interleave_TGT`'s skeleton is

```
P1 . RIP^j . STP . RET^(c·j) . FIN
```

so the lap length must be **affine in the carry length `j`** — and it has to be
affine on *both* branches, the interior (`cview p = (j, Some q)`) and the
overflow (`p = 2^k − 1`).  Wave-8's fingerprinting only ever checked that the
anchor values marched `p → p+1`; it never measured the overflow branch.

`tools/counters/anchor_profile.py` measures both.  Calibration first, because a
test that accepts nothing is worthless:

| population | sampled | both-branch affine |
|---|---|---|
| already-boarded counters (control) | 17 | **17 / 17** — all `Jp`, head `S0`, slope 4 |
| quasihalting counters (`wave8_qh_missed_machines.txt`) | 40 | **0 / 40** (31 are counters; 11 have an affine INTERIOR) |
| unboarded never-QH core (`wave8_counters_todo.txt`) | 80 | **15 / 80** |

The control passing 17/17 is what makes the 0/40 meaningful.

### Why the quasihalting counters fail

Two failure modes, both measured directly from the anchor (not via the
scorer), and both fatal to a fixed-length overflow chain.

**Both branches super-linear.**  `0RB---_1LC---_0RC1LD_1RC0LD` — the machine
wave-8 named as the anchor-scan witness.  Its `Ip` anchor is real and is
confirmed here: `Cc p = (StC, (Ip p, S1, []))`, consecutive `p` from 2.  But

```
interior   j = 0   1    2    3        overflow   j = 2   3    4    5
           n = 6   24   90   348                 n = 56  218  860  3422
```

both roughly `4^j`.  Nothing about this machine is affine.

**Affine interior, exponential overflow.**  `1RB---_1LC1RB_0LB1RD_1LB0RD`
(measured on its mirror, where the counter grows left; anchor
`Cc p = (StC, (Ip p ++ [S1], S1, []))`):

```
interior   j = 0   1   2    3         overflow   j = 2   3   4    5    6
           n = 4   8   12   16                   n = 32  60  112  212  408
```

The interior is a clean `4 + 4j` — which is exactly what wave-8's fingerprint
measured and why the class looked reachable — but the overflow doubles.
Structurally, at overflow these machines *count the field back down* instead
of rippling across it once, so the work is proportional to the counter VALUE,
not to the number of digits.

A single-sweep overflow chain cannot model either shape at any encoding.
**Do not re-attempt the 298 through this template.**  They need a lap whose
overflow branch is itself an induction (see §4b).

## 2. What the `Ip` unblock actually required

Threading `Ip` through the template text — the literal wave-8 TODO — is
necessary but was **not sufficient**.  Four things were hard-coded, and all
four had to become parameters before a single real machine compiled:

1. **The encoding.**  Under `Jp` the carry region reads `rep [S1;S0] j` and
   becomes `rep [S1;S1] j`; under `Ip` it is the other way round.  So the
   ripple pair, the interior stop's flip direction (`S0→S1` not `S1→S0`), the
   return unit's **width** (2 cells, not 1) and the return **count** (`j`, not
   `2j`) all swap with the encoding.  `cycR` is already general enough — the
   return unit just deposits `[S0;S1]` instead of `[S1]`.
2. **The anchor head symbol.**  Wave-8 fixed it at `S0`.  10 of the 15
   template-shaped core machines anchor at head `S1`.
3. **The anchor tail.**  Wave-8 always appended `[S0]`.  10 of the 15 have
   tail `[S1]` — the counter's top data cell sits *under* the marker run, so
   the anchor tape is `Ip p ++ [S1]`, and no blank-terminated tail matches it.
4. **The anchor's FAR side — a blank CELL, not the empty LIST.**  This is the
   subtle one and it is the same lesson the project already learned for the
   near side, applied one level out.  These laps *close* by stepping one cell
   PAST the frontier.  With `far = []` that excursion runs off the window and
   needs an open-right transport; with the denotationally identical `far =
   [S0]` it is an ordinary closed window and `wsteps_frame` applies.
   `glue_neverqh`/`glue_qh` take an arbitrary anchor, so carrying the blank is
   free.  For the reference machine `[S0]` closes both branches exactly while
   `[]` and `[S0;S0]` close neither — it is not a free parameter, it is
   derived.

There is also a **search bug** worth recording: the same tape decodes under
both `Ip` and `Jp` (one ascending, one descending), so a candidate ranked by
"longest consecutive value run" over the *sorted* value set scores the
descending reading just as high.  `anchor_candidates` now requires the run to
ASCEND IN TIME.  Before that fix the search returned `Jp` for machines that
are plainly `Ip`.

## 3. The reference board

`theories/Machines/Counters/ILC_1RB0RC_0LA____0LD1RA_1RC1LD.v` —
`NeverQuasiHaltsSt` for `1RB0RC_0LA---_0LD1RA_1RC1LD`,
`functional_extensionality_dep` only.

```
Cc p = (StD, (Ip p ++ [S1], S1, [S0]))
interior lap  8 + 4j        overflow lap  9 + 4j
```

Both branches land on the next anchor **exactly** (no `lift` fudge, unlike the
`Jp` overflow path, which had to close up to a trailing blank).

One structural note for whoever generalizes the visit obligations: this
machine's `StB` fires **16 times in 200,000 steps, at doubling intervals** —
it is the log-rare carry state, and it appears *only inside the overflow
close*.  No bounded anchor prefix reaches it.  The board therefore witnesses
every state from a single landmark — the configuration the overflow close
starts from — reached by well-founded induction on `tovf`.  That pattern
(`reach_fino`) is strictly more general than wave-8's per-state prefix plan and
should be the default.

## 4. Tools

- `tools/counters/anchor_profile.py` — the measurement instrument.  Wide anchor
  search (state × head × encoding × tail, far side blank-after-stripping) over
  the real run, then the two-branch affine profile.  Also tries the mirror.
- `tools/counters/emit_ip.py` — the `Ip` emitter.  Clones the reference board;
  derives the seven windows by exact symbolic replay against the raw simulator
  (`validate` re-checks step counts AND configurations for `p = 2..99` across
  both branches); emits, runs `coqc`, checks `Print Assumptions`, and **deletes
  the file** if either fails.
- `tools/counters/emit_qh.py` — now carries the widened `anchor_candidates`
  (ranked, ascending-in-time).  Its Coq template is still `Jp`-only; given §1
  that is no longer the priority it looked like.

## 4b. The external datum: mxdys's inductive decider decides this whole residue

Reported by the project owner (2026-07-25): every machine in this residue is
decided by mxdys's *inductive* decider, whose stated limit is

> "my inductive decider can only decide a TM when it can model the forward
> behavior exactly."

That is worth writing down because it lines up exactly with §1 and tells us
which way to build.

- It is **not in this workspace.**  The `Coq-BB5` checkout here ships
  `Decider_Loop`, `Decider_NGramCPS`, `Decider_RepWL`, `Verifier_FAR/WFAR` and
  the halt deciders — no inductive decider.  So it cannot simply be pointed at
  the residue from here; it would have to be fetched or reimplemented.
- **"Models the forward behavior exactly" is the same property our route has**
  and the closure methods do not.  §4b of the wave-8 doc worked out *why* every
  generic decider bounces off these machines: n-gram, RepWL and rank all
  manufacture a spurious carry-free cycle because they ABSTRACT the digit
  pattern, which differs on every increment.  An exact forward model has no
  such failure mode.  Our lap proofs are exact forward models — that is why
  they work — so the two approaches agree about what these machines are; ours
  is just hand-rolled per machine.
- **It predicts §1's failure is a shape limit, not a hardness limit.**  The 298
  quasihalting counters are decidable; our template merely cannot express them,
  because its overflow phase is a FIXED chain and theirs is a `2^j` process
  (the machine counts the field back down).  An exact forward model that may
  recurse handles that; a fixed chain cannot.

**Strategic consequence.**  The per-machine template is a good conveyor for the
affine-lap population and a dead end for the rest.  Rather than widening it
further, the next big win is a *verified inductive decider* — one closure rule
whose soundness theorem is proved once and which then decides machines by
exact forward modelling with an induction on the counter, retiring
per-machine Coq for the whole class.  Before building it, ask the owner for
mxdys's implementation: reimplementing from the one-line description above
would repeat exactly the mistake this project keeps recording (build first,
check for an existing tool second).

## 5. Next, in priority order

1. **Finish the `Ip` core sweep.**  `emit_ip.py --list <remaining> --emit`.
   The measured yield is ~12% of the unboarded core; the run is embarrassingly
   parallel and each board is independently kernel-checked.
2. **Mirror the `Ip` emitter** (`ILCM_` prefix).  About half the both-affine
   core machines are RIGHT-growth; `emit_mirror.py` already has the pattern
   (`mirror_tm` + explicit mirrored table + `mirror_never_qh`), and
   `LapGlueQH.mirror_iqh` is the QH sibling.  This roughly doubles the yield
   for no new theory.
3. **Do NOT** re-point this template at the 298 quasihalting counters (§1).
   If they are worth another wave, the shape to build is a lap whose overflow
   branch is itself an induction, not a fixed chain.
4. The `NOANCHOR` bucket (26 of 80 core machines) is untouched: those are the
   two-sided anchors (a marker riding the far side at varying depth) and the
   run-length/spacer encodings from `MACHINE_NOTES_WAVE8.md`.  `glue_neverqh`
   already accepts such anchors; only the search needs widening again.
