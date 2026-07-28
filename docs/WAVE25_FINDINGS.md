# Wave-25: the CASCADE, boarded

_Branch `claude/cascade-counter-merge-issue-ki8ulc`, 2026-07-28.  Wave-24
built the cascade route end to end — extractor, framing search, level
induction, overflow-branch emitter, 57 of 87 machines compiling — and boarded
NOTHING: an overflow branch is not a board, so PR #54 merged with
`D_remaining` unchanged at 496.  This wave is the boarding it named as the
next task (`docs/WAVE24_FINDINGS.md` §6, `docs/RESIDUE_PROMPT.md` item 0)._

## 1. The one-line result

**All 57 gated machines are boarded.**  `cascade_emit.py` now renders FULL
boards (`CASB_*`), not just the overflow branch: interior lap, bootstrap,
visit witnesses and the closer around wave-24's cascade branch.  Every one
compiles with `Print Assumptions` = `functional_extensionality_dep` only, and
every one was accepted by the kernel on the FIRST render — no per-machine
hand-editing.  `D_remaining` 496 → 439.

## 2. What the wiring measured (the survey, before any Coq)

Per gated machine, the three pieces wave-24 left open were probed first
(survey over all 87; the numbers are for the 57 gated):

* **interior chain**: all 57 derive as a SINGLE chain at the outer anchor —
  9 exactly, 48 up to `lift` (the standard trailing-blank slack; the wave-16
  `GLUE_ONE_LIFT` template takes them unchanged).  No split-mode interior was
  needed anywhere, so the cascade board wires `mode=one` only.
* **bootstrap**: all 57 boot from the blank tape to their `p0` anchor.
* **visits**: all 57 cover all four states — and exactly as §6 predicted,
  every board has states that fire in the BOOT chain (171 of 228 witnesses)
  and exactly one state per board that fires ONLY IN THE CLOSING SWEEP
  (57 of 228).  None needed the interior chain, and none is quiet: no
  `glue_qh`/`glue_qh_abs`/AVOID closer occurs in this population, so the
  cascade board template carries the plain never-QH close only.

## 3. The one genuinely new piece: visits through the cascade

A state that fires only in the closing sweep is reached from an overflow
anchor through the WHOLE cascade — boot to level `j`, exponentially many
counts down to level 0, then a prefix of the sweep's own chain.
`NestedLapCascade.cascade_vis` supplies the descent; the per-board lemma is

    visc_* : srun_st tm true true l CL0_* = Some q ->
             forall p j, cview p = (S j, None) ->
             exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q

with the boot landing (`gbo_*`) as `cascade_vis`'s first premise and
`vis_of_run` on the sweep chain (via `gcl_*`) as its second.  As
`WAVE24_FINDINGS.md` §6 said, only level 0 is available at EVERY outer index
— at `j = 0` the cascade has no descent, so the per-level chains cannot host
a universal witness; the emitter accordingly searches only the boot chain and
the sweep.

Everything else is composition: the whole board runs in `lift` space (the
cascade's overflow closes only up to `lift`), so the closer is
`LapCertGlueLift.glue_neverqh_lift` on all 57, with `lapil_*` restating an
exact interior in `lift` form where needed.

## 4. Emitter shape

`cascade_emit.py` gained `derive_board`/`render_board`/`process_board` and a
`--board SPEC` / `--boards FILE` driver; `emit_lapcert.process` now falls
back to the cascade route after the flat, nested and offset routes — the
third route `WAVE24_FINDINGS.md` §6 asked for, tried LAST because its
extractor replays whole overflow phases and is by far the most expensive
derive.  `PROTO` was split into `PROTO_DOC + PROTO_CORE` so the board
template reuses the overflow-branch body verbatim; the committed `CASC_*`
regression re-renders byte-identically (checked).  The interior branch and
the closer are `emit_lapcert`'s own templates (`INT_ONE`,
`GLUE_ONE`/`GLUE_ONE_LIFT`, `NQH_CLOSE_LIFT`) — nothing was forked.  The 23
mirrored machines go through `mirror_common.mirrorize` unchanged.

No new checker surface and no new axiom: `NestedLapCascade.v`,
`LapDecider.v` and every glue file are untouched by this wave.

## 5. The numbers

* 87 in the `no exit chain` / `no boot chain` bucket; **57 boarded**
  (`CASB_*`, 34 direct / 23 mirror), 30 not gated — the same 30 wave-24
  measured, unchanged: 12 octave-shifted main counts, 17 with one/two counts
  in the phase, 1 with a main count at 4..7.
* `D_remaining` **496 → 439** (4,717 of the frozen 5,156 settled, 91.5%).
  `make closeout` regenerated the stages; `audit.py` OK (exact partition);
  `Closeout.vo` + stages recompiled in-container; `census_cache --check`
  MATCH throughout (nothing under `theories/Census/` touched).

## 6. Do-not-retry, extended

* Do not look for a universal visit witness inside the per-level B→A / A→B
  chains — at `j = 0` they never fire.  Boot chain and closing sweep are the
  only two universal hosts, and they sufficed on all 57.
* The remaining 30 need emitter work on the octave-shifted 12 first
  (`families()` already carries an `oct`); the 17 one/two-count rows are the
  `no boot chain` mirror half plus the odd-shaped rows `CASCADE_EXIT.md` §2
  set aside, and nothing about them is a cascade.
