# Wave-13 — the emitter era ends: one checker, 119 boards, and a named next build

_Branch `claude/lapdecider-residue-reduction-989ggx`, off merged wave-12.  This
wave finished `theories/Checkers/LapDecider.v`, made certificate DERIVATION
mechanical, and boarded 119 machines with it.  Read §4 (what this wave got
wrong) and §6 (the next build) before starting anything._

## 1. Scoreboard

| | |
|---|---:|
| boards this wave | **119** (`LAPC_*`, all through the ONE checker) |
| `D_remaining` | 1,385 → **1,266** |
| frozen rows settled | 3,890 / 5,156 (**75.4%**) |
| new soundness surface | `LapDecider.v` + `LapCertGlue.v`, both **axiom-free** |
| board axiom footprint | `functional_extensionality_dep` only (sampled 6, plus every board compiled) |
| closeout | `audit.py` OK — tables partition the frozen list exactly |
| census | `census_cache --check` = MATCH at every commit; `theories/Census/` untouched |

The 119 break down `Jp/mirror` 66, `Jp` 23, `Ip/mirror` 18, `Ip` 3, plus 9
hole-machines re-derived after a filename fix.

**The point is not the 119.**  It is that a machine now costs a SEARCH, not a
session: `tools/counters/emit_lapcert.py --list FILE --emit` derives, validates
and compiles a board unattended.  Waves 8-12 spent five hand-written emitters
on ~500 boards.

## 2. The build

Full design in `docs/LAPDECIDER.md`.  In one paragraph: a symbolic tape side is
`pre ++ rep u (a*j+b) ++ post ++ X` with `X` an OPAQUE TAIL (the counter bits
above the carry) universally quantified, so one chain covers every `p` in a
branch at once.  A step language of framed windows, open-edge windows, the two
`WTape` cycles, block-boundary rotations and a block-offset fold is run by
`srun`; `srun_sound` turns a successful symbolic run into a concrete `csteps`
for every `j` and every tail; `lap_of_run`/`vis_of_run` feed `glue_neverqh`.

`LAPC_1RB1LA_1LC1RD_1LB1RA_0LA0RB.v` is the architecture proof — the same
machine as `ILS4_…`, whose hand board spent 9 window lemmas, 9 transported
phases and 2 assembled laps.  **24 of 25** sampled hand-emitted `ILS4_*` boards
re-derive automatically.

## 3. The build trap is closed

`tools/closeout/gen_stages.py` now computes the transitive in-tree dependency
closure of every board the stages `Require` and adds whatever is missing to
`_CoqProject` (`theories/Census/` excluded — its `.vo` are committed).
Verified by deleting a board AND its transitive dep `MonoCounter.v` and
watching both come back; and in production this wave, where it added all 114
new board files with no `No rule to make target`.

## 4. Three things this wave got wrong

1. **"A walled window is forced forward, so only the MAXIMAL cut matters."**
   False, and it cost the first search implementation: the last window of a lap
   must often stop SHORT so that a rotation can land the configuration on the
   anchor's syntactic form.  Making the window search target-aware turned 0
   chains into all of them.
2. **"Rotations can reach any equivalent representation."**  False in
   principle.  Rotations move a block BOUNDARY; they cannot change the count's
   constant offset `b`.  An overflow anchor is naturally REACHED as
   `uD ++ rep uD j ++ …` but STATED by `cview` as `rep uD (S j) ++ …`, and
   only the new `SFold` step reconciles them.
3. **"143 machines with no visit witness are rejects."**  False — John:
   *"qh is fine, we just need to know it qh before 32M."*  They are
   quasi-halters and a certified quiet bound boards them just as well.  See §6.

## 5. Where the residue actually stands

Of the 1,385 (measured over the whole list, not a sample):

| bucket | count | status |
|---|---:|---|
| boarded this wave | 119 | done |
| **no interior chain** | ~504 | anchor found, chain search failed — the biggest bucket, unanalysed |
| **no overflow chain** | ~371 | interior derives, overflow does not |
| **quasi-halting** (no visit witness) | ~143 | §6 — a real class with a real route |
| **no anchor** | ~149 | no `Ip/Jp/Kp/Dp/Mp` family at all |

The middle two buckets are where the next boards are.  **Do not template them
blind** — wave-12 §8: trace two or three members before templating, never one.

Note `Kp`/`Dp`/`Mp` are wired but produced almost nothing (`Dp` 6, `Kp` 1, `Mp`
0) — the encoding table is not the binding constraint; the chain search is.

## 6. The next build, precisely

The ~143 quasi-halting counters derive a LAP but have a state that genuinely
goes quiet.  Splitting them:

* **47** have `StA` targeted by NO transition, so its only visit is at
  configuration index 0 and `LapGlueQH.glue_qh` gives `QHBound 1` outright.
  Wired into the emitter; blocked in practice on a second quiet state (`StB`
  fires once at index 1 by the same argument) and on `mirrorize` not knowing
  the QH closing shape.  Both are small.
* **96** have `StA` targeted but fired only during the bootstrap.  The bound is
  `t0+1` where `t0` is the boot length, and it needs exactly ONE new fact:
  *the lap visits only states in `S`*.

That fact is computable from the chain — collect the states of every window
sub-step and every cycle unit run — but it needs a new soundness theorem,
because `wsteps_frame`, `cycL` and `cycR` currently state only their
ENDPOINTS.  The work is a "states visited" variant of each: roughly

    wsteps_states : wsteps bl br tm n c = Some c' ->
      (forall k c2, k <= n -> wsteps bl br tm k c = Some c2 -> In (fst c2) S) ->
      forall L R, ... every intermediate cstep state is in S

plus the same for the two cycles by the same induction they already use.  With
it, `QuietAfter tm q t0` follows for every `q` outside `S`, and `qhbound_mono`
lifts the bound to the census tier's 2000 — far inside the champion's 32.8M.

**This is the highest-value next item**: it converts a measured 143-machine
bucket, and it is one theorem, not one per machine.

## 7. Deferred, unchanged from wave-12

* Census fold-in (route B) — batch once on stable hardware; it is the only
  step that lowers `D_census`.
* The champion `1RB1LD_1RC1RB_1LC1LA_0RC0RD` (`exists B, QHBound B` + a 32.8M
  prefix) and the carry-shifted one-off `0RB1LC_1LC0LC_0RD1LA_1RD1RB`.
* The full `make closeout` COMPILE (`Closeout.vo`) needs the ~719-file board
  `.vo` closure, the documented ~85-minute one-time cost in a fresh container.
  `inventory.py` + `gen_stages.py` + `audit.py` all ran clean this wave and the
  numbers above come from them.

## 8. Do-not-retry, added this wave

* **Maximal-only window cuts in the chain search** (§4.1) — finds nothing.
* **Reaching an anchor's syntactic form by rotations alone** (§4.2) —
  impossible in principle, not a tuning problem.
* **mxdys' implementation** — John reports it is not available.  Stop asking;
  reconstruct from measurements (`WAVE9_FINDINGS.md` §7 is now closed out).
* **Widening the ENCODING table to buy boards** — `Kp`/`Dp`/`Mp` added this
  wave for 7 boards total.  The chain search, not the alphabet, is binding.
