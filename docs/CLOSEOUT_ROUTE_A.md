# Route A: the partial census closeout (no census walk)

_Written 2026-07-25 (branch `claude/residue-reduction-4-2-07rtlv`).  This is
the "wire the proofs in" layer: it connects the per-machine board theorems to
the frozen census list by pure kernel composition, so the certified frontier
tracks the working frontier without ever re-walking the census._

## The statement

The census theorem (`Census/Compute/Census_Theorem.v`, committed `.vo`):

    census_decided : forall tm, QHBound B_census tm \/ Deferred D_census tm

`Deferred D tm` (`Census/TNF_QH.v`) is membership in the ORBIT of the frozen
5,156-row list under three closures: completion (`TM_le` — a listed row may
have undefined slots, and every completion of it is deferred), non-start
state swaps, and mirroring.  The closeout trades that list down against the
boards:

    closeout_partial : forall tm,
      Deferred D_census tm -> boarded tm \/ Deferred D_remaining tm

    census_boarded : forall tm,
      QHBound B_census tm \/ boarded tm \/ Deferred D_remaining tm

with `boarded` the Assembly.v predicate (never-quasihalts, or a non-halting
quasihalter with SOME certified last-visit bound), and `D_remaining` the
literal sub-table of frozen rows that still have no board (1,589 at first
generation).  Each wave of new boards regenerates the tables and shrinks
`D_remaining`; at zero the middle disjunct swallows the third and the
closeout is total.

## The pieces

| file | role | compiles where |
|---|---|---|
| `theories/Closeout/CloseoutKit.v` | hand-written kit: `boarded`, `covers`, completion/swap/mirror transports, row-level reflection (`row_eqb`/`row_inb`), and the one induction `deferred_split` over the deferred orbit | anywhere |
| `theories/Closeout/CB_XX.v` | GENERATED stages: one `covers (row_to_tm r)` lemma per proven frozen row, discharged from the board theorem | anywhere (needs the board `.vo`) |
| `theories/Closeout/Closeout.v` | GENERATED assembly: `proven_rows` app-chain, the `remaining_rows` table, the reflective split check (`vm_compute`), `closeout_partial` | anywhere |
| `theories/Closeout/CloseoutFinal.v` | GENERATED corollary `census_boarded` chaining the committed `census_decided` | census opam switch ONLY (committed census `.vo` are OCaml-toolchain-specific; apt Coq in a fresh container is OCaml 4.14.1, the census `.vo` are 4.14.2) |

Generators: `tools/closeout/inventory.py` (maps every frozen row to an
in-tree theorem by PARSING THE TM BODIES — names are not trusted; output
`frozen_map.tsv` + `frozen_unproven.txt`) and `tools/closeout/gen_stages.py`
(emits the stage files and the two assembly files).

## Measured (first full build, 2026-07-25)

| | |
|---|---:|
| frozen rows with an in-tree theorem | **3,567** |
| frozen rows still unproven (`remaining_rows`) | **1,589** |
| stage files | 36 (100 rows each) |
| stage compile | 2-3 s each, ~90 s wall for all 36 (3 workers) |
| `Closeout.v` compile (incl. the `vm_compute` split check) | **2 m 12 s** |
| `Print Assumptions closeout_partial` | `functional_extensionality_dep` only |

`Check closeout_partial` reads

    forall tm, Deferred D_census tm -> boarded tm \/ Deferred D_remaining tm

so the certified statement is now "every deferred machine is settled, except
these 1,589" — and it re-derives in ~4 minutes after any wave of new boards,
entirely in a container.

The one-time cost is the board `.vo`: building the 559-file dependency
closure of the 478 board files took ~85 min at 3 workers.  Six
`IRules_Batch_*.v` files failed in that parallel build and compile fine
serially (memory contention, not defects); they are on the `Census/Run.v`
path and are NOT in the stage closure.

## The trust story

Everything under `tools/` is untrusted bookkeeping.  The kernel re-checks
every link:

- a stage lemma bridges `row_to_tm <literal row>` to the board's `tm`
  constant through an 8-way case split (`destruct q, s; reflexivity`) — any
  row/board mismatch FAILS TO COMPILE;
- the completion obligation (`covers`) is discharged by `TNF_QH`'s
  don't-care argument (`visits_le` family): a non-halting machine's
  completions share its trace, so one theorem about the row's own machine
  (holes included) settles every completion;
- the split hypothesis (`every frozen row is in proven_rows or
  remaining_rows`) is a single boolean `forallb`/`row_inb` check evaluated
  by `vm_compute` inside the kernel;
- the orbit cases are transported by `boarded_unswap`/`boarded_unmirror`.

`Print Assumptions` on the stage lemmas and on `closeout_partial` shows
`functional_extensionality_dep` only — the same standing assumption as the
census itself.  The census is never re-walked and `theories/Census/` is
never edited; `Closeout.v` consumes only the frozen row tables
(`Deferred_Data`) and the board theorems.

## The per-wave workflow

After a wave of new boards lands (and compiles, with clean assumptions):

    python3 tools/closeout/inventory.py      # remap frozen rows -> theorems
    python3 tools/closeout/gen_stages.py     # regenerate CB_*, Closeout*, tables
    # compile: CloseoutKit, CB_00..CB_NN, Closeout  (coqdep order; the board
    # .vo must exist)
    python3 tools/census_cache.py --check    # must still say MATCH

then commit.  `remaining_rows` shrinks; nothing else moves.  On the census
box (optional, any time): compile `CloseoutFinal.v` under the census switch
to refresh the end-to-end `census_boarded`.

## Relation to route B (the census fold-in)

Route B (`gen_proven.py` + Deferred regen + `make census-verify` +
`census_cache --update`) moves machines into the census's proven tier and
re-freezes a SMALLER `D_census` — it changes the census inputs and needs the
~hours-long walk on stable hardware.  Route A never touches the census; it
proves the stronger refinement of the EXISTING frozen statement.  The two
carry the same mathematical content, so route B can be batched once at the
very end (or skipped entirely — `census_boarded` with `remaining_rows = []`
is already the full closeout).
