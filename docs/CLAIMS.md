# What this repository proves, exactly

_The precise statement, the axiom footprint, and — explicitly — what is NOT
yet proved.  If any other document in this tree contradicts this one, this one
is right and the other is stale._

## The theorem

Kernel-checked, `Qed`, in `theories/Closeout/`:

```coq
closeout_partial : forall tm, Deferred D_census tm ->
                              boarded tm \/ Deferred D_remaining tm

census_boarded   : forall tm, QHBound 2000 tm
                           \/ boarded tm
                           \/ Deferred D_remaining tm
```

Unfolding the definitions (`Census/TNF_QH.v`, `Closeout/CloseoutKit.v`), for
**every** (4,2) Turing machine at least one of the following holds:

1. every state that eventually goes quiet did so before configuration index
   2000 (`QHBound 2000`); or
2. it never quasihalts — no state is eventually quiet, so it has no
   quasihalting score at all (`NeverQuasiHaltsSt`); or
3. it does not halt, it quasihalts, and **some** bound on its quiet states is
   certified (`NonHalt /\ (exists B, QHBound B) /\ QuasiHaltsSt`); or
4. it is one of the **622** machines listed in `D_remaining`
   (`tools/closeout/residue_map.tsv`).

`Deferred D tm` is not list membership: it is membership in the orbit of the
frozen table under completion of undefined transitions, non-start state swaps,
and mirroring.

**Axiom footprint: `functional_extensionality_dep`, and nothing else.**  There
are zero `Admitted.` in `theories/`.  Verify with `Print Assumptions`, or
independently with `coqchk -o`, which additionally reports that nothing relies
on type-in-type, unsafe (co)fixpoints, or assumed positivity.

## What this is NOT

**It is not a proof that BBB(4) = 32,779,478.**  Disjunct 3 above
existentially quantifies the bound.  It records *this machine is decided*, not
*this machine's score is at most the champion's*.  A machine with a certified
bound of 10^9 satisfies `boarded` perfectly well.

Three things are missing before the record itself is a theorem here:

1. **The bound is not aggregated.**  `boarded` should be replaced by, or
   accompanied by, a `boarded_le S` carrying a fixed `S`.  This is expected to
   be mechanical rather than hard: every board in the tree concludes either
   `NeverQuasiHaltsSt` (no score) or `QHBound 2000`, apart from four
   `BlankTail` machines at 2512, 2568, 2819 and 66349.  `qhbound_mono` (already
   proved) lifts all of them to one constant.  The work is re-deriving the
   ~4,534 stage lemmas against the stronger predicate and rebuilding.  **Not
   done.**
2. **The champion has no board.**  `1RB1LD_1RC1RB_1LC1LA_0RC0RD` blanks its
   tape at step 32,779,478 and then spins out in state C.  Its shape is exactly
   what `theories/Counters/BlankTail.v` already closes for the four previous
   champions; what it needs is a 32.8M-step prefix, for which
   `Checkers/TCyclerN.v` already supplies `cstepsN` and `cstepsN_nat`.  It is
   currently one of the 622.  **Not done.**
3. **The 622.**  Any of them could, for all this development knows, be a
   quasihalter with a larger score.  That is what undecided means.

So the honest one-line summary is:

> Every (4,2) machine is decided except 622, and the classification is
> kernel-checked with one standard axiom.  The BBB(4) *value* does not yet
> follow from what is here.

## Scope of the 622

621 are residue — machines no engine in this repository settles, mapped by
shape and blocker in `docs/RESIDUE_MAP.md`.  The 622nd is the last (4,2)
*holdout*, tower #20 (`1RB0RD_1LC1LB_1RA0LB_1LC1RA`); its gadget, sweep and
re-encoding layers are in `theories/Machines/Counters/Tower_20.v` and compile,
but the file carries no top-level theorem, so `inventory.py` correctly leaves
its row in `D_remaining`.

## The trust boundary

* Everything under `tools/` is **untrusted**.  It searches for certificates
  and emits Coq; the kernel re-checks every one.  A wrong certificate makes a
  file fail to compile, not a false theorem.  A verifier need not read any
  Python to believe the theorem.
* `tools/closeout/inventory.py` maps frozen rows to theorems by **parsing TM
  bodies**, never by filename, and each generated `CB_*.v` bridges
  `row_to_tm <literal row>` to the board's `tm` constant through an eight-way
  case split — so a misattribution fails to compile.
* **One number is not kernel-backed:** the kernel proves `closeout_partial`
  regardless of whether `remaining_rows` is padded with rows that are not on
  the frozen list — that would still be true, just weaker.
  `tools/closeout/audit.py` is what checks the two tables partition the frozen
  list exactly, and it is untrusted Python.
* The committed census `.vo` (154 files) are walk output, not source.  Loading
  them is a trust decision; `make census-verify` re-derives them from source
  instead.  See `docs/VERIFYING.md` for both paths.

## Reproducing

See `docs/VERIFYING.md`.  In short: `Closeout.vo` builds from source with
stock apt Coq 8.18.0 and needs **no committed binaries** — its only census
dependencies are `TNF_QH.v`, `Deferred_Defs.v` and `Deferred_Data.v`, none of
which are committed as `.vo`.  Only `CloseoutFinal.v`, which chains to
`census_decided`, loads the walk output.
