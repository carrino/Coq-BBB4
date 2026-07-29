# What this repository proves, exactly

_The precise statement, the axiom footprint, and — explicitly — what is NOT
yet proved.  If any other document in this tree contradicts this one, this one
is right and the other is stale._

## The theorem

Kernel-checked, `Qed`, in `theories/Closeout/` (built and reported by
`make proof`):

```coq
closeout_partial : forall tm, Deferred D_census tm ->
                              boarded tm \/ skipped D_remaining tm

census_boarded   : forall tm, QHBound 2000 tm
                           \/ boarded tm
                           \/ skipped D_remaining tm

bbb4_target      : forall tm, QHBound 32779478 tm
                           \/ NeverQuasiHaltsSt tm
                           \/ skipped D_remaining tm

bbb4_decided_le_prev_champion : forall tm,
  ~ skipped D_remaining tm -> QHBound 66349 tm \/ NeverQuasiHaltsSt tm
```

where (`Closeout/ShadowKit.v`, the bbchallenge community's 0RB observation
made kernel-checked)

```coq
skipped R tm :=  Deferred R tm
             \/ exists qs t, stepn tm t InitES = Some (qs, snd InitES)
                           /\ Deferred R (TM_swap StA qs tm)
```

-- a machine is skipped if it is one of the undecided CORE machines, **or**
it runs an all-blank prefix into the orbit of one (a 0RB re-root SHADOW).
A shadow is not a separate open problem: it resolves automatically the
moment its core machine is boarded.

The last corollary is the previous-record reading: every decided machine
quasihalts by the *previous* champion's 66,349 or never quasihalts.  The four
previous champions themselves (scores 2,512–66,349,
`Machines/Counters/BlankTail_*.v`) are among the decided, so among all known
(4,2) machines only the (still-skipped) champion exceeds the previous record.

`boarded tm` is
`NeverQuasiHaltsSt tm \/ (NonHalt tm /\ QHBound B_board tm /\ QuasiHaltsSt tm)`
with `B_board` = 66,349, the previous champion's score, concrete.  Census-tier
stage boards certify literally `QHBound 2000` (= `B_census`, the census's
in-walk tier strength) and lift by `qhbound_mono`; the four ex-champions enter
at their exact scores through a `B <=? B_board` gate the kernel evaluates
(`covers_iqh_le_at`).  `tools/closeout/inventory.py` refuses any other
statement shapes.

Unfolding the definitions (`Census/TNF_QH.v`, `Closeout/CloseoutKit.v`), for
**every** (4,2) Turing machine at least one of the following holds:

1. every state that eventually goes quiet did so before configuration index
   32,779,478 — the champion's score — so its BBB score is at most the
   champion's (`QHBound 32779478`); or
2. it never quasihalts — no state is eventually quiet, so it has no
   quasihalting score at all (`NeverQuasiHaltsSt`); or
3. it is **skipped**: one of the **192** undecided core machines in
   `D_remaining` (`tools/closeout/core_rows.txt`), or one of their **96**
   0RB re-root shadows (`tools/closeout/shadow_rows.tsv`), which resolve
   automatically as core machines are boarded.

`Deferred D tm` is not list membership: it is membership in the orbit of the
frozen table under completion of undefined transitions, non-start state swaps,
and mirroring.

**Axiom footprint: `functional_extensionality_dep`, and nothing else.**  There
are zero `Admitted.` in `theories/`.  Verify with `Print Assumptions`, or
independently with `coqchk -o`, which additionally reports that nothing relies
on type-in-type, unsafe (co)fixpoints, or assumed positivity.

## What this is NOT

**It is not a proof that BBB(4) = 32,779,478.**  Two things are missing
before the record itself is a theorem here:

1. **The champion has no board.**  `1RB1LD_1RC1RB_1LC1LA_0RC0RD` blanks its
   tape at step 32,779,478 and then spins out in state C.  Its shape is exactly
   what `theories/Counters/BlankTail.v` already closes for the four previous
   champions; what it needs is a 32.8M-step prefix, for which
   `Checkers/TCyclerN.v` already supplies `cstepsN` and `cstepsN_nat`.  It is
   currently one of the 192 core machines.  **Not done.**
2. **The 192 (+ their 96 shadows).**  Any of them could, for all this
   development knows, be a quasihalter with a larger score.  That is what
   undecided means.

(The third gap this section used to list — the score bound existing only
existentially, per-board, instead of as one aggregated constant — is closed:
`boarded` now carries the concrete `QHBound B_board` (= 66,349), and
`bbb4_target` lifts it to the champion's score by `qhbound_mono`.)

So the honest one-line summary is:

> Every (4,2) machine either quasihalts with score at most the champion's
> 32,779,478 or never quasihalts, except 192 still-undecided machines (and
> their 96 0RB re-root shadows) —
> kernel-checked with one standard axiom.  The BBB(4) *value* does not yet
> follow from what is here, because the champion itself is one of the 192.

## Scope of the 192

All 192 core machines are residue — machines no engine in this repository
settles, mapped by
shape and blocker in `docs/RESIDUE_MAP.md`.  The (4,2) *holdout* list is
closed: tower #20, the last of it, was boarded on 2026-07-28
(`NEXT_SESSION.md` §2l).

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
  list exactly, and it is untrusted Python.  (`tools/proof_report.py`, the
  `make proof` reporter, is likewise reporting only.)
* The committed census `.vo` (154 files) are walk output, not source.  Loading
  them is a trust decision; `make census-verify` re-derives them from source
  instead.  See `docs/VERIFYING.md` for both paths.
* **The rule for committed proof binaries:** a `.vo` is committed only when
  reproducing it is prohibitive (the census walk: ~24 h, special toolchain),
  and then only hash-guarded and with a from-source escape hatch.  Nothing
  else in the tree ships as a binary — a file that rebuilds in minutes gets
  rebuilt, not trusted — so the trust surface stays one sharply-drawn line:
  everything up to `Closeout.vo` compiles from source, and exactly one fact
  (`census_decided`) rides on committed output.

## Reproducing

See `docs/VERIFYING.md`.  In short: `make` builds everything through
`Closeout.vo` from source with stock apt Coq 8.18.0 and needs **no committed
binaries** — the closeout's only census dependencies are `TNF_QH.v`,
`Deferred_Defs.v` and `Deferred_Data.v`, none of which are committed as `.vo`.
Only `CloseoutFinal.v` and `BBB4_Theorem.v` (the `make proof` tier, kept out
of the default build) load the walk output.
