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

bbb4_decided_le_prev_champion_or_champion : forall tm,
  ~ skipped D_remaining tm -> QHBound 66349 tm
                           \/ NeverQuasiHaltsSt tm
                           \/ QHBound 32779478 tm
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
A shadow is not a separate open problem — it needs no new mathematics — but
it is not free either: a shadow is a shadow only of a core machine that is
still undecided, so boarding a core machine moves its shadow INTO
`core_rows.txt` until the same argument is transported across the re-root
(`Machines/Counters/RRNQ_0RB0RD_1RC____1RD1LC_0LC1RA.v` is the worked
example).  Budget a core row and its shadows together.

The last corollary is the previous-record reading: every decided machine
quasihalts by the *previous* champion's 66,349, or never quasihalts, or
quasihalts by the champion's own 32,779,478.  The four previous champions
themselves (scores 2,512–66,349, `Machines/Counters/BlankTail_*.v`) are among
the decided, and **exactly one census row is in the third case** — the
champion and its orbit, the single `iqhch` line of
`tools/closeout/frozen_map.tsv`.  So among all known (4,2) machines only the
champion exceeds the previous record, exactly as before it was boarded; what
changed is that it is now *decided* rather than skipped.  (That the third
case holds one row is untrusted bookkeeping, like the partition audit:
`boarded`'s third disjunct carries a bound, not an identity, so the kernel
states the disjunction and not the census of who satisfies it.)

`boarded tm` is

```coq
NeverQuasiHaltsSt tm
\/ (NonHalt tm /\ QHBound B_board tm /\ QuasiHaltsSt tm)
\/ (NonHalt tm /\ QHBound B_champ tm /\ QuasiHaltsSt tm)
```

with `B_board` = 66,349 (the previous champion's score) and `B_champ` =
32,779,478 (the champion's), both concrete.  Census-tier stage boards certify
literally `QHBound 2000` (= `B_census`, the census's in-walk tier strength)
and lift by `qhbound_mono`; the four ex-champions enter at their exact scores
through a `B <=? B_board` gate the kernel evaluates (`covers_iqh_le_at`); the
champion enters through `covers_iqh_champ_at`, whose gate is the *proposition*
`B <= B_champ` discharged by `lia` on two Horner forms — a `<=?` against
32,779,478 would make the kernel build a 32.8M-constructor unary numeral, and
nothing here ever evaluates that number.  `tools/closeout/inventory.py`
refuses any other statement shapes.

Unfolding the definitions (`Census/TNF_QH.v`, `Closeout/CloseoutKit.v`), for
**every** (4,2) Turing machine at least one of the following holds:

1. every state that eventually goes quiet did so before configuration index
   32,779,478 — the champion's score — so its BBB score is at most the
   champion's (`QHBound 32779478`); or
2. it never quasihalts — no state is eventually quiet, so it has no
   quasihalting score at all (`NeverQuasiHaltsSt`); or
3. it is **skipped**: one of the **8** undecided core machines in
   `D_remaining` (`tools/closeout/core_rows.txt`), or one of their **5**
   0RB re-root shadows (`tools/closeout/shadow_rows.tsv`).  A shadow needs
   no new mathematics — it is a blank-prefix re-root of a core machine —
   but it does need its own board, because a shadow is a shadow only of a
   core machine that is still undecided: boarding a core machine moves its
   shadow into `core_rows.txt` until the same argument is transported
   across the re-root.

   _The two counts move every wave; the row files are the authority and
   `python3 tools/closeout/audit.py` prints them live.  8 + 5 is the
   2026-08-01 reading (5,143 of the frozen 5,156 settled, 99.7%)._

`Deferred D tm` is not list membership: it is membership in the orbit of the
frozen table under completion of undefined transitions, non-start state swaps,
and mirroring.

**Axiom footprint: `functional_extensionality_dep`, and nothing else.**  There
are zero `Admitted.` in `theories/`.  Verify with `Print Assumptions`, or
independently with `coqchk -o`, which additionally reports that nothing relies
on type-in-type, unsafe (co)fixpoints, or assumed positivity.

## What this is NOT

**It is not a proof that BBB(4) = 32,779,478.**  One thing is missing before
the record itself is a theorem here:

1. **The 8 core machines (and their 5 shadows).**  Any of them could, for
   all this development knows, be a quasihalter with a larger score.  That is
   what undecided means.  The list is `tools/closeout/core_rows.txt` and the
   map is [`RESIDUE_MAP.md`](RESIDUE_MAP.md).

What *is* now proved, and was not before, is the **lower** bound.  The
champion `1RB1LD_1RC1RB_1LC1LA_0RC0RD` erases its whole working region,
returns to a blank tape in `StC` at step 32,779,478 and spins left in `C`
forever; `theories/Machines/Counters/Champion_1RB1LD_1RC1RB_1LC1LA_0RC0RD.v`
proves `NonHalt /\ QHBound 32779478 /\ QuasiHaltsSt` in one `vm_compute` over
a binary-numeral fuel (`Checkers/TCyclerN.cstepsN`, ~17 s), and since
2026-08-01 the closeout **consumes** it: `boarded` has the third disjunct this
section used to ask for, carried through `covers_iqh_champ_at` and the
swap/mirror lemmas, and `tools/closeout/inventory.py` boards the row as kind
`iqhch`.  So `bbb4_target`'s bound is attained by a machine the theorem
decides, not merely stated.  It stays a lower bound only: closing the 8 is
what would turn it into the value.

_Two gaps this section used to list are closed.  The score bound existing only
existentially, per-board, instead of as one aggregated constant: `boarded`
carries the concrete `QHBound B_board` (= 66,349) or `QHBound B_champ`
(= 32,779,478), and `bbb4_target` lifts either to the champion's score by
`qhbound_mono`.  And the champion's board being unconsumable: the fix taken
was the second of the two this section named — the third disjunct, not raising
`B_board` — precisely so that
`bbb4_decided_le_prev_champion_or_champion` still separates the champion from
the other 5,135 boarded rows instead of coarsening all of them to 32.8M._

So the honest one-line summary is:

> Every (4,2) machine either quasihalts with score at most the champion's
> 32,779,478 or never quasihalts, except 13 still-undecided machines (8
> core rows and their 5 0RB re-root shadows) —
> kernel-checked with one standard axiom.  The bound is ATTAINED (the
> champion is boarded, so BBB(4) >= 32,779,478), but the BBB(4) *value*
> does not follow from what is here while the 13 stand.

## Scope of the 8

All 8 core machines are residue — machines no engine in this repository
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
