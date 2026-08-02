# What this repository proves, exactly

_The precise statement, the axiom footprint, and — explicitly — where the
trust boundaries are.  If any other document in this tree contradicts this
one, this one is right and the other is stale._

## The theorem

**BBB(4) = 32,779,478.**

The CLAIM is stated census-free in `theories/BBB4_Spec.v` — that file plus
the machine model it imports (`theories/BBB4_Statement.v`) is the **entire
trusted statement surface**; nothing in either depends on the census, the
checkers, or the closeout:

```coq
tm_champion    : TM                       (* 1RB1LD_1RC1RB_1LC1LA_0RC0RD  *)
champion_score : nat := N.to_nat 32779478

Attains (tm : TM) (B : nat) : Prop :=
  exists q s, QuietAfter tm q s /\ S s = B

BBB4_is (B : nat) : Prop :=
  (exists tm, Attains tm B)                       (* ATTAINED *)
  /\ (forall tm B', Attains tm B' -> B' <= B)     (* MAXIMAL  *)

BBB4_statement : Prop := BBB4_is champion_score
BBB4_is_unique : forall B B', BBB4_is B -> BBB4_is B' -> B = B'
```

The PROOF is kernel-checked, `Qed`, in `theories/Closeout/BBB4_Value.v`
(built and reported by `make proof`):

```coq
BBB4_value : BBB4_statement
```

Unfolding the definitions (`BBB4_Statement.v`): over all 4-state 2-symbol
Turing machines on a two-way-infinite blank tape (undefined transition =
halt, start state A),

* **ATTAINED** — some machine has a state whose *last* visit is at
  configuration index 32,779,477, i.e. whose last transition fires at step
  32,779,478.  The witness is the spec's own `tm_champion`
  (`1RB1LD_1RC1RB_1LC1LA_0RC0RD`), whose state `D` does exactly that
  (`Machines/Counters/Champion_1RB1LD_1RC1RB_1LC1LA_0RC0RD.v`,
  `champion_attains : Attains tm_champion champion_score` — two binary-fuel
  `vm_compute` runs, one to pin the configuration at index 32,779,477 in
  state `D`, one to pin the landing at 32,779,478 on a blank tape in state
  `C`, plus the terminal C-loop induction showing no state but `C` ever
  appears again).
* **MAXIMAL** — no state of any machine is eventually quiet with a last
  visit at index ≥ 32,779,478 (`bbb4_upper : forall tm, QHBound 32779478
  tm`, with `QHBound` from `Census/TNF_QH.v`; the spec states the same
  bound purely in `Attains` terms).  Machines that never quasihalt satisfy
  `QHBound` vacuously; the two-disjunct reading is `bbb4_unconditional :
  forall tm, QHBound 32779478 tm \/ NeverQuasiHaltsSt tm`.

`BBB4_is_unique` (axiom-free, proved inside `BBB4_Spec.v` itself) confirms
the spec pins one number, so "BBB(4) = 32,779,478" has exactly one reading.

**Axiom footprint: `functional_extensionality_dep`, and nothing else.**
There are zero `Admitted.` in `theories/`.  Verify with `Print Assumptions`
(printed during `make proof`), or independently with `coqchk -o`, which
additionally reports that nothing relies on type-in-type, unsafe
(co)fixpoints, or assumed positivity.

## The convention

"BBB" here is the **state-level Beeping Busy Beaver** of the BBB harness
(carrino/BBB, README "Definitions"), the quasihalting formulation:

* a machine **quasihalts** iff some state is visited at least once but only
  finitely often (`QuasiHaltsSt`); a halting machine quasihalts trivially;
* the **score** of an eventually-quiet state is its last visited
  configuration index + 1 — the step at which its last transition fires
  (steps are numbered 1, 2, …);
* the machine's score is its largest quiet-state score, and BBB(4) is the
  maximum over all machines — which is exactly what `BBB4_is` says without
  needing a max operator: attained by one state somewhere, exceeded
  nowhere.
* never-visited ("silent") states do not witness quasihalting (the
  `Visited` conjunct).  This matches the harness treatment; a silent
  state's score-0 "quasihalt" is a convention question that cannot affect
  any BBB value.

## How the two halves are proved

**The upper bound** is the census + closeout chain:

```coq
census_decided   (the ~7h TNF walk of the whole (4,2) space, committed .vo)
closeout_partial : forall tm, Deferred D_census tm ->
                              boarded tm \/ skipped D_remaining tm
census_boarded   : forall tm, QHBound 2000 tm \/ boarded tm
                                              \/ skipped D_remaining tm
bbb4_target      : forall tm, QHBound 32779478 tm \/ NeverQuasiHaltsSt tm
                                                  \/ skipped D_remaining tm
```

and then the closing move (`BBB4_Value.v`): the residue is **empty**.
`remaining_rows = []` and `shadow_rows.tsv` has no rows (the last core
machine, Drozd's sixth `1RB0RD_1LB1LC_1RC0RA_0LB1RD`, was boarded
2026-08-01), so

```coq
not_deferred_nil : forall tm, ~ Deferred [] tm    (* induction on the derivation *)
not_skipped_nil  : forall tm, ~ skipped [] tm
```

discharge `bbb4_target`'s third disjunct, giving `bbb4_unconditional` and
`bbb4_upper`.  Every one of the frozen census's 5,156 deferred rows is
settled by a kernel-checked board (`python3 tools/closeout/audit.py`
reports 5,156 of 5,156, 100.0%).

`boarded tm` is

```coq
NeverQuasiHaltsSt tm
\/ (NonHalt tm /\ QHBound B_board tm /\ QuasiHaltsSt tm)
\/ (NonHalt tm /\ QHBound B_champ tm /\ QuasiHaltsSt tm)
```

with `B_board` = 66,349 (the previous champion's score) and `B_champ` =
32,779,478, both concrete.  Census-tier stage boards certify literally
`QHBound 2000` (= `B_census`) and lift by `qhbound_mono`; the four
ex-champions enter at their exact scores through a `B <=? B_board` gate the
kernel evaluates (`covers_iqh_le_at`); the champion enters through
`covers_iqh_champ_at` at the spec's own `champion_score` and `tm_champion`,
and its gate is the *proposition* `champion_score <= B_champ` discharged by
`lia` on constants — a `<=?` against 32,779,478 would make the kernel build
a 32.8M-constructor unary numeral, and nothing here ever evaluates that
number.  `tools/closeout/inventory.py` refuses any other statement
shapes.

`Deferred D tm` is not list membership: it is membership in the orbit of
the frozen table under completion of undefined transitions, non-start state
swaps, and mirroring.  `skipped R tm` (`Closeout/ShadowKit.v`) adds the 0RB
re-root disjunct — moot now that `R = []`.

**The lower bound** is one machine.  The champion erases its whole working
region, returns to a blank tape in `StC` at step 32,779,478 and spins left
in `C` forever; state `D`'s last visit is at index 32,779,477.  Both facts
are `vm_compute` over binary-numeral fuel (`Checkers/TCyclerN.cstepsN`,
~10 s each), so the 32.8M-element unary numeral is never built, and

```coq
champion_quiet_after_D  : QuietAfter tm_champion StD 32779477
qhbound_champion_tight  : forall B, QHBound B tm_champion -> 32779478 <= B
champion_attains        : Attains tm_champion champion_score
```

make the bound exact, not merely an upper estimate that happens to match a
simulation.

The previous-record reading survives as
`bbb4_decided_le_prev_champion_or_champion` (`BBB4_Theorem.v`): every
machine quasihalts by the *previous* champion's 66,349, or never
quasihalts, or quasihalts by the champion's 32,779,478 — and exactly one
census row is in the third case, the champion's own orbit (the single
`iqhch` line of `tools/closeout/frozen_map.tsv`; that count is untrusted
bookkeeping, like everything in `tools/`).

## The trust boundary

* Everything under `tools/` is **untrusted**.  It searches for certificates
  and emits Coq; the kernel re-checks every one.  A wrong certificate makes
  a file fail to compile, not a false theorem.  A verifier need not read
  any Python to believe the theorem.
* `tools/closeout/inventory.py` maps frozen rows to theorems by **parsing
  TM bodies**, never by filename, and each generated `CB_*.v` bridges
  `row_to_tm <literal row>` to the board's `tm` constant through an
  eight-way case split — so a misattribution fails to compile.
* The partition audit (`tools/closeout/audit.py`) used to be the one
  headline number not backed by the kernel.  **With the residue empty it no
  longer carries any weight for the value theorem**: `not_skipped_nil`
  discharges the skip disjunct inside Coq, so padding or truncating the
  (empty) remaining table cannot change `BBB4_value`.  The audit remains
  useful bookkeeping for the frozen tables and per-row attribution.
* The committed census `.vo` (154 files) are walk output, not source.
  Loading them is a trust decision; `make census-verify` re-derives them
  from source instead (~24 h).  See `docs/VERIFYING.md` for both paths.
* **The rule for committed proof binaries:** a `.vo` is committed only when
  reproducing it is prohibitive (the census walk: ~24 h, special
  toolchain), and then only hash-guarded and with a from-source escape
  hatch.  Nothing else in the tree ships as a binary — a file that rebuilds
  in minutes gets rebuilt, not trusted — so the trust surface stays one
  sharply-drawn line: everything up to `Closeout.vo` (and the champion's
  exact score) compiles from source, and exactly one fact
  (`census_decided`) rides on committed output.

## What this does NOT claim

* **Not BB(4).**  This is the Beeping Busy Beaver (quasihalting) value, in
  the state-level convention above — not the halting Busy Beaver, whose
  4-state value (107 steps) has been known since 1983.
* **Not machine-count bookkeeping.**  Statements like "exactly one machine
  exceeds the previous record" are untrusted table reads; the kernel proves
  bounds and disjunctions, not censuses of who satisfies them.
* **The convention matters at the margins.**  Under a different silent-state
  or step-numbering convention the number 32,779,478 could shift by the
  corresponding offset; `BBB4_Statement.v` states this repository's
  convention precisely, and `BBB4_is` is stated directly in those terms so
  there is nothing informal to translate.

## Reproducing

See `docs/VERIFYING.md`.  In short: `make` builds everything through
`Closeout.vo` — including the champion's exact-score file — from source
with stock apt Coq 8.18.0 and needs **no committed binaries**; `make proof`
adds the census-backed chain (`CloseoutFinal.v`, `BBB4_Theorem.v`,
`BBB4_Value.v`, the only three files that load the walk output, kept out of
the default build) under the census opam switch; `make census-verify`
removes the last trust by re-walking the census from source.
