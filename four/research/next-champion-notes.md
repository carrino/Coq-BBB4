# Exact champion census board

The new standalone board contains exactly
`1LB2RA1LA1RB_0RB2LB3LB1RA`. Both its state score and instruction score are
**205,770,076,433,044,242,247,860**. This is the left/right reflection of the
machine already proved in `Champion.v`; no new long simulation is needed.

[`ChampionCensusNext.v`](../theories/ChampionCensusNext.v) proves reflection
transport for nonhalting, both upper bounds, and attainment of both bounds.
`canonical_champion_completion_exact` covers every `TM_le` completion. All
eight cells are defined; `canonical_champion_completion` also checks that every
completion agrees at each cell. The singleton board has
`BoardSound scoreN scoreN`, and a bounded `pending_check` proves membership in
the original formal `bootstrap_pending` predicate.

The [one-row inventory](next-champion-inventory.json) uses base-17 packing
`2788885433`. A kernel-checked `manifest_check` equality connects those exact
table cells to the board. The [descriptor](next-champion-board.json) exposes
the existing board interface, its symbolic binary bounds, and exact theorem.
The independent generated wrapper additionally checks that its recorded binary
score equals `Spec.scoreN`.

The [report](next-champion-summary.json) records a successful complete-closure
audit: nine modules were freshly checked, including the original champion
proof, the new board, and its inventory wrapper; 249 unchanged dependencies
were reused through validated source/object/runtime-bound receipts with
recursive ancestry. The replay used one worker and a hard 1 GiB address-space
limit. Only the repository's existing `functional_extensionality_dep`
assumption appears; no new axiom is introduced.

Replay from the repository root with the existing compiled dependencies:

```bash
PATH=/workspace/.opam/census/bin:$PATH \
python3 four/tools/check_champion_census_next.py \
  --audit-cache four/build/campaign-final/campaign-core-audit-000001.json \
  --audit-cache four/build/state-repwl-frontier/kernel-audits/coqchk.json
```

On another checkout, supply matching local audit receipts, or explicitly use
`--recursive` to audit the full dependency closure. The latter may require
larger `--timeout` and `--memory-mib` budgets. Receipts are local cache metadata;
source, inventory, descriptor and theorem are the portable evidence. Replays
preserve earlier audit receipts and logs under `build/next-champion/`.

Keep `scoreN` opaque during tactics. Keep the alias `score := N.to_nat scoreN`
transparent so Coq can match the two statement forms without expanding the
astronomical unary number. The only VM computations here inspect finite table
cells or the nine-level pending path. The generated wrapper first checks a
binary score equality, then rewrites through it to prove the recorded bounds.

This board is separate from the frozen 113-board campaign. The report verifies
the frozen residual hashes and confirms that the champion occurs in both
comparison residuals (33,492 both-bound rows and 2,758 state-bound rows), but
is absent from the 4,592-ID candidate queue. Those historical counts and files
remain unchanged. `champion_census_coverage` and `champion_census_discharged`
provide a sound standalone formal closeout, not a global upper bound.

A future combined aggregator can append this board using its proved
`BoardSound scoreN scoreN` and pending theorem. It must explicitly recognize
the exact champion board instead of treating it as a small-bound solver
result, and respect the descriptor's `state_bound_term` and
`instruction_bound_term` fields. The frozen `check_campaign.py` intentionally
rejects champion controls; removing that guard alone would neither establish
the new proof scope nor ensure safe score handling. A new aggregate theorem,
exact union inventory and complete-closure audit are required before publishing
updated combined residual counts.
