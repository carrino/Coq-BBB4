# docs/ — index

**BBB(4) = 32,779,478, kernel-checked.**  The claim is
`theories/BBB4_Spec.v` (`BBB4_statement`), the proof is
`theories/Closeout/BBB4_Value.v` (`BBB4_value`); the residue closed at
5,156 of 5,156 frozen rows on 2026-08-01.  On any conflict between
documents, [`CLAIMS.md`](CLAIMS.md) is right.

## The result

* [`CLAIMS.md`](CLAIMS.md) — **what is proved, exactly — including what
  is NOT.**
* [`VERIFYING.md`](VERIFYING.md) — how to check any of it yourself, tier
  by tier, with expected outputs and the traps.
* [`TERMINOLOGY.md`](TERMINOLOGY.md) — the vocabulary: the theorem's own
  terms, then census / holdouts / residue / boards / tiers.

## How the last machines fell

The finished write-ups of the closing campaign — completed records, not
live worklists:

* [`RESIDUE_MAP.md`](RESIDUE_MAP.md) — the residue map, **closed out**
  (0 rows since 2026-08-01): how each family of core machines was
  characterised, what blocked it, and how it fell.
* [`REACHST_TIER.md`](REACHST_TIER.md) — the REACHST tier: liveness of a
  machine's sparse state as termination of the state-DELETED sub-machine
  — the idea behind 127 boards.
* [`LADDER_PLAN.md`](LADDER_PLAN.md) (with `LADDER_NOFAM.md`) — the
  ladder: the value-indexed rule family that became the endgame's main
  producer.  A design record with its append-only build log.
* [`WHY_NO_HAMMER.md`](WHY_NO_HAMMER.md) — the measured answer to "why
  not just run every decider over the residue?": the sweep exists, it
  was run, and this records why it could not finish the job.
* [`CORE_3STATE.md`](CORE_3STATE.md) — the `1RB---_...` core rows read
  as three-state machines, and §3 the FIBONACCI finding: they count in
  φ, not in base 2.  All 24 boarded, the last eleven off the ladder at
  `(Fib, 1)` and `(FibL, 1)`; kept for §3's shape — three independent
  negative searches that were all asking the wrong question.
* [`MXDYS_INDUCTIVE_RESIDUE.md`](MXDYS_INDUCTIVE_RESIDUE.md) — mxdys'
  inductive prover run over the community's target list
  (`mxdys_target_rows.txt`), what it decided, and the two anchor
  families it handed over (one of them the champion's board).
* `QUAD_TERMINAL_MEASUREMENT.md` — the QUAD rows' terminal behaviour,
  measured.

## The lab notebook (historical archive)

Everything below is working notes from the sessions that built the
repository: per-wave findings, machine readings, plans that panned out
and plans that did not.  **These are snapshots, not live status** —
nothing in them is needed to verify the results, and their numbers
freeze at their write date — but they record *why* every design choice
was made, and the traps already paid for.  The root-level
[`NEXT_SESSION.md`](../NEXT_SESSION.md) is the accumulated engineering
log and compute playbook.

* **Per-wave findings** — `WAVE4_STAGE.md` through `WAVE38_REST_FOUR.md`
  (with the `WAVE*_PROMPT.md` staging notes): what each proof wave
  boarded and how.
* **Holdout campaign** — `HOLDOUTS_WAVE14.md`, `HOLDOUTS_MXDYS_SN.md`,
  `HOLDOUTS_FRACTAL.md`: the 27 hardest machines, all boarded.
* **Machine readings** — `BOUNCER_COUNTER_READING.md`,
  `SBCV1_READING.md`, `MP_BOOT_READING.txt`, `MACHINE_NOTES_WAVE8.md`,
  `UNCERTAIN_MACHINES.md`: tape decodings behind individual boards.
* **Checker/engine design** — `LAPDECIDER.md`, `RULE_LADDER.md`,
  `NESTED_LAP_PLAN.md`, `CASCADE_EXIT.md`, `WALLLAP_NOTE.md`,
  `COUNTER_CODEGEN_BLOCKERS.md`, `COUNTER_EMITTER_WAVE8.md`,
  `COUNTER_EMITTER_WAVE9.md`, `IRULESQH_WAVE3.md`, `NGHIST_WAVE5.md`,
  `NGHIST_WAVE7.md`, `REPWL_BIGBLOCK_WAVE8.md`.
* **The mxdys inductive prover** — `MXDYS_DECIDERS_PLAN.md` and
  `MXDYS_INDUCTIVE_STAGE0.md` (the measured gate).
* **Closeout/census plumbing** — `CLOSEOUT_ROUTE_A.md`,
  `COUNTER_CLOSEOUT.md`, `REROOT_LISTC_STAGE.md`, `V5GAP_STAGE.md`.
* **Residue campaign (closed)** — `RESIDUE_708_DIAGNOSIS.md`,
  `RESIDUE_HEADROOM.md`, `RESIDUE_VISIT_MEASUREMENT.md`, and the
  session prompts of the era, `RESIDUE_PROMPT.md` /
  `NEXT_SESSION_PROMPT.md`.
