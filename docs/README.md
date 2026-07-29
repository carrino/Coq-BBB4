# docs/ — what to read, and in what order

Three documents are the public face of the project; everything else is
the lab notebook that produced them, kept verbatim.

## Start here

| doc | what it is |
| --- | --- |
| [`CLAIMS.md`](CLAIMS.md) | **What is proved, exactly — including what is NOT.**  If any other document contradicts it, `CLAIMS.md` is right. |
| [`VERIFYING.md`](VERIFYING.md) | How to check any of it yourself, tier by tier, with expected outputs and the traps. |
| [`RESIDUE_MAP.md`](RESIDUE_MAP.md) | The undecided machines, mapped by shape and blocker — the open-problem list, published as targets. |

Two supporting references:

* [`TERMINOLOGY.md`](TERMINOLOGY.md) — the project's vocabulary
  (boards, holdouts, residue, tiers, quasihalting).
* [`WHY_NO_HAMMER.md`](WHY_NO_HAMMER.md) — the measured answer to "why
  not just run every decider over the residue?": the sweep exists, it
  was run, and this records why it cannot finish the job.

## The lab notebook (internal development notes)

Everything below is working notes from the sessions that built the
repository: per-wave findings, machine readings, plans that panned out
and plans that did not.  Nothing in them is needed to verify the
results, and their numbers freeze at their write date — but they record
*why* every design choice was made, and the traps already paid for.
The root-level [`NEXT_SESSION.md`](../NEXT_SESSION.md) is the running
digest of all of it.

* **Per-wave findings** — `WAVE4_STAGE.md` through `WAVE30_FINDINGS.md`
  (with `WAVE30_MACHINES_TO_CHECK.md` and the `WAVE30_PROMPT.md` staging
  note): what each proof wave boarded and how.
* **Holdout campaign** — `HOLDOUTS_WAVE14.md`, `HOLDOUTS_MXDYS_SN.md`,
  `HOLDOUTS_FRACTAL.md`: the 27 hardest machines, now all boarded.
* **Machine readings** — `BOUNCER_COUNTER_READING.md`,
  `SBCV1_READING.md`, `MP_BOOT_READING.txt`, `MACHINE_NOTES_WAVE8.md`,
  `UNCERTAIN_MACHINES.md`: tape decodings behind individual boards.
* **Checker/engine design** — `LAPDECIDER.md`, `RULE_LADDER.md`,
  `NESTED_LAP_PLAN.md`, `CASCADE_EXIT.md`, `WALLLAP_NOTE.md`,
  `COUNTER_CODEGEN_BLOCKERS.md`, `COUNTER_EMITTER_WAVE8.md`,
  `COUNTER_EMITTER_WAVE9.md`, `IRULESQH_WAVE3.md`, `NGHIST_WAVE5.md`,
  `NGHIST_WAVE7.md`, `REPWL_BIGBLOCK_WAVE8.md`, `MXDYS_DECIDERS_PLAN.md`,
  `MXDYS_INDUCTIVE_STAGE0.md`.
* **Closeout/census plumbing** — `CLOSEOUT_ROUTE_A.md`,
  `COUNTER_CLOSEOUT.md`, `REROOT_LISTC_STAGE.md`, `V5GAP_STAGE.md`.
* **Residue campaign** — `RESIDUE_708_DIAGNOSIS.md`,
  `RESIDUE_HEADROOM.md`, `RESIDUE_VISIT_MEASUREMENT.md`, and the live
  session prompts `RESIDUE_PROMPT.md` / `NEXT_SESSION_PROMPT.md`.
