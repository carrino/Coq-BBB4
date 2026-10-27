# Next capacity and instruction-portfolio pilot

This bounded pilot adds **five distinct audited BOTH families**, including
**one newly audited STATE family**, relative to the frozen campaign-final
inventories. It is disjoint from all 4,592 IDs assigned to the next-work queue.
The exact result, compatible board descriptors, and evidence hashes are in
[`next-capacity-summary.json`](next-capacity-summary.json). The original
campaign reports remain unchanged; this increment alone leaves 33,487 BOTH
and 2,757 STATE IDs in their respective baseline residuals. Concurrent work
must be unioned by ID before publishing combined totals.

The discovery input contains 128 IDs selected by a documented SHA256 ordering
from 28,411 eligible baseline BOTH residual IDs, after excluding the complete
queue and the 576 inputs of the previous 64/512-row diagnostics. Thirteen
sample IDs were also in the STATE residual. The manifest pins the selection,
input, exclusion sources, graph binary, and solver sources. This is a bounded
sample, not a claim about the full census or a population estimate.

All 128 machines completed, producing 256 closed orientation graphs. The
unchanged per-instruction solver found one capacity and four portfolio
candidates. There were no worker failures, hard machine timeouts, or LP target
timeouts. Thirteen native events were `closed_partial` in the ranking phase;
their closed graphs were retained, and the observed times were 0.500–0.504 s
against a 0.5 s orientation budget. The native status does not distinguish
timeout from stack overflow. Search consumed 158.1 summed machine wall seconds.
The Python worker peak RSS was 75,588 KiB, excluding its native graph child.
The inherited address-space cap was 1.5 GiB and the hard machine cap was 20 s.
The ledger also identifies 54 completed misses with seven targets in one
orientation, suitable for a later targeted width/window experiment.

The compact certificate bundles total approximately 15 KiB. Search success
alone is recorded in `next-capacity-search-report.json` and does not claim a
proof. The existing capacity-v2 and portfolio checkers separately verified
the certificates, bounds, pending-family membership and all-completion
discharge, followed by full recursive kernel audits. Separate inventory
wrappers prove `manifest_check` and `inventory_exact`, link the exact ordered
machine lists to their boards, and receive another full recursive audit.
Proof replay used one worker with a 2 GiB address-space cap. No frozen checker,
theory, report, manifest or previous generated proof was modified.

To reconstruct discovery from the repository root with the documented native
graph binary already built:

```bash
export PATH=/workspace/.opam/census/bin:$PATH
python3 four/tools/search_next_capacity.py prepare
python3 four/tools/summarize_next_capacity.py --preflight
python3 four/tools/search_next_capacity.py run
python3 four/tools/summarize_next_capacity.py --preflight
```

The preflight checks the binary as well as the source and input hashes. The
runner resumes only an exact input-prefix ledger. Its ignored build directory
holds per-machine graph events, partial witnesses, logs and outcomes. Frozen
compact certificates are sufficient for proof replay; discovery need not be
rerun. The portable adapter preserves published research reports and records
fresh runtime evidence under the selected ignored build directory:

```bash
python3 four/tools/replay_next_capacity.py \
  --output-dir four/build/next-capacity --timeout 300 --audit-timeout 900
```

This rebuilds both certificate boards and their exact inventory wrappers with
the original logical namespaces, then recursively audits them. It requires the
frozen source/certificate/inventory bytes, not historical compiled-object
bytes. An isolated positive replay checked all five families and 274 wrapper
dependencies while preserving every canonical proof and research artifact.

The recorded discovery-accounting summary validates exact candidate/checked
inventory equality, original residual membership, and queue exclusion.
Recreating that search accounting also requires the ignored baseline
inventories, prior-sample inputs, and per-machine discovery ledger. The portable
proof replay above needs only tracked compact inputs and compiled core
dependencies.
