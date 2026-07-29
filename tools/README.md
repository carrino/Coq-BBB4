# tools/ — all of it untrusted

Nothing in this directory carries proof weight.  These programs *search*
for certificates and *emit* Coq; the kernel re-checks everything they
produce, so a bug here makes a file fail to compile, never a false
theorem.  A verifier can ignore this directory entirely
(see `docs/CLAIMS.md`, "The trust boundary").

What lives here:

* **Generators** (`gen_*.py`) — emit the per-machine board files under
  `theories/Machines/` from certificates or searches.
* **Provers / mirrors** (`*_prover.py`, `counters/*.py`) — untrusted
  Python re-implementations of the verified checkers, used to search
  for certificates and to differentially validate a decomposition
  before any Coq is written.
* **Manifests** (`*_manifest.tsv`) — machine → theorem tables for the
  generated boards; `check_coverage.py` cross-checks them against the
  published holdout list (`BBB4_holdouts_3713.txt`, byte-identical to
  the bbchallenge wiki's copy).
* **`closeout/`** — the closeout pipeline: `inventory.py` (map frozen
  census rows to board theorems by parsing TM bodies), `gen_stages.py`
  (emit the `theories/Closeout/` stage files and `BBB4_Theorem.v`),
  `audit.py` (check the proven/remaining tables partition the frozen
  list exactly), and the frozen tables themselves
  (`frozen_unproven.txt` is the authoritative residue list).
* **`census_cache.py`** — the hash guard for the committed census
  `.vo` (build hygiene only; the kernel is what certifies the census).
* **`proof_report.py`** — prints the `make proof` report.
* **Sweep outputs and survivor lists** (`*.tsv`, `*.txt`, `*.json`) —
  kept as the audit trail of the search campaigns; their numbers are
  snapshots from their wave and go stale by design.
