# Advisory TR hint data

`python3 tools/censustr/gen_tr_hints.py` renders the explicitly inventoried
`unitNN.rows.json` files, updates their generated metadata, and synchronizes the
owned `_CoqProject` entries. `--check` compares all expected content without
writing. `--repo PATH` selects another checkout. No Coq/toolchain subprocess runs.
Run the small synthetic Python tests with:

```
python3 -B -m unittest discover -s tools/censustr -p test_gen_tr_hints.py
```

A row is an advisory `(positive machine key, winner code)` pair. Codes 0–37 are
decoded by `HintTagTr`; successful hints must still pass the existing checker on
the actual machine. The renderer generates no axiom or successful verdict.
Empty input explicitly produces `hint_rows_tr : list TrHintRow := []` and the
same informational `hint_data_schema_tr` API. The populated data regression
requires its established Unit10 key; an empty table is an API fixture, not a
substitute for the intended production corpus.

## Input manifest

`trace-source-manifest.json` has exactly these fields:

- `format: "tr-hint-source-v1"`, `schema_version: 1`, `units: 96`,
  `frontier_count: 1792`, and `chunk_size` in 1–1024 (initially 256).
- `unit_files`: sorted entries `{unit, path, sha256}`. Paths must be exactly
  `tools/censustr/hints/unitNN.rows.json`; the files present must match this list.
  Their contents are unchanged `trace_driver.py check` canonical unit JSON.
- `source_digest` and `trace_payload`: retain the **exact** six-field payload
  from the immutable trace manifest: `source_sha256`, `compiled_sha256`,
  `toolchain`, `tag_schema`, `policy`, `parameters_coq_source`. Its digest is
  SHA256 of `json.dumps(payload, sort_keys=True, separators=(',', ':')).encode()`.
  Historical absolute path labels in this documentary payload must not be
  rewritten: they are never resolved or opened by the renderer.
- `checked_interfaces`: current SHA256 values for `HintTagTr.v`, `HintedTr.v`,
  `RunTr_Hinted.v`, `RunTr_Compute.v`, and `RunTr.v` in `theories/CensusTr`, plus
  `HintedTr_Regression.v` and `HintedTr_Data_Regression.v` in `theories/Tests`.
  These stable relative paths are read and checked. Current checked derivative
  sources remain distinct from the exact historical sources that produced rows.
- `trace_provenance`: documentary metadata, including the original manifest
  format/hash, validation evidence hash/scope and subset coverage. The renderer
  does not authenticate a prior execution, rerun the trace or verify an evidence
  hash against an external filesystem path.
- `safety_limits`: positive integer `input_bytes`, `input_rows`, `chunks`, plus
  a nonempty `rationale`. These explicit reviewed budgets fail closed. They
  never truncate, silently increase, or claim that native memory is bounded.

All inputs must share one digest. A new production fallback closure creates a
new digest; regenerate its complete corpus rather than relabeling or merging
old prototype rows. Every supplied unit must have `complete: true` and exactly
`range(unit, 1792, 96)` frontier indices. Missing units are reported explicitly;
96-unit coverage is reported only when all 96 validated records are present.
Row keys must be sorted, unique positive integers at most `17**8`, and tag codes
must be integers 0–37. Conflicting duplicates across units are rejected; repeated
identical winners are deduplicated. Duplicate JSON fields, booleans as integers,
nonstandard JSON numbers and unsafe/symlink operational paths are rejected.

The initial prototype budgets of 65,536 input rows, 1,024 chunks and 16 MiB input
JSON were **pilot limits**, not a predicted full-corpus size. Inspect the actual
validated corpus totals and deliberately document higher budgets before full
rendering if necessary. There is no automatically selected larger cap. The
provenance manifest itself is limited to 4 MiB. The command and generated
metadata report input/unique row counts, input bytes, chunk count, chunk size
and generated Coq source bytes. Neither 256 nor 1024 is claimed optimal.

## Generated files and replay

`HintParts/HintsTr_Data_PNNNN.v` holds bounded literal lists, while
`HintsTr_Data.v` concatenates them. `generated-data.json` records all generated
source hashes, generator/input hashes, exact included/omitted unit coverage and
aggregate sizes. Fixed chunk sizes bound individual list syntax; total native
map preparation and worker RSS still require measurement. Include all data,
wrapper, dispatcher and native preparation in any performance comparison.

The project synchronizer owns only the hint core/data/test paths, kept in one
block immediately before `RunTr_Compute.v`; every unrelated project entry is
preserved. Optional `hint_trace` modules are not registered. To reduce the
number of generated chunks, first explicitly remove the now-stale generated
chunk sources and their stale compiler artifacts; regeneration fails closed
rather than silently deleting source files. Regenerate and run `--check` after
changing inputs, current checked interfaces, budgets or the generator itself.

Python generation/tests establish deterministic source handling only. Coq
regressions, public proof assumptions, populated data/native preparation, and a
fresh complete target build remain separate validation steps.
