# Regenerating instruction-census hints

These optional tools trace `decider_tr_fallback`, the unchanged full ladder.
They share the production fast frontier, 4096 successor rounds and binary queue
budget13. Their exact projection lemmas target `unit_ok_fallback`; they make no
claim that a hinted walk has identical decisions. The normal proof build uses
stored hints and never runs these tools. Trace modules are not in `_CoqProject`.

Use a fresh, frozen checkout. Build `RunTr_WalkCompute` and all of its native
companions with the project's Coq/OCaml toolchain. Compile these optional modules
in order with the mappings below, and retain `TraceAudit.v`'s assumptions output:

```sh
coqc -q -native-compiler yes -Q theories BBB4 -Q tools/censustr/hint_trace BBB4HintTrace tools/censustr/hint_trace/TraceRungsTr.v
coqc -q -native-compiler yes -Q theories BBB4 -Q tools/censustr/hint_trace BBB4HintTrace tools/censustr/hint_trace/TraceWalkTr.v
coqc -q -native-compiler yes -Q theories BBB4 -Q tools/censustr/hint_trace BBB4HintTrace tools/censustr/hint_trace/TraceAudit.v
```

Keep native preparation and offline generation costs separate from a fresh proof
build's time. Do not edit source, compiled prerequisites or the toolchain during a
trace. The driver fingerprints the complete dependency closure, native artifacts,
configuration and tools. Run it from that same frozen checkout:

```sh
python3 tools/censustr/hint_trace/trace_driver.py plan --root "$PWD" --outdir work/trace-unit10 --unit 10
python3 tools/censustr/hint_trace/trace_driver.py run --manifest work/trace-unit10/manifest.json --kind inventory
```

The accepted inventory gives every assigned frontier index. For each index `J`,
use `emit --manifest ... --frontier-index J`, followed by
`run --manifest ... --kind shard --frontier-index J`. After all assigned shards
succeed, `check --manifest ...` validates exact coverage and produces
`complete-unit.rows.json`. Only validated complete-unit JSON is input to the
hint-data generator. Missing/failed shards, changed artifacts, malformed output,
invalid tags and conflicting rows are rejected. Preserve failed attempts and
start a new output directory instead of overwriting run records.

Standalone `run` serializes compiler work with an exclusive checkout-local
`.hint-trace.lock`, outside its timer. `--lock PATH` selects a shared lock used by
other build jobs. A trusted outer supervisor may supply both `--lock PATH` and
`--inherited-lock-fd FD` while already holding that descriptor's exclusive lock.
The child checks the descriptor/path identity and duplicates the same open file
description; it never calls `flock` or `LOCK_UN` in inherited mode. Identity is not
proof of lock ownership. The supervisor must bound its workers and stop/reap all
children before releasing its lock. Version probes and Coq inherit the descriptor.
Do not wrap standalone mode in another acquisition of the same lock.

The parser supports both decimal positives and Coq's typed `BinNums.xO/xI/xH`
printer output. `python3 -m unittest discover -s tools/censustr/hint_trace -p
"test_*.py"` exercises parser and lock-adapter regressions without invoking Coq.
The retained native fixture is a successful177-row output from the validated
Unit10 pilot; a parser test does not constitute a new trace or coverage proof.

The schema's38 tags are advisory. Production accepts a hint only after running
its existing checker on the actual machine, and otherwise invokes the original
fallback. No trace JSON, generator or manifest is part of the proof's trust base.
