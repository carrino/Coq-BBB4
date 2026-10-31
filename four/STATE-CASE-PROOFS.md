# Individual state proofs for BBB(2,4)

These are 36 individually proved families from the original final 78 holdouts, in 30 replay packages. This source checkpoint was frozen when 59 of 78 had proofs and 19 remained. The other 23 accepted families belong to an earlier history-marker batch. This collection does not prove the global upper bound, and makes no instruction-based claim.

Follow the current [public scoreboard](https://github.com/carrino/Coq-BBB4/issues/261) for the complete checklist, review status, and census assembly. Counts there can advance beyond this frozen source checkpoint.

The [additional checkpoint](STATE-CASE-PROOFS-ADDITIONAL.md) supplies seven newer cases and the earlier 23 history-marker cases. Run both checkpoints to reproduce all 66 accepted cases at that freeze.

The [recent checkpoint](STATE-CASE-PROOFS-RECENT.md) adds eleven more reviewed families, bringing source replay to 77 of the original 78 at its freeze.

## Build and audit

Use the repository's tested Coq 8.18.0 / OCaml 4.14.2 toolchain with `coq-native`, GNU make and Python 3; see [toolchain setup](../docs/VERIFYING.md#reproduce-the-complete-targets). From the repository root:

```bash
eval "$(opam env --switch=census)"
python3 four/tools/replay_state_case_proofs.py --list
python3 four/tools/replay_state_case_proofs.py
```

The replay command checks the frozen source/input hashes, builds the required public theories, prepares the shared helper modules, and runs each case proof driver. Each driver compiles the exact transition table, universal machine lemmas, regression controls, census-family wrapper and inventory, then recursively audits the result with `coqchk`. Compiled artifacts and audit receipts are generated under `four/build/`; none need to be downloaded. Run packages sequentially to keep memory use predictable.

For one package, use its name from the table:

```bash
python3 four/tools/replay_state_case_proofs.py --only burn21-s032-finite
```

The frozen historical drivers for next1a, next1b and DoubleZeroRank require workspace-specific compiled-object hashes. For these three cases, the replay command uses a separate portable checker: it verifies the same frozen sources, inputs, generated statements and inventories, then recompiles and recursively audits the current shared dependencies. Historical reports and drivers remain unchanged; no old compiled object is trusted.

The wrapper automatically builds BinaryRank for DoubleZeroRank, the generic HistoryMarker package for next1a/next1b, and CounterObligations for S056. It retains a log for every command and a machine-readable replay result under `four/build/state-case-proof-replay/`. Existing frozen reports are preserved; each driver writes its new audit receipt into its own build directory. A current toolchain on PATH is required.

## Cases and claims

`QHBound 0` here follows from recurrence of both states: the machine never quasihalts. Positive bounds establish a finite upper bound below the champion. They are not necessarily the exact machine score. All rows refer to complete tables and prove the state bound for every completion of that table.

| Cases | Package / proof sources | State bound | Frozen report |
| --- | --- | ---: | --- |
| S024 | [burn17-binary-rank](proof-sources/burn17-binary-rank/) | 0 | [checked](research/burn17-binary-rank-checked.json) |
| S047 | [burn17-quaternary-sibling](proof-sources/burn17-quaternary-sibling/) | 0 | [checked](research/burn17-quaternary-sibling-checked.json) |
| S013 | [burn17-double-zero-rank](proof-sources/burn17-double-zero-rank/) | 0 | [checked](research/burn17-double-zero-rank-checked.json) |
| S046 | [burn17-zero-marker](proof-sources/burn17-zero-marker/) | 0 | [checked](research/burn17-zero-marker-checked.json) |
| S034 | [burn12-history-marker-next1a](proof-sources/burn12-history-marker/) | 0 | [checked](research/burn12-history-marker-next1a-checked.json) |
| S060 | [burn12-history-marker-next1b](proof-sources/burn12-history-marker/) | 0 | [checked](research/burn12-history-marker-next1b-checked.json) |
| S027, S031 | [burn18-cut-siblings](proof-sources/burn18-cut-siblings/) | 0 | [checked](research/burn18-cut-siblings-checked.json) |
| S045 | [burn17-paired-zero-counter](proof-sources/burn17-paired-zero-counter/) | 0 | [checked](research/burn17-paired-zero-counter-checked.json) |
| S048 | [burn17-terminal-pair-counter](proof-sources/burn17-terminal-pair-counter/) | 0 | [checked](research/burn17-terminal-pair-counter-checked.json) |
| S067, S068 | [burn18-paired-carry](proof-sources/burn18-paired-carry/) | 0 | [checked](research/burn18-paired-carry-checked.json) |
| S051, S055 | [burn18-double-pair](proof-sources/burn18-double-pair/) | 0 | [checked](research/burn18-double-pair-checked.json) |
| S001, S002, S003 | [burn19-binary-trio](proof-sources/burn19-binary-trio/) | 0 | [checked](research/burn19-binary-trio-checked.json) |
| S044 | [burn18-s044-counter](proof-sources/burn18-s044-counter/) | 0 | [checked](research/burn18-s044-counter-checked.json) |
| S006 | [burn20-run-counter](proof-sources/burn20-run-counter/) | 0 | [checked](research/burn20-run-counter-checked.json) |
| S065 | [burn18-s065-rightmost](proof-sources/burn18-s065-rightmost/) | 0 | [checked](research/burn18-s065-rightmost-checked.json) |
| S009 | [burn20-run-sibling](proof-sources/burn20-run-sibling/) | 0 | [checked](research/burn20-run-sibling-checked.json) |
| S063 | [burn19-finite-counter](proof-sources/burn19-finite-counter/) | 4,294,967,296 | [checked](research/burn19-finite-counter-checked.json) |
| S012 | [burn18-s012-rightmost](proof-sources/burn18-s012-rightmost/) | 0 | [checked](research/burn18-s012-rightmost-checked.json) |
| S011 | [burn20-unary-counter](proof-sources/burn20-unary-counter/) | 0 | [checked](research/burn20-unary-counter-checked.json) |
| S022 | [burn20-fibonacci-counter](proof-sources/burn20-fibonacci-counter/) | 0 | [checked](research/burn20-fibonacci-counter-checked.json) |
| S077 | [burn19-s077-finite](proof-sources/burn19-s077-finite/) | 4,194,304 | [checked](research/burn19-s077-finite-checked.json) |
| S057 | [burn21-s057-drift](proof-sources/burn21-s057-drift/) | 4,194,304 | [checked](research/burn21-s057-drift-checked.json) |
| S050 | [burn20-paired-wall-counter](proof-sources/burn20-paired-wall-counter/) | 0 | [checked](research/burn20-paired-wall-counter-checked.json) |
| S053 | [burn22-s053-counter](proof-sources/burn22-s053-counter/) | 0 | [checked](research/burn22-s053-counter-checked.json) |
| S075 | [burn20-pair-accumulator](proof-sources/burn20-pair-accumulator/) | 0 | [checked](research/burn20-pair-accumulator-checked.json) |
| S032 | [burn21-s032-finite](proof-sources/burn21-s032-finite/) | 72,057,594,037,927,936 | [checked](research/burn21-s032-finite-checked.json) |
| S069 | [burn23-s069-transducer](proof-sources/burn23-s069-transducer/) | 0 | [checked](research/burn23-s069-transducer-checked.json) |
| S062 | [burn23-s062-counter](proof-sources/burn23-s062-counter/) | 0 | [checked](research/burn23-s062-counter-checked.json) |
| S056 | [burn24-s056-counter](proof-sources/burn24-s056-counter/) | 0 | [checked](research/burn24-s056-counter-checked.json) |
| S004, S005 | [burn23-s004-s005-unary](proof-sources/burn23-s004-s005-unary/) | 0 | [checked](research/burn23-s004-s005-unary-checked.json) |

The [checkpoint manifest](research/state-case-proofs-checkpoint.json) records each exact machine, report digest, package prerequisites and source/input hashes. Each selected package's `*-proof-input.json` and driver identify its exact formal statement and table encoding. The generated `Board.v` and `Inventory.v` connect the machine proof to census membership.

S032 proves an exact state score of **67,093,892,759,901,295**, using a finite macro trace and a closed terminal alphabet; its table entry gives the convenient bound `2^56`. S077 has exact score 2,501,552 and S057 has exact score 2,333,909, both below `2^22`. S063 uses the bound `2^32`; its later all-zero checkpoint is not an exact last-state-visit claim.

Universal counter or transducer lemmas establish the unbounded behavior. Native simulation controls receive no kernel proof credit; finite prefixes checked inside Coq do contribute to the formal proof. Core macro lemmas are checked without axioms; final tape/function transport can use the repository's existing functional extensionality axiom. Inspect each final `Print Assumptions` block and its recursive audit log.

The [state case proof workflow](../.github/workflows/state-cases.yml) replays all 30 packages in three independent source checkouts. Existing proof workflows also run on the PR. This checkpoint adds separate namespaces and leaves existing core proof sources unchanged.
