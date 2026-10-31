# Verified state BBB(2,4) run

The complete selected state proof passed in carrino's WSL run reported on
2026-10-31. Both fresh full-recursive kernel audits completed, the exported
theorem and numeric target were checked, and `make proof-2-4` returned normally.

The result is **state-based BBB(2,4) = 205770076433044242247860** in this
repository's last-configuration-index-plus-one convention. The champion is
`1RB2LA1RA1LB_0LB2RB3RB1LA`. Its last state `A` configuration is at index
205770076433044242247859; the next transition reaches permanent `B0` drift.
The global instruction-based value remains open.

## Accepted statement and source checkpoint

```coq
BBB24.Value.BBB24_state_value : BBB24.ValueSpec.BBB24_state_statement
```

The statement combines
`BBB24_state_lower_bound score /\ (forall tm : TM, QHBound score tm)`:
the champion attains the score and every two-state, four-symbol machine
satisfies the state bound. The quantified machine type includes undefined
halting transitions and arbitrary initial transitions. Its definitions are in
[`ValueSpec.v`](../four/theories/ValueSpec.v) and
[`Spec.v`](../four/theories/Spec.v), using the model in
[`Statement.v`](../four/theories/Statement.v).

| Item | Recorded checkpoint |
| --- | --- |
| Source/build commit | [`b011bd2ec0f27d3cee7ba8f3f9d9989d7bd59331`](https://github.com/carrino/Coq-BBB4/commit/b011bd2ec0f27d3cee7ba8f3f9d9989d7bd59331) |
| Merge into `main` | [`c3bff0a7871e2786c39d3074b5d7a118d5e7d9bc`](https://github.com/carrino/Coq-BBB4/commit/c3bff0a7871e2786c39d3074b5d7a118d5e7d9bc), [PR #275](https://github.com/carrino/Coq-BBB4/pull/275) |
| Exact tested and merged Git tree | `2019ac5b87e73f32cf6f3304e02970ac1ef4d697` |
| Frozen source manifest SHA-256 | `d3dcf2838b64e1fc92a93b6e03ada93d56ae0f2354a91e041ec87d83ce898c3c` |
| Selected project sources | 6,813 |
| Toolchain | Coq 8.18.0, compiled with OCaml 4.14.2 |
| Runtime SHA-256 | `64269705de594329af4f50dd27b0c9c9e68331e0056763f559772b0710567e7e` |
| Full recursive audit roots | `BBB24ValueReport.CheckFinal`, `BBB24ValueReport.CheckValue` |
| Reported final assumptions | `FunctionalExtensionality.functional_extensionality_dep` only |

All seven CI workflows passed at the tested source/build commit before merge.
The merge preserved its exact Git tree and the earlier reviewed commits.
The complete proof was run on WSL; the 16-GiB development cloud environment
validated components and build controls rather than the complete global audit.

## Successful execution profile

The source compilation completed before the successful audit run. The run
below resumed that checkpoint, revalidated the frozen sources and compile
receipts, and performed both complete audits. The host had 64 GiB physical RAM,
with 48 GiB allocated to WSL; Linux reported 48,178 MiB total.

```sh
STATE24_AUDIT_RSS_GIB=40 STATE24_COQCHK_TRACE=1 \
STATE24_COQCHK_OCAMLRUNPARAM='o=40,O=60' \
make proof-2-4 BUILD_JOBS=8 STATE24_RESUME=1 STATE24_PROVIDER_LIGHT=1 \
  STATE24_PREPARED=build/state-value-selected-native \
  STATE24_STATE=build/state-value-proof-native
```

The two audit progress records reported one worker, `o=40,O=60`, and
`rss_guard_mib: 40960`. Their address-space cap was 42 GiB. The saved receipts
reported zero fresh project compilations and 6,813 exact receipts resumed.

| Full recursive audit | Elapsed time | Sampled peak owned-process RSS |
| --- | ---: | ---: |
| `CheckFinal` | 21,400.338 s (5 h 56 m 40 s) | 28.235 GiB |
| `CheckValue` | 21,348.551 s (5 h 55 m 49 s) | 28.739 GiB |

The two audit executions total **42,748.889 s (11 h 52 m 29 s)**. This excludes
the earlier source compilation and other preparation/validation work; the
uninterrupted complete fresh-build time remains unmeasured. The RSS figures
are sampled process-tree measurements, distinct from the 40-GiB configured
guard. Minimum required memory also remains unmeasured.

The [compact receipt summary](BBB24_VERIFIED_RUN.json) records the runtime and
source identifiers, final statuses, timings, RSS measurements, and log hashes:

* `CheckFinal-coqchk.log` SHA-256:
  `04abd1c8c08b24b435e2e3af9bd7e8c78533d18e99fc29535e92d3be5b8be8c4`;
* `CheckValue-coqchk.log` SHA-256:
  `07bedecf0287abfaaced7abad7eadc941ace69e368c7de2408bf12ca3eca3f4b`.

For a fresh source build, use the same profile without `STATE24_RESUME=1` and
choose empty prepared-tree/state paths, or use the default paths in a fresh
checkout. Installation and detailed controls are in
[`VERIFYING_BBB24.md`](VERIFYING_BBB24.md).

## Acceptance evidence

The completed console report included:

```text
BBB(2,4) = 205770076433044242247860 -- state based, kernel checked
BBB24.Value.BBB24_state_value : BBB24.ValueSpec.BBB24_state_statement
The champion attains this score, and every two-state, four-symbol machine satisfies the upper bound.
Full recursive coqchk: passed.
```

The printed statement definitions and numeric evaluation matched the public
claim. The final `Print Assumptions` block listed only
`FunctionalExtensionality.functional_extensionality_dep`, the standard
functional-extensionality assumption used by the other established values.
Both standalone checks were full recursive audits, without `-admit` or
`-norec` dependency exclusions.

Preserve these files from `four/build/state-value-proof-native/` with any
independent reproduction report:

* `build-result.json`, `build-identity.json`, and `runtime.json`;
* `final-gate.json`, `value-alias.json`, and `state-value-result.json`;
* `CheckFinal-compile.log`, `CheckFinal-coqchk.log`, and
  `CheckFinal-audit-policy.json`;
* `CheckValue-compile.log`, `CheckValue-coqchk.log`, and
  `CheckValue-audit-policy.json`.

The receipts bind the statement, source manifest, runtime, current proof
objects and audit logs. The success banner is printed only after both audit
gates pass; the completed command then writes its final build result.
