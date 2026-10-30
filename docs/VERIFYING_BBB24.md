# State BBB(2,4): selected source build

The complete state proof build is under verification. Its source preparation
and resource-profile metadata have been independently checked; the complete Coq
build and its memory fit still need confirmation. Follow the
[scoreboard](https://github.com/carrino/Coq-BBB4/issues/261) for current proof status.

From the repository root, run the reviewed source build with:

```sh
make proof-2-4 BUILD_JOBS=8
```

The selected build prepares the exact source dependency graph from repository
inputs, compiles it in dependency order, and checks the unconditional theorem
`BBB24OpaqueCensus448.Final.BBB24_state_value` against
`BBB24.ValueSpec.BBB24_state_statement`. That statement combines champion
attainment and an upper bound for every machine under the repository's state
quasihalting definition. Its target is **205770076433044242247860**.

The success path prints the statement, both numeric checks, actual theorem
assumptions, and recursive kernel audit results. The only permitted nonempty
assumption set is the standard
`FunctionalExtensionality.functional_extensionality_dep` used elsewhere in this
development. Only a successful complete type, numeric, assumptions and recursive audit run
establishes this state equality. A failed check stops the command and does not
establish a global result.

`Value.v` is generated inside the prepared tree only after the real Final theorem
and its full recursive audit pass. The Value alias then receives a fresh typed
check, assumptions check and another full recursive audit. No root
`four/theories/Value.v` or prebuilt object is distributed as proof evidence.

## Requirements and resource policy

Use the Coq 8.18.0 / OCaml 4.14.2 census toolchain described in
[VERIFYING.md](VERIFYING.md). Source preparation was reproduced using isolated
CPython 3.12.14 and its standard library; Python 3.12 is the tested choice.
Build on a case-sensitive Linux/WSL disk filesystem, such as the WSL Linux home
directory. The driver rejects tmpfs and ramfs for the prepared tree and logs.

The WSL profile is intended for an environment exposing roughly
32 GiB to Linux. It allows ordinary work up to eight workers, provider/check
work up to two, and assembly one at a time. Providers have caps of
8 GiB address space and 7 GiB resident memory per worker; assembly keeps
27 GiB address space and 25 GiB resident memory. Ordinary workers retain their 2-GiB address-space limit.
`SmallBB.Census23Conditional` uses the separate census-check phase, with a
4-GiB address-space and 3686-MiB resident-memory limit; it exceeds the ordinary
limit even with native compilation enabled. The provider allowance gives the
blank-root frontier modules more headroom. These are limits, not measured
requirements or a guarantee that the complete graph fits.

The driver takes the minimum visible Linux and cgroup memory limits. At phase
selection, it reserves `max(1536 MiB, visible RAM / 10)` and caps concurrency by
current usable memory. While commands run, it stops if available memory falls
below half that reserve. Every command also has its own address-space, sampled
RSS, timeout and descendant-cleanup checks. The current implementation does not
promise a separate fixed 4-GiB reserve.

The cloud research runner has a distinct reviewed 14-GiB address-space and
12.25-GiB RSS profile. The portable cloud profile has not passed the
complete build; the portable driver's own memory preflight can refuse it.
A failed command never raises the frozen full-budget limits. The optional
small-budget provider pass below can retry within the existing provider limit.

The default disk guard retains 8 GiB of free space. Generated Coq sources,
objects, runtime receipts and logs occupy additional disk space. Generated
proof sources remain under `four/build/`; they are not committed to the repo.

Before compilation, fresh `coqdep` output must match the selected source graph
exactly. The driver keeps `_CoqProject.selected` in proof state as a log and uses
a temporary project at the prepared tree root for the check. This lets Coq
resolve the relative source and namespace paths correctly when the checkout or
build-state path contains spaces. The temporary project is removed on success
or failure; the state copy and dependency log remain. Warnings, unknown sources,
unknown dependencies, missing sources and graph mismatches stop the build.

The Make build and report targets give their child processes at least a 64-MiB
stack, matching the existing affine replay. The large affine aggregate's
26,970-family count can overflow the usual 8-MiB shell stack. This changes the
process stack allowance; address-space and resident-memory guards still apply.
An already larger or unlimited stack is preserved. A hard stack limit below
64 MiB stops the command with a clear error.

For direct Python-driver invocations, use the same wrapper, for example
`python3 four/tools/with_coq_stack.py python3 four/tools/build_state_value.py ...`.
If resuming an older checkout without updating, run `ulimit -S -s 65536` in that
shell first, then use the same resume command and paths. Completed object
receipts remain reusable; source preparation and compiler flags are unchanged.

The selected compiler uses `-native-compiler ondemand`: census proofs can use
`native_compute` without generating native objects for every module. The driver
checks native capability before compiling, and treats native-to-VM fallback as
an error. Forcing `-native-compiler no` can exhaust memory in
`SmallBB.Census23Conditional`; adding workers does not fix that fallback.

## Logs, resume and separate checks

`BUILD_JOBS` reaches the selected compiler scheduler. Memory limits can reduce
actual concurrency below the requested count. `STATE24_JOBS` is an optional
override for this target alone. The old BBB(4) `proof-all` target remains separate.

For the bulk provider phase, enable the optional faster pass with
`STATE24_PROVIDER_LIGHT=1`. It first tries up to `BUILD_JOBS` files (at most eight)
using the ordinary 2-GiB address-space and 1843-MiB RSS limits. A file that reaches
that memory limit is retried once under its original provider budget, at most
two at a time. The small-budget and full-budget batches never overlap. Type or
statement errors, timeouts, disk failures and the system-memory guard still stop
the build. Dependency readiness and available RAM can reduce concurrency.

This mode changes scheduling, while keeping source preparation, compiler flags,
object validation and final recursive audits intact. Assembly remains serial.
Small-budget logs use `.light.log`; a full-budget retry preserves that log and
records its reason in the successful compile receipt.

To upgrade a running build from `91c48ed4`, press Ctrl+C and wait for the shell
prompt **before updating the checkout**. Then run, preserving the paths used by
that build:

```sh
git fetch origin
git merge --ff-only origin/codex/bbb24-provider-parallelism
make proof-2-4 BUILD_JOBS=8 STATE24_RESUME=1 STATE24_PROVIDER_LIGHT=1 \
  STATE24_PREPARED=build/state-value-selected-native \
  STATE24_STATE=build/state-value-proof-native
```

The resume migration accepts only that exact preceding driver with the same
source graph, toolchain, compiler policy, resource monitor and reporter. It
records the scheduler upgrade, checks every object receipt, and repeats the
final audits. Other identity changes still require a fresh build. Existing
completed files can be reused; no `git clean` is needed. To return to the normal
provider schedule after upgrading, omit `STATE24_PROVIDER_LIGHT=1` on a later
resume.

Default prepared sources and proof state live under
`four/build/state-value-selected/` and `four/build/state-value-proof/`. To place
them on another disk:

```sh
make proof-2-4 BUILD_JOBS=8 \
  STATE24_PREPARED=/path/on/disk/bbb24-prepared \
  STATE24_STATE=/path/on/disk/bbb24-proof-state
```

Resume only the same initialized source graph, toolchain and compiler settings:

```sh
make proof-2-4 BUILD_JOBS=8 STATE24_RESUME=1
```

If upgrading from the build that forced `-native-compiler no`, start in new
prepared-source and proof-state directories. The compiler settings changed, so
its existing receipts cannot be resumed. Preserve the old logs; no repository
cleanup is needed:

```sh
make proof-2-4 BUILD_JOBS=8 \
  STATE24_PREPARED=build/state-value-selected-native \
  STATE24_STATE=build/state-value-proof-native
```

Use those same path overrides with `STATE24_RESUME=1` to resume this new run.

An object is reused only when its complete source, dependency, runtime, selected
path, compiler-flag and object receipts match. Resume still performs the final
recursive audits. A bare `.vo` file or a matching version string is insufficient.
After a completed selected build, `make -C four proof-report` repeats the exact
statement, assumptions and full recursive audit on the current selected graph.

The smaller public checkpoint remains available independently:

```sh
make proof-2-4-checkpoint BUILD_JOBS=8
```

That command checks the public theories/regressions and original hard-machine
proofs. It does not establish the universal state upper bound or print the full
equality success report.
