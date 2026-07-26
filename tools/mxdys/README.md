# mxdys' Inductive/RRBA deciders — Stage 0 measurement harness

_Wave-15.  This directory holds everything needed to rebuild the native
search oracles extracted from mxdys' busycoq tree and re-run the Stage 0
measurement of `docs/MXDYS_DECIDERS_PLAN.md` over the residue.  Everything
here is UNTRUSTED tooling — no board depends on it; it finds certificates,
it does not prove them._

## Provenance

Upstream: `https://github.com/ccz181078/busycoq`, branch `BB6`,
commit `895b0f366643438462c513fe3069233b38b9113e` (2026-07-03).
Base framework MIT-licensed (Maja Kądziołka); mxdys' additions on top.
Per John (2026-07-26): vendor what we need, do not depend on the repo.

One local patch is required for Coq 8.18 (upstream targets newer Rocq):
`busycoq_bb6_local.patch` parenthesizes one `match if ... with` scrutinee
in `RRBA.v`.

## What got verified about the upstream tree (plan §1, re-checked here)

* `Inductive.v` / `RRBA.v` / `RWLAcc.v` have no `Axiom`/`Admitted`.
* The native `./decider` is extracted from `Inductive_inf.v`, which
  instantiates the framework at `BBinf` (`Q := N`, `Sym := N`) — it parses
  the standard text format directly, so a (4,2) machine string works AS IS;
  no `BB42.v`/`Individual42.v` is needed for the *measurement*.
  CAVEAT: `BBinf.v` has two `Admitted` lemmas (`all_qs_spec`,
  `all_syms_spec` — its state enumeration is empty), so the `BBinf`
  instantiation is a SEARCH ORACLE only.  A proof-grade (4,2) instance
  must be the finite `BB42 <: Ctx` (26 lines, pattern on `BB52.v`) —
  that is Stage 1 work, not needed for Stage 0 numbers.

## Build (apt coq 8.18.0, container)

    apt-get install -y coq libcoq-core-ocaml-dev
    git clone --depth 1 --branch BB6 https://github.com/ccz181078/busycoq.git
    cd busycoq/verify
    git apply .../busycoq_bb6_local.patch
    # dep closure of Inductive_inf.v (15 files, ~10 min):
    #   LibTactics Helper Eqb HashTable TM Compute Flip Permute Pigeonhole
    #   Enumerate Individual Ternary Inductive BBinf Inductive_inf
    for f in <that order>; do coqc -native-compiler no -Q . BusyCoq -Q ./BigInt BigInt $f.v; done
    make decider          # ocamlfind + coq-core.kernel; gives ./decider
    coqc -native-compiler no -Q . BusyCoq -Q ./BigInt BigInt RRBA.v RRBAX.v   # RRBAX: see below
    coqc -native-compiler no -Q . BusyCoq -Q ./BigInt BigInt RWLAcc.v RWLX.v
    ocamlfind ocamlopt -O2 -package coq-core.kernel,unix -linkpkg Inductive.mli Inductive.ml measure.ml -o measure
    ocamlfind ocamlopt -O2 -package coq-core.kernel,unix -linkpkg Inductive.mli Inductive.ml measure2.ml -o measure2
    ocamlfind ocamlopt -O2 -package coq-core.kernel,unix -linkpkg RWLX.mli RWLX.ml rwl_measure.ml -o rwl_measure

### Extracting RRBA -- SOLVED, and the recipe matters

`RRBA` is the decider whose stated class is "shift-recursive (counter
balanced, counter inverting), sync bi-counter" -- i.e. our residue's shape
class.  Extracting it defeated several attempts; the fix is one flag:

    Unset Extraction AutoInline.

The default inliner explodes on RRBA's functor body: `coqc` stack-overflows at
the default stack, and with `ulimit -s unlimited` it ran >55 minutes without
finishing.  With auto-inlining off it completes and emits ~291 KB of OCaml.
(`Recursive Extraction Library RRBA` is NOT a fallback -- it emits only a stub
of `open` lines, because the functor body does not survive library
extraction.)

**Do NOT also add `Set Extraction Conservative Types`.**  It makes extraction
emit erased type arguments that OCaml then rejects -- a nullary `ReflectT`
applied to `__`, and `PArray.make` applied to three arguments.  Both are
artifacts of that flag alone.

Build order for the RRBA driver:

    coqc -native-compiler no -Q . BusyCoq -Q ./BigInt BigInt RRBA.v
    ulimit -s unlimited
    coqc -native-compiler no -Q . BusyCoq -Q ./BigInt BigInt RRBAX.v   # ~25 min
    ocamlfind ocamlopt -O2 -package coq-core.kernel,unix -linkpkg \
      RRBAX.mli RRBAX.ml rrba_measure.ml -o rrba_measure

## The drivers

| file | role |
|---|---|
| `measure.ml`  | Inductive sweep: per machine try configs (default, arithseq, exploop, arith+exploop, bsz2, bsz3, bsz2+exploop) at a given `maxT`; on NONHALT, walk the final `hlin_layers` and report endpoint states + `powsum`/`mul` usage |
| `measure2.ml` | re-run DECIDED machines iterating `hlin_layers_step` manually, accumulating rule-endpoint states over the WHOLE derivation (`SaccMS`) next to the final tower (`Sfin`) |
| `rrba_measure.ml` | RRBA `decide_loop2` sweep (params mirror `RRBAv*.v` usage: n_skip 0-2, k 4-8, T 1k-60k, loop1-as-loop2 variant) |
| `rwl_measure.ml`  | RWLAcc `decide_nonhalt` sweep (bsz 2-15, bmaxT 3200, T 1e7) |

Output is one TSV line per machine; `FAIL` means "this sweep found
nothing", never "nonexistent" (wave-14 lesson: survey, then conclude).
