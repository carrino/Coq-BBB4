#!/bin/sh
# UNTRUSTED: rebuild mxdys' Inductive search oracle and sweep a row list.
#
#   sh tools/mxdys/sweep_inductive.sh <workdir> <rowlist> [maxT] [per-cfg-timeout]
#
# Produces <workdir>/sweep.tsv, one line per row, columns as tools/mxdys/measure.ml
# documents: NONHALT with the winning config and the rule-endpoint state sets, or
# FAIL ("this sweep found nothing", never "nonexistent" -- wave-14's lesson).
#
# A NONHALT verdict from this binary is an ORACLE result, not a proof: BBinf.v
# carries the upstream tree's only two Admitted lemmas (all_qs_spec,
# all_syms_spec).  See docs/MXDYS_INDUCTIVE_STAGE0.md section 1.  Nothing under
# theories/ depends on any of this; the kernel re-checks every board.
#
# Cost, measured 2026-07-30 in a stock container: apt coq install ~2 min, clone
# ~30 s, the 15-file dependency closure ~3 min, the driver link ~10 s.  A row
# that DECIDES costs seconds; a row that does not costs 7 x the per-config
# timeout, so run FAIL-heavy lists with a small timeout first.

set -e
WORK=${1:?usage: sweep_inductive.sh <workdir> <rowlist> [maxT] [timeout]}
ROWS=$(realpath "${2:?missing row list}")
MAXT=${3:-100000}
TMO=${4:-30}
HERE=$(cd "$(dirname "$0")" && pwd)

mkdir -p "$WORK"
cd "$WORK"

if [ ! -d busycoq ]; then
  git clone --depth 1 --branch BB6 https://github.com/ccz181078/busycoq.git
  # Coq 8.18 needs one parenthesisation fix; upstream targets newer Rocq.
  (cd busycoq/verify && git apply "$HERE/busycoq_bb6_local.patch")
fi

cd busycoq/verify
if [ ! -f measure ]; then
  # Dependency closure of Inductive_inf.v -- 15 files.  Inductive_inf
  # instantiates the framework at BBinf (Q = Sym = N), so its TM'_from_str
  # parses bbchallenge rows directly and '---' maps to None (halt): a (4,2)
  # row works AS IS, with no BB42.v/Individual42.v.
  for f in LibTactics Helper Eqb HashTable TM Compute Flip Permute Pigeonhole \
           Enumerate Individual Ternary Inductive BBinf Inductive_inf; do
    coqc -native-compiler no -Q . BusyCoq -Q ./BigInt BigInt $f.v
  done
  cp "$HERE/measure.ml" "$HERE/measure2.ml" "$HERE/dump.ml" .
  ocamlfind ocamlopt -O2 -package coq-core.kernel,unix -linkpkg \
    Inductive.mli Inductive.ml measure.ml -o measure
  ocamlfind ocamlopt -O2 -package coq-core.kernel,unix -linkpkg \
    Inductive.mli Inductive.ml dump.ml -o dump
fi

./measure "$ROWS" "$MAXT" "$TMO" | tee "$WORK/sweep.tsv"

echo "# rules of a decided row:  $WORK/busycoq/verify/dump <row> default <maxT> 10000000"
