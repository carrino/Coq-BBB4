#!/usr/bin/env bash
# Build mxdys' RRBA decider and run the three-way control over our residue.
#
# RRBA is the decider whose stated class is "shift-recursive (counter
# balanced, counter inverting), sync bi-counter" -- i.e. our residue's shape
# class.  Wave-15 measured only `Inductive`, which its own author describes as
# getting "SOME OF" the counter families, so the decisive number is missing.
#
# WINDOWS: run this inside WSL2 / Ubuntu, not PowerShell.  It needs apt.
#
#   wsl --install -d Ubuntu     (once, from PowerShell, then reboot)
#   wsl
#   git clone <this repo> && cd Coq-BBB4 && bash tools/mxdys/run_rrba.sh
#
# Wall clock: ~10 min deps + ~25 min extraction + ~20 min the controls.
set -euo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
WORK="${WORK:-$HOME/mxdys-busycoq}"
OUT="${OUT:-$REPO/tools/mxdys/results}"
mkdir -p "$OUT"

say() { printf '\n=== %s ===\n' "$*"; }

say "1/6  toolchain"
if ! command -v coqc >/dev/null; then
  sudo apt-get update -qq
  sudo apt-get install -y coq libcoq-core-ocaml-dev git build-essential
fi
coqc --version | head -1

say "2/6  upstream clone (public repo, ~55 MB)"
if [ ! -d "$WORK" ]; then
  git clone --depth 1 --branch BB6 https://github.com/ccz181078/busycoq.git "$WORK"
fi
cd "$WORK/verify"

# Coq 8.18 needs one scrutinee parenthesised; harmless if already applied.
git apply --reverse --check "$REPO/tools/mxdys/busycoq_bb6_local.patch" 2>/dev/null \
  || git apply "$REPO/tools/mxdys/busycoq_bb6_local.patch" 2>/dev/null || true

say "3/6  dependency closure (15 files, ~10 min)"
Q=(-native-compiler no -Q . BusyCoq -Q ./BigInt BigInt)
for f in LibTactics Helper Eqb HashTable TM Compute Flip Permute Pigeonhole \
         Enumerate Individual Ternary Inductive BBinf Inductive_inf RRBA; do
  [ -f "$f.vo" ] || { echo "  coqc $f.v"; coqc "${Q[@]}" "$f.v"; }
done

say "4/6  extract RRBA (~25 min)"
# Unset Extraction AutoInline is THE fix: the default inliner explodes on
# RRBA's functor body (stack overflow, or >55 min with an unlimited stack).
# Do NOT add Set Extraction Conservative Types -- it emits erased type
# arguments OCaml rejects.
cp "$REPO/tools/mxdys/RRBAX.v" .
if [ ! -f RRBAX.ml ]; then
  ( ulimit -s unlimited 2>/dev/null || true; coqc "${Q[@]}" RRBAX.v )
fi
ls -la RRBAX.ml

say "5/6  build the sweep driver"
cp "$REPO/tools/mxdys/rrba_measure.ml" .
ocamlfind ocamlopt -O2 -package coq-core.kernel,unix -linkpkg \
  RRBAX.mli RRBAX.ml rrba_measure.ml -o rrba_measure

say "6/6  the three-way control"
# A must score HIGH (confirms the rig), B must score ~0 (mxdys' own holdouts),
# C is the question.  A high C is the result that changes the roadmap.
for t in A_boarded B_holdout C_residue; do
  echo "--- $t ---"
  ./rrba_measure "$REPO/tools/mxdys/control/$t.txt" 60 > "$OUT/rrba_$t.tsv" 2>&1 || true
  awk -F'\t' '{c[$2]++} END {printf "  n=%d  NONHALT=%d  FAIL=%d\n", NR, c["NONHALT"], c["FAIL"]}' \
    "$OUT/rrba_$t.tsv"
done

say "SUMMARY"
for t in A_boarded B_holdout C_residue; do
  printf '%-12s ' "$t"
  awk -F'\t' '{c[$2]++} END {printf "n=%3d decided=%3d\n", NR, c["NONHALT"]}' "$OUT/rrba_$t.tsv"
done
echo
echo "Wave-15 got, for the INDUCTIVE decider: A=19/40, B=0/39, C=0/39."
echo "If C is materially above 0 here, RRBA is what eliminated these machines"
echo "and the nested-lap work is re-deriving it by hand."
echo
echo "Raw output in $OUT/ -- commit it and I will pick it up."
