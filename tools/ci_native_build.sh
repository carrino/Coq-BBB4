#!/usr/bin/env bash
# Native computation dependencies first; every requested proof still compiles.
set -euo pipefail
if (( $# == 0 )); then
  echo 'No changed Coq targets.'
  exit 0
fi
ulimit -s unlimited
jobs=$(python3 tools/proof_resources.py --rss-gib 3 --core-cap 2)
echo "Native proof build: $# targets, $jobs workers"
make -f Makefile.coq -j"$jobs" COQEXTRAFLAGS='-native-compiler yes' \
  theories/CensusTr/RepWLMBTr.vo \
  theories/CensusTr/RunTr_WalkCompute.vo \
  theories/Checkers/TCyclerNFast.vo \
  theories/Checkers/FuelMixTargetFastTr.vo \
  theories/Checkers/FuelMixPartialTr.vo
make -f Makefile.coq -j"$jobs" COQEXTRAFLAGS='-native-compiler ondemand' "$@"
