#!/bin/bash
# Clean proven-only (16,115) census walk: compile monolith walk units +
# assemblies + theorem, resumable (.vo-skip), generous per-unit cap so heavy
# GG_1LC units get a full window. No splitting -- the walk is light.
#
# NOT THE SUPPORTED WALK.  `make census-verify' is, and it does strictly
# more: WALK_JOBS parallelism, the separate WALK_ASM_JOBS sizing for the
# 15 files that still Require Run.v (this script would run them at the
# same fan-out as the lean units), per-unit RSS recording to
# census_probes/walk-rss.tsv, and the walk-stamp that quarantines .vo not
# produced by walking THIS tree.  This one is kept only as a serial
# fallback for a box that cannot spare the RAM for any parallelism.
#
# It used to hardcode a container's paths (`cd /home/user/Coq-BBB4' and
# OPAMROOT=/root/.opam), so on any other machine it cd'd nowhere and
# walked whatever happened to be in $PWD.  Both are now derived.
set -u
cd "$(dirname "$(readlink -f "$0")")/.." || exit 1
# Activate the census switch only if it exists and is not already active;
# a caller who has already run `eval $(opam env --switch=census)' keeps it.
if [ -z "${COQBIN:-}" ] && command -v opam >/dev/null 2>&1; then
  if opam switch list --short 2>/dev/null | grep -qx census; then
    eval "$(opam env --switch=census)"
  fi
fi
command -v coqc >/dev/null 2>&1 || { echo "no coqc on PATH -- activate the census switch first"; exit 1; }
CAP="${1:-3600}"
log(){ echo "[$(date +%H:%M:%S)] $*"; }
unit(){ local f="$1" c="${2:-$CAP}"
  [ -f "${f}o" ] && return 0
  local s=$SECONDS
  timeout -s KILL "$c" coqc -Q theories BBB4 "$f" >/dev/null 2>&1; local rc=$?; sync
  if [ $rc -eq 0 ]; then log "OK $(basename $f) $((SECONDS-s))s"; return 0
  elif [ $rc -eq 124 ] || [ $rc -eq 137 ]; then log "TIMEOUT $(basename $f) $((SECONDS-s))s (retry next window)"; return 1
  else log "FAIL $(basename $f) rc=$rc"; return 2; fi
}
log "=== CENSUS WALK start (proven-only 16,115) CAP=${CAP} ==="
# base layers (fast, already built typically)
for f in theories/Census/Run_Split.v theories/Census/Run_Split2.v theories/Census/Run_Split_[01]*.v; do unit "$f" 600 || true; done
# walk units
inc=0; done=0
for f in theories/Census/Compute/GG_1LC_*.v theories/Census/Compute/GGH_*.v; do
  case "$(basename $f)" in GGGH_*) continue;; esac
  if unit "$f"; then done=$((done+1)); else inc=$((inc+1)); fi
done
log "walk units: $done done, $inc incomplete this pass"
[ $inc -gt 0 ] && { log "CENSUS_WALK_INCOMPLETE ($inc units need another window)"; exit 2; }
# assemblies + theorem
for f in theories/Census/Compute/G_*.v; do unit "$f" 900 || { log "CENSUS_WALK_INCOMPLETE"; exit 2; }; done
unit theories/Census/Compute/Census_Theorem.v 1800 || { log "CENSUS_WALK_INCOMPLETE"; exit 2; }
[ -f theories/Census/Compute/Census_Theorem.vo ] && log "CENSUS_ALL_DONE" || log "CENSUS_WALK_INCOMPLETE"
