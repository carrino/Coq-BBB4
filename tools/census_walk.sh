#!/bin/bash
# Clean proven-only (16,115) census walk: compile monolith walk units +
# assemblies + theorem, resumable (.vo-skip), generous per-unit cap so heavy
# GG_1LC units get a full window. No splitting -- the walk is light.
set -u
cd /home/user/Coq-BBB4
export OPAMROOT=/root/.opam; eval $(opam env --switch=census)
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
