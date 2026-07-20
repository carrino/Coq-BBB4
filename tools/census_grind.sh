#!/bin/bash
# Self-splitting census walk grinder (resume-aware).
# Compiles every Compute walk unit; any unit exceeding CAP is deep-split
# via tools/gen_gsplit_deeper.py and REPLACED by its sub-walks, recursing
# on any sub-walk that is itself too heavy.  Banks every .vo (synced),
# fully resumable: skips done .vo, and finishes any unit already split
# (its Run_Split_<U>.v exists) by reusing banked sub-walk .vo.
set -u
cd /home/user/Coq-BBB4
export OPAMROOT=/root/.opam
eval $(opam env --switch=census)
S=/tmp/claude-0/-home-user/2b01b1ad-6519-5466-986f-cbc04a643004/scratchpad
GEN=tools/gen_gsplit_deeper.py
CAP="${1:-180}"
FALLBACK="${2:-3000}"   # large cap: units unsplittable or too deep to split
SPLITDEPTH="${3:-3}"    # cover lemmas OOM at depth>=4; split only depth<3,
                        # fallback-compile deeper heavy units to completion
SET="${4:-all}"         # top-level unit partition: gg | ggh | all
DOCOMMIT="${5:-1}"      # 1=auto-commit snapshots (primary); 0=skip (secondary)
DEPTHCAP=12
case "$SET" in
  gg)  TOPGLOB="theories/Census/Compute/GG_1LC_*.v" ;;
  ggh) TOPGLOB="theories/Census/Compute/GGH_*.v" ;;
  *)   TOPGLOB="theories/Census/Compute/GG_1LC_*.v theories/Census/Compute/GGH_*.v" ;;
esac

log() { echo "[$(date +%H:%M:%S)] $*"; }

# preserve generated .v files (+ theorem) against reclaim; keep tree clean.
snapshot() {
  [ "$DOCOMMIT" = "1" ] || return 0
  git add -A theories/Census/ >/dev/null 2>&1
  git diff --cached --quiet 2>&1 && return 0   # nothing new
  git commit -q -m "census grind snapshot: $1" >/dev/null 2>&1
  for i in 1 2 3 4; do
    git push origin claude/d-census-shrinking-7amyyl >/dev/null 2>&1 && break
    sleep $((i*i))
  done
}

# finish an already-split unit: cover + each sub-walk + replacement.
finish_split() {
  local U="$1" depth="$2"
  [ -f "theories/Census/Run_Split_${U}.vo" ] || \
    coqc -Q theories BBB4 "theories/Census/Run_Split_${U}.v" >/dev/null 2>&1 || \
    { log "COVERFAIL $U"; return 1; }
  local sf su
  for sf in theories/Census/Compute/GGGH_${U}_*.v; do
    su="$(basename "$sf" .v)"
    process_unit "$su" "$((depth+1))" || { log "SUBFAIL $su"; return 1; }
  done
  coqc -Q theories BBB4 "theories/Census/Compute/${U}.v" >/dev/null 2>&1 \
    || { log "REPLFAIL $U"; return 1; }
  log "ASSEMBLED $U"
  return 0
}

# compile one unit; split+recurse if too heavy. args: basename U, depth
process_unit() {
  local U="$1" depth="$2"
  local vf="theories/Census/Compute/${U}.v"
  [ -f "theories/Census/Compute/${U}.vo" ] && return 0
  [ -f "$vf" ] || { log "MISSING $U"; return 1; }
  if [ "$depth" -gt "$DEPTHCAP" ]; then log "DEPTHCAP $U"; return 1; fi
  # already split? (resume path) -- finish without recompiling the monolith
  if [ -f "theories/Census/Run_Split_${U}.v" ]; then
    finish_split "$U" "$depth"; return $?
  fi
  local s=$SECONDS
  timeout -s KILL "$CAP" coqc -Q theories BBB4 "$vf" >/dev/null 2>&1
  local rc=$?; sync
  if [ $rc -eq 0 ]; then log "OK $U $((SECONDS-s))s"; return 0; fi
  if [ $rc -ne 124 ] && [ $rc -ne 137 ]; then log "FAIL $U rc=$rc"; return 2; fi
  # too deep to split (cover lemma OOMs at depth>=4): run to completion
  if [ "$depth" -ge "$SPLITDEPTH" ]; then
    log "MAXDEPTH $U (d$depth) -> fallback ${FALLBACK}s"
    local ds=$SECONDS
    timeout -s KILL "$FALLBACK" coqc -Q theories BBB4 "$vf" >/dev/null 2>&1
    local drc=$?; sync
    if [ $drc -eq 0 ]; then log "OK $U (fallback $((SECONDS-ds))s)"; return 0; fi
    log "FALLBACK_HEAVY $U rc=$drc $((SECONDS-ds))s"; return 1
  fi
  # too heavy -> generate split, then finish it
  log "SPLIT $U (d$depth, ${CAP}s cap hit)"
  local T="$S/gtmp_${U}"
  rm -rf "$T"
  if ! python3 "$GEN" "$T" "$U" >/dev/null 2>&1; then
    # no valid split point (no reachable hole <= B_census): run to completion
    log "NOSPLIT $U -> fallback ${FALLBACK}s compile"
    local fs=$SECONDS
    timeout -s KILL "$FALLBACK" coqc -Q theories BBB4 "$vf" >/dev/null 2>&1
    local frc=$?; sync
    if [ $frc -eq 0 ]; then log "OK $U (fallback $((SECONDS-fs))s)"; return 0; fi
    log "FALLBACK_HEAVY $U rc=$frc $((SECONDS-fs))s"; return 1
  fi
  cp "$T/Run_Split_${U}.v" theories/Census/ || return 1
  cp "$T/GGGH_${U}_"*.v theories/Census/Compute/ || return 1
  cp "$T/${U}.v" theories/Census/Compute/ || return 1   # replacement overwrites
  rm -rf "$T"
  finish_split "$U" "$depth"; return $?
}

log "=== GRIND start CAP=${CAP} SET=${SET} COMMIT=${DOCOMMIT} ==="
for f in $TOPGLOB; do
  U="$(basename "$f" .v)"
  case "$U" in GGGH_*) continue;; esac
  process_unit "$U" 0 || { log "GRIND_FAIL $U"; snapshot "fail-state $U"; exit 1; }
  snapshot "$U done"
done
log "GRIND_WALKS_DONE ($SET)"
# partition runs (gg/ggh) stop after their walks; only a full 'all' run
# does the G_ assemblies + theorem (needs BOTH partitions' walks banked).
[ "$SET" != "all" ] && { log "PARTITION_DONE ($SET)"; exit 0; }
for f in theories/Census/Compute/G_*.v; do
  U="$(basename "$f" .v)"
  [ -f "theories/Census/Compute/${U}.vo" ] && continue
  coqc -Q theories BBB4 "$f" >/dev/null 2>&1 || { log "GFAIL $U"; exit 1; }
  log "G_OK $U"; sync
done
coqc -Q theories BBB4 theories/Census/Compute/Census_Theorem.v >/dev/null 2>&1
snapshot "walks+G complete"
if [ -f theories/Census/Compute/Census_Theorem.vo ]; then log "GRIND_ALL_DONE"; else log "THEOREM_FAIL"; exit 1; fi
