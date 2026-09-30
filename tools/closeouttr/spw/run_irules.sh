#!/bin/bash
# run_irules.sh BUDGET TIMEOUT ROWFILE OUTDIR [JOBS]
# One bin/irules per row under a wall-clock timeout (untrusted search).
# A row with a result in OUTDIR/res is skipped, so the run resumes after a
# restart.  Certificates land in OUTDIR/certs; OUTDIR/res/<row> holds the
# irules CSV line (with --why's failure stage) plus the wall time.
B=$1; T=$2; ROWS=$3; OUT=$4; J=${5:-3}
IR=${IRULES:-/home/user/bbb/bin/irules}
mkdir -p "$OUT/certs" "$OUT/res"
one() {
  m=$1
  [ -s "$OUT/res/$m" ] && return
  s=$(date +%s)
  r=$(echo "$m" | timeout "$3" "$IR" --why --max-steps "$2" --cert-dir "$OUT/certs" - 2>/dev/null | grep -v '^machine')
  [ -z "$r" ] && r="$m,timeout"
  echo "$r,wall=$(( $(date +%s) - s ))" > "$OUT/res/$m"
}
export -f one; export OUT IR
xargs -P "$J" -I{} bash -c "one {} $B $T" < "$ROWS"
