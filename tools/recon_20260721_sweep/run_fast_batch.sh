#!/bin/bash
cd /home/user/BBB
SW=/home/user/Coq-BBB4/tools/recon_20260721_sweep
S=$SW/suppl_listC_400.txt
CD=results/certs_residue_sample/suppl
log=$SW/fast_batch.log; : > "$log"
run(){ n=$1; shift; echo "=== $n ===" >>"$log"; nice -n 15 "$@" 2>/dev/null | awk -F, 'NR>1{print $2}'|sort|uniq -c >>"$log"; echo "certs $(ls $CD/$n 2>/dev/null|wc -l)">>"$log"; }
run rwlrank  ./bin/quietrwl --rank              --cert-dir $CD/rwlrank  $S
run bouncer  ./bin/bouncer --max-steps 2000000  --cert-dir $CD/bouncer  $S
run quietfar ./bin/quietfar                     --cert-dir $CD/quietfar $S
run quietctl ./bin/quietctl                     --cert-dir $CD/quietctl $S
echo FAST_DONE >> "$log"
