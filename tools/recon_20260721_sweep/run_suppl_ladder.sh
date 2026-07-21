#!/bin/bash
# Sequential never-QH ladder on the 400-rep representative listC sample.
set -e
cd /home/user/BBB
SW=/home/user/Coq-BBB4/tools/recon_20260721_sweep
S=$SW/suppl_listC_400.txt
CD=results/certs_residue_sample/suppl
log=$SW/suppl_ladder.log
: > "$log"
run(){ name=$1; shift; echo "=== $name ===" >>"$log"; nice -n 15 "$@" 2>/dev/null \
       | awk -F, 'NR>1{print $2}' | sort | uniq -c >>"$log"; echo "certs $(ls $CD/$name 2>/dev/null|wc -l)" >>"$log"; }
run ngram_rank  ./bin/quietngram --neverqh --rank            --max-n 8 --t 5000000 --cert-dir $CD/ngram_rank  $S
run ngram_fuel  ./bin/quietngram --neverqh --rank --fuel     --max-n 8 --t 5000000 --cert-dir $CD/ngram_fuel  $S
run ngram_drift ./bin/quietngram --neverqh --rank --drift    --max-n 8 --t 5000000 --cert-dir $CD/ngram_drift $S
run rwlrank     ./bin/quietrwl --rank                        --cert-dir $CD/rwlrank  $S
run bouncer     ./bin/bouncer  --max-steps 2000000           --cert-dir $CD/bouncer  $S
run quietfar    ./bin/quietfar                               --cert-dir $CD/quietfar $S
run quietctl    ./bin/quietctl                               --cert-dir $CD/quietctl $S
echo "LADDER_DONE" >>"$log"
