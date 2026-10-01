#!/usr/bin/env python3
"""LE4: where each of the 372 rows stops (UNTRUSTED bookkeeping; SCOPING_INSTR
7.4.LE4).  Reads the outputs of the LE4 tools and writes residue.tsv:

    spec  LE2-bucket  group  stop

with `group` the furthest reading a finder made (zeck2, run2 = marker
terminator run, pos = positional counter, none) and `stop` where it stops
(`boarded LE4_NN`, or the reason).  Prints the summary table.

    python3 tools/closeouttr/le4/residue.py
"""
import collections
import glob
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..', '..'))


def jl(p):
    return [json.loads(l) for l in open(p) if l.strip()]


def main():
    rows = [l.strip() for l in open(os.path.join(HERE, 'rows.txt')) if l.strip()]
    bucket = {}
    for p in glob.glob(os.path.join(HERE, '..', 'le2', 'rows_*.txt')):
        b = os.path.basename(p)[5:-4]
        for l in open(p):
            bucket.setdefault(l.strip(), b)
    boarded = {}
    for l in open(os.path.join(REPO, 'closeouttr_boarded.tsv')):
        f = l.rstrip('\n').split('\t')
        if len(f) >= 2 and f[1].startswith('CBT_LE4_'):
            boarded[f[0]] = f[1][4:]
    z2 = {c['spec']: c for c in jl(os.path.join(HERE, 'zeck2.jsonl'))}
    run2 = {c['spec']: c for c in jl(os.path.join(HERE, 'termrun2.jsonl'))}
    run2why = {}
    for l in open(os.path.join(HERE, 'run2_batch.log')):
        f = l.split()
        if len(f) > 2 and f[1] == 'no':
            w = l.split('no board:', 1)[1]
            run2why[f[0]] = ('refill (cost doubles with the run: a third counting level)'
                             if 'refill: no program' in w else
                             'refill law not D0^(m+a)' if 'not D0^(m+a)' in w else
                             'interior arm' if 'inter_at' in w else w.strip()[:60])
    pos = {c['spec']: c for c in jl(os.path.join(HERE, 'pos.jsonl'))}
    sweep = {c['spec']: c['verdict'] for c in jl(os.path.join(HERE, 'sweep_probe.jsonl'))}
    poswhy = {}
    for p in ('pos_emit_pass1.tsv', 'pos_emit_pass2.tsv'):
        for l in open(os.path.join(HERE, p)):
            s, st, why = l.rstrip('\n').split('\t')
            if st != 'BUILT':
                poswhy[s] = ('fill (cost doubles with the width: the fill counts)'
                             if why.startswith('fill arm') else
                             'interior arm' if why.startswith('interior') else
                             'fill target of 3 digits' if '3 digits' in why else why[:60])
    out = []
    for s in rows:
        b = bucket.get(s, '?')
        if s in z2 and z2[s].get('closed'):
            g = 'zeck2'
        elif s in run2 and run2[s].get('anchor'):
            g = 'run2'
        elif s in pos and pos[s].get('closed'):
            g = 'pos'
        elif s == '0RB1LC_1LC0LC_0RD1LA_1RD1RB':
            g = 'zeck2-down'
        else:
            g = 'none'
        if s in boarded:
            st = 'boarded ' + boarded[s]
        elif g == 'zeck2-down':
            st = 'counts DOWN in the two-cell code'
        elif g == 'run2':
            st = run2why.get(s, '?')
            if st == 'interior arm':
                st = ('interior arm: sweeps the run of top digits'
                      if sweep.get(s) == 'sweep' or s in SWEEP_RUN else
                      'interior arm: carry cost doubles (nested)')
        elif g == 'pos':
            st = poswhy.get(s, '?')
            if st == 'interior arm':
                st = ('interior arm: sweeps the run of top digits'
                      if sweep.get(s) == 'sweep' else 'interior arm: other')
        else:
            st = 'no reading'
        out.append((s, b, g, st))
    with open(os.path.join(HERE, 'residue.tsv'), 'w') as f:
        f.write('# spec\tLE2 bucket\tLE4 reading\twhere it stops\n')
        for r in out:
            f.write('\t'.join(r) + '\n')
    C = collections.Counter((g, st if not st.startswith('boarded') else 'boarded')
                            for _s, _b, g, st in out)
    for k, v in sorted(C.items(), key=lambda kv: (kv[0][0], -kv[1])):
        print('%4d  %-10s %s' % (v, k[0], k[1]))
    print('%4d  rows' % len(out))


# the termrun2 rows whose interior arm has a chain against `x-digit^k` and
# `M T^m suf` tails at a constant cost but none against an opaque tail, and
# whose `d 1` lookahead fails: the carry walks the following run of ones
# (`/tmp` diagnosis, SCOPING_INSTR 7.4.LE4)
SWEEP_RUN = set('''0RB0LA_0RC1RB_0LD1RC_1LA1LD 0RB0LA_0RC1RD_1LA1LC_0LC1RB
0RB0LA_1RC1RB_0LD0RC_1LD1LA 0RB1LA_1RC1RB_0LD0RC_0LA1LD 0RB1LD_1RC1RB_0LD0RC_0LB1LA
0RB1RA_0LC1RB_1LD1LC_0RA0LD 0RB1RC_1LA1RB_0LD0RC_1LD0LA 0RB1RD_1LC1LB_0RA0LC_0LB1RA
1RB1RA_0LC0RB_0LA1LD_0RA1LC 1RB1RA_0LC0RB_0LD1LC_0RA1LD 1RB1RA_0LC0RB_1LC1LD_0RA0LD'''.split())

if __name__ == '__main__':
    main()
