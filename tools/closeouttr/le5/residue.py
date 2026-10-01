#!/usr/bin/env python3
"""LE5: where each of LE4's 345 open rows stops (UNTRUSTED bookkeeping;
SCOPING_INSTR 7.4.LE5).  Reads LE4's residue and the LE5 readers' and batch
logs and writes residue.tsv:

    spec  LE4-reading  LE4-stop  LE5-readings  LE5-stop

`LE5-readings` lists the readers that read the row (run3 =
`termrun3_detect.py`, phrun = `phrun2.py`, alt = `alt_detect.py`), and
`LE5-stop` is `boarded LE5_NN` or the first failure of the batch that tried
it.  Prints the summary tables.

    python3 tools/closeouttr/le5/residue.py
"""
import collections
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..', '..'))


def jl(p):
    p = os.path.join(HERE, p)
    return {json.loads(l)['spec']: json.loads(l) for l in open(p) if l.strip()} \
        if os.path.exists(p) else {}


def why(line):
    w = line.split('no board:', 1)[1].strip()
    w = w.replace('(** ** The closure: NOT BUILT for this row -- ', '')
    w = w.replace('emit failed: emit_ladder.NoClosure: ', '')
    if 'refill: no program' in w:
        return 'refill: no program, or a refill that does not fire everything'
    if 'carry: no program' in w:
        return 'carry: no program, or no rank over the carries that do not fire'
    if 'no move of the kinds stated' in w:
        return 'a phase move of another kind (the run shrinks, or a refill law off)'
    if w.startswith('phase ') and 'narrows but no' in w:
        return 'a narrowing phase with no empty-x move'
    if 'nar_at' in w:
        return 'narrowing: no program'
    if 'inter_at' in w:
        return 'interior: no program'
    if 'not D0^(m+a)' in w:
        return 'refill law not D0^(m+a) E0'
    return w[:70]


def batch_log(p):
    out = {}
    p = os.path.join(HERE, p)
    if not os.path.exists(p):
        return out
    for l in open(p):
        f = l.split()
        if len(f) > 2 and f[1] == 'no':
            out[f[0]] = why(l)
    return out


def main():
    le4 = {}
    for l in open(os.path.join(HERE, '..', 'le4', 'residue.tsv')):
        if l.startswith('#'):
            continue
        s, _b, g, st = l.rstrip('\n').split('\t')
        if not st.startswith('boarded'):
            le4[s] = (g, st)
    boarded = {}
    for l in open(os.path.join(REPO, 'closeouttr_boarded.tsv')):
        f = l.rstrip('\n').split('\t')
        if len(f) >= 2 and f[1].startswith('CBT_LE5_'):
            boarded[f[0]] = f[1][4:]
    remaining = set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))
    tr3, ph = jl('tr3_108.jsonl'), jl('phrun_res.jsonl')
    alt = jl('alt_res.jsonl')
    alt.update({k: v for k, v in jl('alt_res2.jsonl').items() if v.get('keys')})
    logs = [batch_log('run3_batch.log'), batch_log('phrun_batch3.log'),
            batch_log('alt_batch.log'), batch_log('alt_batch2.log')]
    out = []
    for s in sorted(le4):
        g, st = le4[s]
        rd = [n for n, d, k in (('run3', tr3, 'anchor'), ('phrun', ph, 'anchor'),
                                ('alt', alt, 'keys')) if d.get(s, {}).get(k)]
        if s in boarded:
            st5 = 'boarded ' + boarded[s]
        elif s not in remaining:
            st5 = 'boarded elsewhere'
        else:
            st5 = next((lg[s] for lg in logs if s in lg), 'no reading' if not rd else '?')
        out.append((s, g, st, ','.join(rd) or '-', st5))
    with open(os.path.join(HERE, 'residue.tsv'), 'w') as f:
        f.write('# spec\tLE4 reading\tLE4 stop\tLE5 readings\tLE5 stop\n')
        for r in out:
            f.write('\t'.join(r) + '\n')
    C = collections.Counter((r[4] if not r[4].startswith('boarded LE5') else 'boarded')
                            for r in out)
    for k, v in C.most_common():
        print('%4d  %s' % (v, k))
    print('%4d  rows' % len(out))
    print()
    C2 = collections.Counter((r[2][:40], 'boarded' if r[4].startswith('boarded') else 'open')
                             for r in out)
    for k, v in sorted(C2.items()):
        print('%4d  %-42s %s' % (v, k[0], k[1]))


if __name__ == '__main__':
    main()
