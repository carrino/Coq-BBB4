#!/usr/bin/env python3
"""LE12: write a batch boarding rows whose FuelWideTr certificate was split
by fuel_split.py (theories/Machines/FuelSplitTr/FS_<spec>.v proves
[check_<spec>]).

    python3 tools/closeouttr/le12/fuel_batch.py JSONL SPEC [SPEC ...] [--nn NN] [--conj CONJ.jsonl]

--conj: conj_find.py lines whose source is one of the SPECs; each target is
boarded in the SAME batch by [cconj_cover_run] from the source's [cv_]
lemma (a separate batch would make CI build the certificate parts twice).
"""
import json
import os
import sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from cbt import write_batch, next_free


def main():
    args = sys.argv[1:]
    nn = None
    if '--nn' in args:
        i = args.index('--nn')
        nn = int(args[i + 1])
        del args[i:i + 2]
    conjs = []
    if '--conj' in args:
        i = args.index('--conj')
        conjs = [json.loads(l) for l in open(args[i + 1]) if l.strip()]
        del args[i:i + 2]
    jsonl, specs = args[0], args[1:]
    if nn is None:
        nn = next_free('LE12')
    cert = {}
    for line in open(jsonl):
        e = json.loads(line)
        if e.get('status') == 'found' and e['spec'] in specs and e['spec'] not in cert:
            cert[e['spec']] = e
    req = ['From BBB4.Checkers Require Import FuelWideTr.',
           'From BBB4.CensusTr Require Import TNF_QHTr.',
           'From BBB4.Machines.FuelSplitTr Require %s.' % ' '.join('FS_' + s for s in specs)]
    ents = []
    for k, s in enumerate(specs):
        d = cert[s]
        pf = 'apply coversTr_nqh. unfold r_LE12_%02d_%04d. ' % (nn, k)
        if d['mirrored']:
            pf += 'apply neverqhtr_mirror. '
        pf += ('exact (ngram_check_neverqh_fuelwtr_sound _ %d %d %d %d _ FS_%s.check_%s).'
               % (d['n'], d['t'], d['fuel'], d['rounds'], s, s))
        ents.append((s, pf))
    pre = []
    ST = ['StA', 'StB', 'StC', 'StD']
    tac3 = ('[intros q; destruct q; reflexivity | intros q; destruct q; reflexivity'
            ' | intros q s; destruct q, s; reflexivity | vm_compute; reflexivity')
    for c in conjs:
        if c['src'] not in specs or 'm' not in c:
            continue
        assert c['n0'] <= c['m'], c
        k = len(ents)
        j = specs.index(c['src'])
        p = c['p']
        pinv = [p.index(q) for q in range(4)]
        pn = 'p_LE12_%02d_%04d' % (nn, k)
        for nm, pp in ((pn, p), (pn + 'i', pinv)):
            pre.append('Local Definition %s (q : St) : St :=\n  match q with %s end.\n'
                       % (nm, ' | '.join('%s => %s' % (ST[i], ST[pp[i]]) for i in range(4))))
        pf = ('apply (cconj_cover_run (row_to_tm r_LE12_%02d_%04d) _ %s %si %s %d %d); '
              '%s | reflexivity | reflexivity | exact cv_LE12_%02d_%04d].'
              % (nn, j, pn, pn, 'true' if c['flip'] else 'false', c['m'], c['n0'], tac3, nn, j))
        ents.append((c['spec'], pf))
    if len(ents) > len(specs):
        req += ['From BBB4 Require Import CTape.',
                'From BBB4.Counters Require Import CConjugateTr CConjCoverTr.']
    print(write_batch('LE12', nn, req, ents,
                      blurb='FuelWideTr n = 6 certificates split over FuelSplitTr part files, '
                            'and their conjugates (CConjCoverTr)',
                      preamble='\n'.join(pre)))


if __name__ == '__main__':
    main()
