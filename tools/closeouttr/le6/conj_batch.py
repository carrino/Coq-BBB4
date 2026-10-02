#!/usr/bin/env python3
"""LE6: board state-permuted / mirrored conjugates of boarded rows
(CConjCoverTr).  Input: conj_find.py's jsonl.

  n0 <= m : cconj_cover_run, from the source row's own [cv_] lemma
            (any proof: never-QH or a bounded quasihalt);
  n0 >  m : cconj_nqh_run, from the source machine module's [nqhtr_]
            lemma (only when the source batch proves it that way), with a
            boot check K found here.

    python3 tools/closeouttr/le6/conj_batch.py CONJ.jsonl --tag LE6 [--per 20] [--skip SPEC,...]
"""
import json, os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cbt import write_batch, next_free
from conj_check import parse
from conj_find import sim

ST = ['StA', 'StB', 'StC', 'StD']
CT = 'theories/CloseoutTr'


def src_info(batch, spec):
    txt = open(os.path.join(CT, batch + '.v')).read()
    m = re.search(r'\(\* spec %s \*\)\nDefinition (r_\w+)' % re.escape(spec), txt)
    assert m, (batch, spec)
    name = m.group(1)[2:]
    pm = re.search(r'Lemma cv_%s :.*?\nProof\.(.*?)Qed\.' % re.escape(name), txt, re.S)
    nq = None
    if pm:
        q = re.search(r'coversTr_nqh_at (\w+)\.(tm_\w+)\); \[exact \1\.(nqhtr_\w+)', pm.group(1))
        if q:
            mod = q.group(1)
            im = re.search(r'From (BBB4[\w.]*) Require (?:Import )?[^.]*\b%s\b' % mod, txt)
            nq = (im.group(1) if im else None, mod, q.group(2), q.group(3))
    return name, nq


def boot_k(spec, n0, limit=100000):
    """smallest K with every instruction of configs 0..n0-1 refiring in [n0, n0+K)"""
    boot = set(); need = None; seen_after = {}
    for i, q, pos, tape in sim(spec, limit):
        ins = (q, tape[pos])
        if i < n0:
            boot.add(ins)
        else:
            seen_after.setdefault(ins, i)
            if boot <= set(seen_after):
                return max(seen_after[x] for x in boot) - n0 + 1 if boot else 0
    return None


def pfun(name, p):
    return ('Local Definition %s (q : St) : St :=\n  match q with %s end.\n'
            % (name, ' | '.join('%s => %s' % (ST[i], ST[p[i]]) for i in range(4))))


def main():
    a = sys.argv[1:]
    rows = [json.loads(l) for l in open(a[0])]
    tag = a[a.index('--tag') + 1]
    per = int(a[a.index('--per') + 1]) if '--per' in a else 20
    skip = set(a[a.index('--skip') + 1].split(',')) if '--skip' in a else set()
    done = set(open('closeouttr_remaining.txt').read().split())
    todo = []
    for d in rows:
        if 'm' not in d or d['spec'] in skip or d['spec'] not in done:
            continue
        name, nq = src_info(d['batch'], d['src'])
        if d['n0'] <= d['m']:
            todo.append((d, 'cover', name, None))
        elif nq and nq[0]:
            k = boot_k(d['spec'], d['n0'])
            if k is not None:
                todo.append((d, 'nqh', nq, k))
            else:
                print('no boot K', d['spec'])
        else:
            print('late boot, source not nqh_at', d['spec'], d['batch'])
    for i in range(0, len(todo), per):
        chunk = todo[i:i + per]
        nn = next_free(tag)
        reqs = ['From BBB4 Require Import CTape.',
                'From BBB4.Counters Require Import CConjugateTr CConjCoverTr.']
        pre = []
        ents = []
        for j, (d, kind, info, k) in enumerate(chunk):
            p = d['p']; pinv = [p.index(q) for q in range(4)]
            pn = 'p_%s_%02d_%04d' % (tag, nn, j)
            pre.append(pfun(pn, p)); pre.append(pfun(pn + 'i', pinv))
            fl = 'true' if d['flip'] else 'false'
            tac3 = ('[intros q; destruct q; reflexivity | intros q; destruct q; reflexivity'
                    ' | intros q s; destruct q, s; reflexivity | vm_compute; reflexivity')
            if kind == 'cover':
                imp = 'From BBB4.CloseoutTr Require %s.' % d['batch']
                if imp not in reqs:
                    reqs.append(imp)
                pf = ('apply (cconj_cover_run (row_to_tm %s.r_%s) _ %s %si %s %d %d); '
                      '%s | reflexivity | reflexivity | exact %s.cv_%s].'
                      % (d['batch'], info, pn, pn, fl, d['m'], d['n0'], tac3, d['batch'], info))
            else:
                lib, mod, tmn, nqn = info
                imp = 'From %s Require %s.' % (lib, mod)
                if imp not in reqs:
                    reqs.append(imp)
                pf = ('apply coversTr_nqh, (cconj_nqh_run %s.%s _ %s %si %s %d %d %d); '
                      '%s | vm_compute; reflexivity | exact %s.%s].'
                      % (mod, tmn, pn, pn, fl, d['m'], d['n0'], k, tac3, mod, nqn))
            ents.append((d['spec'], pf))
        path = write_batch(tag, nn, reqs, ents,
                           'state-permuted / mirrored conjugates of boarded rows (CConjCoverTr)',
                           preamble='\n'.join(pre))
        print(path, len(ents))


if __name__ == '__main__':
    main()
