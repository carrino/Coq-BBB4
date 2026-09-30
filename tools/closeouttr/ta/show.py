#!/usr/bin/env python3
"""Print a dumped TriGlue family graph as a piecewise-affine map (UNTRUSTED).

    python3 tools/closeouttr/ta/show.py DUMP.jsonl SPEC
"""
import json
import sys

ST = 'ABCD'


def aexp(e, names):
    c, t = e
    parts = ['%s%s' % ('' if a == 1 else str(a), names[k]) for k, a in t]
    if c or not parts:
        parts.append(str(c))
    return '+'.join(parts)


def segs(l, names):
    out = []
    for s in l:
        if s[0] == 'L':
            out.append(''.join(map(str, s[1])))
        else:
            out.append('(%s)^%s' % (''.join(map(str, s[1])), aexp(s[2], names)))
    return ' '.join(out)


def show(d, out=sys.stdout):
    c = d['cert']
    fired = d['fired']
    V = 'abcdefghijk'
    Z = 'zyxwvutsrqp'
    allf = set()
    for f in fired:
        allf |= set(map(tuple, f))
    pins = set(map(tuple, c['pins']))
    rare = [t for t in [(q, h) for q in range(4) for h in range(2)]
            if t not in pins and sum(1 for f in fired if t in map(tuple, f)) <= len(fired) // 2]
    print('%s  mir=%s  %d fams %d leaves  boot f%d %s' % (
        d['spec'], c['mir'], len(c['fams']), len(c['leaves']), c['f0'], c['v0']), file=out)
    for fi, F in enumerate(c['fams']):
        names = V[:F['n']]
        L = segs(list(reversed(F['L'])), names)
        R = segs(F['R'], names)
        print('F%d: %s [%s%d] %s' % (fi, L, ST[F['q']], F['h'], R), file=out)
    for li, lf in enumerate(c['leaves']):
        names = Z[:len(lf['reg'])]
        reg = ','.join('%s=%s' % (V[k], aexp((cc, [(k, M)] if M else []), names).replace(V[k], names[k]) if False else
                                  (('%d%s+%d' % (M, names[k], cc)) if M else str(cc)))
                       for k, (M, cc) in enumerate(lf['reg']))
        tgt = ','.join(aexp(e, names) for e in lf['tgt'])
        fs = ' '.join('%s%d' % (ST[q], h) for q, h in map(tuple, fired[li]) if (q, h) not in pins)
        print('  L%-3d F%d(%s) -> F%d(%s)   fires %s' % (li, lf['f'], reg, lf['g'], tgt, fs),
              file=out)


if __name__ == '__main__':
    for l in open(sys.argv[1]):
        d = json.loads(l)
        if d['spec'] == sys.argv[2] and 'cert' in d:
            show(d)
            break
