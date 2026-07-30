#!/usr/bin/env python3
"""UNTRUSTED probe: is the two-form INTERIOR lap a NESTED lap?

`intfit.py` measures the interior lap of all 40 `no interior j=S j chain` rows
as NON-affine in [j] at both octave parities -- so no chain of any depth
expresses it and the bucket is not a framing problem.  The next question is
what it IS, and there is one shape already built in this development that has
exactly this signature: the NESTED lap, where a second counter runs inside one
lap of the first and contributes a `Theta(2^j)` middle no formula names
(`Counters/NestedLapLift.v`, and `tailcert`'s own overflow arm).

So: take one INTERIOR lap -- anchor [p] to anchor [p + 1], with
`cview p = (j, Some q0)` -- collect its blank-head rests, and ask
`nestcert.families` whether they carry an inner counter, exactly as
`tailcert._nested_ovf` asks it of the OVERFLOW phase.  The runs are reported
with `innerrun.runs`, which does not require a full octave, so a partial inner
run is visible too.

If an inner family is there, the interior branch wants the nested treatment the
overflow branch already has.  If it is not, the reader is wrong for these rows
and the bucket is a reader problem, not a route problem.

Usage
  intnest.py --list FILE [--json OUT] [--top N]
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import innerrun as IR                                              # noqa: E402
import lapcert as LC                                               # noqa: E402
import nestcert as NC                                              # noqa: E402
import tailcert as TC                                              # noqa: E402
from emit_lapcert import ENCDATA, ENC                              # noqa: E402
from emit_interleave import parse, carry                           # noqa: E402
from mirror_common import mirror_spec                              # noqa: E402
from regcert import RegError, octave, _phase                       # noqa: E402


def probe(spec, maxk=7):
    """The DEEPEST interior lap available at each octave parity, and whatever
    inner counter its rests carry."""
    last = None
    for mir in (False, True):
        dspec = mirror_spec(spec) if mir else spec
        tab = parse(dspec)
        try:
            enc, frames, ks = TC.two_form(dspec)
        except RegError as e:
            last = str(e)
            continue
        st = {b: frames[b][0] for b in (0, 1)}
        tl = {b: tuple(frames[b][1]) for b in (0, 1)}
        fr = {b: tuple(frames[b][2]) for b in (0, 1)}
        encf = ENC[enc]

        def anchor(p):
            b = octave(p) % 2
            return (st[b], tuple(encf(p)) + tl[b], 0, fr[b])

        out = dict(spec=spec, dspec=dspec, mirror=mir, enc=enc, ks=ks,
                   parity={})
        for b in (0, 1):
            # the largest j the frozen octave range offers at this parity: the
            # deepest interior lap is the one with the most inner laps in it.
            best = None
            for k in ks:
                if k % 2 != b or k > maxk:
                    continue
                # p = 2^k + (2^(j) - 1) with j as large as the octave allows,
                # i.e. p = 2^k + 2^(k-1) - 1 has carry index k - 1.
                p = (1 << k) + (1 << (k - 1)) - 1
                if carry(p)[1] or octave(p + 1) > ks[-1]:
                    continue
                best = p
            if best is None:
                out['parity'][b] = dict(verdict='no interior anchor')
                continue
            j = carry(best)[0]
            src, nxt = anchor(best), anchor(best + 1)
            try:
                mid = _phase(tab, src, (nxt[0], tuple(nxt[1]),
                                        LC.rstrip0(nxt[3])))
            except RegError as e:
                out['parity'][b] = dict(verdict=str(e), p=best, j=j)
                continue
            K = max(1, j)
            out['parity'][b] = dict(
                verdict='ok', p=best, j=j, nmid=len(mid), K=K,
                full=[[k[0], k[1], list(k[2]), list(k[3]), k[4]]
                      for k in NC.families(mid, ENCDATA, TC.TRY, K=K)],
                hits=IR.runs(mid)[:8])
        return out
    return dict(spec=spec, verdict=last or 'no family')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list')
    ap.add_argument('--spec')
    ap.add_argument('--json')
    ap.add_argument('--top', type=int, default=3)
    a = ap.parse_args()
    specs = ([a.spec] if a.spec else
             [x.split()[0] for x in open(a.list) if x.strip()
              and not x.startswith('#')])
    out, tally = [], {}
    for i, s in enumerate(specs):
        try:
            o = probe(s)
        except Exception as e:                                      # noqa: BLE001
            o = dict(spec=s, verdict='probe failed: %s' % e)
        out.append(o)
        if 'parity' not in o:
            print('%4d/%d %-30s %s' % (i + 1, len(specs), s, o['verdict']))
            tally[o['verdict']] = tally.get(o['verdict'], 0) + 1
            continue
        for b in (0, 1):
            P = o['parity'][b]
            if P['verdict'] != 'ok':
                print('%4d/%d %-30s b%d %s'
                      % (i + 1, len(specs), s, b, P['verdict']))
                tally['b%d %s' % (b, P['verdict'])] = \
                    tally.get('b%d %s' % (b, P['verdict']), 0) + 1
                continue
            v = ('FULL inner family' if P['full'] else
                 ('a run, not a full octave' if P['hits']
                  and P['hits'][0]['run'] > 2 else 'no inner counter'))
            tally['b%d %s' % (b, v)] = tally.get('b%d %s' % (b, v), 0) + 1
            print('%4d/%d %-30s b%d j=%d %4d rests  %-24s %s'
                  % (i + 1, len(specs), s, b, P['j'], P['nmid'], v,
                     ' | '.join('%s q%s run %d %d..%d'
                                % (h['key'][0], h['key'][1], h['run'],
                                   h['lo'], h['hi'])
                                for h in P['hits'][:a.top])))
    print('\n--- tally ---')
    for k in sorted(tally, key=lambda x: -tally[x]):
        print('%5d  %s' % (tally[k], k))
    if a.json:
        with open(a.json, 'w') as f:
            json.dump(out, f, indent=1, sort_keys=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
