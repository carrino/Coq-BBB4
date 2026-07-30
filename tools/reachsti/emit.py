#!/usr/bin/env python3
"""UNTRUSTED emitter for the ReachStI half of a board.

Produces the Coq text for

  * the machine table,
  * the [allowed] state list (the invariant),
  * the measure constants [B], [C] and the rank table [rk], and
  * [nonhalt_...] / [recur_...] via [ReachStI.reach_sti_recurs].

The constants come from [cert_search.py]; nothing here is trusted, because
[inv_ok] and [drop_ok] are re-evaluated by [vm_compute] inside the emitted
proof and a wrong table makes them [false].

Usage: emit.py <machine> [--goal Q]
"""
import argparse
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from cert_search import parse, LAB                                  # noqa: E402
import cert_search                                                  # noqa: E402

ST = ['StA', 'StB', 'StC', 'StD']
SYM = ['S0', 'S1']
DIR = {1: 'DR', -1: 'DL'}


def mach_id(spec):
    return spec.replace('-', '_')


def allowed_set(tab):
    """The largest state set that is total and closed under the table."""
    a = [q for q in range(4) if all(tab[(q, s)] is not None for s in (0, 1))]
    changed = True
    while changed:
        changed = False
        for q in list(a):
            if any(tab[(q, s)][2] not in a for s in (0, 1)):
                a.remove(q)
                changed = True
    return a


def coq_table(spec, tab):
    lines = []
    for q in range(4):
        cells = []
        for s in (0, 1):
            tr = tab[(q, s)]
            cells.append('| %s, %s => %s' % (
                ST[q], SYM[s], 'None' if tr is None else
                'Some (mkTrans %s %s %s)' % (SYM[tr[0]], DIR[tr[1]], ST[tr[2]])))
        lines.append('  ' + ' '.join(cells))
    return ('Definition tm_%s : TM := fun q s =>\n  match q, s with\n%s\n  end.'
            % (mach_id(spec), '\n'.join(lines)))


def coq_rk(spec, rk):
    """rk as a total function on (St * Sym * Sym * Sym); unlisted nodes are 0."""
    arms = []
    for (q, a, h, b), v in sorted(rk.items()):
        if v == 0:
            continue
        arms.append('  | (%s, %s, %s, %s) => %d'
                    % (ST[q], SYM[a], SYM[h], SYM[b], v))
    body = '\n'.join(arms + ['  | _ => 0'])
    return ('Definition rk_%s (nd : mnode) : nat :=\n  match nd with\n%s\n  end.'
            % (mach_id(spec), body))


def derive(spec, goal=None):
    tab = parse(spec)
    allowed = allowed_set(tab)
    goals = [LAB.index(goal)] if goal else allowed
    for qg in goals:
        r = cert_search.search(spec, qg, allowed)
        if r:
            return allowed, qg, r[0], r[1], r[2]
    return None


def emit(spec, goal=None, t=None):
    d = derive(spec, goal)
    if d is None:
        return None
    allowed, qg, B, C, rk = d
    mid = mach_id(spec)
    # the prefix length: the first index whose state is allowed
    tab = parse(spec)
    q, pos, tape, tlen = 0, 0, {}, None
    for i in range(64):
        if q in allowed:
            tlen = i
            break
        tr = tab[(q, tape.get(pos, 0))]
        if tr is None:
            return None
        tape[pos] = tr[0]
        pos += tr[1]
        q = tr[2]
    if tlen is None:
        return None
    out = []
    out.append(coq_table(spec, tab))
    out.append('')
    out.append('Definition allowed_%s : list St := [%s].'
               % (mid, '; '.join(ST[a] for a in allowed)))
    out.append('')
    out.append(coq_rk(spec, rk))
    out.append('')
    out.append("""Lemma live_%s :
  NonHalt tm_%s
  /\\ forall N, exists n, N <= n /\\ VisitsAt tm_%s %s n.
Proof.
  apply (reach_sti_recurs_b tm_%s allowed_%s %s %d %d rk_%s %d);
    vm_compute; reflexivity.
Qed.""" % (mid, mid, mid, ST[qg], mid, mid, ST[qg], B, C, mid, tlen))
    return dict(text='\n'.join(out), allowed=allowed, goal=qg, B=B, C=C,
                t=tlen, rk=rk)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('machine')
    ap.add_argument('--goal')
    a = ap.parse_args()
    r = emit(a.machine, a.goal)
    print(r['text'] if r else '-- no certificate')


if __name__ == '__main__':
    main()
