#!/usr/bin/env python3
"""UNTRUSTED emitter for the REACHST tier: NGramHist for three states, a
[ReachSt] theorem for the fourth.

The residue's counters have exactly ONE state the finite abstraction cannot
discharge (docs/WHY_NO_HAMMER.md).  The avoid sub-machine of that ONE state
is, across the open core, one of FOUR tables, whose termination
[theories/Checkers/ReachSt.v] proves once for all machines that share it:

  flavour B   A0 -> 1RB  A1 -> 0LD  B1 -> 1RA  D0 -> 0RB  D1 -> 1LD   B0 -> ..C
  flavour A   A0 -> 1RB  A1 -> 0LD  B1 -> 1RA  D0 -> 0RA  D1 -> 1LD   B0 -> ..C
  flavour C   A1 -> 0LD  B0 -> 1LD  B1 -> 1RB  D0 -> 0RB  D1 -> 1LA   A0 -> ..C
  flavour D   A1 -> 1LD  B0 -> 1LA  B1 -> 1RB  D0 -> 0RB  D1 -> 0LA   A0 -> ..C

A and B are binary counters running DOWN; C and D are counters in a PAIR
encoding -- C's block GROWS and its counter increments, D's decrements by
borrows.  C and D are the same five arrows with the two blank branches
swapped (docs/REACHST_TIER.md section 8, and the [MC]/[MD] sections of
[ReachSt.v]).  Note the gate into the sparse state is [B0] for A/B and [A0]
for C/D.

So this tool: checks the machine matches one flavour, runs the NGramHist
closure, synthesises liveness certificates for the OTHER three states, and
emits a board that closes with
[NGramHistExt.ngramhist_check_neverqh_lex_ext_sound].

Everything here is untrusted; the kernel re-runs the checker on every line
it emits, and the [ReachSt] side is an ordinary Coq theorem.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import nghist_prove as NP                                          # noqa: E402

# (write, dir, next) triples each flavour requires, keyed by (role, read)
FLAVOURS = {
    'mb': {('A', 0): (1, 'R', 'B'), ('A', 1): (0, 'L', 'D'),
           ('B', 1): (1, 'R', 'A'), ('D', 0): (0, 'R', 'B'),
           ('D', 1): (1, 'L', 'D')},
    'ma': {('A', 0): (1, 'R', 'B'), ('A', 1): (0, 'L', 'D'),
           ('B', 1): (1, 'R', 'A'), ('D', 0): (0, 'R', 'A'),
           ('D', 1): (1, 'L', 'D')},
    'mc': {('A', 1): (0, 'L', 'D'),
           ('B', 0): (1, 'L', 'D'), ('B', 1): (1, 'R', 'B'),
           ('D', 0): (0, 'R', 'B'), ('D', 1): (1, 'L', 'A')},
    'md': {('A', 1): (1, 'L', 'D'),
           ('B', 0): (1, 'L', 'A'), ('B', 1): (1, 'R', 'B'),
           ('D', 0): (0, 'R', 'B'), ('D', 1): (0, 'L', 'A')},
}

# the transition whose target IS the sparse state (its write/dir are free)
GATE = {'mb': ('B', 0), 'ma': ('B', 0), 'mc': ('A', 0), 'md': ('A', 0)}

# where the free (write, dir) pair sits in the lemma's argument list: the
# ma/mb sections bind [wB dB] AFTER the five fixed hypotheses, mc/md bind
# [wA dA] BEFORE their six
GATE_LAST = {'mb': True, 'ma': True, 'mc': False, 'md': False}

FLAV_BLURB = {
    'mb': 'a binary counter running DOWN',
    'ma': 'a binary counter running DOWN',
    'mc': 'a PAIR-encoded counter whose block GROWS',
    'md': 'a PAIR-encoded counter running DOWN by borrows',
}


def sparse_state(mstr, T=200000):
    """The state that fires logarithmically often -- the liveness question."""
    from collections import defaultdict
    tm = decode_tab(mstr)
    tape = defaultdict(int)
    p, q = 0, 0
    cnt = defaultdict(int)
    for _ in range(T):
        cnt[q] += 1
        tr = tm[(q, tape[p])]
        if tr is None:
            break
        tape[p] = tr[0]
        p += tr[1]
        q = tr[2]
    return 'ABCD'[min(range(4), key=lambda i: cnt[i])]


def decode_tab(mstr):
    out = {}
    tm = NP.decode(mstr)
    for qi, q in enumerate('ABCD'):
        for b in (0, 1):
            tr = tm[q][b]
            out[(qi, b)] = (None if tr is None
                            else (tr[0], 1 if tr[1] == 'R' else -1, 'ABCD'.index(tr[2])))
    return out


def flavour_of(tm, sparse):
    """(flavour, (a, b, c, d)) -- the state names playing the four ReachSt
    roles, or None.  The roles need not be A/B/C/D: the sub-machine is what
    matters, so any relabelling of it is the same theorem."""
    import itertools
    for a, b, d in itertools.permutations('ABCD', 3):
        role = {'A': a, 'B': b, 'D': d}
        for name, want in FLAVOURS.items():
            gq, gs = GATE[name]
            gate = tm[role[gq]][gs]
            if gate is None:
                continue
            c = gate[2]
            if c in (a, b, d) or c != sparse:
                continue
            if all(tm[role[rq]][rb] is not None
                   and tm[role[rq]][rb][:2] == tr[:2]
                   and tm[role[rq]][rb][2] == role[tr[2]]
                   for (rq, rb), tr in want.items()):
                return name, (a, b, c, d)
    return None


def total(tm):
    return all(tm[q][b] is not None for q in 'ABCD' for b in (0, 1))


def prove_ext(mstr, k, n, t, fuel, qext='C'):
    """Like nghist_prove.prove, but [qext] carries no abstraction cert."""
    tm = NP.decode(mstr)
    g = NP.grow(tm, k, n, t, fuel)
    if g is None:
        return None, 'closure did not close'
    a0, lset, rset, seen, edges = g
    obliged = set(a[0] for a in seen) | NP.visited_states_prefix(tm, k, t)
    cert = {}
    for q in 'ABCD':
        if q == qext or q not in obliged:
            cert[q] = []
            continue
        c = NP.cert_for_state(tm, seen, edges, q, n=n)
        if c is None:
            return None, 'no liveness cert for state ' + q
        cert[q] = c
    return dict(tm=tm, k=k, n=n, t=t, fuel=fuel, lset=lset, rset=rset,
                seen=seen, edges=edges, cert=cert, nctx=len(seen)), None


HEADER = '''(* UNTRUSTED-generated by tools/nghist/reachst_prove.py; the Coq kernel
   re-checks the abstraction claim via vm_compute and the liveness of {qext}
   as an ordinary theorem.

   {mstr} -- boarded by the REACHST tier: [NGramHist] at k={k} n={n} t={t}
   fuel={fuel} ({nctx} contexts) discharges the liveness of every state but
   {qext}, and [ReachSt.{flav}_ReachSt] discharges {qext} by showing the
   {qext}-avoiding sub-machine -- {blurb} -- terminates
   from EVERY configuration. *)
From Coq Require Import List ZArith FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From BBB4.Checkers Require Import NGram NGramHist NGramHistExt ReachSt.
Import ListNotations.
'''


PICK = ['left; reflexivity',
        'right; left; reflexivity',
        'right; right; left; reflexivity',
        'right; right; right; reflexivity']


def mirror_spec(mstr):
    """The mirrored table (every direction flipped), as a spec string."""
    out = []
    for part in mstr.split('_'):
        f = ''
        for b in (0, 1):
            c = part[3 * b:3 * b + 3]
            f += c if c == '---' else c[0] + ('L' if c[1] == 'R' else 'R') + c[2]
        out.append(f)
    return '_'.join(out)


def emit(mstr, res, flav, roles, mir=None):
    """[mir] is the mirrored spec when it is the MIRROR that carries the
    flavour: [ReachSt] then runs on the mirrored table and
    [Mirror.mirror_visits] carries the recurrence back."""
    nm = mstr
    tm = res['tm']
    thm = 'nqh_' + nm
    a, b, c, d = roles
    qA, qB, qC, qD = ('St' + x for x in roles)
    tmr = NP.decode(mir) if mir else tm
    gq, gs = GATE[flav]
    gate = tmr[{'A': a, 'B': b, 'D': d}[gq]][gs]
    w = NP.c_sym(gate[0])
    dd = 'DR' if gate[1] == 'R' else 'DL'
    nfix = len(FLAVOURS[flav])
    args = (['eq_refl'] * nfix + [w, dd, 'eq_refl'] if GATE_LAST[flav]
            else [w, dd] + ['eq_refl'] * (nfix + 1))
    picks = ' | '.join(PICK[list(roles).index(x)] for x in 'ABCD')
    rt = ('tmm_' + nm) if mir else ('tm_' + nm)
    body = [NP.c_tm(tm, 'tm_' + nm)]
    if mir:
        body.append(
            '(* The MIRROR of the machine.  [ReachSt] runs on it and\n'
            '   [Mirror.mirror_visits] carries the recurrence back. *)\n'
            + NP.c_tm(tmr, 'tmm_' + nm))
        body.append(
            'Lemma mirror_ok_{nm} : mirror_tm tm_{nm} = tmm_{nm}.\n'
            'Proof.\n'
            '  apply functional_extensionality; intro q;\n'
            '    apply functional_extensionality; intro b;\n'
            '    destruct q, b; reflexivity.\n'
            'Qed.'.format(nm=nm))
    body.append(
        'Lemma total_{nm} : Total {rt}.\n'
        'Proof. intros q s; destruct q, s; discriminate. Qed.'.format(nm=nm, rt=rt))
    body.append(
        'Lemma cover_{nm} : forall q, q = {qA} \\/ q = {qB} \\/ q = {qC} \\/ q = {qD}.\n'
        'Proof. destruct q; [ {picks} ]. Qed.'.format(
            nm=nm, qA=qA, qB=qB, qC=qC, qD=qD, picks=picks))
    body.append(
        'Lemma reach_{nm} : ReachSt {rt} {qC}.\n'
        'Proof.\n'
        '  exact ({flav}_ReachSt {rt} {qA} {qB} {qC} {qD} cover_{nm}\n'
        '           {args}).\n'
        'Qed.'.format(nm=nm, flav=flav, rt=rt, qA=qA, qB=qB, qC=qC, qD=qD,
                      args=' '.join(args)))
    if mir:
        body.append(
            'Lemma recurC_{nm} : forall N, exists m, N <= m /\\ VisitsAt tm_{nm} {qC} m.\n'
            'Proof.\n'
            '  intro N.\n'
            '  destruct (reach_st_recurs tmm_{nm} {qC} total_{nm} reach_{nm} N)\n'
            '    as (m & Hm & Hv).\n'
            '  exists m. split; [exact Hm |].\n'
            '  apply (proj1 (mirror_visits tm_{nm} {qC} m)).\n'
            '  rewrite mirror_ok_{nm}. exact Hv.\n'
            'Qed.'.format(nm=nm, qC=qC))
    else:
        body.append(
            'Lemma recurC_{nm} : forall N, exists m, N <= m /\\ VisitsAt tm_{nm} {qC} m.\n'
            'Proof. exact (reach_st_recurs tm_{nm} {qC} total_{nm} reach_{nm}). Qed.'
            .format(nm=nm, qC=qC))
    body.append('Definition lset_' + nm + ' : hgset :=\n  ' + NP.c_gset(res['lset']) + '.')
    body.append('Definition rset_' + nm + ' : hgset :=\n  ' + NP.c_gset(res['rset']) + '.')
    body.append(NP.c_cert(res['cert'], 'cert_' + nm))
    body.append(
        'Theorem {thm} : NeverQuasiHaltsSt tm_{nm}.\n'
        'Proof.\n'
        '  apply (ngramhist_check_neverqh_lex_ext_sound tm_{nm} {k} {n} {t} {fuel}\n'
        '           lset_{nm} rset_{nm} cert_{nm} {qC} recurC_{nm}).\n'
        '  vm_compute. reflexivity.\nQed.'.format(
            thm=thm, nm=nm, qC=qC, k=res['k'], n=res['n'], t=res['t'],
            fuel=res['fuel']))
    return '\n\n'.join(body), thm


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--list', required=True)
    ap.add_argument('--outdir', default='theories/Machines/ReachSt')
    ap.add_argument('-k', type=int, default=2)
    ap.add_argument('-n', type=int, default=2)
    ap.add_argument('-t', type=int, default=200)
    ap.add_argument('--fuel', type=int, default=40000)
    args = ap.parse_args()
    specs = open(args.list).read().split()
    os.makedirs(args.outdir, exist_ok=True)
    ok, bad = [], []
    for mstr in specs:
        tm = NP.decode(mstr)
        if not total(tm):
            bad.append((mstr, 'has an undefined transition'))
            continue
        sparse = sparse_state(mstr)
        got = flavour_of(tm, sparse)
        mir = None
        if got is None:
            mir = mirror_spec(mstr)
            got = flavour_of(NP.decode(mir), sparse)
            if got is None:
                bad.append((mstr, 'not a ReachSt flavour'))
                continue
        flav, roles = got
        res, err = prove_ext(mstr, args.k, args.n, args.t, args.fuel,
                             qext=roles[2])
        if res is None:
            bad.append((mstr, err))
            continue
        body, thm = emit(mstr, res, flav, roles, mir)
        path = os.path.join(args.outdir, 'RST_' + mstr + '.v')
        with open(path, 'w') as f:
            f.write(HEADER.format(mstr=mstr, k=args.k, n=args.n, t=args.t,
                                  fuel=args.fuel, nctx=res['nctx'],
                                  qext='St' + roles[2], flav=flav,
                                  blurb=FLAV_BLURB[flav])
                    + '\n' + body + '\n')
        ok.append((mstr, flav, res['nctx'], path))
        print('OK   %s  %s%s roles=%s  nctx=%d  -> %s'
              % (mstr, flav, '/mir' if mir else '', ''.join(roles),
                 res['nctx'], path))
    for mstr, why in bad:
        print('MISS %s  %s' % (mstr, why))
    print('\n%d emitted, %d missed' % (len(ok), len(bad)))


if __name__ == '__main__':
    main()
