#!/usr/bin/env python3
"""UNTRUSTED emitter: a valfam certificate -> a Coq board for the Stage-B kernel.

Reads the JSON `valfam.close` emits and writes a file that

  * restates the machine's transition table;
  * carries the certificate's LADDER as data -- window rules, each validated
    against the ones before it, discharged by [LadderKernel.rule_sound];
  * carries every ARM as data with the chain that replays it, discharged by
    [LadderKernel.arm_sound];
  * carries the FAMILY -- the fill law per phase, the terminators, the code
    and the step -- as a [LadderFam.Fam] value, so the four things 4f/4g say
    the kernel must not bake in arrive as fields rather than as definitions.

Everything here is untrusted.  The Coq kernel re-runs [check_ladder] and
[check_arm] on every line emitted; a wrong chain, a wrong step count or a
wrong normalisation makes the board fail to compile rather than producing a
wrong theorem.

Usage:  emit_ladder.py CERT.json [-o OUT.v]
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from ladderarm import (ArmShape, normalize, parse_cfg, parse_tm,     # noqa: E402
                       _common_suffix, _split_marker, to_sside)
from ladderchain import _conf, derive_arm                            # noqa: E402
import lapcert as LC                                                 # noqa: E402

ST = ['StA', 'StB', 'StC', 'StD']
SYM = ['S0', 'S1']


def mach_id(spec):
    return spec.replace('-', '_')


def clist(xs, f):
    return '[' + ';'.join(f(x) for x in xs) + ']'


def syms(cells):
    return clist(cells, lambda c: SYM[c])


def coq_side(s):
    pre, u, a, b, post = s
    return 'mkS %s %s %d %d %s' % (syms(pre), syms(u), a, b, syms(post))


def coq_conf(c):
    q, L, h, R = c
    return 'mkC %s (%s) %s (%s)' % (ST[q], coq_side(L), SYM[h], coq_side(R))


def coq_lstep(st):
    if st[0] in ('SWin', 'SWinL', 'SWinR', 'SCycR', 'SRotL', 'SRotR',
                 'SUnrotL', 'SUnrotR', 'SFoldL', 'SFoldR'):
        return '%s %d' % (st[0], st[1])
    if st[0] == 'SCycL':
        return 'SCycL %d %d' % (st[1], st[2])
    raise ValueError(st)


def coq_chain(chain):
    return clist(chain, lambda st: 'RB (%s)' % coq_lstep(st))


def coq_table(spec):
    rows = []
    for q, part in enumerate(spec.strip().split('_')):
        cells = []
        for s in range(len(part) // 3):
            e = part[3 * s:3 * s + 3]
            if e[0] == '-' or e[2] in 'ZH-':
                cells.append('  | %s, %s => None' % (ST[q], SYM[s]))
            else:
                cells.append('  | %s, %s => mk %s %s %s'
                             % (ST[q], SYM[s], SYM[int(e[0])],
                                'DR' if e[1] == 'R' else 'DL',
                                ST[ord(e[2]) - 65]))
        rows.extend(cells)
    return '\n'.join(rows)


# --------------------------------------------------------------- the family --

def coq_fill(f):
    return ('mkFill %d %s %d %s %d'
            % (f['widens_by'], clist(f['target_prefix'], str),
               f['target_fill_digit'], clist(f['target_suffix'], str),
               f['lands_in_phase']))


def coq_fam(cert):
    fam = cert['family']
    fills = cert.get('fill_by_phase') or [cert['fill']]
    return ('mkFam %d %s %s %s %s %d %s %s %s %s %s'
            % (fam['base'],
               clist(fam['digits'], syms),
               syms(fam['near_head_prefix']),
               clist(fam.get('terminators_by_phase', [fam['terminator']]),
                     syms),
               'Gray' if fam.get('code') == 'gray' else 'Binary',
               fam.get('value_step_per_anchor_visit', 1),
               clist(fills, coq_fill),
               'St' + fam['state'],
               SYM[fam['head']],
               'true' if fam['side'] == 'L' else 'false',
               syms(fam['other_side_cells'])))


# ---------------------------------------------------------- the ladder rules --

def ladder_window(r):
    """A ladder rule in WINDOW form: both sides fully concrete, so a later
    rule can invoke it with [RU].  The rule's own symbolic counts cancel --
    `10^u0 -> 10^(u0-1)` IS "consume one 10" -- which is what stripping the
    common suffix of the two sides computes."""
    ql, hl, Ll, Rl = parse_cfg(r['lhs'])
    qr, hr, Lr, Rr = parse_cfg(r['rhs'])
    Ll, _ = _split_marker(Ll)
    Rl, _ = _split_marker(Rl)
    Lr, _ = _split_marker(Lr)
    Rr, _ = _split_marker(Rr)
    Lh, Lrh = _common_suffix(Ll, Lr)
    Rh, Rrh = _common_suffix(Rl, Rr)
    c0 = (ql, hl, to_sside(Lh, None), to_sside(Rh, None))
    c1 = (qr, hr, to_sside(Lrh, None), to_sside(Rrh, None))
    return _conf(c0), _conf(c1)


def derive_ladder(tab, cert, maxdepth=24, nmax=80):
    """[(name, lhs, rhs, chain, cb)] for the rules that reduce to a window
    rule AND replay.  A rule that does not is simply left out: the arms do
    not need it, and a ladder is a list, not a set."""
    out = []
    for r in cert.get('ladder', []):
        try:
            c0, c1 = ladder_window(r)
        except (ArmShape, ValueError):
            continue
        chain = LC.derive_chain(tab, False, False, c0, c1,
                                maxdepth=maxdepth, nmax=nmax)
        if chain is None:
            continue
        got = LC.srun(tab, False, False, chain, c0)
        if got is None or got[0] != c1 or got[1] != 0:
            continue
        out.append((r['name'], c0, c1, chain, got[2]))
    return out


# ---------------------------------------------------------------- the board --

HEADER = '''(** * LDR_%(mid)s: machine %(spec)s, boarded by the STAGE-B LADDER.

    GENERATED by tools/ladder/emit_ladder.py from a `valfam.close`
    certificate -- an UNTRUSTED prover.  Every line below is re-run by the
    Coq kernel: [check_ladder] validates the ladder rules against the rules
    before them, [check_arm] replays every arm, and both are closed by
    [vm_compute].  A wrong chain makes the replay return [None] and this
    file fails to compile.

    The certificate's four PARAMETERS -- the fill law per phase with the
    phase it lands in, the terminator of each phase, the counter's code and
    its step per anchor visit -- arrive as fields of a [LadderFam.Fam]
    value, not as definitions in the kernel (LADDER_PLAN.md 4f).

    Axiom footprint: [functional_extensionality_dep], via [CTape.lift]. *)
From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape.
From BBB4.Checkers Require Import LapDecider LadderKernel LadderFam.
Import ListNotations.

Definition mk_%(mid)s (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).
Local Notation mk := mk_%(mid)s.

(** %(spec)s *)
Definition tm_%(mid)s : TM := fun q s => match q, s with
%(table)s
  end.
Local Notation tm := tm_%(mid)s.
'''


def emit(cert, out):
    spec = cert['spec']
    mid = mach_id(spec)
    tab = parse_tm(spec)
    L = []
    L.append(HEADER % dict(mid=mid, spec=spec, table=coq_table(spec)))

    # -- the family, as data
    L.append('''
(** ** The family, as DATA

    The successor is a PARAMETER here, not a law: [fam_succ] reads the fill
    of the phase it is in, the code the digits are written in, and the step
    the counter advances by, all off this record. *)
Definition fam_%(mid)s : Fam := %(fam)s.
Local Notation FAM := fam_%(mid)s.
''' % dict(mid=mid, fam=coq_fam(cert)))

    # -- the ladder
    lad = derive_ladder(tab, cert)
    items = []
    for name, c0, c1, chain, cb in lad:
        items.append('(mkLRule (%s) (%s) 0 %d, %s)'
                     % (coq_conf(c0), coq_conf(c1), cb, coq_chain(chain)))
    L.append('''
(** ** The ladder, as DATA

    %(n)d window rule(s).  [check_ladder] validates rule i against rules
    0..i-1 only, and [rule_sound] -- ONE theorem, by induction on ladder
    POSITION -- turns that into soundness for all of them. *)
Definition lad_%(mid)s : list (LRule * list rstep) :=
  [%(items)s].
Local Notation lad := lad_%(mid)s.

Definition rules_%(mid)s : list LRule := map fst lad.
Local Notation rules := rules_%(mid)s.

Lemma ladder_ok_%(mid)s : check_ladder tm [] lad = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rules_sound_%(mid)s : Forall (RuleSound tm false false) rules.
Proof. apply rule_sound_nil. exact ladder_ok_%(mid)s. Qed.
''' % dict(mid=mid, n=len(lad), items=';\n   '.join(items) if items else ''))

    # -- the arms
    L.append('''
(** ** The arms, as DATA

    Each is a rule the kernel re-derives from the machine.  [el]/[er] record
    whether that side's tail is known empty: the fill arm must see the end
    of the counter, the interior arms hold against an arbitrary tail. *)
''')
    good, bad = [], []
    for a in cert['arms']:
        nm = a['name']
        try:
            chain, ca, cb, el, er, c0, c1 = derive_arm(
                tab, a['lhs'], a['rhs'], a['steps'], a.get('lbs'))
        except (ArmShape, ValueError) as e:
            bad.append((nm, str(e)))
            L.append('(* %s: NO KERNEL CHAIN -- %s *)\n' % (nm, e))
            continue
        good.append((nm, el, er))
        L.append('''(* %(orig)s  ==>  %(origr)s   [%(steps)s steps] *)
Definition %(nm)s_%(mid)s : LRule :=
  mkLRule (%(lhs)s)
          (%(rhs)s) %(ca)d %(cb)d.
Definition ch_%(nm)s_%(mid)s : list rstep := %(chain)s.
Lemma ok_%(nm)s_%(mid)s :
  check_arm tm %(el)s %(er)s rules %(nm)s_%(mid)s ch_%(nm)s_%(mid)s = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sound_%(nm)s_%(mid)s : RuleSound tm %(el)s %(er)s %(nm)s_%(mid)s.
Proof. eapply arm_sound; [exact rules_sound_%(mid)s | exact ok_%(nm)s_%(mid)s]. Qed.

''' % dict(nm=nm, mid=mid, lhs=coq_conf(c0), rhs=coq_conf(c1), ca=ca, cb=cb,
           chain=coq_chain(chain), el=str(el).lower(), er=str(er).lower(),
           orig=a['lhs'], origr=a['rhs'], steps=a['steps']))

    L.append('''(** ** What this board establishes

    %(ng)d of %(nt)d arms of the certificate are re-derived by the kernel and
    sound: each [sound_*] is a theorem that the machine, from that arm's
    left-hand side and against any tail the flags permit, reaches the arm's
    right-hand side in exactly the certificate's step count. *)
''' % dict(ng=len(good), nt=len(cert['arms'])))

    open(out, 'w').write(''.join(L))
    return good, bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cert')
    ap.add_argument('-o', '--out')
    args = ap.parse_args()
    cert = json.load(open(args.cert))
    if isinstance(cert, list):
        cert = cert[0]
    out = args.out or os.path.join(
        HERE, '..', '..', 'theories', 'Machines', 'Ladder',
        'LDR_%s.v' % mach_id(cert['spec']))
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    good, bad = emit(cert, out)
    print('%s: %d arms boarded, %d without a chain' % (out, len(good),
                                                       len(bad)))
    for nm, e in bad:
        print('  %-8s %s' % (nm, e))
    return 0


if __name__ == '__main__':
    sys.exit(main())
