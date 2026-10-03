#!/usr/bin/env python3
"""LE10: a conjugate of an LP_ source row whose blank run enters the source's
lap family [Cg x] somewhere the source's own run does not (LoopConjTr).
Writes theories/Machines/LoopTr/LP_<dst>.v and lists it in _CoqProject.

    python3 tools/closeouttr/le10/conj_family.py SRC DST P0P1P2P3 FLIP X T
(p as in le6/conj_find.py: dst state p[q] plays src state q; X, T: the
destination reaches cconj (Cg X) after T steps from blank)."""
import os, sys
src, dst, pp, flip, x, T = sys.argv[1:7]
p = [int(c) for c in pp]
flip = int(flip)
REPO = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
ST = ['StA', 'StB', 'StC', 'StD']


def mach(spec):
    out = []
    for qi, t in enumerate(spec.split('_')):
        for b in range(2):
            e = t[3 * b:3 * b + 3]
            out.append('  | %s, S%d => Some (mkTrans S%s %s St%s)' % (ST[qi], b, e[0], 'DR' if e[1] == 'R' else 'DL', e[2]))
    return '\n'.join(out) + '\n  end.\n'


pm = ' | '.join('%s => %s' % (ST[q], ST[p[q]]) for q in range(4))
inv = {p[q]: q for q in range(4)}
txt = '''(** * LP_%(d)s (SCOPING_INSTR 7.4.LE10)

    A state-renamed%(mir)s copy of [LP_%(s)s].  Its blank run enters
    that row's lap family [Cg] at [Cg %(x)s] (after %(T)s steps), which the
    source's own run never visits, so the two runs never fall into lockstep
    and [CConjCoverTr] does not apply.  [LoopConjTr.conj_family_neverqhtr]
    carries the source's lap for every member of the family.

    Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import CConjugateTr LoopConjTr.
From BBB4.Machines.LoopTr Require LP_%(s)s.
Import ListNotations.

Definition tm_%(d)s : TM := fun q s => match q, s with
%(m)sDefinition p_%(d)s (q : St) : St := match q with %(pm)s end.

Theorem nqhtr_%(d)s : NeverQuasiHaltsTr tm_%(d)s.
Proof.
  apply (conj_family_neverqhtr LP_%(s)s.tm_%(s)s tm_%(d)s p_%(d)s %(fl)s LP_%(s)s.Cg).
  - intros q s; destruct q, s; reflexivity.
  - intros q; destruct q; [exists %(i0)s | exists %(i1)s | exists %(i2)s | exists %(i3)s]; reflexivity.
  - exists %(T)s, %(x)s. apply conj_boot_ok. vm_compute. reflexivity.
  - intros m. exists (3 + m). apply LP_%(s)s.lap_g.
  - exact LP_%(s)s.fires_g.
Qed.
''' % dict(d=dst, s=src, x=x, T=T, m=mach(dst), pm=pm, fl='true' if flip else 'false',
           mir=' and mirrored' if flip else '',
           i0=ST[inv[0]], i1=ST[inv[1]], i2=ST[inv[2]], i3=ST[inv[3]])
dstp = os.path.join(REPO, 'theories', 'Machines', 'LoopTr', 'LP_%s.v' % dst)
open(dstp, 'w').write(txt)
cp = os.path.join(REPO, '_CoqProject')
lines = open(cp).read().split('\n')
ent = 'theories/Machines/LoopTr/LP_%s.v' % dst
if ent not in lines:
    lines.insert(lines.index('theories/Machines/LoopTr/LP_%s.v' % src) + 1, ent)
    open(cp, 'w').write('\n'.join(lines))
print(dstp)
