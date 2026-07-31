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
From BBB4.Checkers Require Import LapDecider LadderKernel LadderFam LadderCheck.
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


# ------------------------------------------------------------- the closure --

class NoClosure(Exception):
    pass


def coq_chain_l(chain):
    """A chain of BASE steps only, for [srun_st] (no [rstep] wrapper)."""
    return clist(chain, coq_lstep)


def closure_data(cert, tab):
    """The two CLASS arms, the boot and the per-state visits, or NoClosure.

    LADDER_PLAN 4h(a): coverage reduces to a finite case split -- every
    digit string is t^n ++ d :: rest with d <> t, or t^k.  The arms that
    serve those two classes are not the mined arms the certificate carries:
    those are the same rules with every run length but one pinned to its
    lower bound.  Here they are built from the FAMILY, so there is one
    interior arm per digit below the top and one fill arm, whatever the
    certificate happened to emit.

    The fill arm is the one that must see the end of the counter, so its
    guaranteed block copy is materialised into s_pre (4h) -- without that
    it has no chain at all.
    """
    fam = cert['family']
    fills = cert.get('fill_by_phase') or [cert['fill']]
    if fam.get('code') != 'binary':
        raise NoClosure('code %s: LadderCheck states (Binary, 1) only'
                        % fam.get('code'))
    if fam.get('value_step_per_anchor_visit', 1) != 1:
        raise NoClosure('step %d: LadderCheck states (Binary, 1) only'
                        % fam.get('value_step_per_anchor_visit', 1))
    if len(fills) != 1:
        raise NoClosure('%d phases: the closure pins the phase at 0'
                        % len(fills))
    f = fills[0]
    if f['widens_by'] < 1 or f['lands_in_phase'] != 0:
        raise NoClosure('fill law does not land back in phase 0')
    m = len(f['target_prefix']) + len(f['target_suffix'])
    if m > 1 + f['widens_by']:
        raise NoClosure('fill target names %d digits but widens by %d'
                        % (m, f['widens_by']))
    b = fam['base']
    if b < 2:
        raise NoClosure('base %d' % b)

    digs = [tuple(w) for w in fam['digits']]
    pre = tuple(fam['near_head_prefix'])
    tail0 = tuple((fam.get('terminators_by_phase') or [fam['terminator']])[0])
    other = tuple(fam['other_side_cells'])
    q = ord(fam['state']) - 65
    hs = fam['head']
    left = fam['side'] == 'L'
    mid = f['target_fill_digit']
    OTHER = (other, (), 0, 0, ())

    def conf(sd):
        return (q, sd, hs, OTHER) if left else (q, OTHER, hs, sd)

    def derive(el, er, c0, c1, what):
        ch = LC.derive_chain(tab, el, er, c0, c1, maxdepth=32, nmax=120,
                             lift=True)
        if ch is None:
            raise NoClosure('%s: no chain' % what)
        got = LC.srun(tab, el, er, ch, c0)
        if got is None or got[0] != c1:
            raise NoClosure('%s: chain lands off the rhs' % what)
        if got[2] == 0:
            raise NoClosure('%s: zero-step rule' % what)
        return ch, got[1], got[2]

    # the interior class arms: t^n ++ d :: rest  ->  0^n ++ (d+1) :: rest
    inter = []
    for d in range(b - 1):
        c0 = conf((pre, digs[b - 1], 1, 0, digs[d]))
        c1 = conf((pre, digs[0], 1, 0, digs[d + 1]))
        el, er = (not left), left
        ch, ca, cb = derive(el, er, c0, c1, 'interior arm d=%d' % d)
        inter.append((d, c0, c1, ch, ca, cb, el, er))

    # the fill arm: t^(1+n) -> the fill law's target at width 1+n+s, both
    # tails known empty.  [fm1] guaranteed copies of the fill digit sit
    # before the symbolic run and [fm2] after; 4h's normalisation is that at
    # least one must be materialised into [s_pre], so try fm1 = 1 first.
    fpre = tuple(x for d in f['target_prefix'] for x in digs[d])
    fsuf = tuple(x for d in f['target_suffix'] for x in digs[d])
    fl = conf((pre + digs[b - 1], digs[b - 1], 1, 0, tail0))
    fm1, fm2, fr, fch, fca, fcb = None, None, None, None, None, None
    for m1 in (1, 0):
        m2 = 1 + f['widens_by'] - m - m1
        if m2 < 0:
            continue
        cand = conf((pre + fpre + digs[mid] * m1, digs[mid], 1, 0,
                     digs[mid] * m2 + fsuf + tail0))
        try:
            fch, fca, fcb = derive(True, True, fl, cand, 'fill arm')
        except NoClosure:
            continue
        fm1, fm2, fr = m1, m2, cand
        break
    if fr is None:
        raise NoClosure('fill arm: no chain at either copy split')

    # the boot, and a chain to every state from the fill's anchor
    boot = cert['boot']
    ds0 = list(boot['digits_lsb_first'])
    cells = list(pre)
    for d in ds0:
        cells.extend(digs[d])
    cells.extend(tail0)
    if cells != list(boot['cells']):
        raise NoClosure('boot cells %r are not the family at %r'
                        % (boot['cells'], ds0))
    if not ds0:
        raise NoClosure('boot digit string is empty')

    vis, cand = {}, []
    for n in range(0, 25):
        cand.append([('SWin', n)])
    for k in range(0, 20):
        cand.append(fch[:3] + [('SWinL', k)])
        for m in range(0, 6):
            cand.append(fch[:3] + [('SWinL', k), ('SWin', m)])
    for ch in cand:
        r = LC.srun(tab, True, True, ch, fl)
        if r:
            vis.setdefault(r[0][0], ch)
    missing = [ST[i] for i in range(4) if i not in vis]
    if missing:
        raise NoClosure('no chain from the fill anchor to %s'
                        % ','.join(missing))

    return dict(b=b, inter=inter, fill=(fl, fr, fch, fca, fcb),
                fm1=fm1, fm2=fm2,
                ds0=ds0, t0=boot['steps_from_blank'], vis=vis)


CLOSURE_NONE = '''
(** ** The closure: NOT BUILT for this row -- %s

    The board above still proves every rule the certificate carries; what
    is missing is the machine-level theorem.  LADDER_PLAN 4h(a) names the
    condition: [LadderCheck] states the class-successor lemma for
    [(Binary, 1)] only, so a family with another code or another step needs
    its own instance of [ClassSucc] before this section can be emitted. *)
'''

CLOSURE_HEAD = '''
(** ** The closure: from the RULES to [NeverQuasiHaltsSt]

    The arms below are the case split of [LadderCheck.digs_decomp], built
    from the FAMILY rather than mined: an interior arm per digit below the
    top, and the fill arm.  Every certificate arm above is one of these
    with its run lengths pinned to their lower bounds, which is why %d of
    them collapse to %d here.

    [board_neverqh] consumes them, the boot, and one chain per state, and
    returns the machine-level theorem. *)
'''

CLOSURE_IARM = '''Definition iarm%(d)d_%(mid)s : LRule :=
  mkLRule (%(lhs)s)
          (%(rhs)s) %(ca)d %(cb)d.
Definition ch_iarm%(d)d_%(mid)s : list rstep := %(ch)s.
Lemma ok_iarm%(d)d_%(mid)s :
  check_arm tm %(el)s %(er)s rules iarm%(d)d_%(mid)s ch_iarm%(d)d_%(mid)s = true.
Proof. vm_compute. reflexivity. Qed.

'''

CLOSURE_IDISP = '''Definition iarm_%(mid)s (d : nat) : LRule :=
  match d with
  %(br)s
  | _ => iarm0_%(mid)s   (* unreachable: the closure asks only d < b - 1 *)
  end.

'''

CLOSURE_FARM = '''(** The fill arm.  Both tails are known empty -- it is the only arm that
    sees the end of the counter -- and its guaranteed block copy is
    materialised into [s_pre], without which it has no chain at all. *)
Definition farm_%(mid)s : LRule :=
  mkLRule (%(lhs)s)
          (%(rhs)s) %(ca)d %(cb)d.
Definition ch_farm_%(mid)s : list rstep := %(ch)s.
Lemma ok_farm_%(mid)s :
  check_arm tm true true rules farm_%(mid)s ch_farm_%(mid)s = true.
Proof. vm_compute. reflexivity. Qed.

'''

CLOSURE_VIS = '''(** One chain per state, from the fill's anchor.  [vis_of_run] turns each
    into a visit, and [tops_cofinal] says those anchors keep coming. *)
Definition vis_%(mid)s (q : St) : list lstep :=
  match q with
  %(vb)s
  end.

'''

CLOSURE_THM = '''Lemma iarm_sound_%(mid)s : forall d, d < fm_b FAM - 1 ->
  RuleSound tm (negb (fm_left FAM)) (fm_left FAM) (iarm_%(mid)s d).
Proof.
  intros d Hd. vm_compute in Hd.
%(bsound)s  exfalso; lia.
Qed.

Lemma iarm_lhs_%(mid)s : forall d, d < fm_b FAM - 1 ->
  lr_lhs (iarm_%(mid)s d) = cls_conf FAM (cls_side FAM (fm_b FAM - 1) [d]).
Proof.
  intros d Hd. vm_compute in Hd.
%(bcomp)s  exfalso; lia.
Qed.

Lemma iarm_rhs_%(mid)s : forall d, d < fm_b FAM - 1 ->
  lr_rhs (iarm_%(mid)s d) = cls_conf FAM (cls_side FAM 0 [S d]).
Proof.
  intros d Hd. vm_compute in Hd.
%(bcomp)s  exfalso; lia.
Qed.

Lemma iarm_cb_%(mid)s : forall d, d < fm_b FAM - 1 ->
  0 < lr_cb (iarm_%(mid)s d).
Proof.
  intros d Hd. vm_compute in Hd.
%(blia)s  exfalso; lia.
Qed.

Lemma farm_sound_%(mid)s : RuleSound tm true true farm_%(mid)s.
Proof. eapply arm_sound; [exact rules_sound_%(mid)s | exact ok_farm_%(mid)s]. Qed.

Lemma boot_%(mid)s : csteps tm %(t0)d c0 = Some (fam_cfg FAM (%(ds0)s, 0, 0)).
Proof. vm_compute. reflexivity. Qed.

(** The machine-level theorem.  Every argument is either a [RuleSound] the
    Stage-B kernel discharged, or an equation two [vm_compute]s decide. *)
Theorem nqh_%(mid)s : NeverQuasiHaltsSt tm.
Proof.
  apply (board_neverqh tm FAM iarm_%(mid)s farm_%(mid)s vis_%(mid)s
                       %(ds0)s %(t0)d %(fm1)d %(fm2)d).
  - vm_compute; lia.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; repeat constructor.
  - vm_compute; repeat constructor.
  - vm_compute; lia.
  - vm_compute; lia.
  - vm_compute; reflexivity.
  - vm_compute; lia.
  - repeat constructor.
  - vm_compute; lia.
  - exact boot_%(mid)s.
  - exact iarm_sound_%(mid)s.
  - exact iarm_lhs_%(mid)s.
  - exact iarm_rhs_%(mid)s.
  - exact iarm_cb_%(mid)s.
  - exact farm_sound_%(mid)s.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; lia.
  - intros q; destruct q; vm_compute; reflexivity.
Qed.
'''


def emit_closure(cert, tab, mid):
    """The Coq for LadderCheck.board_neverqh, or a note on what stopped it."""
    try:
        cd = closure_data(cert, tab)
    except NoClosure as e:
        return CLOSURE_NONE % e, None

    b = cd['b']
    L = [CLOSURE_HEAD % (len(cert['arms']), b)]
    for d, c0, c1, ch, ca, cb, el, er in cd['inter']:
        L.append(CLOSURE_IARM % dict(
            d=d, mid=mid, lhs=coq_conf(c0), rhs=coq_conf(c1), ca=ca, cb=cb,
            ch=coq_chain(ch), el=str(el).lower(), er=str(er).lower()))
    L.append(CLOSURE_IDISP % dict(
        mid=mid,
        br='\n  '.join('| %d => iarm%d_%s' % (d, d, mid)
                       for d, _, _, _, _, _, _, _ in cd['inter'])))
    fl, fr, fch, fca, fcb = cd['fill']
    L.append(CLOSURE_FARM % dict(
        mid=mid, lhs=coq_conf(fl), rhs=coq_conf(fr), ca=fca, cb=fcb,
        ch=coq_chain(fch)))
    L.append(CLOSURE_VIS % dict(
        mid=mid,
        vb='\n  '.join('| %s => %s' % (ST[i], coq_chain_l(cd['vis'][i]))
                       for i in range(4))))
    def branches(body):
        return ''.join(
            '  destruct d as [|d]; [%s|].\n' % (body % dict(d=d, mid=mid))
            for d in range(b - 1))
    L.append(CLOSURE_THM % dict(
        mid=mid, t0=cd['t0'], ds0=clist(cd['ds0'], str),
        fm1=cd['fm1'], fm2=cd['fm2'],
        bsound=branches('eapply arm_sound; '
                        '[exact rules_sound_%(mid)s | exact ok_iarm%(d)d_%(mid)s]'),
        bcomp=branches('vm_compute; reflexivity'),
        blia=branches('vm_compute; lia')))
    return ''.join(L), cd


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

    closure, cd = emit_closure(cert, tab, mid)
    L.append(closure)

    open(out, 'w').write(''.join(L))
    return good, bad, cd


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
    good, bad, cd = emit(cert, out)
    print('%s: %d arms boarded, %d without a chain, closure %s'
          % (out, len(good), len(bad),
             'BUILT (%d interior + 1 fill)' % len(cd['inter']) if cd
             else 'not built'))
    for nm, e in bad:
        print('  %-8s %s' % (nm, e))
    return 0


if __name__ == '__main__':
    sys.exit(main())
