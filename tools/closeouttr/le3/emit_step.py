#!/usr/bin/env python3
"""UNTRUSTED emitter: a valfam certificate whose counter adds a STEP s > 1 per
anchor visit -> a Coq board closed by [LadderCheckStepTr] (SCOPING_INSTR
7.4.LE3).

`emit_ladder.py` refuses these ("step 3: LadderCheck states (Binary, 1)
only").  This module reuses everything of it but the closure: the machine,
the family record, the mined ladder and arms are written by
`emit_ladder.emit`, whose `emit_closure` is replaced here by one for the
three-way split of [LadderCheckStepTr]:

* no carry (`u + s < b`): one arm per low digit `u`, `u X -> (u+s) X`, the
  rest of the counter opaque;
* a carry: one arm per low digit `u >= b - s`, digit `d < b - 1` and arm
  index `r`, `u t^n d X -> (u+s-b) 0^n (d+1) X`;
* the fill: one arm per index `r` (on the top run `t^(k-1)`) and phase, from
  the phase's one top string `utop ph t^(k-1)`.

The residue of each phase (`cres`) is read off the boot and the fill laws;
`utop ph` is the one low digit in `b-s .. b-1` with that residue.  Every arm
is a `LadderNest` segment program (a plain chain is a one-segment program),
so the arm search is `emit_ladder`'s: a chain, a chain that lands off its
target only by blanks the machine wrote beside a known-empty tail, or a
nested program.

    python3 emit_step.py CERT.json -o OUT.v [--qh]

Nothing here carries proof weight: the kernel re-checks every arm, the boot,
the residues and the visits.
"""
import argparse
import copy
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'ladder'))
import emit_ladder as E  # noqa: E402
from emit_ladder import (NoClosure, blk, ARM_GRID, coq_conf, coq_seg,  # noqa: E402
                         coq_chain, coq_chain_l, clist, ST, SYM, _splits,
                         _rstrip0)

LC = E.LC
nest = E.nest


# nested programs are costly (seconds an arm): the emitters try every arm
# without them first, and again with them only if that fails
NEST_OK = [True]


class Arms:
    """the arm search shared by the LE3 emitters: a chain, a chain that lands
    off its target only by blanks beside a known-empty tail ([ceqL]), or a
    [LadderNest] program"""

    def __init__(self, tab):
        self.tab = tab
        self.cache = {}

    def nested(self, el, er, c0, c1, what, why):
        key = (el, er, c0, c1)
        if key not in self.cache:
            self.cache[key] = nest.derive_nested(self.tab, el, er, c0, c1)
        r = self.cache[key]
        if r is None:
            raise NoClosure('%s: %s, and no nested program' % (what, why))
        return ('NEST', r[0], r[1])

    def derive(self, el, er, c0, c1, what):
        """a segment program from c0 to c1 (up to lift), or NoClosure"""
        tab = self.tab
        ch = LC.derive_chain(tab, el, er, c0, c1, maxdepth=32, nmax=120,
                             lift=True)
        if ch is not None:
            got = LC.srun(tab, el, er, ch, c0)
            if got is not None and got[0] == c1 and got[2] > 0:
                return ch
            if got is not None and got[2] > 0 and nest.ceqL(el, er, got[0], c1):
                return ('NEST', [('NCh', ch)], [])
        if not NEST_OK[0]:
            raise NoClosure('%s: no chain (nested programs off)' % what)
        return self.nested(el, er, c0, c1, what, 'no chain')


def nvisits(tab, want, fl, prog):
    """(segment prefix, chain) per instruction, from every prefix of a fill
    arm's program"""
    if not (isinstance(prog, tuple) and prog[:1] == ('NEST',)):
        prog = ('NEST', [('NCh', prog)], [])
    _t, segs, rules = prog
    rr = [(a, b_) for a, b_, _c in rules]
    seen = {}
    for k in range(len(segs) + 1):
        got = nest.nrun(tab, True, True, rr, segs[:k], fl)
        if got is None:
            break
        ck = got[0]
        chs = ([segs[k][1][:i] for i in range(len(segs[k][1]) + 1)]
               if k < len(segs) and segs[k][0] == 'NCh' else [[]])
        for base in chs:
            for kind in ('SWin', 'SWinL', 'SWinR'):
                for n in range(0, 600):
                    g = LC.srun(tab, True, True, base + [(kind, n)], ck)
                    if g is None:
                        break
                    seen.setdefault((g[0][0], g[0][2]),
                                    (list(segs[:k]), base + [(kind, n)]))
            if all(i in seen for i in want):
                return seen
    return seen


def prog_coq(tab, inner, ch):
    """the Coq segments of a program, its inner rules appended to [inner]"""
    if isinstance(ch, tuple) and ch[:1] == ('NEST',):
        off = len(inner)
        for lhs, rhs, ich in ch[2]:
            got = LC.srun(tab, False, False, ich, lhs)
            inner.append((lhs, rhs, ich, got[1], got[2]))
        return [coq_seg(sg, off) for sg in ch[1]]
    return [coq_seg(('NCh', ch), 0)]


INNER = '''(** *** The inner rules: what the nested arms iterate *)
Definition nlad_%(mid)s : list (LRule * list rstep) :=
  [%(items)s].
Definition nrules_%(mid)s : list LRule := map fst nlad_%(mid)s.
Local Notation nrules := nrules_%(mid)s.

Lemma nladder_ok_%(mid)s : check_ladder tm [] nlad_%(mid)s = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nrules_sound_%(mid)s : Forall (RuleSound tm false false) nrules.
Proof. apply rule_sound_nil. exact nladder_ok_%(mid)s. Qed.

'''


def inner_coq(mid, inner):
    return INNER % dict(mid=mid, items=';\n   '.join(
        '(mkLRule (%s) (%s) %d %d, %s)' % (coq_conf(l), coq_conf(r), ca, cb,
                                          coq_chain(ch))
        for l, r, ch, ca, cb in inner))


def two_pass(fn, cert, tab):
    """fn(cert, tab) with nested programs off, then on; the closure data or
    the last NoClosure"""
    try:
        NEST_OK[0] = False
        return fn(cert, tab)
    except NoClosure:
        pass
    finally:
        NEST_OK[0] = True
    try:
        return fn(cert, tab)
    except NoClosure as e:
        return e


def _resolve_cres(b, s, fills, nph, ds0, ph0):
    """the value's residue mod s in each phase, or NoClosure"""
    v0 = 0
    for d in reversed(ds0):
        v0 = v0 * b + d
    cres = {ph0: v0 % s}
    for ph, f in enumerate(fills):
        c = (sum(f['target_prefix']) + sum(f['target_suffix'])) % s
        to = f['lands_in_phase']
        if cres.setdefault(to, c) != c:
            raise NoClosure('phase %d is entered at residue %d and %d mod %d'
                            % (to, cres[to], c, s))
    return [cres.get(ph, 0) for ph in range(nph)]


def closure_data_step(cert, tab):
    fam = cert['family']
    fills = cert.get('fill_by_phase') or [cert['fill']]
    nph = len(fills)
    s = fam.get('value_step_per_anchor_visit', 1)
    b = fam['base']
    if fam.get('code') != 'binary':
        raise NoClosure('code %s: LadderCheckStepTr states Binary only'
                        % fam.get('code'))
    if fam.get('weights') is not None:
        raise NoClosure('numeration %s: positional base-b only'
                        % fam.get('numeration'))
    if b < 2 or s < 1 or (b - 1) % s:
        raise NoClosure('step %d does not divide b - 1 = %d' % (s, b - 1))
    for ph, f in enumerate(fills):
        if not 0 <= f['lands_in_phase'] < nph:
            raise NoClosure('phase %d fills into phase %d' % (ph, f['lands_in_phase']))
        if f['widens_by'] < 0:
            raise NoClosure('phase %d fill narrows' % ph)
        if len(f['target_prefix']) + len(f['target_suffix']) > 1 + f['widens_by']:
            raise NoClosure('phase %d fill target names too many digits' % ph)
        if f['target_fill_digit'] % s:
            raise NoClosure('phase %d fill digit %d is not 0 mod %d'
                            % (ph, f['target_fill_digit'], s))
    digs = [tuple(w) for w in fam['digits']]
    pre = tuple(fam['near_head_prefix'])
    tails = [tuple(t) for t in
             (fam.get('terminators_by_phase') or [fam['terminator']])]
    if len(tails) < nph:
        raise NoClosure('%d fill laws but %d terminators' % (nph, len(tails)))
    boot = cert['boot']
    ph0 = boot.get('phase', 0)
    ds0 = list(boot['digits_lsb_first'])
    if not ds0 or not 0 <= ph0 < nph:
        raise NoClosure('boot %r in phase %d' % (ds0, ph0))
    cres = _resolve_cres(b, s, fills, nph, ds0, ph0)
    utop = [next(u for u in range(b - s, b) if u % s == c) for c in cres]
    other = tuple(fam['other_side_cells'])
    q = ord(fam['state']) - 65
    hs = fam['head']
    left = fam['side'] == 'L'
    OTHER = (other, (), 0, 0, ())

    def conf(sd):
        return (q, sd, hs, OTHER) if left else (q, OTHER, hs, sd)

    derive = Arms(tab).derive

    el, er = (not left), left
    # no carry: one flat arm per low digit
    aarms = []
    for u in range(b - s):
        c0 = conf(blk(pre + digs[u], digs[0], 0, ()))
        c1 = conf(blk(pre + digs[u + s], digs[0], 0, ()))
        aarms.append((u, c0, c1, derive(el, er, c0, c1, 'no-carry arm u=%d' % u)))

    def carry_at(n0, stride):
        got = []
        for u in range(b - s, b):
            for d in range(b - 1):
                for r in range(n0 + stride):
                    st = 0 if r < n0 else stride
                    c0 = conf(blk(pre + digs[u] + digs[b - 1] * r, digs[b - 1],
                                  st, digs[d]))
                    c1 = conf(blk(pre + digs[u + s - b] + digs[0] * r, digs[0],
                                  st, digs[d + 1]))
                    try:
                        ch = derive(el, er, c0, c1,
                                    'carry arm u=%d d=%d r=%d' % (u, d, r))
                    except NoClosure:
                        return None
                    got.append((u, d, r, c0, c1, ch))
        return got

    barms, n0i, sti = None, None, None
    for n0, stride in ARM_GRID:
        got = carry_at(n0, stride)
        if got is not None:
            barms, n0i, sti = got, n0, stride
            break
    if barms is None:
        raise NoClosure('carry arm: no program at any threshold and stride')

    def fill_at(n0, stride):
        got = []
        for ph, f in enumerate(fills):
            to = f['lands_in_phase']
            mid = f['target_fill_digit']
            mf = len(f['target_prefix']) + len(f['target_suffix'])
            fpre = tuple(x for d in f['target_prefix'] for x in digs[d])
            fsuf = tuple(x for d in f['target_suffix'] for x in digs[d])
            for r in range(n0 + stride):
                st = 0 if r < n0 else stride
                fl = conf(blk(pre + digs[utop[ph]] + digs[b - 1] * r, digs[b - 1],
                              st, tails[ph]))
                total = r + 1 + f['widens_by'] - mf
                if total < 0:
                    return None
                hit = None
                for m1 in _splits(total):
                    cand = conf(blk(pre + fpre + digs[mid] * m1, digs[mid], st,
                                    digs[mid] * (total - m1) + fsuf + tails[to]))
                    try:
                        ch = derive(True, True, fl, cand,
                                    'fill arm r=%d ph=%d' % (r, ph))
                    except NoClosure:
                        continue
                    hit = (r, ph, m1, total - m1, fl, cand, ch)
                    break
                if hit is None:
                    return None
                got.append(hit)
        return got

    want = [(q_, s_) for q_ in range(4) for s_ in range(2)
            if (q_, s_) not in E.TR_PINS]

    def visit_phase(fill):
        seen_at = {(r, ph): nvisits(tab, want, fl, ch) for r, ph, _1, _2, fl, _c, ch in fill}
        for pv in range(nph):
            if all(i in seen_at[k] for k in seen_at if k[1] == pv for i in want):
                return pv, {r: {i: seen_at[(r, p)][i] for i in want}
                            for (r, p) in seen_at if p == pv}
        return None

    fill, n0f, stf, pv, nvis = None, None, None, None, None
    for n0, stride in ARM_GRID:
        f2 = fill_at(n0, stride)
        if f2 is None:
            continue
        vp = visit_phase(f2)
        if vp is None:
            continue
        fill, n0f, stf = f2, n0, stride
        pv, nvis = vp
        break
    if fill is None:
        raise NoClosure('fill arm: no program, or no visit phase, at any '
                        'threshold and stride')

    def kto(ph, tgt):
        cur = ph
        for k in range(nph + 1):
            if cur == tgt:
                return k
            cur = fills[cur]['lands_in_phase']
        return None
    kcyc = [kto(ph, pv) for ph in range(nph)]
    if any(k is None for k in kcyc):
        raise NoClosure('the phase cycle does not reach phase %d' % pv)

    cells = list(pre)
    for d in ds0:
        cells.extend(digs[d])
    cells.extend(tails[ph0])
    if _rstrip0(cells) != _rstrip0(boot['cells']):
        raise NoClosure('boot cells %r are not the family at %r'
                        % (boot['cells'], ds0))
    return dict(nest=True, b=b, s=s, el=el, er=er, nph=nph, ph0=ph0, pv=pv,
                kcyc=kcyc, cres=cres, utop=utop, aarms=aarms, barms=barms,
                n0i=n0i, sti=sti, fill=fill, n0f=n0f, stf=stf, ds0=ds0,
                t0=boot['steps_from_blank'], nvis=nvis, want=want,
                # emit_ladder's report line
                inter=barms)


ARM = '''Definition %(nm)s_%(mid)s : LRule :=
  mkLRule (%(lhs)s)
          (%(rhs)s) 0 1.
Definition ch_%(nm)s_%(mid)s : list nseg :=
  [%(segs)s].
Lemma ok_%(nm)s_%(mid)s :
  check_narm tm %(el)s %(er)s nrules %(nm)s_%(mid)s ch_%(nm)s_%(mid)s = true.
Proof. vm_compute. reflexivity. Qed.

'''

THM = '''Lemma aarm_reach_%(mid)s : forall u, u + fm_step FAM < fm_b FAM ->
  ReachL tm (negb (fm_left FAM)) (fm_left FAM)
    (lr_lhs (aarm_%(mid)s u)) (lr_rhs (aarm_%(mid)s u)).
Proof.
  intros u Hu. %(chg)s
%(asound)s  exfalso; lia.
Qed.

Lemma aarm_lhs_%(mid)s : forall u, u + fm_step FAM < fm_b FAM ->
  lr_lhs (aarm_%(mid)s u) = cls_conf FAM (cls_side FAM [u] 0 0 0 []).
Proof.
  intros u Hu. %(chg)s
%(acomp)s  exfalso; lia.
Qed.

Lemma aarm_rhs_%(mid)s : forall u, u + fm_step FAM < fm_b FAM ->
  lr_rhs (aarm_%(mid)s u) = cls_conf FAM (cls_side FAM [u + fm_step FAM] 0 0 0 []).
Proof.
  intros u Hu. %(chg)s
%(acomp)s  exfalso; lia.
Qed.

Lemma barm_reach_%(mid)s : forall u d r,
  fm_b FAM <= u + fm_step FAM -> u < fm_b FAM -> d < fm_b FAM - 1 ->
  r < %(n0i)d + %(sti)d ->
  ReachL tm (negb (fm_left FAM)) (fm_left FAM)
    (lr_lhs (barm_%(mid)s u d r)) (lr_rhs (barm_%(mid)s u d r)).
Proof.
  intros u d r Hu1 Hu2 Hd Hr. %(chg)s
%(bsound)s  exfalso; lia.
Qed.

Lemma barm_lhs_%(mid)s : forall u d r,
  fm_b FAM <= u + fm_step FAM -> u < fm_b FAM -> d < fm_b FAM - 1 ->
  r < %(n0i)d + %(sti)d ->
  lr_lhs (barm_%(mid)s u d r)
    = cls_conf FAM (cls_side FAM [u] (fm_b FAM - 1) r
                      (astride %(n0i)d %(sti)d r) [d]).
Proof.
  intros u d r Hu1 Hu2 Hd Hr. %(chg)s
%(bcomp)s  exfalso; lia.
Qed.

Lemma barm_rhs_%(mid)s : forall u d r,
  fm_b FAM <= u + fm_step FAM -> u < fm_b FAM -> d < fm_b FAM - 1 ->
  r < %(n0i)d + %(sti)d ->
  lr_rhs (barm_%(mid)s u d r)
    = cls_conf FAM (cls_side FAM [u + fm_step FAM - fm_b FAM] 0 r
                      (astride %(n0i)d %(sti)d r) [S d]).
Proof.
  intros u d r Hu1 Hu2 Hd Hr. %(chg)s
%(bcomp)s  exfalso; lia.
Qed.

Lemma farm_reach_%(mid)s : forall r ph, r < %(n0f)d + %(stf)d -> ph < %(nph)d ->
  ReachL tm true true (lr_lhs (farm_%(mid)s r ph)) (lr_rhs (farm_%(mid)s r ph)).
Proof.
  intros r ph Hr Hph.
%(fsound)s  exfalso; lia.
Qed.

Lemma farm_lhs_%(mid)s : forall r ph, r < %(n0f)d + %(stf)d -> ph < %(nph)d ->
  lr_lhs (farm_%(mid)s r ph)
    = cls_conf FAM (run_side FAM (fm_b FAM - 1) r (astride %(n0f)d %(stf)d r)
                      0 ph [utop_%(mid)s ph] []).
Proof.
  intros r ph Hr Hph.
%(fcomp)s  exfalso; lia.
Qed.

Lemma farm_rhs_%(mid)s : forall r ph, r < %(n0f)d + %(stf)d -> ph < %(nph)d ->
  lr_rhs (farm_%(mid)s r ph)
    = cls_conf FAM (run_side FAM (f_mid (fam_fill FAM ph)) (fm1_%(mid)s r ph)
                      (astride %(n0f)d %(stf)d r) (fm2_%(mid)s r ph)
                      (f_to (fam_fill FAM ph))
                      (f_pre (fam_fill FAM ph)) (f_suf (fam_fill FAM ph))).
Proof.
  intros r ph Hr Hph.
%(fcomp)s  exfalso; lia.
Qed.

Lemma fm12_%(mid)s : forall r ph, r < %(n0f)d + %(stf)d -> ph < %(nph)d ->
  fm1_%(mid)s r ph + fm2_%(mid)s r ph
  + (length (f_pre (fam_fill FAM ph)) + length (f_suf (fam_fill FAM ph)))
  = S r + f_s (fam_fill FAM ph).
Proof.
  intros r ph Hr Hph.
%(flia)s  exfalso; lia.
Qed.

Lemma vis_ok_%(mid)s : forall r t, ~ In t pins_%(mid)s ->
  r < %(n0f)d + %(stf)d ->
  nfire tm true true nrules (vsegs_%(mid)s r t) (vis_%(mid)s r t)
    (lr_lhs (farm_%(mid)s r %(pv)d)) = Some t.
Proof.
  intros r t Hnp Hr.
%(fvis)s  exfalso; lia.
Qed.

'''

BOOTL = '''Lemma bootl_%(mid)s :
  stepn %(tmb)s %(t0)d InitES = Some (lift (fam_cfg FAM (%(ds0)s, 0, %(ph0)d))).
Proof.
  assert (H : match csteps %(tmb)s %(t0)d c0 with
              | Some c => ceqb c (fam_cfg FAM (%(ds0)s, 0, %(ph0)d))
              | None => false end = true) by (vm_compute; reflexivity).
  destruct (csteps %(tmb)s %(t0)d c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

'''

NQH = '''(** The machine-level theorem, at the INSTRUCTION level, through the step
    board [LadderCheckStepTr.boardS_neverqhtr]. *)
Theorem nqhtr_%(mid)s : NeverQuasiHaltsTr tm_%(mid)s.
Proof.
  eapply (boardS_neverqhtr tm_%(mid)s pins_%(mid)s FAM %(nph)d
                           cres_%(mid)s utop_%(mid)s aarm_%(mid)s barm_%(mid)s
                           %(n0i)d %(sti)d farm_%(mid)s %(n0f)d %(stf)d
                           fm1_%(mid)s fm2_%(mid)s %(pv)d
                           nrules vsegs_%(mid)s vis_%(mid)s
                           %(ds0)s %(ph0)d).
%(args)s  - exact bootl_%(mid)s.
Qed.
'''

QH = '''(** a pinned instruction fired before the boot: the quasihalt witness *)
Lemma wit_%(mid)s :
  existsb (fun tg => cfires tm_%(mid)s c0 %(t0)d tg) pins_%(mid)s = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bnd_%(mid)s : (%(t0)d <=? 32779478) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(** The machine-level theorem, on the QUASIHALTING side, through the step
    board [LadderCheckStepTr.boardS_qhtr]. *)
Theorem qhtr_%(mid)s :
  NonHalt tm_%(mid)s /\\ QHBoundTr 32779478 tm_%(mid)s /\\ QuasiHaltsTr tm_%(mid)s.
Proof.
  eapply (boardS_qhtr tm_%(mid)s pins_%(mid)s FAM %(nph)d
                      cres_%(mid)s utop_%(mid)s aarm_%(mid)s barm_%(mid)s
                      %(n0i)d %(sti)d farm_%(mid)s %(n0f)d %(stf)d
                      fm1_%(mid)s fm2_%(mid)s %(pv)d
                      nrules vsegs_%(mid)s vis_%(mid)s
                      %(ds0)s %(ph0)d).
%(args)s  - exact bootl_%(mid)s.
  - exact wit_%(mid)s.
  - exact bnd_%(mid)s.
Qed.
'''

HEAD = '''
(** ** The closure: a counter that adds %(s)d per visit ([LadderCheckStepTr])

    [LadderCheck]'s class split is for a step of 1; this family adds %(s)d
    per anchor visit in base %(b)d, and %(s)d divides %(b)d - 1, so the value
    mod %(s)d is the digit sum mod %(s)d and depends on the phase alone
    ([cres]).  The split is on the low digit: %(na)d no-carry arm(s), the
    carry arms at threshold %(n0i)d stride %(sti)d, and the fill arms at
    threshold %(n0f)d stride %(stf)d from each phase's one top string
    ([utop]).  Every arm is a [LadderNest] segment program. *)
From BBB4.Checkers Require Import LadderCheckStepTr.

'''


def emit_closure_step(cert, tab, mid):
    cd = two_pass(closure_data_step, cert, tab)
    if isinstance(cd, NoClosure):
        return E.CLOSURE_NONE % cd, None
    b, s = cd['b'], cd['s']
    n0i, sti, n0f, stf = cd['n0i'], cd['sti'], cd['n0f'], cd['stf']
    nph, ph0, pv = cd['nph'], cd['ph0'], cd['pv']
    nA, nF = n0i + sti, n0f + stf
    el, er = cd['el'], cd['er']
    L = [HEAD % dict(s=s, b=b, na=len(cd['aarms']), n0i=n0i, sti=sti,
                     n0f=n0f, stf=stf)]
    inner, arms = [], []

    def prog(ch):
        return prog_coq(tab, inner, ch)

    for u, c0, c1, ch in cd['aarms']:
        arms.append(('aarm%d' % u, c0, c1, prog(ch), el, er))
    for u, d, r, c0, c1, ch in cd['barms']:
        arms.append(('barm%d_%d_%d' % (u, d, r), c0, c1, prog(ch), el, er))
    offs = {}
    for r, ph, _m1, _m2, fl, fr, fch in cd['fill']:
        offs[(r, ph)] = len(inner)
        arms.append(('farm%d_%d' % (r, ph), fl, fr, prog(fch), True, True))
    L.append(inner_coq(mid, inner))
    for nm, c0, c1, segs, el_, er_ in arms:
        L.append(ARM % dict(nm=nm, mid=mid, lhs=coq_conf(c0), rhs=coq_conf(c1),
                            segs=';\n   '.join(segs), el=str(el_).lower(),
                            er=str(er_).lower()))
    a0 = cd['aarms'][0][0]
    u0, d0, r0 = cd['barms'][0][:3]
    fr0, fp0 = cd['fill'][0][:2]
    L.append('''(** *** The dispatch, the residues and the tops *)
Definition aarm_%(mid)s (u : nat) : LRule :=
  match u with
  %(ab)s
  | _ => aarm%(a0)d_%(mid)s
  end.

Definition barm_%(mid)s (u d r : nat) : LRule :=
  match u, d, r with
  %(bb)s
  | _, _, _ => barm%(u0)d_%(d0)d_%(r0)d_%(mid)s
  end.

Definition farm_%(mid)s (r ph : nat) : LRule :=
  match r, ph with
  %(fb)s
  | _, _ => farm%(fr0)d_%(fp0)d_%(mid)s
  end.

Definition fm1_%(mid)s (r ph : nat) : nat :=
  match r, ph with %(b1)s | _, _ => 0 end.
Definition fm2_%(mid)s (r ph : nat) : nat :=
  match r, ph with %(b2)s | _, _ => 0 end.

Definition cres_%(mid)s (ph : nat) : nat :=
  match ph with %(cb)s | _ => 0 end.
Definition utop_%(mid)s (ph : nat) : nat :=
  match ph with %(ub)s | _ => 0 end.

Definition vis_%(mid)s (r : nat) (t : Instr) : list lstep :=
  match r, t with
  %(vb)s
  | _, _ => []
  end.

Definition vsegs_%(mid)s (r : nat) (t : Instr) : list nseg :=
  match r, t with
  %(sb)s
  | _, _ => []
  end.

''' % dict(
        mid=mid, a0=a0, u0=u0, d0=d0, r0=r0, fr0=fr0, fp0=fp0,
        ab='\n  '.join('| %d => aarm%d_%s' % (u, u, mid) for u, *_ in cd['aarms']),
        bb='\n  '.join('| %d, %d, %d => barm%d_%d_%d_%s' % (u, d, r, u, d, r, mid)
                       for u, d, r, *_ in cd['barms']),
        fb='\n  '.join('| %d, %d => farm%d_%d_%s' % (r, ph, r, ph, mid)
                       for r, ph, *_ in cd['fill']),
        b1=' '.join('| %d, %d => %d' % (r, ph, m1) for r, ph, m1, *_ in cd['fill']),
        b2=' '.join('| %d, %d => %d' % (r, ph, m2)
                    for r, ph, _m1, m2, *_ in cd['fill']),
        cb=' '.join('| %d => %d' % (ph, c) for ph, c in enumerate(cd['cres'])),
        ub=' '.join('| %d => %d' % (ph, u) for ph, u in enumerate(cd['utop'])),
        vb='\n  '.join('| %d, (%s, %s) => %s'
                       % (r, ST[i[0]], SYM[i[1]], coq_chain_l(v[1]))
                       for r in sorted(cd['nvis'])
                       for i, v in sorted(cd['nvis'][r].items())),
        sb='\n  '.join('| %d, (%s, %s) => [%s]'
                       % (r, ST[i[0]], SYM[i[1]],
                          '; '.join(coq_seg(sg, offs[(r, pv)]) for sg in v[0]))
                       for r in sorted(cd['nvis'])
                       for i, v in sorted(cd['nvis'][r].items()))))

    def reach(nm):
        return ('eapply narm_reach; [exact nrules_sound_%(mid)s '
                '| exact ok_' + nm + '_%(mid)s]')

    def abranches(body):
        out = []
        for u in range(b - s):
            out.append('  destruct u as [|u].\n  { %s. }\n'
                       % (body.replace('%(u)d', str(u)) % dict(mid=mid)))
        return ''.join(out)

    def bbranches(body):
        out = []
        for u in range(b):
            if u < b - s:
                out.append('  destruct u as [|u].\n  { exfalso; lia. }\n')
                continue
            db = []
            for d in range(b - 1):
                rb = []
                for r in range(nA):
                    rb.append('      destruct r as [|r].\n      { %s. }\n'
                              % (body % dict(u=u, d=d, r=r, mid=mid)))
                db.append('    destruct d as [|d].\n    {\n%s      exfalso; lia.\n    }\n'
                          % ''.join(rb))
            out.append('  destruct u as [|u].\n  {\n%s    exfalso; lia.\n  }\n'
                       % ''.join(db))
        return ''.join(out)

    def fbranches(body):
        out = []
        for r in range(nF):
            pb = []
            for ph in range(nph):
                pb.append('    destruct ph as [|ph].\n    { %s. }\n'
                          % (body % dict(r=r, ph=ph, mid=mid)))
            out.append('  destruct r as [|r].\n  {\n%s    exfalso; lia.\n  }\n'
                       % ''.join(pb))
        return ''.join(out)

    fvis = ''.join('  destruct r as [|r].\n  { destruct t as [q s]; destruct q, s; '
                   'try (exfalso; apply Hnp; simpl; tauto); '
                   'vm_compute; reflexivity. }\n' for _ in range(nF))
    L.append(THM % dict(
        mid=mid, nph=nph, n0i=n0i, sti=sti, n0f=n0f, stf=stf, pv=pv,
        chg='change (fm_step FAM) with %d in *; change (fm_b FAM) with %d in *.'
            % (s, b),
        asound=abranches(reach('aarm%(u)d')),
        acomp=abranches('vm_compute; reflexivity'),
        bsound=bbranches(reach('barm%(u)d_%(d)d_%(r)d')),
        bcomp=bbranches('vm_compute; reflexivity'),
        fsound=fbranches(reach('farm%(r)d_%(ph)d')),
        fcomp=fbranches('vm_compute; reflexivity'),
        flia=fbranches('vm_compute; lia'),
        fvis=fvis))
    L.append(BOOTL % dict(mid=mid, t0=cd['t0'], ds0=clist(cd['ds0'], str),
                          ph0=ph0,
                          tmb=('tm_%s' % mid) if E.TR_QH is not None else 'tm'))

    def pharg(body):
        out = ['  - intros ph Hph.\n']
        for _ in range(nph):
            out.append('    destruct ph as [|ph].\n    { %s. }\n' % body)
        out.append('    exfalso; lia.\n')
        return ''.join(out)

    hcyc = ''.join(['  - intros ph Hph.\n']
                   + ['    destruct ph as [|ph].\n'
                      '    { exists %d; vm_compute; reflexivity. }\n' % k
                      for k in cd['kcyc']]
                   + ['    exfalso; lia.\n'])
    args = ''.join([
        '  - vm_compute; lia.\n',                       # Hb
        '  - vm_compute; reflexivity.\n',               # Hcode
        '  - vm_compute; lia.\n',                       # Hs0
        '  - vm_compute; reflexivity.\n',               # Hbs
        pharg('vm_compute; repeat constructor'),        # Hfpre
        pharg('vm_compute; repeat constructor'),        # Hfsuf
        pharg('vm_compute; lia'),                       # Hfmid
        pharg('vm_compute; lia'),                       # Hfs
        pharg('vm_compute; lia'),                       # Hfto
        pharg('vm_compute; reflexivity'),               # Hfmids
        pharg('vm_compute; reflexivity'),               # Hfres
        pharg('vm_compute; split; [lia | split; [lia | reflexivity]]'),  # Hutop
        '  - lia.\n',                                   # Hpv
        hcyc,                                           # Hcyc
        '  - exact fm12_%s.\n' % mid,
        '  - repeat constructor.\n',                    # Hbnd0
        '  - vm_compute; lia.\n',                       # Hlen0
        '  - lia.\n',                                   # Hph0
        '  - vm_compute; reflexivity.\n',               # Hres0
        '  - exact aarm_reach_%s.\n' % mid,
        '  - exact aarm_lhs_%s.\n' % mid,
        '  - exact aarm_rhs_%s.\n' % mid,
        '  - lia.\n',                                   # Hsti
        '  - exact barm_reach_%s.\n' % mid,
        '  - exact barm_lhs_%s.\n' % mid,
        '  - exact barm_rhs_%s.\n' % mid,
        '  - lia.\n',                                   # Hstf
        '  - exact farm_reach_%s.\n' % mid,
        '  - exact farm_lhs_%s.\n' % mid,
        '  - exact farm_rhs_%s.\n' % mid,
        '  - exact nrules_sound_%s.\n' % mid,
        '  - exact vis_ok_%s.\n' % mid,
    ])
    common = dict(mid=mid, t0=cd['t0'], ds0=clist(cd['ds0'], str), ph0=ph0,
                  nph=nph, pv=pv, n0i=n0i, sti=sti, n0f=n0f, stf=stf, args=args)
    L.append((QH if E.TR_QH is not None else NQH) % common)
    return ''.join(L), cd


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cert')
    ap.add_argument('-o', '--out', required=True)
    ap.add_argument('--qh', action='store_true')
    ap.add_argument('--scan', default=os.path.join(HERE, '..', '..', '..',
                                                   'censustr_v9_scan_1e8.txt'))
    args = ap.parse_args()
    cert = json.load(open(args.cert))
    if isinstance(cert, list):
        cert = cert[0]
    E.emit_closure = emit_closure_step
    if args.qh:
        row = None
        for l in open(args.scan):
            if l.startswith(cert['spec'] + ' '):
                row = l.split()[1:]
                break
        E.TR_PINS, lastf = E.quiet_pins(cert['spec'], row)
        t0, ds, ph, cells = E.qh_boot(cert, lastf)
        cert['boot'] = dict(cert['boot'], steps_from_blank=t0,
                            digits_lsb_first=ds, phase=ph, cells=cells)
        E.TR_QH = t0
    else:
        E.TR_PINS = E.unfired(cert['spec'], 10 ** 6)
    good, bad, cd = E.emit(cert, args.out)
    print('%s: closure %s' % (args.out, 'BUILT' if cd else 'not built'))
    return 0 if cd else 1


if __name__ == '__main__':
    sys.exit(main())
