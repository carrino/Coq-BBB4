#!/usr/bin/env python3
"""UNTRUSTED emitter: the QUAD/QUAD rows -- linear-search-carry counters.

WAVE26 section 7 characterised the 41 QUAD/QUAD rows of the `no interior
chain` bucket as ONE shape: a binary increment whose carry is done by linear
search, one round trip per digit, so the lap makes Theta(j) micro excursions
and no single LapDecider chain reaches it at any framing.  Each micro lap IS
a chain (2-3 window steps, counts affine in the probe index), and the
composition theorem is [Counters/QuadGlue.quad_lap] (MeasureGlue.mrun at
abstract state (probe depth k, unprobed count m)).

This emitter reads the shape off the measured restore points (quad_probe's
marks), derives the NINE chains a board needs --

    BOOT1 / BOOT0 / BOOTO   anchor -> M(0)   (interior j>=1 / j=0 / overflow)
    MC1p / MC0p             the micro hop at k = S k' (landing on a digit /
                            on the stop cell)
    MC1z / MC0z             the micro hop at k = 0
    TCp / TCz               the carry-and-clear terminal at k = S k' / k = 0

-- validates EVERY lap differentially against the raw simulator (exact
restore configurations, exact totals, j = 2..10, interior AND overflow), and
renders the QMG_* board: the two-index family [Cq W k m] with the deep word
W opaque, the hop and terminal lemmas by cden bridges, [quad_lap] for the
composition, and the [glue_neverqh_lift] close.

SCOPE: the single-class anchor-pivot machines with a 1-cell stride (the Kp
cluster).  The parity-class and 2-cell-stride machines (Bp, Alph_00_10_1)
need per-parity chain pairs and rep-rotation glue; measured but not wired.

Usage
  quad_emit.py --spec SPEC [--emit]
  quad_emit.py --list FILE [--emit] [--json OUT]
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

import emit_lapcert as EL                                          # noqa: E402
from emit_lapcert import ENCDATA, ENC, confs, eqlift, sim, coqc    # noqa: E402
from emit_interleave import (parse, LAB, ST, SYM, mach_id,         # noqa: E402
                             coq_table, clist)
from mirror_common import mirror_spec, mirrorize                   # noqa: E402
import lapcert as LC                                               # noqa: E402
import quad_probe as QP                                            # noqa: E402

PREFIX = 'QMG'
OUTDIR = os.path.join(REPO, 'theories', 'Machines', 'Counters')


class QuadEmitError(Exception):
    pass


def _cfgs_at(tab, cfg0, times):
    """Raw configurations at the given step indices."""
    want = sorted(set(times))
    out, cfg = {}, cfg0
    for t in range(want[-1] + 1):
        if t in want:
            out[t] = cfg
        if t < want[-1]:
            cfg = LC.wstep(tab, False, False, cfg)
    return [out[t] for t in times]


def _flat(cells):
    return (tuple(cells), (), 0, 0, ())


def _den(side, j):
    pre, u, a, b, post = side
    return tuple(pre) + tuple(u) * (a * j + b) + tuple(post)


def _denc(sc, j):
    q, ls, h, rs = sc
    return (q, _den(ls, j), h, _den(rs, j))


def _chain(tab, els, src, dst):
    for el in els:
        ch = None
        try:
            ch = LC.derive_chain(tab, el, True, src, dst)
        except Exception:                                          # noqa: BLE001
            ch = None
        if ch is not None:
            rn = LC.srun(tab, el, True, ch, src)
            if rn is not None and rn[0] == dst:
                return ch, el, (rn[1], rn[2])
    return None, None, None


def extract(spec):
    """The whole law as concrete sconf endpoints + derived chains."""
    law = QP.read_law(spec)
    if law['mode'] != (-1, False):
        raise QuadEmitError('mode %r (deep-pivot / rightward) not wired'
                            % (law['mode'],))
    for cl in ('micro', 'term', 'ovf', 'bootint', 'bootovf'):
        if len(law[cl]) != 1:
            raise QuadEmitError('parity classes (%s) not wired' % cl)
    if law['nint'] != (1, 1) or law['novf'] != (1, 2):
        raise QuadEmitError('mark-count law %r/%r not the plain ladder'
                            % (law['nint'], law['novf']))
    A = law['anchor']
    tab = parse(A['dspec'])
    d = ENCDATA[A['enc']]
    if len(d['uS']) != 1:
        raise QuadEmitError('%s: 2-cell stride not wired' % A['enc'])
    tail, far = tuple(A['tail']), tuple(A['far'])
    uS, sS, uD, sD = (tuple(d[k]) for k in ('uS', 'sS', 'uD', 'sD'))

    # mark configurations at two adjacent J, interior and overflow
    J0 = 6
    shapes = {}
    for J, ovf in ((J0, False), (J0 + 1, False), (J0, True)):
        p = QP.overflow_p(J) if ovf else QP.interior_p(J)
        T, marks, _ = QP.lap_marks(tab, A, p, law['mode'])
        marks = [m for m in marks if m[1] == law['qr'][0]]
        nm = J + 2 if ovf else J + 1
        if len(marks) != nm:
            raise QuadEmitError('%d marks at J=%d ovf=%s, want %d'
                                % (len(marks), J, ovf, nm))
        cfg0 = QP.anchor_cfg(A, p)
        cfgs = _cfgs_at(tab, cfg0, [t for (t, _, _) in marks])
        end = _cfgs_at(tab, cfg0, [T])[0]
        shapes[(J, ovf)] = (marks, cfgs, end, T)

    marks, cfgs, endc, T = shapes[(J0, False)]
    # the pieces, off the interior marks at J0
    qr = law['qr'][0]
    lus = [tuple(c[1]) for c in cfgs]
    d1 = len(lus[0]) - len(lus[1])
    LU = lus[0][:d1]
    if any(lus[k][d1:] != lus[k + 1]
           or lus[k][:d1] != LU for k in range(len(lus) - 2)):
        raise QuadEmitError('left sides do not slide by one unit')
    if lus[-2][len(lus[-2]) - len(lus[-1]):] != lus[-1]:
        raise QuadEmitError('the stop slide does not nest')
    W = lus[-1]                        # the deep word at m = 0
    LSTOP = lus[-2][:len(lus[-2]) - len(W)]
    HH = {c[2] for c in cfgs[:-1]}
    if len(HH) != 1:
        raise QuadEmitError('head symbol varies across the ladder')
    HH = HH.pop()
    HSTOP = cfgs[-1][2]
    rs = [tuple(c[3]) for c in cfgs]
    # READ THE LANDING, NOT ITS PADDING (WAVE27 section 2, WAVE28 section 5).
    # rs[0] is the ladder's FIRST rung and the cell past it has not been
    # written yet, so it is one trailing BLANK short of rep RU 0 ++ RPOST.
    # Taking the stride off rs[0]/rs[1] then reads RU two cells wide and the
    # test fails on every rung; take it off two rungs that are both fully
    # written, and compare up to trailing blanks the way the rest of this
    # emitter does.
    if len(rs) < 3:
        raise QuadEmitError('ladder too short to read the right stride')
    d2 = len(rs[2]) - len(rs[1])
    RU = rs[2][:d2]
    RPOST = rs[1][d2:]
    for k, r in enumerate(rs):
        if LC.rstrip0(r) != LC.rstrip0(RU * k + RPOST):
            raise QuadEmitError('right sides are not rep RU k ++ RPOST')
    if LU != uS or LSTOP != sS:
        raise QuadEmitError('probe unit %r/%r vs alphabet %r/%r'
                            % (LU, LSTOP, uS, sS))
    if {c[0] for c in cfgs} != {qr}:
        raise QuadEmitError('mark states vary')

    # the interior deep word must be E q0 ++ tail (here q0's encoding is
    # opaque -- just check the prefix relation via the anchor)
    p = QP.interior_p(J0)
    word = tuple(A['encf'](p)) + tail
    if word != HH_word(LU, J0, sS, W, HH):
        raise QuadEmitError('anchor word %r does not match ladder %r'
                            % (word, (LU, sS, W)))

    # the overflow shapes
    markso, cfgso, endo, To = shapes[(J0, True)]
    Wovf = tuple(cfgso[-1][1])
    if tuple(cfgso[0][1]) != LU * J0 + LSTOP + Wovf:
        raise QuadEmitError('overflow ladder does not share LU/LSTOP')
    if cfgso[0][2] != HH or cfgso[-1][2] != HSTOP:
        raise QuadEmitError('overflow head symbols differ')

    # the terminal landing: sconf against the lap-end configuration
    # reached left = rep uD j ++ SDW ++ W (exact), right = TFAR
    lend = tuple(endc[1])
    sdw = lend[len(uD) * J0:len(lend) - len(W)]
    if lend != uD * J0 + sdw + W:
        raise QuadEmitError('terminal landing %r not rep uD j ++ x ++ W'
                            % (lend,))
    TFAR = tuple(endc[3])
    if endc[0] != A['st0'] or endc[2] != 0:
        raise QuadEmitError('terminal lands off-anchor')
    lendo = tuple(endo[1])
    if lendo != uD * (J0 + 1) + sdw + Wovf or tuple(endo[3]) != TFAR:
        raise QuadEmitError('overflow terminal landing differs: %r'
                            % (lendo,))

    F = (far, (), 0, 0, ())
    E0 = ((), (), 0, 0, ())

    # ------------------------------------------------------- the chains ---
    chains = {}

    def want(name, els, src, dst):
        ch, el, c = _chain(tab, els, src, dst)
        if ch is None:
            raise QuadEmitError('no %s chain' % name)
        chains[name] = dict(ch=ch, el=el, c=c, src=src, dst=dst)

    # micro hops (peeled, index k')
    want('MC1p', (False,),
         (qr, _flat(LU), HH, (RU, RU, 1, 0, RPOST)),
         (qr, E0, HH, (RU, RU, 1, 1, RPOST)))
    want('MC0p', (False,),
         (qr, _flat(LSTOP), HH, (RU, RU, 1, 0, RPOST)),
         (qr, E0, HSTOP, (RU, RU, 1, 1, RPOST)))
    # micro hops at k = 0
    want('MC1z', (False,),
         (qr, _flat(LU), HH, _flat(RPOST)),
         (qr, E0, HH, _flat(RU + RPOST)))
    want('MC0z', (False,),
         (qr, _flat(LSTOP), HH, _flat(RPOST)),
         (qr, E0, HSTOP, _flat(RU + RPOST)))
    # terminal (peeled, index k')
    want('TCp', (False,),
         (qr, E0, HSTOP, (RU, RU, 1, 0, RPOST)),
         (A['st0'], ((), uD, 1, 1, sdw), 0, _flat(TFAR)))
    want('TCz', (False,),
         (qr, E0, HSTOP, _flat(RPOST)),
         (A['st0'], _flat(uD * 0 + sdw), 0, _flat(TFAR)))
    # boots
    want('BOOT1', (False, True),
         (A['st0'], (uS, uS, 1, 0, sS), 0, F),
         (qr, ((), LU, 1, 0, LSTOP), HH, _flat(RPOST)))
    want('BOOT0', (False, True),
         (A['st0'], (sS, (), 0, 0, ()), 0, F),
         (qr, E0, HSTOP, _flat(RPOST)))
    B0 = confs(A['enc'], A['st0'], tail, far)[2]
    want('BOOTO', (False, True),
         B0,
         (qr, ((), LU, 1, 0, LSTOP + Wovf), HH, _flat(RPOST)))

    D = dict(spec=spec, law=law, A=A, enc=A['enc'], tail=tail, far=far,
             qr=qr, LU=LU, LSTOP=LSTOP, HH=HH, HSTOP=HSTOP, RU=RU,
             RPOST=RPOST, SDW=sdw, TFAR=TFAR, Wovf=Wovf, chains=chains,
             uS=uS, sS=sS, uD=uD, sD=sD)

    ok, why = validate(tab, A, D)
    if not ok:
        raise QuadEmitError('validation: ' + why)
    D['val'] = why

    # bootstrap: reuse the anchor-times route
    from ovfshape import anchor_times
    at = anchor_times(A['dspec'], A['st0'], A['encf'], tail, far, 300,
                      4000000)
    if not at:
        raise QuadEmitError('no bootstrap anchor')
    p0 = min(at, key=lambda p: at[p])
    if p0 < 2:
        p0 = min((p for p in at if p >= 2), key=lambda p: at[p])
    D['p0'], D['boot'] = p0, at[p0]

    # visit witnesses: prefixes from the overflow anchor
    vis = {}
    bo = chains['BOOTO']
    for q in range(4):
        pre = LC.reach_state(tab, bo['el'], True, B0, bo['ch'], q)
        if pre is None:
            raise QuadEmitError('no visit witness for state %s' % LAB[q])
        vis[q] = pre
    D['vis'] = vis
    D['B0'] = B0
    return D


def HH_word(LU, J, sS, W, HH):
    """The anchor word reassembled from the ladder pieces: head cell + the
    slide."""
    return (HH,) + LU * (J - 1) + sS + W


def validate(tab, A, D, jlo=2, jhi=10):
    """Every lap, both branches: exact mark configurations against the
    two-index family, exact totals from the chain costs."""
    n = 0
    for j in range(jlo, jhi + 1):
        for ovf in (False, True):
            p = QP.overflow_p(j) if ovf else QP.interior_p(j)
            cfg = QP.anchor_cfg(A, p)
            nprobe = j + 1 if ovf else j
            W = D['Wovf'] if ovf else tuple(A['encf'](
                _upper(p, j))) + D['tail']
            # boot
            if nprobe == 0:
                bo = D['chains']['BOOT0']
                steps = bo['c'][1]
            elif ovf:
                bo = D['chains']['BOOTO']
                steps = bo['c'][0] * j + bo['c'][1]
            else:
                bo = D['chains']['BOOT1']
                steps = bo['c'][0] * (j - 1) + bo['c'][1]
            cfg = sim(tab, cfg, steps)
            tot = steps
            for k in range(nprobe + 1):
                m = nprobe - k
                want = _cq(D, W, k, m)
                if cfg != want:
                    return False, ('j=%d ovf=%s k=%d: %r want %r'
                                   % (j, ovf, k, cfg, want))
                if m > 0:
                    nm = 'MC%sz' % (1 if m > 1 else 0) if k == 0 else \
                         'MC%sp' % (1 if m > 1 else 0)
                    c = D['chains'][nm]['c']
                    steps = c[0] * (k - 1) + c[1] if k else c[1]
                    cfg = sim(tab, cfg, steps)
                    tot += steps
            nm = 'TCz' if nprobe == 0 else 'TCp'
            c = D['chains'][nm]['c']
            steps = c[0] * (nprobe - 1) + c[1] if nprobe else c[1]
            cfg = sim(tab, cfg, steps)
            tot += steps
            wantend = (A['st0'],
                       D['uD'] * nprobe + D['SDW'] + W, 0, D['TFAR'])
            if cfg != wantend:
                return False, 'j=%d ovf=%s end: %r want %r' % (
                    j, ovf, cfg, wantend)
            wanta = (A['st0'], tuple(A['encf'](p + 1)) + D['tail'], 0,
                     D['far'])
            if not eqlift(cfg, wanta):
                return False, 'j=%d ovf=%s anchor: %r want %r' % (
                    j, ovf, cfg, wanta)
            n += 1
    return True, ('%d laps, interior+overflow, exact marks and totals '
                  '(j=%d..%d)' % (n, jlo, jhi))


def _upper(p, j):
    """q0 with cview p = (j, Some q0)."""
    return p >> (j + 1)


def _cq(D, W, k, m):
    if m == 0:
        return (D['qr'], W, D['HSTOP'], D['RU'] * k + D['RPOST'])
    return (D['qr'], D['LU'] * (m - 1) + D['LSTOP'] + W, D['HH'],
            D['RU'] * k + D['RPOST'])


# ------------------------------------------------------------- rendering ---

def _fmtside(side):
    pre, u, a, b, post = side
    return 'mkS %s %s %d %d %s' % (clist(pre), clist(u), a, b, clist(post))


def _fmtconf(c):
    q, ls, h, rs = c
    return 'mkC %s (%s) %s (%s)' % (ST[q], _fmtside(ls), SYM[h], _fmtside(rs))


def cstep_str(st):
    if st[0] == 'SCycL':
        return 'SCycL %d %d' % (st[1], st[2])
    return '%s %d' % (st[0], st[1])


def cchain(ch):
    return '[' + '; '.join(cstep_str(s) for s in ch) + ']'


def _pad(base, n):
    out = base
    for _ in range(n):
        out = '(%s) ++ [S0]' % out
    return out


HEADER = r'''(** * QMG_@ID@: machine @SPEC@, boarded by CERTIFICATE (QUAD route).

    Auto-emitted by tools/counters/quad_emit.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  A linear-search-carry
    binary counter (WAVE26 section 7) under the @ENC@ alphabet: the interior
    lap makes Theta(j) micro excursions -- one round trip per digit -- so no
    single chain is the lap; each ROUND TRIP is a chain, and
    [Counters/QuadGlue.quad_lap] (MeasureGlue.mrun at abstract state
    (probe depth k, unprobed count m)) composes them into the quadratic lap.

      anchor    Cc p = (@ST0@, (@ENC@ p ++ @TAIL@, S0, @FAR@))
      family    Cq W k m: k probed digits right of the head, m unprobed
                behind it, the deep word W OPAQUE
      hop       Cq W k (S m) -> Cq W (S k) m   (chains MC*, exact)
      terminal  Cq W k 0 -> the incremented word (chains TC*, exact)

    The interior lap composes boot + j hops + terminal; the OVERFLOW lap is
    the SAME composition with j+1 probes (the carry lands on the tail cell).
    Both close up to [lift], so the closer is
    [LapCertGlueLift.glue_neverqh_lift].

    Differentially validated against the raw simulator -- @VAL@.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter JpCounter
                                  @ENCMOD@ LapCertGlue LapCertGlueLift
                                  MeasureGlue QuadGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_@ID@ (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_@ID@.

(** @SPEC@ *)
Definition tm_@ID@ : TM := fun q s => match q, s with
@TABLE@ end.
Local Notation tm := tm_@ID@.

Definition Cc_@ID@ (p : positive) : cconf := (@ST0@, (@ENC@ p ++ @TAIL@, S0, @FAR@)).
Local Notation Cc := Cc_@ID@.

(** The two-index probe family (WAVE26 7d): k probed digits, m unprobed,
    deep word W opaque. *)
Definition Cq_@ID@ (W : list Sym) (k m : nat) : cconf :=
  match m with
  | O => (@QR@, (W, @HSTOP@, rep @RU@ k ++ @RPOST@))
  | S m' => (@QR@, (rep @LU@ m' ++ @LSTOP@ ++ W, @HH@, rep @RU@ k ++ @RPOST@))
  end.
Local Notation Cq := Cq_@ID@.

(** ** The certificate: nine chains, all run by the kernel *)

@CHAINDEFS@

(** ** The micro hop *)

Lemma hop_@ID@ : forall W k m, exists n,
  csteps tm n (Cq W k (S m)) = Some (Cq W (S k) m) /\ 0 < n.
Proof.
  intros W k m.
  destruct m as [|m']; destruct k as [|k'].
  - (* k = 0, landing on the stop cell *)
    exists (@AMC0Z@ * 0 + @BMC0Z@). split; [|lia].
    change (Cq W 0 1) with (cden W [] 0 c_MC0z0_@ID@).
    rewrite (srun_sound tm false true ch_MC0z_@ID@ c_MC0z0_@ID@ c_MC0z1_@ID@
               @AMC0Z@ @BMC0Z@ run_MC0z_@ID@ W [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    reflexivity.
  - (* k = S k', landing on the stop cell *)
    exists (@AMC0P@ * k' + @BMC0P@). split; [|lia].
    assert (HS : Cq W (S k') 1 = cden W [] k' c_MC0p0_@ID@).
    { unfold Cq_@ID@, cden, c_MC0p0_@ID@, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * k' + 0) with k' by lia.
      cbn [rep app]. rewrite <- ?app_assoc. reflexivity. }
    rewrite HS.
    rewrite (srun_sound tm false true ch_MC0p_@ID@ c_MC0p0_@ID@ c_MC0p1_@ID@
               @AMC0P@ @BMC0P@ run_MC0p_@ID@ W [] k'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal; first
      [ reflexivity
      | unfold cden, c_MC0p1_@ID@, Cq_@ID@, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post];
        replace (1 * k' + 1) with (S k') by lia;
        cbn [rep app]; rewrite <- ?app_assoc; reflexivity ].
  - (* k = 0, landing on a digit *)
    exists (@AMC1Z@ * 0 + @BMC1Z@). split; [|lia].
    change (Cq W 0 (S (S m')))
      with (cden (rep @LU@ m' ++ @LSTOP@ ++ W) [] 0 c_MC1z0_@ID@).
    rewrite (srun_sound tm false true ch_MC1z_@ID@ c_MC1z0_@ID@ c_MC1z1_@ID@
               @AMC1Z@ @BMC1Z@ run_MC1z_@ID@ (rep @LU@ m' ++ @LSTOP@ ++ W) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    reflexivity.
  - (* k = S k', landing on a digit *)
    exists (@AMC1P@ * k' + @BMC1P@). split; [|lia].
    assert (HS : Cq W (S k') (S (S m'))
                 = cden (rep @LU@ m' ++ @LSTOP@ ++ W) [] k' c_MC1p0_@ID@).
    { unfold Cq_@ID@, cden, c_MC1p0_@ID@, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * k' + 0) with k' by lia.
      cbn [rep app]. rewrite <- ?app_assoc. reflexivity. }
    rewrite HS.
    rewrite (srun_sound tm false true ch_MC1p_@ID@ c_MC1p0_@ID@ c_MC1p1_@ID@
               @AMC1P@ @BMC1P@ run_MC1p_@ID@ (rep @LU@ m' ++ @LSTOP@ ++ W) [] k'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal; first
      [ reflexivity
      | unfold cden, c_MC1p1_@ID@, Cq_@ID@, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post];
        replace (1 * k' + 1) with (S k') by lia;
        cbn [rep app]; rewrite <- ?app_assoc; reflexivity ].
Qed.

(** ** The terminal: the carry write and the clearing sweep.  Its chain
    count is the FINAL probe depth k -- the anchor's carry index. *)

Lemma term_@ID@ : forall W k, exists n c',
  csteps tm n (Cq W k 0) = Some c'
  /\ c' = (@ST0@, (rep @UD@ k ++ @SDW@ ++ W, S0, @TFARL@)) /\ 0 < n.
Proof.
  intros W k. destruct k as [|k'].
  - exists (@ATCZ@ * 0 + @BTCZ@). eexists. split; [|split; [reflexivity | lia]].
    change (Cq W 0 0) with (cden W [] 0 c_TCz0_@ID@).
    rewrite (srun_sound tm false true ch_TCz_@ID@ c_TCz0_@ID@ c_TCz1_@ID@
               @ATCZ@ @BTCZ@ run_TCz_@ID@ W [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal; first
      [ reflexivity
      | unfold cden, c_TCz1_@ID@, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post];
        cbn [rep app]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity ].
  - exists (@ATCP@ * k' + @BTCP@). eexists.
    split; [|split; [reflexivity | lia]].
    assert (HS : Cq W (S k') 0 = cden W [] k' c_TCp0_@ID@).
    { unfold Cq_@ID@, cden, c_TCp0_@ID@, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * k' + 0) with k' by lia.
      cbn [rep app]. rewrite <- ?app_assoc. reflexivity. }
    rewrite HS.
    rewrite (srun_sound tm false true ch_TCp_@ID@ c_TCp0_@ID@ c_TCp1_@ID@
               @ATCP@ @BTCP@ run_TCp_@ID@ W [] k'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal; first
      [ reflexivity
      | unfold cden, c_TCp1_@ID@, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post];
        replace (1 * k' + 1) with (S k') by lia;
        cbn [rep app]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity ].
Qed.

(** ** The composed lap: boot + Theta(j) hops + terminal *)

Lemma qrun_@ID@ : forall W j, exists n c',
  csteps tm n (Cq W 0 j) = Some c'
  /\ lift c' = lift ((@ST0@, (rep @UD@ j ++ @SDW@ ++ W, S0, @TFARL@)) : cconf)
  /\ 0 < n.
Proof.
  intros W j.
  apply (quad_lap tm j (Cq_@ID@ W)).
  - intros k m _. exact (hop_@ID@ W k m).
  - intros k Hk. rewrite Nat.add_0_r in Hk. subst k.
    destruct (term_@ID@ W j) as (n & c' & Hrun & -> & Hn).
    exists n. eexists. split; [exact Hrun | split; [reflexivity | exact Hn]].
Qed.

(** ** The interior lap *)

Lemma lapi_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  destruct (@ENCMOD@.@SOME@ p j q0 E) as (H1 & H2).
  destruct j as [|j''].
  - (* j = 0: the boot lands directly on the stop cell *)
    destruct (qrun_@ID@ (@ENC@ q0 ++ @TAIL@) 0) as (n & c' & Hrun & Hl & Hn).
    exists ((@AB0@ * 0 + @BB0@) + n), c'. split; [lia|]. split.
    { rewrite csteps_add.
      assert (HB : Cc p = cden (@ENC@ q0 ++ @TAIL@) [] 0 c_BOOT00_@ID@).
      { unfold Cc_@ID@, cden, c_BOOT00_@ID@, sden;
          cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
        rewrite H1. cbn [rep app]. rewrite <- ?app_assoc. reflexivity. }
      rewrite HB.
      rewrite (srun_sound tm @ELB0@ true ch_BOOT0_@ID@ c_BOOT00_@ID@
                 c_BOOT01_@ID@ @AB0@ @BB0@ run_BOOT0_@ID@
                 (@ENC@ q0 ++ @TAIL@) [] 0 ltac:(@ELB0H@) ltac:(reflexivity)).
      assert (HQ : cden (@ENC@ q0 ++ @TAIL@) [] 0 c_BOOT01_@ID@
                   = Cq (@ENC@ q0 ++ @TAIL@) 0 0).
      { unfold cden, c_BOOT01_@ID@, Cq_@ID@, sden;
          cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
        cbn [rep app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity. }
      rewrite HQ. exact Hrun. }
    { rewrite Hl. unfold Cc_@ID@. rewrite H2. cbn [rep app].
      first [ reflexivity
            | rewrite <- ?app_assoc; cbn [app]; reflexivity ]. }
  - (* j = S j'': the boot lands on the first digit *)
    destruct (qrun_@ID@ (@ENC@ q0 ++ @TAIL@) (S j''))
      as (n & c' & Hrun & Hl & Hn).
    exists ((@AB1@ * j'' + @BB1@) + n), c'. split; [lia|]. split.
    { rewrite csteps_add.
      assert (HB : Cc p = cden (@ENC@ q0 ++ @TAIL@) [] j'' c_BOOT10_@ID@).
      { unfold Cc_@ID@, cden, c_BOOT10_@ID@, sden;
          cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
        replace (1 * j'' + 0) with j'' by lia.
        rewrite H1. cbn [rep app]. rewrite <- ?app_assoc. reflexivity. }
      rewrite HB.
      rewrite (srun_sound tm @ELB1@ true ch_BOOT1_@ID@ c_BOOT10_@ID@
                 c_BOOT11_@ID@ @AB1@ @BB1@ run_BOOT1_@ID@
                 (@ENC@ q0 ++ @TAIL@) [] j''
                 ltac:(@ELB1H@) ltac:(reflexivity)).
      assert (HQ : cden (@ENC@ q0 ++ @TAIL@) [] j'' c_BOOT11_@ID@
                   = Cq (@ENC@ q0 ++ @TAIL@) 0 (S j'')).
      { unfold cden, c_BOOT11_@ID@, Cq_@ID@, sden;
          cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
        replace (1 * j'' + 0) with j'' by lia.
        cbn [rep app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity. }
      rewrite HQ. exact Hrun. }
    { rewrite Hl. unfold Cc_@ID@. rewrite H2. cbn [rep app].
      first [ reflexivity
            | rewrite <- ?app_assoc; cbn [app]; reflexivity ]. }
Qed.

(** ** The overflow lap: the same ladder, one probe deeper *)

Lemma gso_@ID@ : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j c_BOOTO0_@ID@.
Proof.
  intros p j E. destruct (@ENCMOD@.@NONE@ p j E) as (H1 & _).
  unfold Cc_@ID@, cden, c_BOOTO0_@ID@, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  replace (1 * j + @OBSP@) with @CNTP@ by lia.
  rewrite H1; cbn [rep app].
  first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_@ID@ : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma lapo_@ID@ : forall p j, cview p = (S j, None) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j E.
  destruct (@ENCMOD@.@NONE@ p j E) as (_ & H2).
  destruct (qrun_@ID@ @WOVF@ (S j)) as (n & c' & Hrun & Hl & Hn).
  exists ((@ABO@ * j + @BBO@) + n), c'. split; [lia|]. split.
  { rewrite csteps_add.
    rewrite (gso_@ID@ p j E).
    rewrite (srun_sound tm @ELBO@ true ch_BOOTO_@ID@ c_BOOTO0_@ID@
               c_BOOTO1_@ID@ @ABO@ @BBO@ run_BOOTO_@ID@ [] [] j
               ltac:(@ELBOH@) ltac:(reflexivity)).
    assert (HQ : cden [] [] j c_BOOTO1_@ID@ = Cq @WOVF@ 0 (S j)).
    { unfold cden, c_BOOTO1_@ID@, Cq_@ID@, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * j + 0) with j by lia.
      cbn [rep app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity. }
    rewrite HQ. exact Hrun. }
  { rewrite Hl. unfold Cc_@ID@.
    assert (HG : @ENC@ (Pos.succ p) ++ @TAIL@ = @OVPAD@).
    { rewrite H2.
      first [ rewrite <- !app_assoc; reflexivity
            | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
    rewrite HG. @OVCLOSE@ }
Qed.

(** ** The full lap *)

Lemma lap_@ID@ : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E; destruct oq as [q0|].
  - destruct (lapi_@ID@ p j q0 E) as (n & c' & Hn & Hrun & Hl).
    exists n, c'. split; [exact Hrun | split; [exact Hl | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    destruct (lapo_@ID@ p j' E) as (n & c' & Hn & Hrun & Hl).
    exists n, c'. split; [exact Hrun | split; [exact Hl | exact Hn]].
Qed.

(** ** Bootstrap *)

Lemma boot_@ID@ : exists t0, stepn tm t0 InitES = Some (lift (Cc @P0@)).
Proof.
  exists @BOOT@.
  assert (H : match csteps tm @BOOT@ c0 with
              | Some c => ceqb c (Cc @P0@) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm @BOOT@ c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits: every state fires inside the overflow ladder *)

Lemma viso_@ID@ : forall (l : list lstep) (q : St),
  srun_st tm @ELBO@ true l c_BOOTO0_@ID@ = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc @ELBO@ true l c_BOOTO0_@ID@ p j [] []);
    [exact Hst | ltac:(intro; @ELBOH2@) | reflexivity
     | exact (gso_@ID@ p j E)].
Qed.

Lemma vis_@ID@ : forall p q,
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q.
  apply (vis_via_ovf_lift tm Cc lapi_@ID@ q).
  intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
  destruct q.
@VISITS@
Qed.

Theorem nqh_@ID@ : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc @P0@). - exact boot_@ID@. - intros p _. apply lap_@ID@. - intros p q _. apply vis_@ID@. Qed.

Theorem nonhalt_@ID@ : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_@ID@. Qed.
'''

CHAINDEF = r'''Definition c_%(n)s0_@ID@ : sconf := %(src)s.
Definition c_%(n)s1_@ID@ : sconf := %(dst)s.
Definition ch_%(n)s_@ID@ : list lstep := %(ch)s.

Lemma run_%(n)s_@ID@ : srun tm %(el)s true ch_%(n)s_@ID@ c_%(n)s0_@ID@ = Some (c_%(n)s1_@ID@, %(ca)d, %(cb)d).
Proof. vm_compute. reflexivity. Qed.'''


def render_quad(D):
    spec = D['A']['dspec']              # the table every lemma runs on
    ID = mach_id(spec)
    d = ENCDATA[D['enc']]
    A = D['A']

    chaindefs = []
    for n, c in D['chains'].items():
        chaindefs.append(CHAINDEF % dict(
            n=n, src=_fmtconf(c['src']), dst=_fmtconf(c['dst']),
            ch=cchain(c['ch']), el='true' if c['el'] else 'false',
            ca=c['c'][0], cb=c['c'][1]))

    # the overflow close: the reached word rep uD (S j) ++ SDW ++ Wovf vs
    # the anchor's rep uD (S j) ++ soD ++ tail -- trailing blanks only
    wanttl = tuple(d['soD']) + D['tail']
    gottl = D['SDW'] + D['Wovf']
    npad = len(wanttl) - len(gottl)
    if (npad < 0 or wanttl[:len(gottl)] != gottl
            or any(wanttl[len(gottl):])):
        raise QuadEmitError('overflow close %r vs %r' % (gottl, wanttl))
    ovpad = _pad('rep @UD@ (S j) ++ %s' % clist(gottl), npad)
    ovclose = ('rewrite !lbl_@ID@. ' if npad else '') + 'reflexivity.'
    # the exact-close template needs the terminal to land on the anchor's
    # own far side and the interior tail verbatim
    if D['TFAR'] != D['far']:
        raise QuadEmitError('terminal far %r vs %r not wired'
                            % (D['TFAR'], D['far']))
    if D['SDW'] != D['sD']:
        raise QuadEmitError('stop-digit landing %r vs sD %r not wired'
                            % (D['SDW'], D['sD']))

    vis = []
    for q in range(4):
        pre = D['vis'][q]
        if not pre:
            vis.append('  - (* %s: the anchor state *)\n'
                       '    rewrite (gso_%s p1 j1 E1).\n'
                       '    exists 0. eexists. split; reflexivity.'
                       % (ST[q], ID))
        else:
            vis.append('  - (* %s *)\n'
                       '    exact (viso_%s %s %s\n'
                       '             ltac:(vm_compute; reflexivity) p1 j1 E1).'
                       % (ST[q], ID, cchain(pre), ST[q]))

    ch = D['chains']
    reps = {
        '@ID@': ID, '@SPEC@': spec,
        '@ENC@': d.get('fn', D['enc']),
        '@ENCMOD@': d['mod'], '@SOME@': d['some'], '@NONE@': d['none'],
        '@ST0@': ST[A['st0']], '@TAIL@': clist(D['tail']),
        '@FAR@': clist(D['far']), '@TABLE@': coq_table(spec),
        '@QR@': ST[D['qr']], '@HH@': SYM[D['HH']], '@HSTOP@': SYM[D['HSTOP']],
        '@LU@': clist(D['LU']), '@LSTOP@': clist(D['LSTOP']),
        '@RU@': clist(D['RU']), '@RPOST@': clist(D['RPOST']),
        '@UD@': clist(D['uD']), '@SDW@': clist(D['SDW']),
        '@TFARL@': clist(D['TFAR']),
        '@WOVF@': clist(D['Wovf']),
        '@CHAINDEFS@': '\n\n'.join(chaindefs),
        '@OBSP@': str(d['obS'] - 1 if d['obS'] >= 1 else 0),
        '@CNTP@': 'j' if d['obS'] >= 1 else 'j',
        '@OVPAD@': ovpad, '@OVCLOSE@': ovclose,
        '@P0@': str(D['p0']), '@BOOT@': str(D['boot']),
        '@VISITS@': '\n'.join(vis),
        '@VAL@': D['val'],
    }
    for n in ('MC1p', 'MC0p', 'MC1z', 'MC0z', 'TCp', 'TCz'):
        key = n.upper()
        reps['@A%s@' % key] = str(ch[n]['c'][0])
        reps['@B%s@' % key] = str(ch[n]['c'][1])
        reps['@C%s@' % key] = str(ch[n]['c'][1])
    reps['@AB0@'] = str(ch['BOOT0']['c'][0])
    reps['@BB0@'] = str(ch['BOOT0']['c'][1])
    reps['@CB0@'] = str(ch['BOOT0']['c'][1])
    reps['@AB1@'] = str(ch['BOOT1']['c'][0])
    reps['@BB1@'] = str(ch['BOOT1']['c'][1])
    reps['@ABO@'] = str(ch['BOOTO']['c'][0])
    reps['@BBO@'] = str(ch['BOOTO']['c'][1])
    for n, hole in (('BOOT0', 'ELB0'), ('BOOT1', 'ELB1'), ('BOOTO', 'ELBO')):
        el = ch[n]['el']
        reps['@%s@' % hole] = 'true' if el else 'false'
        reps['@%sH@' % hole] = 'reflexivity' if el else 'discriminate'
        reps['@%sH2@' % hole] = 'reflexivity' if el else 'discriminate'

    out = HEADER
    for _ in range(4):
        for k, v in reps.items():
            out = out.replace(k, v)
    return out


def process(spec, do_emit, force=False):
    try:
        D = extract(spec)
    except (QuadEmitError, QP.QuadError, LC.Halt) as e:
        return dict(spec=spec, ok=False, why=str(e))
    except Exception as e:                                        # noqa: BLE001
        return dict(spec=spec, ok=False, why='%s: %s' % (type(e).__name__, e))
    info = dict(spec=spec, ok=True, enc=D['enc'],
                mirror=D['A']['mirror'])
    if not do_emit:
        return info
    path = os.path.join(OUTDIR, '%s_%s.v' % (PREFIX, mach_id(spec)))
    if os.path.exists(path) and not force:
        info.update(file=path, skipped=True)
        return info
    try:
        src = render_quad(D)
        if D['A']['mirror']:
            src = mirrorize(src, spec, D['A']['dspec'])
    except (QuadEmitError, RuntimeError) as e:
        return dict(spec=spec, ok=False, why='render: %s' % e)
    open(path, 'w').write(src)
    ok, log = coqc(os.path.relpath(path, REPO))
    if not ok:
        os.remove(path)
        lg = [x for x in log.strip().splitlines() if x.strip()]
        return dict(spec=spec, ok=False,
                    why='coqc: ' + (lg[-1] if lg else '?'))
    info['file'] = path
    return info


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list')
    ap.add_argument('--spec')
    ap.add_argument('--emit', action='store_true')
    ap.add_argument('--json')
    ap.add_argument('--force', action='store_true')
    a = ap.parse_args()

    if a.list:
        specs = [x.split()[0] for x in open(a.list) if x.strip()]
    else:
        specs = [a.spec]
    res, nok = [], 0
    for i, spec in enumerate(specs):
        r = process(spec, a.emit, a.force)
        res.append(r)
        nok += bool(r['ok'])
        print('%3d/%d %-40s %s' % (
            i + 1, len(specs), spec,
            'OK %s%s' % (r['enc'], '/mirror' if r.get('mirror') else '')
            if r['ok'] else 'no: %s' % r['why'][:110]), flush=True)
    print('\n%d / %d boarded' % (nok, len(specs)))
    if a.json:
        json.dump(res, open(a.json, 'w'), indent=1)


if __name__ == '__main__':
    main()
