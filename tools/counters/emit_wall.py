#!/usr/bin/env python3
"""UNTRUSTED emitter for WALL-LAP interleaved counters (the W-Ip shape).

The wall-lap family (WAVE11_MIRROR.md section 2, WALLLAP_NOTE.md): the
counter holds a small fixed WALL on the far side; every lap crosses the
wall, blanks it, and rebuilds it one cell further out before closing back
(lift-equal up to far blanks).  This emitter covers the dominant shape --
Ip flip anchors with tail [S1;S0]:

  Cc p = (E, Ip p ++ [S1;S0], S0, FW)     FW = the wall word (fixed)

  interior : P1w (right-open bounce THROUGH the wall) .
             RIP^(2j+cR) (1-cell) . STPI . TRN .
             RET^(j+cT) ([S1;S1]->[S0;S1]) .
             FINw (right-open close rebuilding the wall)
  overflow : P1w . RIP^(2j'+cRo) . STPO (left-open, off the deep edge) .
             RET^(j'+cTo) . FINw2

Both branches are AFFINE (no inner counter -- machines whose overflow is
exponential fail the overflow derive here and stay in the IXP wall-inner
bucket).  Laps close up to trailing far blanks (lift), so no exactness is
needed anywhere: [glue_neverqh] takes lift-equal laps, and the visit
witnesses are chain prefixes on whichever [cview] branch p is in.

Everything here is UNTRUSTED: the Coq kernel re-checks every board.

Usage
  emit_wall.py --list FILE [--emit] [--mirror] [--json OUT]
"""
import argparse
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

from executor import Exec, Wall                                    # noqa: E402
from emit_interleave import (Raw, strip0, LAB, ST, SYM, ENC, parse,  # noqa: E402
                             DeriveError, derive_tail_far, mach_id,
                             coq_table, clist, ccons, cwin)
from emit_shape4 import conc, cycl, cycr, m_int, nrm                 # noqa: E402
from mirror_common import mirror_spec, mirrorize                     # noqa: E402

Ip = ENC['Ip']
OUTDIR = os.path.join(REPO, 'theories', 'Machines', 'Counters')
TAIL = [1, 0]


def j_of(v):
    j = 0
    while (v >> j) & 1:
        j += 1
    return j


def cc(E, p, FW):
    return (E, Ip(p) + TAIL, 0, list(FW))


def raw_lap(spec, E, FW, m, maxsteps=300000):
    raw = Raw(spec)
    cfg = cc(E, m, FW)
    tgt = nrm(cc(E, m + 1, FW))
    for t in range(1, maxsteps):
        cfg = raw.step(cfg)
        if cfg is None:
            return None
        if nrm(cfg) == tgt:
            return t
    return None


# ---------------------------------------------------------- chain replays ----
def replay_int(ex, E, FW, m, j, s):
    cfg = cc(E, m, FW)
    U = {}
    cfg, U['P1w'] = conc(ex, cfg, True, False, s['nP1'], 0, None)
    ones = 0
    while ones < len(cfg[1]) and cfg[1][ones] == 1:
        ones += 1
    kr = ones + 1            # ripple runs through the ones AND the clear bit
    cfg, u = cycl(ex, cfg, 1, s['nRIP'], ones)
    if u:
        U['RIP'] = u
    cfg, U['STPI'] = conc(ex, cfg, True, True, s['nSTP'], 1, 0)
    cfg, U['TRN'] = conc(ex, cfg, True, True, s['nTRN'], 0, 1)
    pairs = 0
    while (2 * pairs + 1 < len(cfg[3]) and cfg[3][2 * pairs] == 1
           and cfg[3][2 * pairs + 1] == 1):
        pairs += 1
    cfg, u = cycr(ex, cfg, 2, s['nRET'], pairs)
    if u:
        U['RET'] = u
    U['kr'] = ones
    U['kt'] = pairs
    cfg, U['FINw'] = conc(ex, cfg, True, False, s['nFIN'], s['lwF'], None)
    n = (s['nP1'] + s['nRIP'] * ones + s['nSTP'] + s['nTRN']
         + s['nRET'] * pairs + s['nFIN'])
    return cfg, n, U


def replay_ov(ex, E, FW, m, jp, s):
    cfg = cc(E, m, FW)
    U = {}
    cfg, U['P1wo'] = conc(ex, cfg, True, False, s['nP1'], 0, None)
    ones = 0
    while ones < len(cfg[1]) and cfg[1][ones] == 1:
        ones += 1
    ko = ones + s.get('dRO', 0)
    cfg, u = cycl(ex, cfg, 1, s['nRIP'], ko)
    if u:
        U['RIPo'] = u
    cfg, U['STPO'] = conc(ex, cfg, False, True, s['nSTPO'], None, 0)
    pairs = 0
    while (2 * pairs + 1 < len(cfg[3]) and cfg[3][2 * pairs] == 1
           and cfg[3][2 * pairs + 1] == 1):
        pairs += 1
    cfg, u = cycr(ex, cfg, 2, s['nRET'], pairs)
    U['kro'] = ko
    U['kto'] = pairs
    cfg, U['FINw2'] = conc(ex, cfg, True, False, s['nFIN2'], s['lwF2'], None)
    n = (s['nP1'] + s['nRIP'] * ko + s['nSTPO'] + s['nRET'] * pairs
         + s['nFIN2'])
    return cfg, n, U


# -------------------------------------------------------------- derivation ---
def affine2(pts):
    js = sorted(pts)
    if len(js) < 2:
        return None
    if (pts[js[1]] - pts[js[0]]) % (js[1] - js[0]):
        return None
    b = (pts[js[1]] - pts[js[0]]) // (js[1] - js[0])
    a = pts[js[0]] - b * js[0]
    return (a, b) if all(pts[j] == a + b * j for j in js) else None


def derive_interior(spec, E, FW):
    ex = Exec(spec)
    ints = {}
    for j in range(0, 4):
        m = m_int(j)
        n = raw_lap(spec, E, FW, m)
        if n is None:
            raise DeriveError('interior lap does not close (j=%d)' % j)
        ints[j] = n
    if affine2(ints) is None:
        raise DeriveError('interior laps not affine: %s' % ints)
    JI = 3
    m = m_int(JI)
    tgt = cc(E, m + 1, FW)
    for nP1 in range(1, 10):
        for nRIP in range(1, 4):
            for nSTP in range(1, 10):
                for nTRN in range(1, 6):
                    for nRET in range(1, 7):
                        for nFIN in range(1, 14):
                            for lwF in range(0, 4):
                                s = dict(nP1=nP1, nRIP=nRIP, nSTP=nSTP,
                                         nTRN=nTRN, nRET=nRET, nFIN=nFIN,
                                         lwF=lwF)
                                try:
                                    cfg, n, U = replay_int(ex, E, FW, m,
                                                           JI, s)
                                except (Wall, KeyError, IndexError):
                                    continue
                                if n == ints[JI] and cfg == tgt:
                                    return s, U
    raise DeriveError('no wall interior skeleton fits (%s)' % ints)


def derive_overflow(spec, E, FW, s):
    ex = Exec(spec)
    ovs = {}
    for K in range(2, 6):
        n = raw_lap(spec, E, FW, (1 << K) - 1)
        if n is None:
            raise DeriveError('overflow lap does not close (K=%d)' % K)
        ovs[K] = n
    if affine2(ovs) is None:
        raise DeriveError('overflow laps not affine: %s (inner-counter '
                          'machine?)' % ovs)
    KO = 4
    m = (1 << KO) - 1
    tgt = nrm(cc(E, m + 1, FW))
    for dRO in range(0, 3):
        for nSTPO in range(1, 14):
            for nFIN2 in range(1, 16):
                for lwF2 in range(0, 4):
                    s2 = dict(s, dRO=dRO, nSTPO=nSTPO, nFIN2=nFIN2,
                              lwF2=lwF2)
                    try:
                        cfg, n, U = replay_ov(ex, E, FW, m, KO, s2)
                    except (Wall, KeyError, IndexError):
                        continue
                    if n == ovs[KO] and nrm(cfg) == tgt:
                        return s2, U
    raise DeriveError('no wall overflow skeleton fits (%s)' % ovs)


def check_shapes(E, FW, s, U):
    """The W-Ip template needs exactly these window shapes and counts."""
    msgs = []
    (Pe, Px) = U['P1w']
    (Re, Rx) = U['RIP']
    (Se, Sx) = U['STPI']
    (Ne, Nx) = U['TRN']
    (Te, Tx) = U['RET']
    (Fe, Fx) = U['FINw']
    (Oe, Ox) = U['STPO']
    (Ge, Gx) = U['FINw2']
    Erip = Px[0]
    QR = Nx[0]
    P1R = list(Px[3])
    if Pe != (E, (), 0, tuple(FW)) or Px[1:3] != ((1,), 1):
        msgs.append('P1w %s -> %s (need (E,[],0,FW)->(Erip,[S1],S1,w))'
                    % (Pe, Px))
    if Re != (Erip, (1,), 1, ()) or Rx != (Erip, (), 1, (1,)):
        msgs.append('ripple %s -> %s' % (Re, Rx))
    if Se != (Erip, (0,), 1, ()) or Sx != (Erip, (), 0, (1,)):
        msgs.append('interior stop %s -> %s' % (Se, Sx))
    if Ne != (Erip, (), 0, (1,)) or Nx != (QR, (1,), 1, ()):
        msgs.append('turn %s -> %s' % (Ne, Nx))
    if Te != (QR, (), 1, (1, 1)) or Tx != (QR, (0, 1), 1, ()):
        msgs.append('return %s -> %s' % (Te, Tx))
    if Fe != (QR, (0,), 1, tuple(P1R)) or Fx != (E, (), 0, tuple(FW)):
        msgs.append('close %s -> %s (need (QR,[S0],S1,P1R)->(E,[],0,FW))'
                    % (Fe, Fx))
    if Oe != (Erip, (0,), 1, ()) or Ox != (QR, (1,), 1, ()):
        msgs.append('overflow stop %s -> %s' % (Oe, Ox))
    if Ge != (QR, (), 1, tuple([1] + P1R)) or Gx[0] != E or Gx[2] != 0 \
            or Gx[1] != (1,):
        msgs.append('overflow close %s -> %s (need (QR,[],1,S1::P1R)->'
                    '(E,[S1],0,Fx))' % (Ge, Gx))
    FX2 = list(Gx[3])
    if FX2 + [0] != list(FW):
        msgs.append('overflow close far %s + blank != wall %s' % (FX2, FW))
    if (s['cR'], s['cT'], s['cRo'], s['cTo']) != (2, 1, 1, 0):
        msgs.append('count offsets (cR=%s cT=%s cRo=%s cTo=%s) not the '
                    'templated (2,1,1,0) -- a second wall shape'
                    % (s['cR'], s['cT'], s['cRo'], s['cTo']))
    return msgs, Erip, QR, P1R, FX2


def validate(spec, E, FW, s):
    ex = Exec(spec)
    for m in range(2, 200):
        j = j_of(m)
        if m == (1 << j) - 1:
            continue
        cfg, n, U = replay_int(ex, E, FW, m, j, s)
        if cfg != cc(E, m + 1, FW):
            raise DeriveError('interior m=%d: not EXACT' % m)
        if n != raw_lap(spec, E, FW, m):
            raise DeriveError('interior m=%d: step mismatch' % m)
        if U['kr'] != 2 * j + s['cR'] or U['kt'] != j + s['cT']:
            raise DeriveError('interior m=%d: counts drift (kr=%d kt=%d)'
                              % (m, U['kr'], U['kt']))
    for K in range(1, 8):
        m = (1 << K) - 1
        cfg, n, U = replay_ov(ex, E, FW, m, K - 1, s)
        if nrm(cfg) != nrm(cc(E, m + 1, FW)):
            raise DeriveError('overflow K=%d: misses anchor' % K)
        if n != raw_lap(spec, E, FW, m):
            raise DeriveError('overflow K=%d: step mismatch' % K)
        if U['kro'] != 2 * K + s['cRo'] or U['kto'] != K + s['cTo']:
            raise DeriveError('overflow K=%d: counts drift (kro=%d kto=%d)'
                              % (K, U['kro'], U['kto']))
    return True


def boot_probe(spec, E, FW, p0, maxT=100000):
    raw = Raw(spec)
    tgts = {p: nrm(cc(E, p, FW)) for p in range(max(p0, 1), max(p0, 1) + 9)}
    cfg = (0, [], 0, [])
    for t in range(maxT):
        c = nrm(cfg)
        for p, tgt in tgts.items():
            if c == tgt:
                return p, t
        cfg = raw.step(cfg)
        if cfg is None:
            raise DeriveError('halts during bootstrap at t=%d' % t)
    raise DeriveError('no bootstrap to Cc(%d..%d)' % (p0, p0 + 8))


# ------------------------------------------------------------------ visits ---
def visit_plan(spec, E, Erip, QR, FW, P1R, s):
    """Witness routes: the P1w-window prefix (uniform in p) or a deep
    overflow-chain position under the tovf induction."""
    ex = Exec(spec)
    tab = parse(spec)
    plan = {E: ('anchor',)}
    for q in range(4):
        if q in plan:
            continue
        found = None
        for t in range(1, s['nP1'] + 1):
            try:
                o = ex.wsteps(True, False, E, [], 0, list(FW), t)
            except Wall:
                break
            if o[0] == q:
                found = ('p1w', t, (o[0], tuple(o[1]), o[2], tuple(o[3])))
                break
        if found is None and q == QR:
            found = ('qr',)
        if found is None:
            e = tab.get((QR, 1))
            if e is not None and e[1] > 0 and e[2] == q:
                found = ('vc', e[0])
        if found is None:
            for t in range(1, s['nSTPO']):
                try:
                    o = ex.wsteps(False, True, Erip, [0], 1, [], t)
                except Wall:
                    break
                if o[0] == q:
                    found = ('stpo', t,
                             (o[0], tuple(o[1]), o[2], tuple(o[3])))
                    break
        if found is None:
            for t in range(1, s['nFIN2']):
                try:
                    o = ex.wsteps(True, False, QR, [], 1, [1] + list(P1R),
                                  t)
                except Wall:
                    break
                if o[0] == q:
                    found = ('fin2', t,
                             (o[0], tuple(o[1]), o[2], tuple(o[3])))
                    break
        if found is None:
            raise DeriveError('no visit witness for state %s' % LAB[q])
        plan[q] = found
    return plan


# ------------------------------------------------------------ Coq emission ---
HEAD_W = r'''(** * WLS_@ID@: wall-lap interleaved counter, machine @SPEC@.

    Auto-emitted by tools/counters/emit_wall.py (UNTRUSTED emitter; the Coq
    kernel re-checks every line below).  Left-growth counter under the
    DIRECT interleave encoding [Ip], holding a fixed WALL on the far side
    (WALLLAP_NOTE.md; WAVE11_MIRROR.md section 2):

      Cc p = (@EDGE@, (Ip p ++ [S1;S0], S0, @FW@))

    One lap crosses the wall, blanks it, ripples the carry, returns, and
    REBUILDS the wall:

      P1w  bounce through the wall (@NP1@ steps, right-open window);
      RIP  leftward 1-cell ripple (@NRIP@ step per cell; 2j+2 cells
           interior, 2j'+3 overflow);
      STPI/TRN  pop the clear bit and turn (interior);
      STPO overflow stop at the deep edge (@NSTPO@ steps);
      RET  rightward rewrite [S1;S1] -> [S0;S1] (@NRET@ steps per pair;
           j+1 pairs interior, j'+1 overflow);
      FINw interior close rebuilding the wall (@NFIN@ steps, EXACT) /
      FINw2 overflow close (@NFIN2@ steps; lands one left blank and one
           far blank short of the next anchor -- a [lift] close).

    The interior branch is EXACT, feeding the [tovf] well-founded
    induction that carries every deep visit witness to an overflow anchor.
    Derived by exact symbolic replay; validated against the raw simulator
    on BOTH cview branches (interior p = 2..199, overflow K = 1..7, step
    counts AND landings).  Axiom footprint:
    [functional_extensionality_dep] (via CTape.lift). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter JpCounter.
Import ListNotations.

Definition mk_@ID@ (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_@ID@.

(** @SPEC@ *)
Definition tm_@ID@ : TM := fun q s => match q, s with
@TABLE@ end.
Local Notation tm := tm_@ID@.

Definition Cc_@ID@ (p : positive) : cconf := (@EDGE@, (Ip p ++ [S1;S0], S0, @FW@)).
Local Notation Cc := Cc_@ID@.

(** ** The window units (each closed by [reflexivity]) *)
Lemma U_P1w_@ID@ : wsteps true false tm @NP1@ (@EDGE@,([],S0,@FW@)) = Some (@ERIP@,([S1],S1,@P1R@)). Proof. reflexivity. Qed.
Lemma U_RIP_@ID@ : wsteps true true tm @NRIP@ (@ERIP@,([S1],S1,[])) = Some (@ERIP@,([],S1,[S1])). Proof. reflexivity. Qed.
Lemma U_STPI_@ID@ : wsteps true true tm @NSTP@ (@ERIP@,([S0],S1,[])) = Some (@ERIP@,([],S0,[S1])). Proof. reflexivity. Qed.
Lemma U_TRN_@ID@ : wsteps true true tm @NTRN@ (@ERIP@,([],S0,[S1])) = Some (@QR@,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_RET_@ID@ : wsteps true true tm @NRET@ (@QR@,([],S1,[S1;S1])) = Some (@QR@,([S0;S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FINw_@ID@ : wsteps true false tm @NFIN@ (@QR@,([S0],S1,@P1R@)) = Some (@EDGE@,([],S0,@FW@)). Proof. reflexivity. Qed.
Lemma U_STPO_@ID@ : wsteps false true tm @NSTPO@ (@ERIP@,([S0],S1,[])) = Some (@QR@,([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FINw2_@ID@ : wsteps true false tm @NFIN2@ (@QR@,([],S1,S1::@P1R@)) = Some (@EDGE@,([S1],S0,@FX2@)). Proof. reflexivity. Qed.
@UVIS@
(** ** Transported phases *)
Lemma phP1w_@ID@ : forall L, csteps tm @NP1@ (@EDGE@,(L,S0,@FW@)) = Some (@ERIP@,(S1::L,S1,@P1R@)).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_P1w_@ID@). Qed.
Lemma phRIP_@ID@ : forall k L R, csteps tm (@NRIP@*k) (@ERIP@,(rep [S1] k ++ L,S1,R)) = Some (@ERIP@,(L,S1,rep [S1] k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP_@ID@ k L R) as H; cbn [app] in H; exact H. Qed.
Lemma phSTPI_@ID@ : forall L R, csteps tm @NSTP@ (@ERIP@,(S0::L,S1,R)) = Some (@ERIP@,(L,S0,S1::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI_@ID@). Qed.
Lemma phTRN_@ID@ : forall L R, csteps tm @NTRN@ (@ERIP@,(L,S0,S1::R)) = Some (@QR@,(S1::L,S1,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_TRN_@ID@). Qed.
Lemma phRET_@ID@ : forall k L R, csteps tm (@NRET@*k) (@QR@,(L,S1,rep [S1;S1] k ++ R)) = Some (@QR@,(rep [S0;S1] k ++ L,S1,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET_@ID@ k L R). Qed.
Lemma phFINw_@ID@ : forall L, csteps tm @NFIN@ (@QR@,(S0::L,S1,@P1R@)) = Some (@EDGE@,(L,S0,@FW@)).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_FINw_@ID@). Qed.
Lemma phSTPO_@ID@ : forall R, csteps tm @NSTPO@ (@ERIP@,([S0],S1,R)) = Some (@QR@,([S1],S1,R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO_@ID@). Qed.
Lemma phFINw2_@ID@ : forall L, csteps tm @NFIN2@ (@QR@,(L,S1,S1::@P1R@)) = Some (@EDGE@,(S1::L,S0,@FX2@)).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_FINw2_@ID@). Qed.
@PHVIS@
Lemma lift_lblank_@ID@ : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

(** ** The OUTER interior lap: EXACT *)
Lemma lap_int_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j q0 Ecv. unfold Cc_@ID@.
  destruct (cview_some_I p j q0 Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  + rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl.
    eapply csteps_chain. { apply phP1w_@ID@. }
    rewrite rep_slide, <- rep_dbl, pair_fold, rep_dbl.
    replace (2 * S j) with (S (S (2 * j))) by lia.
    eapply csteps_chain. { apply (phRIP_@ID@ (S (S (2 * j)))). }
    eapply csteps_chain. { apply phSTPI_@ID@. }
    eapply csteps_chain. { apply phTRN_@ID@. }
    change (rep [S1] (S (S (2 * j))) ++ @P1R@)
      with (S1 :: S1 :: rep [S1] (2 * j) ++ @P1R@).
    rewrite <- rep_dbl.
    change (S1 :: S1 :: rep [S1;S1] j ++ @P1R@)
      with (rep [S1;S1] (S j) ++ @P1R@).
    eapply csteps_chain. { apply (phRET_@ID@ (S j)). }
    change (rep [S0;S1] (S j) ++ S1 :: (Ip q0 ++ [S1;S0]))
      with (S0 :: S1 :: rep [S0;S1] j ++ S1 :: (Ip q0 ++ [S1;S0])).
    apply phFINw_@ID@.
  + rewrite HIs, <- app_assoc. cbn [app].
    change (rep [S1;S0] j ++ S1 :: S1 :: (Ip q0 ++ [S1;S0]))
      with (rep [S1;S0] j ++ [S1] ++ (S1 :: (Ip q0 ++ [S1;S0]))).
    rewrite app_assoc, pair_rot. reflexivity.
  + lia.
Qed.

(** ** The overflow lap: closes one left blank and one far blank short *)
Lemma lap_ov_@ID@ : forall p j', cview p = (S j', None) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j' Ecv. unfold Cc_@ID@.
  destruct (cview_none_I p j' Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  + rewrite HIp, <- app_assoc. cbn [app].
    rewrite rep_dbl.
    eapply csteps_chain. { apply phP1w_@ID@. }
    rewrite rep_slide, <- rep_dbl, pair_fold, rep_dbl.
    replace (2 * S j') with (S (S (2 * j'))) by lia.
    rewrite <- rep_slide.
    change (S1 :: rep [S1] (S (S (2 * j'))) ++ [S0])
      with (rep [S1] (S (S (S (2 * j')))) ++ [S0]).
    eapply csteps_chain. { apply (phRIP_@ID@ (S (S (S (2 * j'))))). }
    eapply csteps_chain. { apply phSTPO_@ID@. }
    replace (S (S (S (2 * j')))) with (2 * S j' + 1) by lia.
    rewrite rep_add, <- app_assoc, <- rep_dbl. cbn [rep app].
    eapply csteps_chain. { apply (phRET_@ID@ (S j')). }
    apply phFINw2_@ID@.
  + rewrite HIs, pair_rot.
    replace (@FW@) with (@FX2@ ++ [S0]) by reflexivity.
    rewrite lift_app_blank. cbn [app].
    replace (S1 :: rep [S0;S1] (S j') ++ S1 :: S0 :: nil)
      with ((S1 :: rep [S0;S1] (S j') ++ [S1]) ++ [S0])
      by (cbn [app]; rewrite <- app_assoc; reflexivity).
    rewrite lift_lblank_@ID@. reflexivity.
  + lia.
Qed.

Lemma lap_@ID@ : forall p, exists n c', csteps tm n (Cc p) = Some c' /\
  lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (lap_int_@ID@ p j q0 Ecv) as (n & c' & H1 & H2 & H3).
    exists n, c'. split; [exact H1|split; [rewrite H2; reflexivity|exact H3]].
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    exact (lap_ov_@ID@ p j' Ecv).
Qed.

Lemma boot_@ID@ : exists t0, stepn tm t0 InitES = Some (lift (Cc @P0@)).
Proof.
  exists @BOOT@.
  assert (H : match csteps tm @BOOT@ c0 with Some c => ceqb c (Cc @P0@) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm @BOOT@ c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits *)

@VISLEMMAS@
Lemma vis_@ID@ : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct q.
@VISCASES@
Qed.

Theorem nqh_@ID@ : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc @P0@). - exact boot_@ID@. - intros p _. apply lap_@ID@. - intros p q _. apply vis_@ID@. Qed.

Theorem nonhalt_@ID@ : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_@ID@. Qed.
'''



VIS_P1W = (
    '(** @QV@: @T@ steps from the anchor, inside the P1w window (uniform in p). *)\n'
    'Lemma vis_A@N@_@ID@ : forall p, exists k c, csteps tm k (Cc p) = Some c /\\ fst c = @QV@.\n'
    'Proof.\n'
    '  intro p. unfold Cc_@ID@. exists @T@. eexists. split.\n'
    '  - apply phVP@N@_@ID@.\n'
    '  - reflexivity.\n'
    'Qed.\n')

_OV_PREFIX = (
    '    + rewrite HIp, <- app_assoc. cbn [app].\n'
    '      rewrite rep_dbl.\n'
    '      eapply csteps_chain. { apply phP1w_@ID@. }\n'
    '      rewrite rep_slide, <- rep_dbl, pair_fold, rep_dbl.\n'
    '      replace (2 * S j\') with (S (S (2 * j\'))) by lia.\n'
    '      rewrite <- rep_slide.\n'
    '      change (S1 :: rep [S1] (S (S (2 * j\'))) ++ @P1R@)\n'
    '        with (rep [S1] (S (S (S (2 * j\')))) ++ @P1R@).\n'
    '      eapply csteps_chain. { apply (phRIP_@ID@ (S (S (S (2 * j\'))))). }\n')

VIS_DEEP = (
    '(** @QV@: reached inside the OVERFLOW lap; every p reduces to an\n'
    '    all-ones anchor by well-founded induction on [tovf] (the interior\n'
    '    laps close EXACTLY). *)\n'
    'Lemma vis_D@N@_@ID@ : forall p, exists k c, csteps tm k (Cc p) = Some c /\\ fst c = @QV@.\n'
    'Proof.\n'
    '  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.\n'
    '  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.\n'
    '  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].\n'
    '  - assert (Hnz : tovf p <> 0).\n'
    '    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }\n'
    '    destruct (lap_int_@ID@ p j q0 Ecv) as (n & c\' & Hrun & Hc\' & _). subst c\'.\n'
    '    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ p) eq_refl) as (k & c & Hk & Hq).\n'
    '    exists (n + k), c. rewrite csteps_add, Hrun. exact (conj Hk Hq).\n'
    '  - destruct j as [|j\'].\n'
    '    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }\n'
    '    destruct (cview_none_I p j\' Ecv) as (HIp & _).\n'
    '    unfold Cc_@ID@. eexists. eexists. split.\n'
    + _OV_PREFIX +
    '@DEEPTAC@\n'
    '    + reflexivity.\n'
    'Qed.\n')

DEEP_QR = '      apply phSTPO_@ID@.'

DEEP_VC = (
    '      eapply csteps_chain. { apply phSTPO_@ID@. }\n'
    '      change (rep [S1] (S (S (S (2 * j\')))) ++ @P1R@)\n'
    '        with (S1 :: rep [S1] (S (S (2 * j\'))) ++ @P1R@).\n'
    '      apply phVC_@ID@.')

DEEP_STPO = '      apply phVS@N@_@ID@.'

DEEP_FIN2 = (
    '      eapply csteps_chain. { apply phSTPO_@ID@. }\n'
    '      replace (S (S (S (2 * j\')))) with (2 * S j\' + 1) by lia.\n'
    '      rewrite rep_add, <- app_assoc, <- rep_dbl. cbn [rep app].\n'
    '      eapply csteps_chain. { apply (phRET_@ID@ (S j\')). }\n'
    '      apply phVF@N@_@ID@.')

PHVC = (
    'Lemma phVC_@ID@ : forall x L R, csteps tm 1 (@QR@,(L,S1,x::R)) = Some (@QVC@,(@WVC@::L,x,R)).\n'
    'Proof. intros. reflexivity. Qed.\n')


def render_vis(spec, E, Erip, QR, FW, P1R, s, plan):
    uvis, phvis, lemmas, cases = [], [], [], []
    na = nd = 0
    for q in range(4):
        kind = plan[q][0]
        if kind == 'anchor':
            cases.append('  - (* %s : the anchor state *)\n'
                         '    exists 0. eexists. split; reflexivity.' % ST[q])
        elif kind == 'p1w':
            na += 1
            t, ext = plan[q][1], plan[q][2]
            uvis.append(
                'Lemma U_VP%d_@ID@ : wsteps true false tm %d '
                '(@EDGE@,([],S0,@FW@)) = Some %s. Proof. reflexivity. Qed.'
                % (na, t, cwin(ext)))
            phvis.append(
                'Lemma phVP%d_@ID@ : forall L, csteps tm %d '
                '(@EDGE@,(L,S0,@FW@)) = Some (%s,(%s,%s,%s)).\n'
                'Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ '
                'L U_VP%d_@ID@). Qed.'
                % (na, t, ST[ext[0]], ccons(ext[1], 'L'), SYM[ext[2]],
                   clist(ext[3]), na))
            lemmas.append(VIS_P1W.replace('@QV@', ST[q])
                          .replace('@N@', str(na)).replace('@T@', str(t)))
            cases.append('  - apply vis_A%d_@ID@.' % na)
        elif kind in ('qr', 'vc', 'stpo', 'fin2'):
            nd += 1
            if kind == 'qr':
                tac = DEEP_QR
            elif kind == 'vc':
                tac = DEEP_VC
                lemmas.append(PHVC.replace('@QVC@', ST[q])
                              .replace('@WVC@', SYM[plan[q][1]]))
            elif kind == 'stpo':
                t, ext = plan[q][1], plan[q][2]
                uvis.append(
                    'Lemma U_VS%d_@ID@ : wsteps false true tm %d '
                    '(@ERIP@,([S0],S1,[])) = Some %s. '
                    'Proof. reflexivity. Qed.' % (nd, t, cwin(ext)))
                phvis.append(
                    'Lemma phVS%d_@ID@ : forall R, csteps tm %d '
                    '(@ERIP@,([S0],S1,R)) = Some (%s,(%s,%s,%s)).\n'
                    'Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ '
                    '_ _ R U_VS%d_@ID@). Qed.'
                    % (nd, t, ST[ext[0]], clist(ext[1]), SYM[ext[2]],
                       ccons(ext[3], 'R'), nd))
                tac = DEEP_STPO.replace('@N@', str(nd))
            else:
                t, ext = plan[q][1], plan[q][2]
                uvis.append(
                    'Lemma U_VF%d_@ID@ : wsteps true false tm %d '
                    '(@QR@,([],S1,S1::@P1R@)) = Some %s. '
                    'Proof. reflexivity. Qed.' % (nd, t, cwin(ext)))
                phvis.append(
                    'Lemma phVF%d_@ID@ : forall L, csteps tm %d '
                    '(@QR@,(L,S1,S1::@P1R@)) = Some (%s,(%s,%s,%s)).\n'
                    'Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ '
                    '_ _ L U_VF%d_@ID@). Qed.'
                    % (nd, t, ST[ext[0]], ccons(ext[1], 'L'), SYM[ext[2]],
                       clist(ext[3]), nd))
                tac = DEEP_FIN2.replace('@N@', str(nd))
            lemmas.append(VIS_DEEP.replace('@QV@', ST[q])
                          .replace('@N@', str(nd))
                          .replace('@DEEPTAC@', tac))
            cases.append('  - apply vis_D%d_@ID@.' % nd)
        else:
            raise DeriveError('unknown visit kind %s' % kind)
    return uvis, phvis, lemmas, cases


def emit_source(spec, E, Erip, QR, FW, P1R, FX2, s, plan, p0, boot):
    ID = mach_id(spec)
    uvis, phvis, lemmas, cases = render_vis(spec, E, Erip, QR, FW, P1R, s,
                                            plan)
    sub = {
        '@ID@': ID, '@SPEC@': spec, '@TABLE@': coq_table(spec),
        '@EDGE@': ST[E], '@ERIP@': ST[Erip], '@QR@': ST[QR],
        '@FW@': clist(FW), '@P1R@': clist(P1R), '@FX2@': clist(FX2),
        '@NP1@': str(s['nP1']), '@NRIP@': str(s['nRIP']),
        '@NSTP@': str(s['nSTP']), '@NTRN@': str(s['nTRN']),
        '@NRET@': str(s['nRET']), '@NFIN@': str(s['nFIN']),
        '@NSTPO@': str(s['nSTPO']), '@NFIN2@': str(s['nFIN2']),
        '@P0@': str(p0), '@BOOT@': str(boot),
        '@UVIS@': ('\n'.join(uvis) + '\n') if uvis else '',
        '@PHVIS@': ('\n'.join(phvis) + '\n') if phvis else '',
        '@VISLEMMAS@': '\n'.join(lemmas),
        '@VISCASES@': '\n'.join(cases),
    }
    out = HEAD_W
    for _ in range(3):
        for k, v in sorted(sub.items(), key=lambda kv: -len(kv[0])):
            out = out.replace(k, v)
    return out


def coqc(path):
    p = subprocess.run(
        ['bash', '-lc', 'cd %s && coqc -native-compiler no -Q theories BBB4 %s'
         % (REPO, path)], capture_output=True, text=True, timeout=1800)
    return p.returncode, p.stdout + p.stderr


def print_assumptions(ID, scratch, pref):
    chk = os.path.join(scratch, 'paw_%s.v' % ID)
    with open(chk, 'w') as f:
        f.write('From BBB4.Machines.Counters Require Import %s_%s.\n'
                'Print Assumptions nqh_%s.\n' % (pref, ID, ID))
    return coqc(chk)


def process(spec, do_emit, scratch, force=False, mirror=False):
    res = {'spec': spec, 'ok': False, 'mirror': mirror}
    rspec = spec
    if mirror:
        spec = mirror_spec(spec)
    try:
        edge, tail, p0, far = derive_tail_far(spec, 'A', encname='Ip')
        if list(tail) != TAIL:
            raise DeriveError('anchor tail %s is not [1,0]' % tail)
        if not strip0(far):
            raise DeriveError('far side is blank (not a wall machine)')
        E = LAB.index(edge)
        FW = strip0(far) + [0]
        s, U = derive_interior(spec, E, FW)
        s['cR'] = U['kr'] - 2 * 3
        s['cT'] = U['kt'] - 3
        s2, U2 = derive_overflow(spec, E, FW, s)
        s2['cRo'] = U2['kro'] - 2 * 4
        s2['cTo'] = U2['kto'] - 4
        UU = dict(U)
        UU.update(U2)
        msgs, Erip, QR, P1R, FX2 = check_shapes(E, FW, s2, UU)
        if msgs:
            raise DeriveError('shape: ' + '; '.join(msgs))
        validate(spec, E, FW, s2)
        res.update({'edge': edge, 'FW': FW,
                    'Erip': LAB[Erip], 'QR': LAB[QR],
                    'skel': {k: v for k, v in s2.items()}})
        p0, boot = boot_probe(spec, E, FW, p0)
        plan = visit_plan(spec, E, Erip, QR, FW, P1R, s2)
    except (DeriveError, Wall, AssertionError, KeyError, IndexError) as e:
        res['why'] = str(e)
        return res
    res.update({'p0': p0, 'boot': boot, 'P1R': P1R,
                'plan': {LAB[q]: plan[q][0] for q in plan}})
    if not do_emit:
        res['ok'] = True
        res['why'] = 'derived+validated (not emitted)'
        return res
    ID = mach_id(rspec)
    pref = 'WLSM' if mirror else 'WLS'
    path = os.path.join(OUTDIR, '%s_%s.v' % (pref, ID))
    if os.path.exists(path) and not force:
        res['ok'] = True
        res['why'] = 'file exists -- skipped emission'
        return res
    try:
        src2 = emit_source(spec, E, Erip, QR, FW, P1R, FX2, s2, plan, p0,
                           boot)
        if mirror:
            src2 = mirrorize(src2, rspec, spec)
    except (DeriveError, RuntimeError) as e:
        res['why'] = 'emit: %s' % e
        return res
    with open(path, 'w') as f:
        f.write(src2)
    res['file'] = path
    rc, out = coqc(path)
    if rc != 0:
        res['why'] = 'coqc failed'
        res['log'] = out[-2500:]
        os.remove(path)
        return res
    rc, out = print_assumptions(ID, scratch, pref)
    names = set()
    inax = False
    for ln in out.splitlines():
        if ln.startswith('Axioms:'):
            inax = True
            continue
        if not inax or not ln.strip() or ln[:1].isspace():
            continue
        nm = ln.strip().split(':')[0].strip()
        if re.match(r"^[A-Za-z_][A-Za-z_0-9.']*$", nm):
            names.add(nm.split('.')[-1])
    res['axioms'] = sorted(names)
    res['ok'] = (res['axioms'] == ['functional_extensionality_dep'])
    if not res['ok']:
        res['why'] = 'unexpected axioms: %s' % res['axioms']
        os.remove(path)
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('specs', nargs='*')
    ap.add_argument('--list')
    ap.add_argument('--emit', action='store_true')
    ap.add_argument('--mirror', action='store_true')
    ap.add_argument('--force', action='store_true')
    ap.add_argument('--json')
    ap.add_argument('--limit', type=int)
    ap.add_argument('--scratch', default='/tmp')
    a = ap.parse_args()
    specs = list(a.specs)
    if a.list:
        specs += [x.strip() for x in open(a.list) if x.strip()]
    if a.limit:
        specs = specs[:a.limit]
    out = []
    for spec in specs:
        try:
            r = process(spec, a.emit, a.scratch, a.force, a.mirror)
        except Exception as e:                                # noqa: BLE001
            r = {'spec': spec, 'ok': False,
                 'why': 'CRASH %s: %s' % (type(e).__name__, e)}
        out.append(r)
        extra = ''
        if 'skel' in r:
            extra = ' E=%s Erip=%s QR=%s FW=%s skel=%s plan=%s' % (
                r['edge'], r['Erip'], r['QR'], r['FW'], r['skel'],
                r.get('plan'))
        print('%s %s %s%s' % ('PASS' if r['ok'] else 'FAIL', spec,
                              r.get('why', ''), extra))
        sys.stdout.flush()
    if a.json:
        with open(a.json, 'w') as f:
            json.dump(out, f, indent=1, default=str)
    print('== %d/%d passed' % (sum(1 for r in out if r['ok']), len(out)))


if __name__ == '__main__':
    main()
