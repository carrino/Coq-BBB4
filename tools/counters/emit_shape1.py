#!/usr/bin/env python3
"""UNTRUSTED emitter for LAP-SHAPE-1 interleaved counters under [Jp].

Clones theories/Machines/Counters/ILS1_1RB0RB_1LA1LC_1LB0RD_0LC1RD.v, the
hand-authored 4-window reference board (docs/COUNTER_CLOSEOUT.md section 10
step 1).  Differences from the 6-window emit_interleave.py template:

  - NO P1 prologue: the anchor's blank head rotates through the cycL ripple
    unit as its own data cell (unit [S1;S0] -> deposit [S1;S1]);
  - the anchor far side is the blank CELL [S0], so the INTERIOR branch closes
    EXACTLY (which is all the deep-visit tovf induction needs);
  - the return cycle has unit width 1 ([S1]) and count a_i + 2j (interior)
    / a_o + 2j' (overflow), where a_i / a_o are the stop windows' right
    deposits, measured per machine;
  - the OVERFLOW branch either closes exactly (blank-tail machines) or up to
    ONE trailing blank on the LEFT (wall machines: the overflow rebuilds the
    wall one cell deeper and the anchor's synthetic deep blank is consumed).
    Both go through one uniform fold_tgt/fold_ovL/closeO junction, the wall
    case adding a [lift_side_app_blank] step -- the same close the wave-9
    ILC_ boards used.

Everything here is UNTRUSTED: a wrong constant cannot mis-prove anything, it
fails to typecheck.  The Coq kernel re-checks every emitted board.

Usage
  emit_shape1.py --list FILE [--emit] [--json OUT]
  emit_shape1.py SPEC... [--emit]
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

from executor import Exec, Wall                                     # noqa: E402
from emit_interleave import (Raw, strip0, LAB, ST, SYM, ENC,          # noqa: E402
                             DeriveError, derive_tail, mach_id, coq_table,
                             clist, ccons, cwin)

OUTDIR = os.path.join(REPO, 'theories', 'Machines', 'Counters')
FAR = [0]
MAXN = 16


def carry(m):
    j = 0
    while (m >> j) & 1:
        j += 1
    return j, (m == (1 << j) - 1)


def m_int(j):
    """Smallest value whose cview is (j, Some _)."""
    return (1 << (j + 1)) + (1 << j) - 1 if j else 2


def nrm(cfg):
    q, l, h, r = cfg
    return (q, tuple(strip0(l)), h, tuple(strip0(r)))


# ------------------------------------------------------------------ traces ---
def lap_len(spec, E, encf, tail, m, maxsteps=200000):
    """Raw steps to the next anchor, matched up to blank padding."""
    raw = Raw(spec)
    cfg = (E, encf(m) + list(tail), 0, list(FAR))
    tgt = nrm((E, encf(m + 1) + list(tail), 0, list(FAR)))
    for n in range(1, maxsteps):
        cfg = raw.step(cfg)
        if cfg is None:
            return None
        if nrm(cfg) == tgt:
            return n
    return None


def affine(pts):
    js = sorted(pts)
    if len(js) < 2:
        return None
    j0, j1 = js[0], js[1]
    n0, n1 = pts[j0], pts[j1]
    if (n1 - n0) % (j1 - j0):
        return None
    b = (n1 - n0) // (j1 - j0)
    a = n0 - b * j0
    return (a, b) if all(pts[j] == a + b * j for j in js) else None


def profile(spec, E, encf, tail):
    inter, over = {}, {}
    for j in range(0, 4):
        n = lap_len(spec, E, encf, tail, m_int(j))
        if n is None:
            return None
        inter[j] = n
    for j in range(2, 5):
        n = lap_len(spec, E, encf, tail, (1 << j) - 1)
        if n is None:
            return None
        over[j] = n
    ai, ao = affine(inter), affine(over)
    return None if (ai is None or ao is None) else (ai, ao)


# ------------------------------------------------- windowed-run primitives ---
def conc(ex, cfg, bl, br, n, lw, rw):
    q, l, h, r = cfg
    lw = len(l) if lw is None else lw
    rw = len(r) if rw is None else rw
    if lw > len(l) or rw > len(r):
        raise Wall('window deeper than tape')
    out = ex.wsteps(bl, br, q, l[:lw], h, r[:rw], n)
    ent = (q, tuple(l[:lw]), h, tuple(r[:rw]))
    ext = (out[0], tuple(out[1]), out[2], tuple(out[3]))
    return (out[0], out[1] + l[lw:], out[2], out[3] + r[rw:]), (ent, ext)


def cycl(ex, cfg, ulen, P, k):
    q, l, h, r = cfg
    if k == 0:
        return cfg, None
    if ulen > len(l):
        raise Wall('cycL window')
    u = l[:ulen]
    out = ex.wsteps(True, True, q, u, h, [], P)
    if not (out[0] == q and out[2] == h and out[1] == []):
        raise Wall('not a cycL unit')
    w = out[3]
    if l[:ulen * k] != u * k:
        raise Wall('left is not u^k')
    return ((q, l[ulen * k:], h, w * k + r),
            ((q, tuple(u), h, ()), (q, (), h, tuple(w))))


def cycr(ex, cfg, ulen, P, k):
    q, l, h, r = cfg
    if k == 0:
        return cfg, None
    if ulen * k > len(r):
        raise Wall('cycR window')
    u = r[:ulen]
    out = ex.wsteps(True, True, q, [], h, u, P)
    if not (out[0] == q and out[2] == h and out[3] == []):
        raise Wall('not a cycR unit')
    w = out[1]
    if r[:ulen * k] != u * k:
        raise Wall('right is not u^k')
    return ((q, w * k + l, h, r[ulen * k:]),
            ((q, (), h, tuple(u)), (q, tuple(w), h, ())))


def replay_int(ex, E, encf, tail, m, j, s):
    cfg = (E, encf(m) + list(tail), 0, list(FAR))
    U = {}
    cfg, u = cycl(ex, cfg, 2, s['nRIP'], j)
    if u:
        U['RIP'] = u
    cfg, U['STPI'] = conc(ex, cfg, True, True, s['nSTP'], 2, 0)
    k = len(cfg[3]) - len(FAR)
    if k < 1:
        raise Wall('return count')
    cfg, u = cycr(ex, cfg, 1, s['nRET'], k)
    if u:
        U['RET'] = u
    U['kint'] = k
    cfg, U['FIN'] = conc(ex, cfg, True, True, s['nFIN'], 0, None)
    return cfg, U


def replay_ov(ex, E, encf, tail, m, j, s):
    cfg = (E, encf(m) + list(tail), 0, list(FAR))
    U = {}
    cfg, u = cycl(ex, cfg, 2, s['nRIP'], j)
    if u:
        U['RIP'] = u
    cfg, U['STPO'] = conc(ex, cfg, False, True, s['nSTPO'], None, 0)
    k = len(cfg[3]) - len(FAR)
    if k < 1:
        raise Wall('overflow return count')
    cfg, u = cycr(ex, cfg, 1, s['nRET'], k)
    if u:
        U['RET'] = u
    U['kov'] = k
    cfg, U['FIN2'] = conc(ex, cfg, True, True, s['nFIN'], 0, None)
    return cfg, U


def ov_targets(E, encf, tail, m):
    """(exact, one-left-blank-short) closes of the overflow lap."""
    return ((E, encf(m + 1) + list(tail), 0, list(FAR)),
            (E, encf(m + 1) + list(tail[:-1]), 0, list(FAR)))


def derive(spec, E, encf, tail, ai, ao):
    """Fit the step counts, then confirm by exact symbolic replay.

    interior n(j) = nRIP*j + nSTP + nRET*(a_i + 2j) + nFIN
    overflow n(j')= nRIP*j' + nSTPO + nRET*(a_o + 2j') + nFIN
    so the interior slope is nRIP + 2*nRET."""
    a, b = ai        # n_int(j) = a + b*j
    aoa, aob = ao    # n_ov keyed by cview j (= j' + 1)
    ex = Exec(spec)
    JI, KO = 3, 4
    tgt_i = (E, encf(m_int(JI) + 1) + list(tail), 0, list(FAR))
    tgt_oe, tgt_ol = ov_targets(E, encf, tail, (1 << KO) - 1)
    for nRIP in range(1, 9):
        for nRET in range(1, 5):
            if nRIP + 2 * nRET != b:
                continue
            for nSTP in range(1, MAXN):
                for nFIN in range(1, MAXN):
                    s = dict(nRIP=nRIP, nRET=nRET, nSTP=nSTP, nFIN=nFIN)
                    try:
                        cfg, U = replay_int(ex, E, encf, tail, m_int(JI), JI, s)
                    except (Wall, KeyError, IndexError):
                        continue
                    if cfg != tgt_i:
                        continue
                    if a + b * JI != (nRIP * JI + nSTP + nRET * U['kint']
                                      + nFIN):
                        continue
                    for nSTPO in range(1, MAXN + 10):
                        s2 = dict(s, nSTPO=nSTPO)
                        try:
                            cfg2, UO = replay_ov(ex, E, encf, tail,
                                                 (1 << KO) - 1, KO - 1, s2)
                        except (Wall, KeyError, IndexError):
                            continue
                        if cfg2 == tgt_oe:
                            exact_ov = True
                        elif cfg2 == tgt_ol:
                            exact_ov = False
                        else:
                            continue
                        if aoa + aob * KO != (nRIP * (KO - 1) + nSTPO
                                              + nRET * UO['kov'] + nFIN):
                            continue
                        U.update(UO)
                        return s2, U, exact_ov
    raise DeriveError('no shape-1 skeleton fits both lap branches')


def shape_check(s, U, tail, exact_ov):
    """The emitted proof script needs exactly these window shapes."""
    msgs = []
    (Re, Rx) = U['RIP']
    (Se, Sx) = U['STPI']
    (Oe, Ox) = U['STPO']
    (Te, Tx) = U['RET']
    (Fe, Fx) = U['FIN']
    E = Re[0]
    if Re != (E, (1, 0), 0, ()) or Rx != (E, (), 0, (1, 1)):
        msgs.append('ripple %s -> %s is not [S1;S0]|S0 -> [S1;S1]' % (Re, Rx))
    QT, HT = Te[0], Te[2]
    if HT != 1 or Te != (QT, (), 1, (1,)) or Tx != (QT, (1,), 1, ()):
        msgs.append('return %s -> %s is not a width-1 [S1] cycle' % (Te, Tx))
    if Se[0] != E or Se[1] != (1, 1) or Se[2] != 0 or Se[3] != ():
        msgs.append('interior stop entry %s is not (E,[S1;S1],S0,[])' % (Se,))
    if Sx[0] != QT or Sx[2] != 1:
        msgs.append('interior stop exit %s is not (QT,_,S1,_)' % (Sx,))
    a_i = len(Sx[3])
    if Sx[3] != (1,) * a_i or (1,) * a_i + Sx[1] != (1, 0):
        msgs.append('interior stop deposit %s|%s does not rebuild [S1;S0]'
                    % (Sx[1], Sx[3]))
    if a_i not in (0, 1):
        msgs.append('a_i=%d not in {0,1}' % a_i)
    if Oe != (E, (1,) + tuple(tail), 0, ()):
        msgs.append('overflow stop entry %s is not (E,[S1]++tail,S0,[])'
                    % (Oe,))
    if Ox[0] != QT or Ox[2] != 1:
        msgs.append('overflow stop exit %s is not (QT,_,S1,_)' % (Ox,))
    a_o = len(Ox[3])
    t_ov = tuple(tail) if exact_ov else tuple(tail[:-1])
    if Ox[3] != (1,) * a_o or (1,) * a_o + Ox[1] != (1, 1, 1) + t_ov:
        msgs.append('overflow deposit %s|%s does not rebuild [S1;S1;S1]++%s'
                    % (Ox[1], Ox[3], list(t_ov)))
    if a_o < 1 or a_o > 3:
        msgs.append('a_o=%d not in {1,2,3}' % a_o)
    if Fe != (QT, (), 1, tuple(FAR)) or Fx != (E, (), 0, tuple(FAR)):
        msgs.append('close %s -> %s is not (QT,[],S1,far)->(E,[],S0,far)'
                    % (Fe, Fx))
    if U.get('FIN2') and U['FIN2'] != U['FIN']:
        msgs.append('overflow close %s differs from interior close %s'
                    % (U['FIN2'], U['FIN']))
    return msgs, a_i, a_o


def visit_probe(spec, E, tail, s, U):
    """Visit plan: edge@0, X@1 (first step off the anchor), QT at both stop
    exits, and the remaining state as an offset INSIDE the overflow stop
    window (reached via the tovf induction)."""
    ex = Exec(spec)
    one = ex.wsteps(True, True, E, [1], 0, [], 1)
    X, wdep = one[0], one[3]
    if one[1] != [] or one[2] != 1:
        raise DeriveError('first step off the anchor is not a 1-cell pop')
    QT = U['RET'][0][0]
    if len({E, X, QT}) != 3:
        raise DeriveError('anchor/first-step/return states collide '
                          '(%s/%s/%s) -- visit plan needs rework'
                          % (LAB[E], LAB[X], LAB[QT]))
    deep = {}
    ent = [1] + list(tail)
    for q in range(4):
        if q in (E, X, QT):
            continue
        found = None
        for t in range(1, s['nSTPO']):
            out = ex.wsteps(False, True, E, ent, 0, [], t)
            if out[0] == q:
                found = (t, (out[0], tuple(out[1]), out[2], tuple(out[3])))
                break
        if found is None:
            raise DeriveError('state %s has no witness in the overflow stop '
                              '(needs the interior-hop plan -- report)'
                              % LAB[q])
        deep[q] = found
    if len(deep) != 1:
        raise DeriveError('expected exactly one deep state, got %s'
                          % [LAB[q] for q in deep])
    return X, wdep, deep


def boot_probe(spec, E, encf, tail, p0, maxT=40000):
    raw = Raw(spec)
    tgt = nrm((E, encf(p0) + list(tail), 0, list(FAR)))
    cfg = (0, [], 0, [])
    for t in range(maxT):
        if nrm(cfg) == tgt:
            return t
        cfg = raw.step(cfg)
        if cfg is None:
            raise DeriveError('halts during bootstrap at t=%d' % t)
    raise DeriveError('no bootstrap to Cc(%d)' % p0)


def validate(spec, E, encf, tail, s, exact_ov, hi=160):
    ex = Exec(spec)
    n = 0
    for m in list(range(1, hi)) + [2**10 - 1, 2**10, 2**13 - 1, 2**13 + 5]:
        j, ov = carry(m)
        raw = lap_len(spec, E, encf, tail, m)
        if raw is None:
            raise DeriveError('raw lap does not close at m=%d' % m)
        if ov:
            tgt_oe, tgt_ol = ov_targets(E, encf, tail, m)
            tgt = tgt_oe if exact_ov else tgt_ol
            cfg, U = replay_ov(ex, E, encf, tail, m, j - 1, s)
            got = (s['nRIP'] * (j - 1) + s['nSTPO'] + s['nRET'] * U['kov']
                   + s['nFIN'])
        else:
            tgt = (E, encf(m + 1) + list(tail), 0, list(FAR))
            cfg, U = replay_int(ex, E, encf, tail, m, j, s)
            got = (s['nRIP'] * j + s['nSTP'] + s['nRET'] * U['kint']
                   + s['nFIN'])
        if cfg != tgt:
            raise DeriveError('m=%d: symbolic lap misses the next anchor' % m)
        if got != raw:
            raise DeriveError('m=%d: symbolic %d != raw %d' % (m, got, raw))
        n += 1
    return n


# ------------------------------------------------------------- Coq emission --
HEAD = r'''(** * ILS1_@ID@: 4-window [Jp] interleaved binary counter, machine
    @SPEC@ (lap-shape family of tools/counter_lapshapes.tsv ranks 1 and 3).

    Auto-emitted by tools/counters/emit_shape1.py (UNTRUSTED emitter; the Coq
    kernel re-checks every line below), cloning the hand-authored reference
    board ILS1_1RB0RB_1LA1LC_1LB0RD_0LC1RD.v.  Left-growth counter under the
    complemented interleave encoding [Jp] (JpCounter.v), anchored at

      Cc p = (@EDGE@, (Jp p ++ @TAIL@, S0, @FAR@))

    -- the counter on the LEFT list nearest-first, a blank head at the fixed
    right frontier, and a blank far-side CELL (not the empty list).  One lap
    Cc p -> Cc (p+1) is a FOUR-window chain: RIP leftward carry ripple (cycL,
    @NRIP@ steps per low set pair; no P1 prologue -- the anchor's blank head
    rotates through as the unit's own data cell); STPI interior stop (@NSTP@
    steps) / STPO overflow stop off the deep-left edge (@NSTPO@ steps,
    left-open); RET rightward return (cycR, @NRET@ step per deposited cell,
    count @AI@+2j interior / @AO@+2j' overflow); FIN frontier close (@NFIN@
    steps, shared by both branches).  The INTERIOR branch closes EXACTLY
    (feeding the deep-visit induction); the overflow branch closes @OVKIND@.

    Step counts were derived by exact symbolic replay and the decomposition
    was differentially validated against the raw simulator on BOTH cview
    branches (step counts AND exact configurations, p = 1..160 plus sparse
    p up to 2^13).  Axiom footprint: [functional_extensionality_dep] (via
    CTape.lift). *)
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

Definition Cc_@ID@ (p : positive) : cconf := (@EDGE@, (Jp p ++ @TAIL@, S0, @FAR@)).
Local Notation Cc := Cc_@ID@.

(** ** The four lap unit windows + the visit units (each closed by [reflexivity]) *)
Lemma U_RIP_@ID@ : wsteps true true tm @NRIP@ @RIPE@ = Some @RIPX@. Proof. reflexivity. Qed.
Lemma U_STPI_@ID@ : wsteps true true tm @NSTP@ @STPIE@ = Some @STPIX@. Proof. reflexivity. Qed.
Lemma U_STPO_@ID@ : wsteps false true tm @NSTPO@ @STPOE@ = Some @STPOX@. Proof. reflexivity. Qed.
Lemma U_RET_@ID@ : wsteps true true tm @NRET@ @RETE@ = Some @RETX@. Proof. reflexivity. Qed.
Lemma U_FIN_@ID@ : wsteps true true tm @NFIN@ @FINE@ = Some @FINX@. Proof. reflexivity. Qed.
@UVDEEP@Lemma U_VX_@ID@ : wsteps true true tm 1 (@EDGE@,([S1],S0,[])) = Some (@QX@,([],S1,@WDEP@)). Proof. reflexivity. Qed.

(** ** Transported phases (framing = each unit's bl/br) *)
Lemma phRIP_@ID@ : forall k L R, csteps tm (@NRIP@*k) (@EDGE@,(rep [S1;S0] k ++ L,S0,R)) = Some (@EDGE@,(L,S0,rep [S1;S1] k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP_@ID@ k L R) as H; cbn [app] in H; exact H. Qed.
Lemma phSTPI_@ID@ : forall L R, csteps tm @NSTP@ (@EDGE@,(S1::S1::L,S0,R)) = Some (@QT@,(@STPIDL@L,S1,@STPIDR@R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI_@ID@). Qed.
Lemma phSTPO_@ID@ : forall R, csteps tm @NSTPO@ (@EDGE@,(@STPOEL@,S0,R)) = Some (@QT@,(@STPOL@,S1,@STPODR@R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO_@ID@). Qed.
Lemma phRET_@ID@ : forall k L R, csteps tm (@NRET@*k) (@QT@,(L,S1,rep [S1] k ++ R)) = Some (@QT@,(rep [S1] k ++ L,S1,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET_@ID@ k L R). Qed.
Lemma phFIN_@ID@ : forall L R, csteps tm @NFIN@ (@QT@,(L,S1,S0::R)) = Some (@EDGE@,(L,S0,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FIN_@ID@). Qed.
@PHVDEEP@Lemma phVX_@ID@ : forall L R, csteps tm 1 (@EDGE@,(S1::L,S0,R)) = Some (@QX@,(L,S1,@WDEPC@R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_VX_@ID@). Qed.

(** ** The lap

    Interior branch: EXACT (the next anchor on the nose) -- the deep-visit
    induction below chains on this equality. *)
Lemma lap_int_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j q0 Ecv. unfold Cc_@ID@.
  destruct (cview_some_J p j q0 Ecv) as (HJp & HJs).
  do 2 eexists. split; [|split].
  + rewrite HJp, <- app_assoc. cbn [app].
    eapply csteps_chain. { apply phRIP_@ID@. }
    eapply csteps_chain. { apply phSTPI_@ID@. }
    rewrite rep_dbl.
@INTCHG@    eapply csteps_chain. { apply (phRET_@ID@ @KINT@). }
    apply phFIN_@ID@.
  + rewrite HJs, rep_dbl, <- app_assoc. cbn [app].
    @INTG2@
  + lia.
Qed.

(** Fold the next anchor's counter into a single run of ones. *)
Lemma fold_tgt_@ID@ : forall k, (rep [S1;S1] k ++ [S1]) ++ @TAIL@ = rep [S1] (S (2*k)) ++ @TAIL@.
Proof. intro k. rewrite rep_dbl, rep_shift. reflexivity. Qed.
@OVHELPERS@
Lemma lap_ov_@ID@ : forall p j', cview p = (S j', None) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j' Ecv. unfold Cc_@ID@.
  destruct (cview_none_J p j' Ecv) as (HJp & HJs).
  do 2 eexists. split; [|split].
  + rewrite HJp, <- app_assoc. cbn [app].
    eapply csteps_chain. { apply phRIP_@ID@. }
    eapply csteps_chain. { apply phSTPO_@ID@. }
    rewrite rep_dbl.
@OVCHG@    eapply csteps_chain. { apply (phRET_@ID@ @KOV@). }
    apply phFIN_@ID@.
  + rewrite HJs, fold_tgt_@ID@@OVFOLD@. apply closeO_@ID@. lia.
  + lia.
Qed.

Lemma lap_@ID@ : forall p, exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
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

@VISDEEP@
(** @QT@ is entered by BOTH stop windows, so every lap visits it: case on
    [cview] and run ripple + the matching stop. *)
Lemma vis_T_@ID@ : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = @QT@.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - destruct (cview_some_J p j q0 Ecv) as (HJp & _).
    unfold Cc_@ID@. eexists. eexists. split.
    + rewrite HJp, <- app_assoc. cbn [app].
      eapply csteps_chain. { apply phRIP_@ID@. }
      apply phSTPI_@ID@.
    + reflexivity.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & _).
    unfold Cc_@ID@. eexists. eexists. split.
    + rewrite HJp, <- app_assoc. cbn [app].
      eapply csteps_chain. { apply phRIP_@ID@. }
      apply phSTPO_@ID@.
    + reflexivity.
Qed.

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

CLOSE_EXACT = r'''
(** Exact-overflow close: both sides already share the tail. *)
Lemma closeO_@ID@ : forall a b (q : St) (h : Sym) r, a = b ->
  lift (q,(rep [S1] a ++ @TOV@, h, r)) = lift (q,(rep [S1] b ++ @TAIL@, h, r)).
Proof. intros a b q h r ->. reflexivity. Qed.
'''

CLOSE_LIFT = r'''
(** Wall-overflow close: the overflow rebuilds the wall one cell deeper and
    consumes the anchor's synthetic deep blank; the two agree under [lift]. *)
Lemma lift_lblank_@ID@ : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma closeO_@ID@ : forall a b (q : St) (h : Sym) r, a = b ->
  lift (q,(rep [S1] a ++ @TOV@, h, r)) = lift (q,(rep [S1] b ++ @TAIL@, h, r)).
Proof.
  intros a b q h r ->.
  replace (rep [S1] b ++ @TAIL@) with ((rep [S1] b ++ @TOV@) ++ [S0])
    by (rewrite <- app_assoc; reflexivity).
  rewrite lift_lblank_@ID@. reflexivity.
Qed.
'''

FOLD_OVL = r'''
(** Fold the overflow stop's left deposit into the run of ones. *)
Lemma fold_ovL_@ID@ : forall k, rep [S1] k ++ @LOLIT@ = rep [S1] (k + @CO@) ++ @TOV@.
Proof. intro k. rewrite rep_add, <- !app_assoc. reflexivity. Qed.
'''

VISDEEP = r'''(** @QZ@ fires only inside the OVERFLOW stop; reach an all-ones counter by
    well-founded induction on [tovf] (strictly decreasing along interior
    laps, which close EXACTLY), then run the stop prefix. *)
Lemma vis_Z_@ID@ : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = @QZ@.
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_int_@ID@ p j q0 Ecv) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ p) eq_refl) as (k & c & Hk & Hq).
    exists (n + k), c. rewrite csteps_add, Hrun. exact (conj Hk Hq).
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & _).
    unfold Cc_@ID@. eexists. eexists. split.
    * rewrite HJp, <- app_assoc. cbn [app].
      eapply csteps_chain. { apply phRIP_@ID@. }
      apply phVZ_@ID@.
    * reflexivity.
Qed.
'''


def emit_source(spec, E, tail, p0, boot, s, U, a_i, a_o, exact_ov,
                X, wdep, deep):
    ID = mach_id(spec)
    (Re, Rx) = U['RIP']
    (Se, Sx) = U['STPI']
    (Oe, Ox) = U['STPO']
    (Te, Tx) = U['RET']
    (Fe, Fx) = U['FIN']
    QT = Te[0]
    t_ov = list(tail) if exact_ov else list(tail[:-1])
    c_o = len(Ox[1]) - len(t_ov)
    if c_o < 0 or list(Ox[1]) != [1] * c_o + t_ov:
        raise DeriveError('overflow left deposit %s is not S1^c ++ %s'
                          % (list(Ox[1]), t_ov))

    def srep(n, base):
        return '(' + 'S (' * n + base + ')' * n + ')' if n else '(' + base + ')'

    kint = srep(a_i, '2*j')
    kov = srep(a_o, "2*j'")
    if a_i == 1:
        intchg = ('    change (S1 :: rep [S1] (2*j) ++ %s) with '
                  '(rep [S1] (S (2*j)) ++ %s).\n' % (clist(FAR), clist(FAR)))
        intg2 = 'rewrite <- rep_slide. reflexivity.'
    else:
        intchg = ''
        intg2 = 'reflexivity.'
    ovchg = ('    change (%srep [S1] (2*j\') ++ %s) with '
             '(rep [S1] %s ++ %s).\n'
             % ('S1 :: ' * a_o, clist(FAR), kov, clist(FAR)))

    sub = {
        '@ID@': ID, '@SPEC@': spec, '@TABLE@': coq_table(spec),
        '@EDGE@': ST[E], '@TAIL@': clist(tail), '@FAR@': clist(FAR),
        '@TOV@': clist(t_ov), '@LOLIT@': clist(Ox[1]), '@CO@': str(c_o),
        '@P0@': str(p0), '@BOOT@': str(boot),
        '@NRIP@': str(s['nRIP']), '@NSTP@': str(s['nSTP']),
        '@NSTPO@': str(s['nSTPO']), '@NRET@': str(s['nRET']),
        '@NFIN@': str(s['nFIN']),
        '@AI@': str(a_i), '@AO@': str(a_o),
        '@OVKIND@': ('exactly too' if exact_ov else
                     'up to one trailing blank on the left (the wall case)'),
        '@RIPE@': cwin(Re), '@RIPX@': cwin(Rx),
        '@STPIE@': cwin(Se), '@STPIX@': cwin(Sx),
        '@STPOE@': cwin(Oe), '@STPOX@': cwin(Ox),
        '@RETE@': cwin(Te), '@RETX@': cwin(Tx),
        '@FINE@': cwin(Fe), '@FINX@': cwin(Fx),
        '@QT@': ST[QT], '@QX@': ST[X],
        '@STPIDL@': ccons(Sx[1], ''), '@STPIDR@': ccons(Sx[3], ''),
        '@STPOEL@': clist(Oe[1]), '@STPOL@': clist(Ox[1]),
        '@STPODR@': ccons(Ox[3], ''),
        '@WDEP@': clist(wdep), '@WDEPC@': ccons(wdep, ''),
        '@KINT@': kint, '@KOV@': kov,
        '@INTCHG@': intchg, '@INTG2@': intg2, '@OVCHG@': ovchg,
        '@OVFOLD@': (', fold_ovL_%s' % ID) if c_o > 0 else '',
    }
    helpers = ''
    if c_o > 0:
        helpers += FOLD_OVL
    helpers += CLOSE_EXACT if exact_ov else CLOSE_LIFT
    sub['@OVHELPERS@'] = helpers
    # the single deep state: tovf-induction witness inside the overflow stop
    (qz, (tz, ext)) = next(iter(deep.items()))
    sub['@UVDEEP@'] = (
        'Lemma U_VZ_@ID@ : wsteps false true tm %d %s = Some %s. '
        'Proof. reflexivity. Qed.\n'
        % (tz, cwin((E, Oe[1], 0, ())), cwin(ext)))
    sub['@PHVDEEP@'] = (
        'Lemma phVZ_@ID@ : forall R, csteps tm %d (@EDGE@,(%s,S0,R)) '
        '= Some (%s,(%s,%s,%s)).\n'
        'Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R '
        'U_VZ_@ID@). Qed.\n'
        % (tz, clist(Oe[1]), ST[ext[0]], clist(ext[1]), SYM[ext[2]],
           ccons(ext[3], 'R')))
    sub['@VISDEEP@'] = VISDEEP.replace('@QZ@', ST[qz])
    cases = []
    for q in range(4):
        if q == E:
            cases.append('  - (* %s : the anchor state *)\n'
                         '    exists 0. eexists. split; reflexivity.' % ST[q])
        elif q == X:
            cases.append(
                '  - (* %s : 1 step from the anchor *)\n'
                '    destruct (Jp_head p) as (w & Hw). unfold Cc_@ID@.\n'
                '    rewrite Hw. cbn [app]. exists 1. eexists. split.\n'
                '    + apply phVX_@ID@.\n'
                '    + reflexivity.' % ST[q])
        elif q == QT:
            cases.append('  - apply vis_T_@ID@.')
        elif q == qz:
            cases.append('  - apply vis_Z_@ID@.')
        else:
            raise DeriveError('state %s has no visit case' % LAB[q])
    sub['@VISCASES@'] = '\n'.join(cases)
    src = HEAD
    for _ in range(3):
        for k, v in sorted(sub.items(), key=lambda kv: -len(kv[0])):
            src = src.replace(k, v)
    return src


# ----------------------------------------------------------------- pipeline --
def coqc(path):
    p = subprocess.run(
        ['bash', '-lc', 'cd %s && coqc -native-compiler no -Q theories BBB4 %s'
         % (REPO, path)], capture_output=True, text=True, timeout=1800)
    return p.returncode, p.stdout + p.stderr


def print_assumptions(ID, scratch):
    chk = os.path.join(scratch, 'pa_%s.v' % ID)
    with open(chk, 'w') as f:
        f.write('From BBB4.Machines.Counters Require Import ILS1_%s.\n'
                'Print Assumptions nqh_%s.\n' % (ID, ID))
    return coqc(chk)


def process(spec, fp_edge, do_emit, scratch, force=False):
    res = {'spec': spec, 'ok': False}
    try:
        edge, tail, p0 = derive_tail(spec, fp_edge, encname='Jp')
        E = LAB.index(edge)
        encf = ENC['Jp']
        pr = profile(spec, E, encf, tail)
        if pr is None:
            raise DeriveError('laps not affine on both branches')
        ai_fit, ao_fit = pr
        s, U, exact_ov = derive(spec, E, encf, tail, ai_fit, ao_fit)
        msgs, a_i, a_o = shape_check(s, U, tail, exact_ov)
        if msgs:
            raise DeriveError('shape: ' + '; '.join(msgs))
        X, wdep, deep = visit_probe(spec, E, tail, s, U)
        nchk = validate(spec, E, encf, tail, s, exact_ov)
        boot = boot_probe(spec, E, encf, tail, p0)
    except (DeriveError, Wall, AssertionError, KeyError, IndexError) as e:
        res['why'] = str(e)
        return res
    res.update({'edge': edge, 'tail': list(tail), 'p0': p0, 'boot': boot,
                'skel': s, 'a_i': a_i, 'a_o': a_o, 'exact_ov': exact_ov,
                'X': LAB[X], 'QT': LAB[U['RET'][0][0]],
                'deep': {LAB[q]: t for q, (t, _) in deep.items()},
                'nchecked': nchk})
    if not do_emit:
        res['ok'] = True
        res['why'] = 'derived+validated (not emitted)'
        return res
    ID = mach_id(spec)
    path = os.path.join(OUTDIR, 'ILS1_%s.v' % ID)
    if os.path.exists(path) and not force:
        res['ok'] = True
        res['why'] = 'file exists (hand board?) -- skipped emission'
        return res
    try:
        src = emit_source(spec, E, tail, p0, boot, s, U, a_i, a_o, exact_ov,
                          X, wdep, deep)
    except DeriveError as e:
        res['why'] = 'emit: %s' % e
        return res
    with open(path, 'w') as f:
        f.write(src)
    res['file'] = path
    rc, out = coqc(path)
    if rc != 0:
        res['why'] = 'coqc failed'
        res['log'] = out[-2500:]
        os.remove(path)
        return res
    rc, out = print_assumptions(ID, scratch)
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
    ap.add_argument('--force', action='store_true')
    ap.add_argument('--json')
    ap.add_argument('--scratch', default='/tmp')
    a = ap.parse_args()
    specs = list(a.specs)
    if a.list:
        specs += [x.strip() for x in open(a.list) if x.strip()]
    out = []
    for spec in specs:
        r = process(spec, 'C', a.emit, a.scratch, a.force)
        out.append(r)
        extra = ''
        if 'skel' in r:
            extra = (' skel=%s ai=%d ao=%d exact_ov=%s X=%s QT=%s deep=%s '
                     'boot=%d p0=%d tail=%s' % (
                         r['skel'], r['a_i'], r['a_o'], r['exact_ov'], r['X'],
                         r['QT'], r['deep'], r['boot'], r['p0'], r['tail']))
        print('%s %s %s%s' % ('PASS' if r['ok'] else 'FAIL', spec,
                              r.get('why', ''), extra))
        if r.get('log'):
            for ln in r['log'].splitlines()[-12:]:
                print('      | %s' % ln)
        sys.stdout.flush()
    if a.json:
        with open(a.json, 'w') as f:
            json.dump(out, f, indent=1)
    print('== %d/%d passed' % (sum(1 for r in out if r['ok']), len(out)))


if __name__ == '__main__':
    main()
