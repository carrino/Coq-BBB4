#!/usr/bin/env python3
"""UNTRUSTED emitter for the ERASE/REBUILD wall shape (the W-Jp family).

The second wall-lap template (WALLLAP_NOTE.md; the first is emit_wall.py's
W-Ip shape).  Under the COMPLEMENTED encoding [Jp] the head stays BLANK
across the whole lap and the carry runs as an erase-then-rebuild pass:

  Cc p = (E, Jp p ++ [S0], S0, FW)      FW = wall word ++ [S0]

  interior : ER^j   cycL [S1;S0] -> deposits [S0;S0]  (erase the low pairs)
             ST     stop on the clear pair [S1;S1]
             RB^k   cycR [S0] -> [S1]   (rebuild, k = 2j+3, consuming the
                    deposited blanks AND the wall's own blanks)
             CL     right-open close, rebuilding the wall one cell out
  overflow : ER^(j'+1) (the anchor tail completes a final [S1;S0] pair)
             STO    LEFT-OPEN stop off the deep tape edge
             RB^(2j'+5) . CL

Anchoring the wall WITH its trailing blank (FW = wall ++ [S0]) makes the
interior branch land EXACTLY -- that is what lets the [tovf] well-founded
induction carry the deep visit witnesses, exactly as in emit_wall.py.

Everything here is UNTRUSTED: the Coq kernel re-checks every board.

Usage
  emit_wallj.py --list FILE [--emit] [--mirror] [--json OUT]
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

Jp = ENC['Jp']
OUTDIR = os.path.join(REPO, 'theories', 'Machines', 'Counters')
TL = [0]


def j_of(v):
    j = 0
    while (v >> j) & 1:
        j += 1
    return j


def cc(E, p, FW):
    return (E, Jp(p) + TL, 0, list(FW))


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


def nblanks(r):
    k = 0
    while k < len(r) and r[k] == 0:
        k += 1
    return k


# ---------------------------------------------------------- chain replays ----
def replay_int(ex, E, FW, m, j, s):
    cfg = cc(E, m, FW)
    U = {}
    cfg, u = cycl(ex, cfg, 2, s['nER'], j)
    if u:
        U['ER'] = u
    cfg, U['ST'] = conc(ex, cfg, True, True, s['nST'], 2, 0)
    k = nblanks(cfg[3])
    cfg, u = cycr(ex, cfg, 1, s['nRB'], k)
    if u:
        U['RB'] = u
    U['k'] = k
    cfg, U['CL'] = conc(ex, cfg, True, False, s['nCL'], 2, None)
    n = s['nER'] * j + s['nST'] + s['nRB'] * k + s['nCL']
    return cfg, n, U


def replay_ov(ex, E, FW, m, jp, s):
    cfg = cc(E, m, FW)
    U = {}
    cfg, u = cycl(ex, cfg, 2, s['nER'], jp + 1)
    if u:
        U['ERo'] = u
    cfg, U['STO'] = conc(ex, cfg, False, True, s['nSTO'], None, 0)
    k = nblanks(cfg[3])
    cfg, u = cycr(ex, cfg, 1, s['nRB'], k)
    U['ko'] = k
    cfg, U['CLO'] = conc(ex, cfg, True, False, s['nCL'], 2, None)
    n = s['nER'] * (jp + 1) + s['nSTO'] + s['nRB'] * k + s['nCL']
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


def derive(spec, E, FW):
    ex = Exec(spec)
    ints = {}
    for j in range(1, 5):
        n = raw_lap(spec, E, FW, m_int(j))
        if n is None:
            raise DeriveError('interior lap does not close (j=%d)' % j)
        ints[j] = n
    if affine2(ints) is None:
        raise DeriveError('interior laps not affine: %s' % ints)
    JI = 3
    m = m_int(JI)
    tgt = cc(E, m + 1, FW)
    sol = None
    for nER in range(1, 5):
        for nST in range(1, 10):
            for nRB in range(1, 4):
                for nCL in range(1, 22):
                    s = dict(nER=nER, nST=nST, nRB=nRB, nCL=nCL)
                    try:
                        cfg, n, U = replay_int(ex, E, FW, m, JI, s)
                    except (Wall, KeyError, IndexError):
                        continue
                    if n == ints[JI] and cfg == tgt:
                        sol = (s, U)
                        break
                if sol:
                    break
            if sol:
                break
        if sol:
            break
    if not sol:
        raise DeriveError('no Jp-wall interior skeleton fits (%s)' % ints)
    s, U = sol
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
    for nSTO in range(1, 16):
        s2 = dict(s, nSTO=nSTO)
        try:
            cfg, n, UO = replay_ov(ex, E, FW, m, KO - 1, s2)
        except (Wall, KeyError, IndexError):
            continue
        if n == ovs[KO] and nrm(cfg) == tgt:
            U.update(UO)
            return s2, U
    raise DeriveError('no Jp-wall overflow stop fits (%s)' % ovs)


def check_shapes(E, FW, s, U):
    msgs = []
    (Ee, Ex) = U['ER']
    (Se, Sx) = U['ST']
    (Re, Rx) = U['RB']
    (Ce, Cx) = U['CL']
    (Oe, Ox) = U['STO']
    QD = Sx[0]
    if Ee != (E, (1, 0), 0, ()) or Ex != (E, (), 0, (0, 0)):
        msgs.append('erase %s -> %s (need (E,[S1;S0],S0,[])->(E,[],S0,'
                    '[S0;S0]))' % (Ee, Ex))
    if Se != (E, (1, 1), 0, ()) or Sx != (QD, (0,), 0, (0,)):
        msgs.append('stop %s -> %s (need (E,[S1;S1],S0,[])->(QD,[S0],S0,'
                    '[S0]))' % (Se, Sx))
    if Re != (QD, (), 0, (0,)) or Rx != (QD, (1,), 0, ()):
        msgs.append('rebuild %s -> %s (need (QD,[],S0,[S0])->(QD,[S1],S0,'
                    '[]))' % (Re, Rx))
    if Ce != (QD, (1, 1), 0, tuple(FW[len(FW) - 1:])) and Ce[:3] != (QD, (1, 1), 0):
        msgs.append('close entry %s (need (QD,[S1;S1],S0,rest))' % (Ce,))
    if Cx[0] != E or Cx[1] != () or Cx[2] != 0:
        msgs.append('close exit %s (need (E,[],S0,FW))' % (Cx,))
    if list(Cx[3]) != list(FW):
        msgs.append('close far %s != wall %s' % (Cx[3], FW))
    if Oe[0] != E or Oe[1] != () or Oe[2] != 0 or Ox != Sx:
        msgs.append('overflow stop %s -> %s (need (E,[],S0,[]) and the '
                    'interior stop exit)' % (Oe, Ox))
    if QD == E:
        msgs.append('QD collides with E')
    W = len(FW) - 1              # wall cells before the padded blank
    if nblanks(list(FW)) != 2:
        msgs.append('far blank run is %d, not the templated 2 (the exact '
                    'close needs one leftover S1)' % nblanks(list(FW)))
    if U['k'] != 2 * 3 + 1 + nblanks(list(FW)):
        msgs.append('rebuild count %d is not 2j+1+|far blanks|' % U['k'])
    if U['ko'] != 2 * 3 + 3 + nblanks(list(FW)):
        msgs.append('overflow rebuild count %d off' % U['ko'])
    return msgs, QD, W


def validate(spec, E, FW, s):
    ex = Exec(spec)
    nb = nblanks(list(FW))
    for m in range(2, 200):
        j = j_of(m)
        if m == (1 << j) - 1 or j == 0:
            continue
        cfg, n, U = replay_int(ex, E, FW, m, j, s)
        if cfg != cc(E, m + 1, FW):
            raise DeriveError('interior m=%d: not EXACT' % m)
        if n != raw_lap(spec, E, FW, m):
            raise DeriveError('interior m=%d: step mismatch' % m)
        if U['k'] != 2 * j + 1 + nb:
            raise DeriveError('interior m=%d: rebuild count drift' % m)
    for K in range(2, 9):
        m = (1 << K) - 1
        cfg, n, U = replay_ov(ex, E, FW, m, K - 1, s)
        if nrm(cfg) != nrm(cc(E, m + 1, FW)):
            raise DeriveError('overflow K=%d: misses anchor' % K)
        if n != raw_lap(spec, E, FW, m):
            raise DeriveError('overflow K=%d: step mismatch' % K)
        if U['ko'] != 2 * K + 1 + nb:
            raise DeriveError('overflow K=%d: rebuild count drift (%d)'
                              % (K, U['ko']))
    return True


def boot_probe(spec, E, FW, p0, maxT=100000):
    raw = Raw(spec)
    tgts = {p: nrm(cc(E, p, FW)) for p in range(max(p0, 2), max(p0, 2) + 9)}
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


def visit_plan(spec, E, QD, FW, s):
    """Witnesses: prefixes of the ER unit (uniform in p, at the anchor) or
    of the overflow stop (deep, under the tovf induction)."""
    ex = Exec(spec)
    plan = {E: ('anchor',)}
    for q in range(4):
        if q in plan:
            continue
        found = None
        for t in range(1, s['nER'] + 1):
            try:
                o = ex.wsteps(True, True, E, [1, 0], 0, [], t)
            except Wall:
                break
            if o[0] == q:
                found = ('er', t, (o[0], tuple(o[1]), o[2], tuple(o[3])))
                break
        if found is None:
            for t in range(1, s['nSTO'] + 1):
                try:
                    o = ex.wsteps(False, True, E, [], 0, [], t)
                except Wall:
                    break
                if o[0] == q:
                    found = ('sto', t,
                             (o[0], tuple(o[1]), o[2], tuple(o[3])))
                    break
        if found is None:
            raise DeriveError('no visit witness for state %s' % LAB[q])
        plan[q] = found
    return plan


HEAD_J = r'''(** * WLJ_@ID@: erase/rebuild wall counter, machine @SPEC@.

    Auto-emitted by tools/counters/emit_wallj.py (UNTRUSTED emitter; the Coq
    kernel re-checks every line below).  Left-growth counter under the
    COMPLEMENTED interleave encoding [Jp], holding a fixed WALL on the far
    side (WALLLAP_NOTE.md, the erase/rebuild shape):

      Cc p = (@EDGE@, (Jp p ++ [S0], S0, @FW@))

    The head stays BLANK across the whole lap; the carry runs as an
    erase-then-rebuild pass:

      ER^j  cycL [S1;S0] -> deposits [S0;S0]  (@NER@ steps per pair) --
            erase the low set pairs, piling blanks onto the far side;
      ST    stop on the clear pair [S1;S1] (@NST@ steps);
      RB^k  cycR [S0] -> [S1] (@NRB@ step per cell) -- rebuild, consuming
            the deposited blanks AND the wall's own (k = 2j+1+@NB@);
      CL    right-open close (@NCL@ steps) rebuilding the wall.

    The overflow branch runs ER^(S j') -- the anchor tail completes a final
    [S1;S0] pair -- then a LEFT-OPEN stop off the deep tape edge (@NSTO@
    steps) and the same rebuild/close.

    Anchoring the wall WITH its trailing blank makes the interior branch
    land EXACTLY, which is what carries the [tovf] well-founded induction
    for the deep visit witnesses.  Validated against the raw simulator on
    BOTH cview branches (interior p = 2..199, overflow K = 2..8; step
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

Definition Cc_@ID@ (p : positive) : cconf := (@EDGE@, (Jp p ++ [S0], S0, @FW@)).
Local Notation Cc := Cc_@ID@.

(** ** The window units (each closed by [reflexivity]) *)
Lemma U_ER_@ID@ : wsteps true true tm @NER@ (@EDGE@,([S1;S0],S0,[])) = Some (@EDGE@,([],S0,[S0;S0])). Proof. reflexivity. Qed.
Lemma U_ST_@ID@ : wsteps true true tm @NST@ (@EDGE@,([S1;S1],S0,[])) = Some (@QD@,([S0],S0,[S0])). Proof. reflexivity. Qed.
Lemma U_RB_@ID@ : wsteps true true tm @NRB@ (@QD@,([],S0,[S0])) = Some (@QD@,([S1],S0,[])). Proof. reflexivity. Qed.
Lemma U_CL_@ID@ : wsteps true false tm @NCL@ (@QD@,([S1;S1],S0,@CLR@)) = Some (@EDGE@,([],S0,@FW@)). Proof. reflexivity. Qed.
Lemma U_STO_@ID@ : wsteps false true tm @NSTO@ (@EDGE@,([],S0,[])) = Some (@QD@,([S0],S0,[S0])). Proof. reflexivity. Qed.
@UVIS@
(** ** Transported phases *)
Lemma phER_@ID@ : forall k L R, csteps tm (@NER@*k) (@EDGE@,(rep [S1;S0] k ++ L,S0,R)) = Some (@EDGE@,(L,S0,rep [S0;S0] k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_ER_@ID@ k L R) as H; cbn [app] in H; exact H. Qed.
Lemma phST_@ID@ : forall L R, csteps tm @NST@ (@EDGE@,(S1::S1::L,S0,R)) = Some (@QD@,(S0::L,S0,S0::R)).
Proof. intros. pose proof (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_ST_@ID@) as H; cbn [app] in H; exact H. Qed.
Lemma phRB_@ID@ : forall k L R, csteps tm (@NRB@*k) (@QD@,(L,S0,rep [S0] k ++ R)) = Some (@QD@,(rep [S1] k ++ L,S0,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RB_@ID@ k L R). Qed.
Lemma phCL_@ID@ : forall L, csteps tm @NCL@ (@QD@,(S1::S1::L,S0,@CLR@)) = Some (@EDGE@,(L,S0,@FW@)).
Proof. intros. pose proof (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_CL_@ID@) as H; cbn [app] in H; exact H. Qed.
Lemma phSTO_@ID@ : forall R, csteps tm @NSTO@ (@EDGE@,([],S0,R)) = Some (@QD@,([S0],S0,S0::R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STO_@ID@). Qed.
@PHVIS@
(** The far side entering the rebuild: the erased pairs, the stop's blank,
    and the wall's own blanks form one run of @NB@ + 1 + 2j cells. *)
Lemma far_run_@ID@ : forall j, S0 :: rep [S0;S0] j ++ @FW@ = rep [S0] (S (2*j) + @NB@) ++ @CLR@.
Proof.
  intro j. rewrite rep_add, rep_dbl. cbn [rep app]. rewrite <- !app_assoc.
  reflexivity.
Qed.

(** ** The interior lap: EXACT *)
Lemma lap_int_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j q0 Ecv. unfold Cc_@ID@.
  destruct (cview_some_J p j q0 Ecv) as (HJp & HJs).
  do 2 eexists. split; [|split].
  + rewrite HJp, <- app_assoc. cbn [app].
    eapply csteps_chain. { apply phER_@ID@. }
    eapply csteps_chain. { apply phST_@ID@. }
    rewrite far_run_@ID@.
    eapply csteps_chain. { apply (phRB_@ID@ (S (2*j) + @NB@)). }
    replace (S (2*j) + @NB@) with (S (S (2*j + @NBM@))) by lia.
    cbn [rep app].
    apply phCL_@ID@.
  + rewrite HJs, rep_dbl, <- !app_assoc. cbn [app].
    replace (2 * j + 1) with (S (2 * j)) by lia.
    cbn [rep app]. rewrite rep_slide. reflexivity.
  + lia.
Qed.

(** ** The overflow lap *)
Lemma lap_ov_@ID@ : forall p j', cview p = (S j', None) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j' Ecv. unfold Cc_@ID@.
  destruct (cview_none_J p j' Ecv) as (HJp & HJs).
  do 2 eexists. split; [|split].
  + rewrite HJp, <- app_assoc. cbn [app]. rewrite pair_fold.
    eapply csteps_chain. { apply (phER_@ID@ (S j')). }
    eapply csteps_chain. { apply phSTO_@ID@. }
    rewrite far_run_@ID@.
    eapply csteps_chain. { apply (phRB_@ID@ (S (2*(S j')) + @NB@)). }
    replace (S (2*(S j')) + @NB@) with (S (S (2*(S j') + @NBM@))) by lia.
    cbn [rep app].
    apply phCL_@ID@.
  + rewrite HJs, rep_dbl, <- !app_assoc. cbn [app].
    replace (2 * S j' + 1) with (S (2 * S j')) by lia.
    cbn [rep app]. rewrite rep_slide. reflexivity.
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

VIS_ER = (
    '(** @QV@: @T@ steps into the erase unit.  At the anchor the unit is\n'
    '    only present when j > 0, so route every p to an all-ones counter by\n'
    '    well-founded induction on [tovf] (interior laps close EXACTLY) --\n'
    '    the overflow anchor always starts with a full [S1;S0] pair. *)\n'
    'Lemma vis_A@N@_@ID@ : forall p, exists k c, csteps tm k (Cc p) = Some c /\\ fst c = @QV@.\n'
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
    '    destruct (cview_none_J p j\' Ecv) as (HJp & _).\n'
    '    unfold Cc_@ID@. exists @T@. eexists. split.\n'
    '    + rewrite HJp, <- app_assoc. cbn [app]. rewrite pair_fold.\n'
    '      cbn [rep app]. apply phVE@N@_@ID@.\n'
    '    + reflexivity.\n'
    'Qed.\n')

VIS_STO = (
    '(** @QV@ fires only in the OVERFLOW stop; reach an all-ones counter by\n'
    '    well-founded induction on [tovf] (interior laps close EXACTLY). *)\n'
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
    '    destruct (cview_none_J p j\' Ecv) as (HJp & _).\n'
    '    unfold Cc_@ID@. eexists. eexists. split.\n'
    '    + rewrite HJp, <- app_assoc. cbn [app]. rewrite pair_fold.\n'
    '      eapply csteps_chain. { apply (phER_@ID@ (S j\')). }\n'
    '      apply phVO@N@_@ID@.\n'
    '    + reflexivity.\n'
    'Qed.\n')


def render_vis(E, QD, FW, s, plan):
    uvis, phvis, lemmas, cases = [], [], [], []
    na = nd = 0
    for q in range(4):
        kind = plan[q][0]
        if kind == 'anchor':
            cases.append('  - (* %s : the anchor state *)\n'
                         '    exists 0. eexists. split; reflexivity.' % ST[q])
        elif kind == 'er':
            na += 1
            t, ext = plan[q][1], plan[q][2]
            uvis.append(
                'Lemma U_VE%d_@ID@ : wsteps true true tm %d '
                '(@EDGE@,([S1;S0],S0,[])) = Some %s. Proof. reflexivity. Qed.'
                % (na, t, cwin(ext)))
            phvis.append(
                'Lemma phVE%d_@ID@ : forall L R, csteps tm %d '
                '(@EDGE@,(S1::S0::L,S0,R)) = Some (%s,(%s,%s,%s)).\n'
                'Proof. intros. pose proof (wsteps_frame _ _ _ _ _ _ _ _ _ _ '
                'L R U_VE%d_@ID@) as H; cbn [app] in H; exact H. Qed.'
                % (na, t, ST[ext[0]], ccons(ext[1], 'L'), SYM[ext[2]],
                   ccons(ext[3], 'R'), na))
            lemmas.append(VIS_ER.replace('@QV@', ST[q])
                          .replace('@N@', str(na)).replace('@T@', str(t)))
            cases.append('  - apply vis_A%d_@ID@.' % na)
        elif kind == 'sto':
            nd += 1
            t, ext = plan[q][1], plan[q][2]
            uvis.append(
                'Lemma U_VO%d_@ID@ : wsteps false true tm %d '
                '(@EDGE@,([],S0,[])) = Some %s. Proof. reflexivity. Qed.'
                % (nd, t, cwin(ext)))
            phvis.append(
                'Lemma phVO%d_@ID@ : forall R, csteps tm %d '
                '(@EDGE@,([],S0,R)) = Some (%s,(%s,%s,%s)).\n'
                'Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R '
                'U_VO%d_@ID@). Qed.'
                % (nd, t, ST[ext[0]], clist(ext[1]), SYM[ext[2]],
                   ccons(ext[3], 'R'), nd))
            lemmas.append(VIS_STO.replace('@QV@', ST[q])
                          .replace('@N@', str(nd)))
            cases.append('  - apply vis_D%d_@ID@.' % nd)
        else:
            raise DeriveError('unknown visit kind %s' % kind)
    return uvis, phvis, lemmas, cases


def emit_source(spec, E, QD, FW, s, plan, p0, boot):
    ID = mach_id(spec)
    nb = nblanks(list(FW))
    CLR = list(FW)[nb:]
    uvis, phvis, lemmas, cases = render_vis(E, QD, FW, s, plan)
    sub = {
        '@ID@': ID, '@SPEC@': spec, '@TABLE@': coq_table(spec),
        '@EDGE@': ST[E], '@QD@': ST[QD],
        '@FW@': clist(FW), '@CLR@': clist(CLR), '@NB@': str(nb),
        '@NBM@': str(nb - 1),
        '@NER@': str(s['nER']), '@NST@': str(s['nST']),
        '@NRB@': str(s['nRB']), '@NCL@': str(s['nCL']),
        '@NSTO@': str(s['nSTO']),
        '@P0@': str(p0), '@BOOT@': str(boot),
        '@UVIS@': ('\n'.join(uvis) + '\n') if uvis else '',
        '@PHVIS@': ('\n'.join(phvis) + '\n') if phvis else '',
        '@VISLEMMAS@': '\n'.join(lemmas),
        '@VISCASES@': '\n'.join(cases),
    }
    out = HEAD_J
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
    chk = os.path.join(scratch, 'pawj_%s.v' % ID)
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
        edge, tail, p0, far = derive_tail_far(spec, 'A', encname='Jp')
        if list(tail) != TL:
            raise DeriveError('anchor tail %s is not [S0]' % tail)
        if not strip0(far):
            raise DeriveError('far side is blank (not a wall machine)')
        E = LAB.index(edge)
        FW = strip0(far) + [0]
        s, U = derive(spec, E, FW)
        msgs, QD, W = check_shapes(E, FW, s, U)
        if msgs:
            raise DeriveError('shape: ' + '; '.join(msgs))
        validate(spec, E, FW, s)
        res.update({'edge': edge, 'FW': FW, 'QD': LAB[QD],
                    'skel': {k: v for k, v in s.items()}})
        p0, boot = boot_probe(spec, E, FW, p0)
        plan = visit_plan(spec, E, QD, FW, s)
    except (DeriveError, Wall, AssertionError, KeyError, IndexError) as e:
        res['why'] = str(e)
        return res
    res.update({'p0': p0, 'boot': boot,
                'plan': {LAB[q]: plan[q][0] for q in plan}})
    if not do_emit:
        res['ok'] = True
        res['why'] = 'derived+validated (not emitted)'
        return res
    ID = mach_id(rspec)
    pref = 'WLJM' if mirror else 'WLJ'
    path = os.path.join(OUTDIR, '%s_%s.v' % (pref, ID))
    if os.path.exists(path) and not force:
        res['ok'] = True
        res['why'] = 'file exists -- skipped emission'
        return res
    try:
        src2 = emit_source(spec, E, QD, FW, s, plan, p0, boot)
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
    ap.add_argument('--scratch', default='/tmp')
    a = ap.parse_args()
    specs = list(a.specs)
    if a.list:
        specs += [x.strip() for x in open(a.list) if x.strip()]
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
            extra = ' E=%s QD=%s FW=%s skel=%s plan=%s' % (
                r['edge'], r['QD'], r['FW'], r['skel'], r.get('plan'))
        print('%s %s %s%s' % ('PASS' if r['ok'] else 'FAIL', spec,
                              r.get('why', ''), extra))
        sys.stdout.flush()
    if a.json:
        with open(a.json, 'w') as f:
            json.dump(out, f, indent=1, default=str)
    print('== %d/%d passed' % (sum(1 for r in out if r['ok']), len(out)))


if __name__ == '__main__':
    main()
