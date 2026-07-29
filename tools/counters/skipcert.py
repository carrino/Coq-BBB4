#!/usr/bin/env python3
"""UNTRUSTED emitter: SKIP counters -- the "no overflow phase" bucket.

WAVE26 section 8 (John's decode, verified): these machines are ordinary
binary counters whose overflow sweep writes the LSB pair's data cell LAST,
already incremented -- so the counter NEVER RESTS AT A POWER OF TWO and
`phase_mid`, waiting for E(2^K) exactly, reported `no overflow phase` for
the whole bucket.  The overflow lap is

    fill(2^K - 1)  ->  2^K + s        (s = 1 or 2, read off the machine)

and the skipped values exist only as the machine's TRANSIENT forms.  The
route (RESIDUE_PROMPT item 3, no checker extension):

    Cc p = if p is skipped then VIRT p else E p ++ tail

closed by [LapGlue.glue_neverqh] directly, with [Counters/SkipGlue.v]
supplying the power-of-two view ([pexp]/[pexpi]) and the reach/vis plumbing
([reach_ovf_skip]/[vis_via_skip]).  All laps are ordinary affine chains:

    interior            E p -> E (succ p)      (pexp p = None)
    fill -> VIRT        the overflow sweep     (exact)
    VIRT -> E(2^K + 1)  the landing            (up to lift)    [s = 1]
    VIRT -> VIRT2 -> E(2^K + 2)                                [s = 2]

This module is scan + extractor + derive + validate + render:
  * [phase_skip] is `nestcert.phase_mid` with the closure reading s OFF THE
    MACHINE: the phase ends at the first E(2^K + s), s = 0..SMAX;
  * [virt_candidates] extracts the VIRT anchor family from two adjacent
    phases (K and K+1): a configuration pair that aligns as one sside
    family (pre ++ rep u (j + b) ++ post) is a candidate split point;
  * [derive_skip] derives the chains through the best candidate and
    differentially validates EVERY lap (interior, fill, virt) against the
    raw simulator -- exact step counts and exact configurations;
  * [render_skip] emits the board (prefix SKIP_*).

Everything here is untrusted: the kernel re-runs [srun] on every chain, and
the anchor glue is proved, not assumed.

Usage
  skipcert.py --list FILE [--emit] [--json OUT]
  skipcert.py --spec SPEC [--emit]
  skipcert.py --scan --list FILE      (classify skip sets only)
"""
import argparse
import collections
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

import emit_lapcert as EL                                          # noqa: E402
from emit_lapcert import (ENCDATA, ENC, ENCS, confs, boot_probe,   # noqa: E402
                          eqlift, sim, cchain, cconf, coqc)
from emit_interleave import (parse, LAB, ST, SYM, carry, mach_id,  # noqa: E402
                             coq_table, clist, DeriveError)
from mirror_common import mirror_spec, mirrorize                   # noqa: E402
from ovfshape import anchor_times                                  # noqa: E402
import lapcert as LC                                               # noqa: E402

PREFIX = 'SKIP'
OUTDIR = os.path.join(REPO, 'theories', 'Machines', 'Counters')

SMAX = 3          # highest skip the phase closure will read
PMAX = 300        # anchor_times horizon
NOISE = 8         # small-p region where concrete skip noise is tolerated


class SkipError(Exception):
    """This machine does not take the skip route."""


# ------------------------------------------------------------------ scan ---

def classify_skip(missing, pmax):
    """The machine's skip set, read off the anchor-times gaps.  Returns
    (s, noise) with s in {1, 2}: missing = {2^k (, 2^k+1)} above NOISE,
    anything below NOISE is per-machine concrete noise."""
    pows = [2 ** k for k in range(1, 20) if 2 ** k <= pmax - 2]
    hi = [m for m in missing if m >= NOISE]
    noise = [m for m in missing if m < NOISE]
    for s in (1, 2):
        want = set()
        for p in pows:
            want.update(p + i for i in range(s))
        if set(hi) == set(w for w in want if w >= NOISE):
            # the noise region must still be consistent with the skip set
            # plus concrete extras -- anything goes below NOISE
            return s, noise
    return None, noise


def phase_skip(tab, st0, encf, tail, far, K=6, smax=SMAX, maxT=400000):
    """One overflow phase from E(2^K - 1), closing at the first
    E(2^K + s) for s = 0..smax.  Returns (s, trace) with trace the raw
    configuration at every step, phase end included."""
    tail, far = tuple(tail), tuple(far)
    cfg = (st0, tuple(encf(2 ** K - 1)) + tail, 0, far)
    wants = {}
    for s in range(smax + 1):
        w = (st0, LC.rstrip0(tuple(encf(2 ** K + s)) + tail),
             LC.rstrip0(far))
        wants[w] = s
    trace = [cfg]
    for _ in range(maxT):
        try:
            cfg = LC.wstep(tab, False, False, cfg)
        except LC.Halt:
            break
        trace.append(cfg)
        q, l, h, r = cfg
        if h == 0:
            s = wants.get((q, LC.rstrip0(l), LC.rstrip0(r)))
            if s is not None:
                return s, trace
    raise SkipError('no overflow phase closure at K=%d, s<=%d' % (K, smax))


# ------------------------------------------------------------- extraction ---

def _align_side(l0, l1, j0):
    """All sside families (pre, u, a=1, b, post) with den(j0) = l0 and
    den(j0 + 1) = l1.  Sides are adjacent-first tuples."""
    l0, l1 = tuple(l0), tuple(l1)
    out = []
    ulen = len(l1) - len(l0)
    if ulen == 0:
        if l0 == l1:
            out.append((l0, (), 0, 0, ()))
        return out
    if ulen < 0:
        return out
    seen = set()
    for i in range(len(l0) + 1):
        u = l1[i:i + ulen]
        if l1 != l0[:i] + u + l0[i:]:
            continue
        # maximal run of u around the insertion point
        lo = i
        while lo >= ulen and l0[lo - ulen:lo] == u:
            lo -= ulen
        hi = i
        while hi + ulen <= len(l0) and l0[hi:hi + ulen] == u:
            hi += ulen
        reps = (hi - lo) // ulen
        b = reps - j0
        pre, post = l0[:lo], l0[hi:]
        if b < 0:
            # fewer copies than the count: fold the deficit into the count
            # by moving the family out of reach -- not expressible as an
            # sside (b is a nat); skip
            continue
        key = (pre, u, b, post)
        if key in seen:
            continue
        seen.add(key)
        out.append((pre, u, 1, b, post))
    return out


def virt_candidates(tr0, tr1, K0, st0):
    """Candidate virtual-anchor families from two adjacent phases.

    A candidate is a time pair (t0, t1) whose configurations align as ONE
    sside family on the left with identical state, head symbol and (flat)
    right side.  Ordered by phase position.  The phase-end configurations
    are excluded (they are the NEXT anchor, not a virtual one)."""
    j0 = K0 - 1
    out = []
    for t0 in range(1, len(tr0) - 1):
        q0, l0, h0, r0 = tr0[t0]
        for t1 in range(1, len(tr1) - 1):
            q1, l1, h1, r1 = tr1[t1]
            if q1 != q0 or h1 != h0 or tuple(r0) != tuple(r1):
                continue
            for fam in _align_side(l0, l1, j0):
                out.append((t0, t1, (q0, fam, h0,
                                     (tuple(r0), (), 0, 0, ()))))
    return out


def _chain2(tab, er, src, dst):
    """derive_chain with the left-open flag searched."""
    for el in (True, False):
        ch = None
        try:
            ch = LC.derive_chain(tab, el, er, src, dst)
        except Exception:                                          # noqa: BLE001
            ch = None
        if ch is not None:
            rn = LC.srun(tab, el, er, ch, src)
            if rn is not None and rn[0] == dst:
                return ch, el, (rn[1], rn[2])
    return None, None, None


# ------------------------------------------------------------- derivation ---

def derive_skip(dspec, edge, tail, enc, far):
    tab = parse(dspec)
    st0 = LAB.index(edge)
    encf = ENC[enc]
    d = ENCDATA[enc]
    tail, far = tuple(tail), tuple(far)
    if d['obS'] != 0:
        raise SkipError('obS != 0 alphabets not wired for the skip route')

    # the skip, read off the machine at two sizes (they must agree)
    s6, tr6 = phase_skip(tab, st0, encf, tail, far, K=6)
    s7, tr7 = phase_skip(tab, st0, encf, tail, far, K=7)
    if s6 != s7:
        raise SkipError('skip disagrees across K: %d vs %d' % (s6, s7))
    s = s6
    if s == 0:
        raise SkipError('s = 0: no skip, the flat route applies')
    if s > 2:
        raise SkipError('s = %d: only 1 and 2 are wired' % s)

    # the interior chain (ONE mode only; split-mode machines are logged)
    A0, A1, B0, B1 = confs(enc, st0, tail, far)
    chi = LC.derive_chain(tab, False, True, A0, A1)
    if chi is None:
        raise SkipError('no interior chain (one mode)')
    ri = LC.srun(tab, False, True, chi, A0)
    if ri is None or ri[0] != A1:
        raise SkipError('interior srun mismatch')
    ci = (ri[1], ri[2])
    if ci[1] == 0:
        raise SkipError('interior lap of zero length at j=0')

    # the E-form landing target: E(2^K + 1) = uS ++ rep uD j ++ soD
    # (s = 1), or E(2^K + 2) = uD ++ uS ++ rep uD j'' ++ soD at the
    # reindexed count (s = 2).
    F = (far, (), 0, 0, ())
    cands = virt_candidates(tr6, tr7, 6, st0)
    if not cands:
        raise SkipError('no virtual anchor family aligns')

    got = None
    if s == 1:
        E1 = (st0, (d['uS'], d['uD'], 1, 0, d['soD']), 0, F)
        tried = 0
        for (t0, t1, V) in cands:
            chf, elf, cf = _chain2(tab, True, B0, V)
            if chf is None:
                continue
            chv, elv, cv = _chain2(tab, True, V, E1)
            if chv is None:
                continue
            tried += 1
            got = dict(s=1, V=V, chf=chf, elf=elf, cf=cf,
                       chv=chv, elv=elv, cv=cv, E1=E1, tv=(t0, t1))
            break
        if got is None:
            raise SkipError('no chain pipeline through any of %d candidates'
                            % len(cands))
    else:
        # s = 2: fill -> V -> W -> E(2^K + 2).  W's landing target carries
        # the reindexed count: source W at j = S j'' (one unit folded into
        # the prefix), target count j''.
        E2 = (st0, (d['uD'] + d['uS'], d['uD'], 1, 0, d['soD']), 0, F)
        for iv in range(len(cands)):
            t0v, t1v, V = cands[iv]
            chf, elf, cf = _chain2(tab, True, B0, V)
            if chf is None:
                continue
            for iw in range(len(cands)):
                t0w, t1w, W = cands[iw]
                if t0w <= t0v:
                    continue
                chv, elv, cv = _chain2(tab, True, V, W)
                if chv is None:
                    continue
                # the reindexed W: one unit copy folded into the prefix
                wq, (wpre, wu, wa, wb, wpost), wh, wr = W
                if wa != 1:
                    continue
                WS = (wq, (tuple(wpre) + tuple(wu), wu, 1, wb, wpost), wh, wr)
                chw, elw, cw = _chain2(tab, True, WS, E2)
                if chw is None:
                    continue
                got = dict(s=2, V=V, W=W, WS=WS, chf=chf, elf=elf, cf=cf,
                           chv=chv, elv=elv, cv=cv,
                           chw=chw, elw=elw, cw=cw, E2=E2,
                           tv=(t0v, t1v), tw=(t0w, t1w))
                break
            if got is not None:
                break
        if got is None:
            raise SkipError('no s=2 chain pipeline (%d candidates)'
                            % len(cands))

    D = dict(spec=dspec, enc=enc, st0=st0, tail=list(tail), far=list(far),
             chi=chi, ci=ci, A0=A0, A1=A1, B0=B0)
    D.update(got)

    ok, why = validate_skip(tab, st0, encf, tail, far, D)
    if not ok:
        raise SkipError('validation: ' + why)
    D['val'] = why

    # bootstrap: the earliest measured anchor at p >= 9 that is not virtual
    at = anchor_times(dspec, st0, encf, tail, far, PMAX, 4000000)
    best = None
    for p, t in at.items():
        if p < 9 or _isvirt(p, s):
            continue
        if best is None or t < at[best]:
            best = p
    if best is None:
        raise SkipError('no bootstrap anchor')
    D['p0'], D['boot'] = best, at[best]

    # visits: prefixes of the fill chain, then of the virt chain(s)
    vis = {}
    for q in range(4):
        pre = LC.reach_state(tab, D['elf'], True, B0, D['chf'], q)
        if pre is not None:
            vis[q] = ('fill', pre)
            continue
        pre = LC.reach_state(tab, D['elv'], True, D['V'], D['chv'], q)
        if pre is not None:
            vis[q] = ('virt', pre)
            continue
        if s == 2:
            pre = LC.reach_state(tab, D['elw'], True, D['WS'], D['chw'], q)
            if pre is not None:
                vis[q] = ('virt2', pre)
                continue
        pre = LC.reach_state(tab, False, True, A0, chi, q)
        if pre is not None:
            raise SkipError('state %s fires only in the interior lap'
                            % LAB[q])
        raise SkipError('no visit witness for state %s' % LAB[q])
    D['vis'] = vis
    return D


def _isvirt(p, s):
    if p & (p - 1) == 0 and p >= 2:
        return True
    return s == 2 and (p - 1) & (p - 2) == 0 and p - 1 >= 2


def _den(side, j):
    pre, u, a, b, post = side
    return tuple(pre) + tuple(u) * (a * j + b) + tuple(post)


def _denc(sc, j, far):
    q, ls, h, rs = sc
    return (q, _den(ls, j), h, _den(rs, j))


def validate_skip(tab, st0, encf, tail, far, D, hi=200):
    """Differential validation of EVERY lap against the raw simulator:
    exact step counts, exact intermediate (virtual) anchors, [lift]-equal
    landings."""
    tail, far = tuple(tail), tuple(far)
    s = D['s']
    n = 0
    for p in range(2, hi):
        j, ov = carry(p)
        if _isvirt(p, s):
            # the virt lap(s), from the extracted forms
            k = (p.bit_length() - 1) - 1
            if p & (p - 1) == 0:
                start = _denc(D['V'], k, far)
                if s == 1:
                    steps = D['cv'][0] * k + D['cv'][1]
                    want = (st0, tuple(encf(p + 1)) + tail, 0, far)
                else:
                    steps = D['cv'][0] * k + D['cv'][1]
                    want = _denc(D['W'], k, far)
            else:
                k = ((p - 1).bit_length() - 1) - 1
                start = _denc(D['W'], k, far)
                if k == 0:
                    continue        # p = 3: fenced below p0
                steps = D['cw'][0] * (k - 1) + D['cw'][1]
                want = (st0, tuple(encf(p + 1)) + tail, 0, far)
            got = sim(tab, start, steps)
            if not eqlift(got, want):
                return False, 'p=%d virt lap: %d steps -> %r want %r' % (
                    p, steps, got, want)
        elif ov:
            # fill -> V, landing EXACTLY on the virtual anchor
            steps = D['cf'][0] * (j - 1) + D['cf'][1]
            start = (st0, tuple(encf(p)) + tail, 0, far)
            want = _denc(D['V'], j - 1, far)
            got = sim(tab, start, steps)
            if not eqlift(got, want):
                return False, 'p=%d fill lap: %d steps -> %r want %r' % (
                    p, steps, got, want)
        else:
            steps = D['ci'][0] * j + D['ci'][1]
            start = (st0, tuple(encf(p)) + tail, 0, far)
            want = (st0, tuple(encf(p + 1)) + tail, 0, far)
            got = sim(tab, start, steps)
            if not eqlift(got, want):
                return False, 'p=%d int lap: %d steps -> %r want %r' % (
                    p, steps, got, want)
        n += 1
    return True, '%d anchors (s=%d)' % (n, s)


# ------------------------------------------------------------------ scan ---

def scan(spec):
    """Classify the machine's skip set over every anchor candidate."""
    for mirrored in (False, True):
        dspec = mirror_spec(spec) if mirrored else spec
        for (edge, tail, p0, enc, far) in EL.anchors(dspec):
            st0 = LAB.index(edge)
            encf = ENC[enc]
            try:
                at = anchor_times(dspec, st0, encf, tail, far, PMAX, 4000000)
            except Exception:                                      # noqa: BLE001
                continue
            if len(at) < PMAX // 2:
                continue
            missing = [p for p in range(1, PMAX + 1) if p not in at]
            s, noise = classify_skip(missing, PMAX)
            if s is None:
                return dict(spec=spec, ok=False, why='unnamed skip set',
                            enc=enc, mirror=mirrored, missing=missing[:24])
            return dict(spec=spec, ok=True, s=s, noise=noise, enc=enc,
                        edge=edge, tail=list(tail), far=list(far),
                        mirror=mirrored)
    return dict(spec=spec, ok=False, why='no anchor family')


# --------------------------------------------------------------- render ---

HEADER = r'''(** * SKIP_@ID@: machine @SPEC@, boarded by CERTIFICATE (SKIP route).

    Auto-emitted by tools/counters/skipcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  A left-growth binary
    counter under the @ENC@ digit alphabet (@ENCMOD@.v) that NEVER RESTS AT
    A POWER OF TWO: the overflow lap runs fill(2^K - 1) -> 2^K + @S@, so the
    skipped value@SPLUR@ exist@SSING@ only as the machine's transient form@SPLUR@
    (WAVE26 section 8).  The anchor family carries VIRTUAL anchors there:

      Cc p = @CCDOC@

    Laps are DATA for [Checkers/LapDecider.v], run by the kernel through
    [vm_compute] and discharged by [srun_sound]:

      interior  (pexp p = None):   @NI@ steps, exact
      fill      (cview (S j, None)): @NF@ steps, exact, onto the VIRTUAL anchor
@NVDOC@
    [Counters/SkipGlue.v] supplies the power-of-two view and the reach/vis
    plumbing; the closer is [LapGlue.glue_neverqh] directly.

    Differentially validated against the raw simulator on EVERY branch --
    step counts AND configurations -- for @VAL@.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter JpCounter
                                  @ENCMOD@ LapCertGlue LapCertGlueLift
                                  IXPGadgets SkipGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_@ID@ (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_@ID@.

(** @SPEC@ *)
Definition tm_@ID@ : TM := fun q s => match q, s with
@TABLE@ end.
Local Notation tm := tm_@ID@.

@CCDEF@
Local Notation Cc := Cc_@ID@.

Definition virt_@ID@ (p : positive) : bool := @VIRTDEF@.
Local Notation virt := virt_@ID@.

(** ** The certificate *)

Definition A0_@ID@ : sconf := @A0@.
Definition A1_@ID@ : sconf := @A1@.
Definition chi_@ID@ : list lstep := @CHI@.

Lemma run_int_@ID@ : srun tm false true chi_@ID@ A0_@ID@ = Some (A1_@ID@, @CAI@, @CBI@).
Proof. vm_compute. reflexivity. Qed.

Definition B0_@ID@ : sconf := @B0@.
Definition V0_@ID@ : sconf := @V0@.
Definition chf_@ID@ : list lstep := @CHF@.

Lemma run_fill_@ID@ : srun tm @ELF@ true chf_@ID@ B0_@ID@ = Some (V0_@ID@, @CAF@, @CBF@).
Proof. vm_compute. reflexivity. Qed.

@VIRTCERT@

(** ** Anchor glue -- the only per-machine mathematics *)

(** The alphabet at a power of two: all digits clear over the terminator. *)
Lemma apow_@ID@ : forall r k, pexp r = Some k -> @ENC@ r = rep @UD@ k ++ @SOD@.
Proof.
  induction r; intros k H; simpl in H.
  - discriminate.
  - destruct (pexp r) as [k'|] eqn:E; [|discriminate].
    injection H as <-. simpl. rewrite (IHr k' eq_refl). reflexivity.
  - injection H as <-. reflexivity.
Qed.

Lemma gsi_@ID@ : forall p j q0, cview p = (j, Some q0) -> pexp p = None -> @GSIH@
  Cc p = cden (@ENC@ q0 ++ @TAIL@) [] j A0_@ID@.
Proof.
  intros p j q0 E Hx @GSIHN@. unfold Cc_@ID@. rewrite Hx. @GSIRED@
  destruct (@ENCMOD@.@SOME@ p j q0 E) as (H1 & _).
  unfold cden, A0_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep @US@ j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_@ID@ : forall p j q0, cview p = (j, Some q0) -> pexp p = None -> @GSIH@
  cden (@ENC@ q0 ++ @TAIL@) [] j A1_@ID@ = Cc (Pos.succ p).
Proof.
  intros p j q0 E Hx @GSIHN@. unfold Cc_@ID@.
  rewrite (pexp_succ_int p j q0 E). @GEIRED@
  destruct (@ENCMOD@.@SOME@ p j q0 E) as (_ & H2).
  unfold cden, A1_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep @UD@ j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_@ID@ : forall p j q0, cview p = (j, Some q0) -> pexp p = None -> @GSIH@
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hx @GSIHN@. exists (@CAI@ * j + @CBI@). split; [lia|].
  rewrite (gsi_@ID@ p j q0 E Hx @GSIHN@).
  rewrite (srun_sound tm false true chi_@ID@ A0_@ID@ A1_@ID@ @CAI@ @CBI@
             run_int_@ID@ (@ENC@ q0 ++ @TAIL@) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_@ID@ p j q0 E Hx @GSIHN@).
Qed.

Lemma gso_@ID@ : forall p j, cview p = (S j, None) -> @GSOH@
  Cc p = cden [] [] j B0_@ID@.
Proof.
  intros p j E @GSOHN@. unfold Cc_@ID@.
  destruct (pexp p) as [[|k]|] eqn:Epx.
  - rewrite (pexp_zero p Epx) in E |- *.
    cbn in E. injection E as <-. reflexivity.
  - exfalso. exact (pexp_not_fill p j k E Epx).
  - @GSORED@destruct (@ENCMOD@.@NONE@ p j E) as (H1 & _).
    unfold cden, B0_@ID@; cbn [c_st c_l c_h c_r].
    unfold sden; cbn [s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The fill lap lands EXACTLY on the virtual anchor. *)
Lemma geov_@ID@ : forall p j, cview p = (S j, None) ->
  cden [] [] j V0_@ID@ = Cc (Pos.succ p).
Proof.
  intros p j E. unfold Cc_@ID@.
  rewrite (pexp_succ_fill p (S j) E).
  unfold cden, V0_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + @VB@) with @VBJ@ by lia.
  first [ reflexivity
        | cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapf_@ID@ : forall p j, cview p = (S j, None) -> @GSOH@
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j E @GSOHN@. exists (@CAF@ * j + @CBF@). split; [lia|].
  rewrite (gso_@ID@ p j E @GSOHN@).
  rewrite (srun_sound tm @ELF@ true chf_@ID@ B0_@ID@ V0_@ID@ @CAF@ @CBF@
             run_fill_@ID@ [] [] j
             ltac:(@ELFH@) ltac:(reflexivity)).
  f_equal. exact (geov_@ID@ p j E).
Qed.

Lemma lbl_@ID@ : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

@VIRTGLUE@

(** ** The lap *)

Lemma lap_@ID@ : forall p, (@P0@ <= p)%positive -> exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p Hp. destruct (cview p) as [j oq] eqn:E; destruct oq as [q0|].
@LAPINT@
@LAPFILL@
Qed.

(** ** SkipGlue's hypotheses *)

Lemma hint_@ID@ : forall p j q0, (@P0@ <= p)%positive ->
  cview p = (j, Some q0) -> virt p = false ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
@HINT@
Qed.

Lemma hsucc_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  virt p = false -> virt (Pos.succ p) = false.
Proof.
@HSUCC@
Qed.

Lemma hvlap_@ID@ : forall p, (@P0@ <= p)%positive -> virt p = true ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
@HVLAP@
Qed.

Lemma hvrun_@ID@ : forall p, (@P0@ <= p)%positive -> virt p = true ->
  virt (Pos.succ p) = true -> virt (Pos.succ (Pos.succ p)) = false.
Proof.
@HVRUN@
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

(** ** Visits

    Every state fires inside the overflow sweep (fill chain) or in the
    virtual laps behind it; [SkipGlue.vis_via_skip] carries the fill-anchor
    witnesses to every anchor at or above p0. *)

Lemma viso_@ID@ : forall (l : list lstep) (q : St),
  srun_st tm @ELF@ true l B0_@ID@ = Some q ->
  forall p j, cview p = (S j, None) -> @GSOH@
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E @GSOHN@.
  apply (vis_of_run tm Cc @ELF@ true l B0_@ID@ p j [] []);
    [exact Hst | ltac:(intro; @ELFH2@) | reflexivity
     | exact (gso_@ID@ p j E @GSOHN@)].
Qed.

@VISVLEM@

Lemma vis_@ID@ : forall p q, (@P0@ <= p)%positive ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q Hp.
  apply (vis_via_skip tm Cc virt @P0@ hint_@ID@ hsucc_@ID@ hvlap_@ID@
           hvrun_@ID@ q); [| exact Hp].
  intros p1 j1 Hp1 E1.
@VISFENCE@
  destruct q.
@VISITS@
Qed.

Theorem nqh_@ID@ : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc @P0@). - exact boot_@ID@. - intros p Hp. apply (lap_@ID@ p Hp). - intros p q Hp. apply (vis_@ID@ p q Hp). Qed.

Theorem nonhalt_@ID@ : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_@ID@. Qed.
'''

CC_S1 = r'''Definition Cc_@ID@ (p : positive) : cconf :=
  match pexp p with
  | Some (S k) => (@VST@, (@VPRE@ ++ rep @VU@ k ++ @VPOST@, @VH@, @VFARL@))
  | _ => (@ST0@, (@ENC@ p ++ @TAIL@, S0, @FAR@))
  end.'''

VIRT_S1 = r'''match pexp p with Some (S _) => true | _ => false end'''

VIRTCERT_S1 = r'''Definition E1_@ID@ : sconf := @E1@.
Definition chv_@ID@ : list lstep := @CHV@.

Lemma run_virt_@ID@ : srun tm @ELV@ true chv_@ID@ V0_@ID@ = Some (E1_@ID@, @CAV@, @CBV@).
Proof. vm_compute. reflexivity. Qed.'''

VIRTGLUE_S1 = r'''Lemma gsv_@ID@ : forall p k, pexp p = Some (S k) ->
  Cc p = cden [] [] k V0_@ID@.
Proof.
  intros p k Hx. unfold Cc_@ID@. rewrite Hx.
  unfold cden, V0_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + @VB@) with @VBK@ by lia.
  first [ reflexivity
        | cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The landing: E(2^(S k) + 1) = uS ++ rep uD k ++ soD, one trailing
    blank short of the anchor tail -- invisible to [lift]. *)
Lemma gev_@ID@ : forall p k, pexp p = Some (S k) ->
  lift (cden [] [] k E1_@ID@) = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hx.
  destruct (pexp_shape p k Hx) as (r & -> & Hr).
  unfold Cc_@ID@. cbn [Pos.succ pexp].
  assert (HD : cden [] [] k E1_@ID@ = (@ST0@, (@E1DEN@, S0, @E1FAR@))).
  { unfold cden, E1_@ID@, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * k + 0) with k by lia.
    first [ reflexivity
      | cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : (@ST0@, (@ENC@ (xI r) ++ @TAIL@, S0, @FAR@))
             = (@ST0@, (@E1PAD@, S0, @FAR@)) :> cconf).
  { simpl @ENC@. rewrite (apow_@ID@ r k Hr).
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. @VCLOSE@
Qed.

Lemma lapv_@ID@ : forall p k, pexp p = Some (S k) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hx.
  exists (@CAV@ * k + @CBV@), (cden [] [] k E1_@ID@).
  split; [lia|]. split; [| exact (gev_@ID@ p k Hx)].
  rewrite (gsv_@ID@ p k Hx).
  exact (srun_sound tm @ELV@ true chv_@ID@ V0_@ID@ E1_@ID@ @CAV@ @CBV@
           run_virt_@ID@ [] [] k ltac:(@ELVH@) ltac:(reflexivity)).
Qed.'''

LAPINT_S1 = r'''  - destruct (pexp p) as [[|k]|] eqn:Epx.
    + rewrite (pexp_zero p Epx) in E. cbn in E. discriminate.
    + destruct (lapv_@ID@ p k Epx) as (n & c' & Hn & Hrun & Hl).
      exists n, c'. split; [exact Hrun | split; [exact Hl | exact Hn]].
    + destruct (lapi_@ID@ p j q0 E Epx) as (n & Hn & Hrun).
      exists n, (Cc (Pos.succ p)).
      split; [exact Hrun | split; [reflexivity | exact Hn]].'''

LAPFILL_S1 = r'''  - destruct (cview_pos p j E) as (j' & ->).
    destruct (lapf_@ID@ p j' E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].'''

HINT_S1 = r'''  intros p j q0 _ E Hv. unfold virt_@ID@ in Hv.
  destruct (pexp p) as [[|k]|] eqn:Epx.
  - rewrite (pexp_zero p Epx) in E. cbn in E. discriminate.
  - discriminate Hv.
  - exact (lapi_@ID@ p j q0 E Epx).'''

HSUCC_S1 = r'''  intros p j q0 E _. unfold virt_@ID@.
  rewrite (pexp_succ_int p j q0 E). reflexivity.'''

HVLAP_S1 = r'''  intros p _ Hv. unfold virt_@ID@ in Hv.
  destruct (pexp p) as [[|k]|] eqn:Epx; try discriminate.
  exact (lapv_@ID@ p k Epx).'''

HVRUN_S1 = r'''  intros p _ H1 H2. exfalso. unfold virt_@ID@ in *.
  destruct (pexp p) as [[|k]|] eqn:E1; try discriminate.
  rewrite (pexp_succ_virt p k E1) in H2. discriminate.'''

VISV_LEMMA = r'''(** A state that fires only in the virtual lap: the fill lap runs to the
    virtual anchor EXACTLY, then the virt-chain prefix fires. *)
Lemma visv_@ID@ : forall (l : list lstep) (q : St),
  srun_st tm @ELV@ true l V0_@ID@ = Some q ->
  forall p j, cview p = (S j, None) -> @GSOH@
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E @GSOHN@.
  destruct (vis_of_run tm (fun _ => cden [] [] j V0_@ID@) @ELV@ true l
              V0_@ID@ 1%positive j [] [] q Hst
              ltac:(intro; @ELVH2@) ltac:(reflexivity) eq_refl)
    as (k & c & Hk & Hc).
  exists ((@CAF@ * j + @CBF@) + k), c. split; [| exact Hc].
  rewrite csteps_add.
  rewrite (gso_@ID@ p j E @GSOHN@).
  rewrite (srun_sound tm @ELF@ true chf_@ID@ B0_@ID@ V0_@ID@ @CAF@ @CBF@
             run_fill_@ID@ [] [] j
             ltac:(@ELFH@) ltac:(reflexivity)).
  exact Hk.
Qed.'''


def _fmtside(side):
    pre, u, a, b, post = side
    return 'mkS %s %s %d %d %s' % (clist(pre), clist(u), a, b, clist(post))


def _fmtconf(c):
    q, ls, h, rs = c
    return 'mkC %s (%s) %s (%s)' % (ST[q], _fmtside(ls), SYM[h], _fmtside(rs))


def _pad(base, n):
    """base wrapped in n one-blank paddings: ((base ++ [S0]) ++ [S0]) ..."""
    out = base
    for _ in range(n):
        out = '(%s) ++ [S0]' % out
    return out


def render_skip(D):
    spec = D['spec']
    ID = mach_id(spec)
    d = ENCDATA[D['enc']]
    s = D['s']
    if s != 1:
        raise SkipError('render: only s=1 wired so far')

    vq, (vpre, vu, va, vb, vpost), vh, vr = D['V']
    if va != 1 and vu:
        raise SkipError('render: virt anchor a != 1')
    vfar = tuple(vr[0]) + tuple(vr[4])
    if vr[1]:
        raise SkipError('render: virt anchor far side carries a rep')
    if not vu:
        raise SkipError('render: virt anchor is flat (no rep)')

    # the E1 landing vs the true anchor: E(2^(S k)+1) ++ tail has the
    # reached word plus trailing blanks only
    e1 = D['E1']
    e1den = '%s ++ rep %s k ++ %s' % (clist(e1[1][0]), clist(e1[1][1]),
                                      clist(e1[1][4]))
    want = tuple(d['uS']) + tuple(d['soD']) + tuple(D['tail'])
    got = tuple(e1[1][0]) + tuple(e1[1][4])
    npad = len(want) - len(got)
    if npad < 0 or want[:len(got)] != got or any(want[len(got):]):
        raise SkipError('render: E1 landing %r vs anchor %r' % (got, want))
    e1far = clist([x for x in (tuple(e1[3][0]) + tuple(e1[3][4]))])
    ffar = tuple(D['far'])
    gfar = tuple(e1[3][0]) + tuple(e1[3][4])
    if LC.rstrip0(gfar) != LC.rstrip0(ffar):
        raise SkipError('render: E1 far %r vs %r' % (gfar, ffar))
    nfarpad = len(gfar) - len(ffar)
    if nfarpad < 0 or gfar[:len(ffar)] != ffar:
        raise SkipError('render: E1 far pad %r vs %r' % (gfar, ffar))

    vclose = []
    if npad:
        vclose.append('rewrite !lbl_%s.' % ID)
    if nfarpad:
        vclose.append('rewrite !lift_app_blank.')
    vclose.append('reflexivity.')

    vis = []
    for q in range(4):
        mode, pre = D['vis'][q]
        if mode == 'fill' and not pre:
            vis.append('  - (* %s: the anchor state *)\n'
                       '    rewrite (gso_%s p1 j1 E1).\n'
                       '    exists 0. eexists. split; reflexivity.'
                       % (ST[q], ID))
        elif mode == 'fill':
            vis.append('  - (* %s *)\n'
                       '    exact (viso_%s %s %s\n'
                       '             ltac:(vm_compute; reflexivity) p1 j1 E1%s).'
                       % (ST[q], ID, cchain(pre), ST[q], '@GSOA@'))
        elif mode == 'virt':
            vis.append('  - (* %s: fires in the virtual lap *)\n'
                       '    exact (visv_%s %s %s\n'
                       '             ltac:(vm_compute; reflexivity) p1 j1 E1%s).'
                       % (ST[q], ID, cchain(pre), ST[q], '@GSOA@'))
        else:
            raise SkipError('render: visit mode %s not wired' % mode)

    need_visv = any(m == 'virt' for m, _ in D['vis'].values())

    reps = {
        '@ID@': ID, '@SPEC@': spec, '@S@': str(s),
        '@SPLUR@': '' if s == 1 else 's',
        '@SSING@': 's' if s == 1 else '',
        '@CCDOC@': ('VIRT k at p = 2^(S k), else E p ++ tail' if s == 1 else
                    'VIRT anchors at p = 2^(S k) and 2^(S k)+1, else E p ++ tail'),
        '@ENC@': d.get('fn', D['enc']),
        '@ENCMOD@': d['mod'], '@SOME@': d['some'], '@NONE@': d['none'],
        '@ST0@': ST[D['st0']], '@TAIL@': clist(D['tail']),
        '@FAR@': clist(D['far']), '@TABLE@': coq_table(spec),
        '@US@': clist(d['uS']), '@UD@': clist(d['uD']),
        '@SOD@': clist(d['soD']),
        '@CCDEF@': CC_S1, '@VIRTDEF@': VIRT_S1,
        '@VST@': ST[vq], '@VPRE@': clist(vpre), '@VU@': clist(vu),
        '@VPOST@': clist(vpost), '@VH@': SYM[vh], '@VFARL@': clist(vfar),
        '@VB@': str(vb),
        '@VBK@': '(%s)' % ' '.join(['S'] * vb + ['k']) if vb else 'k',
        '@VBJ@': '(%s)' % ' '.join(['S'] * vb + ['j']) if vb else 'j',
        '@A0@': _fmtconf(D['A0']), '@A1@': _fmtconf(D['A1']),
        '@CHI@': cchain(D['chi']),
        '@CAI@': str(D['ci'][0]), '@CBI@': str(D['ci'][1]),
        '@B0@': _fmtconf(D['B0']), '@V0@': _fmtconf(D['V']),
        '@CHF@': cchain(D['chf']),
        '@CAF@': str(D['cf'][0]), '@CBF@': str(D['cf'][1]),
        '@ELF@': 'true' if D['elf'] else 'false',
        '@ELFH@': 'reflexivity' if D['elf'] else 'discriminate',
        '@ELFH2@': ('reflexivity' if D['elf'] else 'discriminate'),
        '@VIRTCERT@': VIRTCERT_S1, '@VIRTGLUE@': VIRTGLUE_S1,
        '@E1@': _fmtconf(e1), '@CHV@': cchain(D['chv']),
        '@CAV@': str(D['cv'][0]), '@CBV@': str(D['cv'][1]),
        '@ELV@': 'true' if D['elv'] else 'false',
        '@ELVH@': 'reflexivity' if D['elv'] else 'discriminate',
        '@ELVH2@': ('reflexivity' if D['elv'] else 'discriminate'),
        '@E1DEN@': e1den, '@E1FAR@': e1far,
        '@E1PAD@': _pad(e1den, npad),
        '@VCLOSE@': ' '.join(vclose),
        '@LAPINT@': LAPINT_S1, '@LAPFILL@': LAPFILL_S1,
        '@HINT@': HINT_S1, '@HSUCC@': HSUCC_S1,
        '@HVLAP@': HVLAP_S1, '@HVRUN@': HVRUN_S1,
        '@GSIH@': '', '@GSIHN@': '', '@GSIRED@': '', '@GEIRED@': '',
        '@GSOH@': '', '@GSOHN@': '', '@GSORED@': '', '@GSOA@': '',
        '@VISFENCE@': '',
        '@VISVLEM@': VISV_LEMMA if need_visv else '',
        '@VISITS@': '\n'.join(vis),
        '@P0@': str(D['p0']), '@BOOT@': str(D['boot']),
        '@NI@': '%d*j+%d' % D['ci'], '@NF@': '%d*j+%d' % D['cf'],
        '@NVDOC@': ('      virt      (pexp p = Some (S k)): %d*k+%d steps, '
                    'up to [lift]\n' % D['cv']),
        '@VAL@': D['val'],
    }
    out = HEADER
    for _ in range(4):
        for k, v in reps.items():
            out = out.replace(k, v)
    # collapse the doubled spaces left by empty hypothesis holes
    out = out.replace(' \n', '\n').replace('E1 )', 'E1)')
    out = out.replace(', )', ')').replace('(  ', '(')
    return out


# ---------------------------------------------------------------- process ---

def process(spec, do_emit, force=False):
    last = None
    for mirrored in (False, True):
        dspec = mirror_spec(spec) if mirrored else spec
        for (edge, tail, p0, enc, far) in EL.anchors(dspec):
            try:
                D = derive_skip(dspec, edge, tail, enc, far)
            except (SkipError, DeriveError, LC.Halt) as e:
                last = str(e)
                continue
            except Exception as e:                                # noqa: BLE001
                last = '%s: %s' % (type(e).__name__, e)
                continue
            tag = enc + ('/mirror' if mirrored else '')
            info = dict(spec=spec, ok=True, enc=tag, s=D['s'],
                        ni='%d*j+%d' % tuple(D['ci']),
                        nf='%d*j+%d' % tuple(D['cf']))
            if not do_emit:
                return info
            path = os.path.join(OUTDIR, '%s_%s.v' % (PREFIX, mach_id(spec)))
            if os.path.exists(path) and not force:
                info.update(file=path, skipped=True)
                return info
            try:
                src = render_skip(D)
                if mirrored:
                    src = mirrorize(src, spec, dspec)
            except (SkipError, DeriveError, RuntimeError) as e:
                last = 'render: %s' % e
                continue
            open(path, 'w').write(src)
            ok, log = coqc(os.path.relpath(path, REPO))
            if not ok:
                os.remove(path)
                lg = [x for x in log.strip().splitlines() if x.strip()]
                last = 'coqc: ' + (lg[-1] if lg else '?')
                continue
            info['file'] = path
            return info
    return dict(spec=spec, ok=False, why=last or 'no anchor')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list')
    ap.add_argument('--spec')
    ap.add_argument('--emit', action='store_true')
    ap.add_argument('--scan', action='store_true')
    ap.add_argument('--json')
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--force', action='store_true')
    a = ap.parse_args()

    specs = ([a.spec] if a.spec else
             [x.strip() for x in open(a.list) if x.strip()])
    if a.limit:
        specs = specs[:a.limit]

    res, nok = [], 0
    cnt = collections.Counter()
    for i, spec in enumerate(specs):
        if a.scan:
            r = scan(spec)
            key = ('s=%d' % r['s'] if r.get('ok') else r['why'])
            cnt[key] += 1
            print('%5d/%d %-40s %s%s' % (
                i + 1, len(specs), spec,
                key, (' noise=%s' % r['noise']
                      if r.get('ok') and r['noise'] else '')), flush=True)
        else:
            r = process(spec, a.emit, a.force)
            nok += bool(r['ok'])
            print('%5d/%d %-40s %s' % (
                i + 1, len(specs), spec,
                ('OK s=%s %s int=%s fill=%s' % (r.get('s'), r['enc'],
                                                r.get('ni'), r.get('nf')))
                if r['ok'] else 'no: %s' % r['why'][:110]), flush=True)
        res.append(r)
    if a.scan:
        print('\n=== skip sets ===')
        for k, v in cnt.most_common():
            print('%5d  %s' % (v, k))
    else:
        print('\n%d / %d derived' % (nok, len(specs)))
    if a.json:
        json.dump(res, open(a.json, 'w'), indent=1)


if __name__ == '__main__':
    main()
