#!/usr/bin/env python3
"""UNTRUSTED emitter: lap certificates for GRAY-CODE counters.

WAVE13_FINDINGS.md section 9d read [0RB0LA_0RC1RC_1LD0LD_1LA1RB] as a counter
whose tape word is the reflected-binary (Gray) code rather than the binary
expansion, and established that the decomposition is nevertheless AFFINE in
the carry index -- so it is expressible by the EXISTING checker
(theories/Checkers/LapDecider.v) and needs no new soundness surface.  This is
that build.  The only new Coq is theories/Counters/GpCounter.v.

Why a separate emitter rather than a sixth ENCDATA row in emit_lapcert.py:
those five rows all have the shape

    E p = rep uS j ++ sS ++ E q0

-- one repeated block, one stop word, and a tail that is the SAME encoding of
the higher part.  Gray has none of those three properties.  Its lap flips a
single cell of the high part ([x] below), so the tail is [Gp q0] with its low
cell REMOVED, and source and target differ in their PREFIX as well as their
block.  Forcing that into ENCDATA would have meant generalising the row shape
for every existing row; 119 boards depend on those, so this is additive.

The branch shapes, from GpCounter.cview_some_G / cview_some0_G / cview_none_G
(each proved by induction on p, and each checked against the raw simulator for
p = 1 .. 19999 before the Coq was written):

  interior, cview p = (S j, Some q0), Gp q0 = x :: G
      Gp p        = S1 :: rep [S0] j ++ S1 :: x      :: G
      Gp (succ p) = S0 :: rep [S0] j ++ S1 :: negs x : G
  interior, cview p = (0, Some q0), Gp q0 = x :: G
      Gp p        = S0 :: x      :: G
      Gp (succ p) = S1 :: negs x :: G
  overflow, cview p = (S j, None)
      Gp p        = S1 :: rep [S0] j ++ [S1]
      Gp (succ p) = S0 :: rep [S0] j ++ [S1; S1]

[x] is a single CONCRETE cell, so the interior branch splits into two
sub-cases exactly as section 9a splits on j = 0 -- and that split is what
makes the opaque tail [G] the SAME on both sides of the lap, which is what
[srun_sound] requires.  Five chains per machine: (j=0, j>=1) x (x=S0, x=S1)
plus the overflow.

Everything here is untrusted; the Coq kernel re-runs [srun] on every chain.

Usage
  emit_graycert.py --list FILE [--emit] [--json OUT]
  emit_graycert.py --spec SPEC [--emit]
"""
import argparse
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

from emit_interleave import (parse, carry, LAB, ST, SYM,               # noqa: E402
                             DeriveError, mach_id, coq_table, clist)
from mirror_common import mirror_spec, mirrorize                       # noqa: E402
import lapcert as LC                                                   # noqa: E402

OUTDIR = os.path.join(REPO, 'theories', 'Machines', 'Counters')
PREFIX = 'LAPG'
S0, S1 = 0, 1
Halt_ = LC.Halt


# --------------------------------------------------------------- encoding ---

def Gp(p):
    """The anchor word, LSB nearest the head.  [Gp p = bits (gray (2p))]."""
    if p == 1:
        return [S1, S1]
    q, b = p >> 1, p & 1
    w = Gp(q)
    return [S0] + w if b == 0 else [S1] + [1 - w[0]] + w[1:]


def confs(st0, tail, far, x):
    """The five symbolic (start, end) pairs for one flipped-cell value [x]."""
    tail, far = tuple(tail), tuple(far)
    F = (far, (), 0, 0, ())
    y = 1 - x
    # interior, j = S j' : one copy of nothing in the prefix, block = rep [S0] j'
    P0 = (st0, ((S1,), (S0,), 1, 0, (S1, x)), 0, F)
    P1 = (st0, ((S0,), (S0,), 1, 0, (S1, y)), 0, F)
    # interior, j = 0 : wholly concrete
    Z0 = (st0, ((S0, x), (), 0, 0, ()), 0, F)
    Z1 = (st0, ((S1, y), (), 0, 0, ()), 0, F)
    # overflow : the tail is CONCRETE (nothing is written above the counter)
    B0 = (st0, ((S1,), (S0,), 1, 0, (S1,) + tail), 0, F)
    B1 = (st0, ((S0,), (S0,), 1, 0, (S1, S1) + tail), 0, F)
    return (P0, P1), (Z0, Z1), (B0, B1)


# ------------------------------------------------------------- validation ---

def sim(tab, cfg, n):
    for _ in range(n):
        cfg = LC.wstep(tab, False, False, cfg)
    return cfg


def eqlift(a, b):
    return (a[0] == b[0] and a[2] == b[2]
            and LC.rstrip0(a[1]) == LC.rstrip0(b[1])
            and LC.rstrip0(a[3]) == LC.rstrip0(b[3]))


def validate(tab, st0, tail, far, cost, hi=300):
    """Differentially check EVERY branch against the raw simulator: exact step
    counts and exact configurations, for every p in range."""
    tail, far = tuple(tail), tuple(far)
    n = 0
    for p in range(2, hi):
        j, ov = carry(p)
        q0 = None if ov else (p >> (j + 1))
        x = None if ov else Gp(q0)[0]
        steps = cost(j, ov, x)
        if steps is None:
            return False, 'p=%d: no branch' % p
        start = (st0, tuple(Gp(p)) + tail, 0, far)
        want = (st0, tuple(Gp(p + 1)) + tail, 0, far)
        got = sim(tab, start, steps)
        if not eqlift(got, want):
            return False, ('p=%d %s x=%s: %d steps -> %r want %r'
                           % (p, 'ovf' if ov else 'int', x, steps, got, want))
        n += 1
    return True, '%d anchors' % n


def boot_probe(tab, st0, tail, far, p0, maxT=400000):
    want = (st0, tuple(Gp(p0)) + tuple(tail), 0, tuple(far))
    cfg = (0, (), 0, ())
    for t in range(maxT):
        if eqlift(cfg, want):
            return t
        cfg = LC.wstep(tab, False, False, cfg)
    return None


# ------------------------------------------------------------------ derive ---

def derive(spec, st0, tail, p0, far=()):
    tab = parse(spec)
    ch, run = {}, {}
    for x in (S0, S1):
        (P0, P1), (Z0, Z1), (B0, B1) = confs(st0, tail, far, x)
        for key, (a, b, el) in (('p%d' % x, (P0, P1, False)),
                                ('z%d' % x, (Z0, Z1, False))):
            c = LC.derive_chain(tab, el, True, a, b)
            if c is None:
                raise DeriveError('no interior chain (%s)' % key)
            ch[key] = c
            run[key] = LC.srun(tab, el, True, c, a)
            if run[key][2] == 0:
                raise DeriveError('lap of zero length (%s)' % key)
    (_, _), (_, _), (B0, B1) = confs(st0, tail, far, S0)
    c = LC.derive_chain(tab, True, True, B0, B1)
    if c is None:
        raise DeriveError('no overflow chain')
    ch['o'] = c
    run['o'] = LC.srun(tab, True, True, c, B0)
    if run['o'][2] == 0:
        raise DeriveError('lap of zero length (o)')

    def cost(j, ov, x):
        if ov:
            r = run['o']
            return r[1] * (j - 1) + r[2]
        r = run['z%d' % x] if j == 0 else run['p%d' % x]
        return r[1] * (0 if j == 0 else j - 1) + r[2]

    ok, why = validate(tab, st0, tail, far, cost)
    if not ok:
        raise DeriveError('validation: ' + why)

    untargeted = all(t is None or t[2] != 0 for t in tab.values())
    vis, qh = {}, False
    for q in range(4):
        pre = LC.reach_state(tab, True, True, B0, ch['o'], q)
        if pre is None:
            if q == 0 and untargeted:
                qh = True
                continue
            raise DeriveError('no visit witness for state %s%s' % (
                LAB[q], '' if q or untargeted else ' (StA is targeted)'))
        vis[q] = pre

    boot = boot_probe(tab, st0, tail, far, p0)
    if boot is None:
        raise DeriveError('no bootstrap to p0=%d' % p0)

    got = run['o'][0][1][4]
    want = (S1, S1) + tuple(tail)
    if LC.rstrip0(got) != LC.rstrip0(want):
        raise DeriveError('overflow close mismatch %r vs %r' % (got, want))

    return dict(spec=spec, st0=st0, tail=list(tail), far=list(far), p0=p0,
                ch=ch, run=run, vis=vis, qh=qh, boot=boot,
                ovpost=list(got), ovwant=list(want), val=why)


# ------------------------------------------------------------ Coq emission ---

def cstep_str(st):
    if st[0] == 'SCycL':
        return 'SCycL %d %d' % (st[1], st[2])
    return '%s %d' % (st[0], st[1])


def cchain(ch):
    return '[' + '; '.join(cstep_str(s) for s in ch) + ']'


def cside(s):
    pre, u, a, b, post = s
    return 'mkS %s %s %d %d %s' % (clist(pre), clist(u), a, b, clist(post))


def cconf(c):
    return 'mkC %s (%s) %s (%s)' % (ST[c[0]], cside(c[1]), SYM[c[2]],
                                    cside(c[3]))


HEADER = r'''(** * @PREF@_@ID@: machine @SPEC@, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_graycert.py (UNTRUSTED emitter; the
    Coq kernel re-runs the checker on every line below).  This is a GRAY-CODE
    counter: the tape word is the reflected-binary code of the count, not its
    binary expansion (WAVE13_FINDINGS.md section 9d), so it is anchored on
    [Counters/GpCounter.v] rather than on one of the five digit alphabets.

      Cc p = (@ST0@, (Gp p ++ @TAIL@, S0, @FAR@))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound] -- unchanged, because
    [srun_sound] never sees the encoding, only the symbolic sides.

    FIVE branches.  The Gray increment flips ONE cell of the high part; the
    interior branch therefore splits on the value [x] of that cell, which
    makes the opaque tail [G] identical on both sides of the lap (the tail is
    universally quantified in [srun_sound], so it must be).

      interior j=0,   x=S0 : @NZ0@ steps      x=S1 : @NZ1@ steps
      interior j=S j', x=S0 : @NP0@           x=S1 : @NP1@
      overflow             : @NO@

    Differentially validated against the raw simulator on ALL FIVE branches --
    step counts AND exact configurations -- for @VAL@.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH MonoCounter
                                  JpCounter GpCounter LapCertGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_@ID@ (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_@ID@.

(** @SPEC@ *)
Definition tm_@ID@ : TM := fun q s => match q, s with
@TABLE@ end.
Local Notation tm := tm_@ID@.

Definition Cc_@ID@ (p : positive) : cconf := (@ST0@, (Gp p ++ @TAIL@, S0, @FAR@)).
Local Notation Cc := Cc_@ID@.

(** ** The certificate *)

Definition Z0a_@ID@ : sconf := @Z0A@.
Definition Z1a_@ID@ : sconf := @Z1A@.
Definition chza_@ID@ : list lstep := @CHZA@.
Lemma run_za_@ID@ : srun tm false true chza_@ID@ Z0a_@ID@ = Some (Z1a_@ID@, @CAZA@, @CBZA@).
Proof. vm_compute. reflexivity. Qed.

Definition Z0b_@ID@ : sconf := @Z0B@.
Definition Z1b_@ID@ : sconf := @Z1B@.
Definition chzb_@ID@ : list lstep := @CHZB@.
Lemma run_zb_@ID@ : srun tm false true chzb_@ID@ Z0b_@ID@ = Some (Z1b_@ID@, @CAZB@, @CBZB@).
Proof. vm_compute. reflexivity. Qed.

Definition P0a_@ID@ : sconf := @P0A@.
Definition P1a_@ID@ : sconf := @P1A@.
Definition chpa_@ID@ : list lstep := @CHPA@.
Lemma run_pa_@ID@ : srun tm false true chpa_@ID@ P0a_@ID@ = Some (P1a_@ID@, @CAPA@, @CBPA@).
Proof. vm_compute. reflexivity. Qed.

Definition P0b_@ID@ : sconf := @P0B@.
Definition P1b_@ID@ : sconf := @P1B@.
Definition chpb_@ID@ : list lstep := @CHPB@.
Lemma run_pb_@ID@ : srun tm false true chpb_@ID@ P0b_@ID@ = Some (P1b_@ID@, @CAPB@, @CBPB@).
Proof. vm_compute. reflexivity. Qed.

Definition B0_@ID@ : sconf := @B0@.
Definition B1_@ID@ : sconf := @B1@.
Definition cho_@ID@ : list lstep := @CHO@.
Lemma run_ovf_@ID@ : srun tm true true cho_@ID@ B0_@ID@ = Some (B1_@ID@, @CAO@, @CBO@).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics

    Each is one [GpCounter] rewrite plus [app_assoc].  The [x] argument is
    the flipped high cell, made concrete by the split. *)

Lemma gza_@ID@ : forall p q0 G, cview p = (0, Some q0) -> Gp q0 = S0 :: G ->
  Cc p = cden (G ++ @TAIL@) [] 0 Z0a_@ID@ /\
  cden (G ++ @TAIL@) [] 0 Z1a_@ID@ = Cc (Pos.succ p).
Proof.
  intros p q0 G E HG. destruct (cview_some0_G p q0 S0 G E HG) as (H1 & H2).
  unfold Cc_@ID@, cden, Z0a_@ID@, Z1a_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split; [rewrite H1 | rewrite H2]; cbn [rep app negs];
    rewrite <- ?app_assoc; cbn [app]; reflexivity.
Qed.

Lemma gzb_@ID@ : forall p q0 G, cview p = (0, Some q0) -> Gp q0 = S1 :: G ->
  Cc p = cden (G ++ @TAIL@) [] 0 Z0b_@ID@ /\
  cden (G ++ @TAIL@) [] 0 Z1b_@ID@ = Cc (Pos.succ p).
Proof.
  intros p q0 G E HG. destruct (cview_some0_G p q0 S1 G E HG) as (H1 & H2).
  unfold Cc_@ID@, cden, Z0b_@ID@, Z1b_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split; [rewrite H1 | rewrite H2]; cbn [rep app negs];
    rewrite <- ?app_assoc; cbn [app]; reflexivity.
Qed.

Lemma gpa_@ID@ : forall p j q0 G, cview p = (S j, Some q0) -> Gp q0 = S0 :: G ->
  Cc p = cden (G ++ @TAIL@) [] j P0a_@ID@ /\
  cden (G ++ @TAIL@) [] j P1a_@ID@ = Cc (Pos.succ p).
Proof.
  intros p j q0 G E HG. destruct (cview_some_G p j q0 S0 G E HG) as (H1 & H2).
  unfold Cc_@ID@, cden, P0a_@ID@, P1a_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split; [rewrite H1 | rewrite H2]; cbn [rep app negs];
    rewrite <- ?app_assoc; cbn [app]; reflexivity.
Qed.

Lemma gpb_@ID@ : forall p j q0 G, cview p = (S j, Some q0) -> Gp q0 = S1 :: G ->
  Cc p = cden (G ++ @TAIL@) [] j P0b_@ID@ /\
  cden (G ++ @TAIL@) [] j P1b_@ID@ = Cc (Pos.succ p).
Proof.
  intros p j q0 G E HG. destruct (cview_some_G p j q0 S1 G E HG) as (H1 & H2).
  unfold Cc_@ID@, cden, P0b_@ID@, P1b_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split; [rewrite H1 | rewrite H2]; cbn [rep app negs];
    rewrite <- ?app_assoc; cbn [app]; reflexivity.
Qed.

(** ** The interior lap *)

Lemma lapi_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (Gp_shape q0) as (x & G & HG).
  destruct j as [|j']; destruct x.
  - destruct (gza_@ID@ p q0 G E HG) as (HA & HB).
    exists (@CAZA@ * 0 + @CBZA@). split; [lia|]. rewrite HA.
    rewrite (srun_sound tm false true chza_@ID@ Z0a_@ID@ Z1a_@ID@ @CAZA@ @CBZA@
               run_za_@ID@ (G ++ @TAIL@) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gzb_@ID@ p q0 G E HG) as (HA & HB).
    exists (@CAZB@ * 0 + @CBZB@). split; [lia|]. rewrite HA.
    rewrite (srun_sound tm false true chzb_@ID@ Z0b_@ID@ Z1b_@ID@ @CAZB@ @CBZB@
               run_zb_@ID@ (G ++ @TAIL@) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gpa_@ID@ p j' q0 G E HG) as (HA & HB).
    exists (@CAPA@ * j' + @CBPA@). split; [lia|]. rewrite HA.
    rewrite (srun_sound tm false true chpa_@ID@ P0a_@ID@ P1a_@ID@ @CAPA@ @CBPA@
               run_pa_@ID@ (G ++ @TAIL@) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gpb_@ID@ p j' q0 G E HG) as (HA & HB).
    exists (@CAPB@ * j' + @CBPB@). split; [lia|]. rewrite HA.
    rewrite (srun_sound tm false true chpb_@ID@ P0b_@ID@ P1b_@ID@ @CAPB@ @CBPB@
               run_pb_@ID@ (G ++ @TAIL@) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

(** ** The overflow lap *)

Lemma gso_@ID@ : forall p j, cview p = (S j, None) -> Cc p = cden [] [] j B0_@ID@.
Proof.
  intros p j E. destruct (cview_none_G p j E) as (H1 & _).
  unfold Cc_@ID@, cden, B0_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1; cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; reflexivity.
Qed.

Lemma lbl_@ID@ : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_@ID@ : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_@ID@) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (cview_none_G p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_@ID@
             = (@ST0@, (S0 :: rep [S0] j ++ @OVPOST@, S0, @FAR@))).
  { unfold cden, B1_@ID@, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. reflexivity. }
  assert (HC : Cc (Pos.succ p) = (@ST0@, (@HCLEFT@, S0, @FAR@))).
  { unfold Cc_@ID@. rewrite H2. cbn [app]; rewrite <- ?app_assoc;
    cbn [app]; rewrite ?app_nil_r; reflexivity. }
  rewrite HD, HC. @CLOSE@
Qed.

(** ** The lap *)

Lemma lap_@ID@ : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_@ID@ p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_@ID@ B0_@ID@ B1_@ID@ @CAO@ @CBO@ p j' [] []).
    + exact run_ovf_@ID@.
    + reflexivity.
    + reflexivity.
    + exact (gso_@ID@ p j' E).
    + exact (geo_@ID@ p j' E).
    + lia.
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

(** ** Visits *)

Lemma viso_@ID@ : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_@ID@ = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_@ID@ p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_@ID@ p j E)].
Qed.

Lemma vis_@ID@ : @VISHYP@ exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  @VISINTRO@.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_@ID@.
  destruct q.
@VISA@
@VISITS@
Qed.

@FINAL@
'''

NQH_CLOSE = '''Theorem nqh_@ID@ : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc @P0@). - exact boot_@ID@. - intros p _. apply lap_@ID@. - intros p q _. apply vis_@ID@. Qed.

Theorem nonhalt_@ID@ : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_@ID@. Qed.'''

QH_CLOSE = '''(** StA is TARGETED BY NOTHING, so its only visit is at configuration index
    0 and the quiet bound is 1 -- weakened to the census tier's 2000. *)
Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\\ QHBound 2000 tm /\\ QuasiHaltsSt tm.

Theorem iqh_@ID@ : iqh tm.
Proof.
  destruct (glue_qh tm Cc @P0@ boot_@ID@ (fun p _ => lap_@ID@ p)
                    (fun p q _ Hq => vis_@ID@ p q Hq)
                    (ltac:(intros q b tr Ht; destruct q, b; cbn in Ht;
                           try discriminate; injection Ht as <-; discriminate)))
    as (Hn & Hb & Hq).
  split; [exact Hn | split; [| exact Hq]].
  apply (qhbound_mono 1 2000); [lia | exact Hb].
Qed.

Theorem nonhalt_@ID@ : NonHalt tm.
Proof. apply (proj1 iqh_@ID@). Qed.'''


def render(D):
    spec = D['spec']
    ID = mach_id(spec)
    ovpost, ovwant = tuple(D['ovpost']), tuple(D['ovwant'])
    body = 'rep [S0] j ++ %s' % clist(ovpost)
    pad = len(ovwant) - len(ovpost)
    if pad < 0 or ovwant[:len(ovpost)] != ovpost or any(ovwant[len(ovpost):]):
        raise DeriveError('overflow close %r vs %r' % (ovpost, ovwant))
    if pad == 0:
        hcleft, close = 'S0 :: ' + body, 'reflexivity.'
    else:
        hcleft = ('S0 :: ' + '(' * pad + body
                  + ''.join(') ++ [S0]' for _ in range(pad)))
        close = 'rewrite !lbl_%s. reflexivity.' % ID
    vis = []
    for q in sorted(D['vis']):
        pre = D['vis'][q]
        if not pre:
            vis.append('  - (* %s: the anchor state *)\n'
                       '    exists 0. eexists. split; reflexivity.' % ST[q])
        else:
            vis.append('  - (* %s *)\n'
                       '    apply (vis_via_ovf tm Cc Hi %s), viso_%s\n'
                       '      with (l := %s).\n'
                       '    vm_compute; reflexivity.'
                       % (ST[q], ST[q], ID, cchain(pre)))
    r = D['run']
    reps = {
        '@PREF@': PREFIX, '@ID@': ID, '@SPEC@': spec,
        '@ST0@': ST[D['st0']], '@TAIL@': clist(D['tail']),
        '@FAR@': clist(D['far']), '@TABLE@': coq_table(spec),
        '@Z0A@': cconf(confs(D['st0'], D['tail'], D['far'], S0)[1][0]),
        '@Z1A@': cconf(confs(D['st0'], D['tail'], D['far'], S0)[1][1]),
        '@Z0B@': cconf(confs(D['st0'], D['tail'], D['far'], S1)[1][0]),
        '@Z1B@': cconf(confs(D['st0'], D['tail'], D['far'], S1)[1][1]),
        '@P0A@': cconf(confs(D['st0'], D['tail'], D['far'], S0)[0][0]),
        '@P1A@': cconf(confs(D['st0'], D['tail'], D['far'], S0)[0][1]),
        '@P0B@': cconf(confs(D['st0'], D['tail'], D['far'], S1)[0][0]),
        '@P1B@': cconf(confs(D['st0'], D['tail'], D['far'], S1)[0][1]),
        '@B0@': cconf(confs(D['st0'], D['tail'], D['far'], S0)[2][0]),
        '@B1@': cconf(r['o'][0]),
        '@CHZA@': cchain(D['ch']['z0']), '@CHZB@': cchain(D['ch']['z1']),
        '@CHPA@': cchain(D['ch']['p0']), '@CHPB@': cchain(D['ch']['p1']),
        '@CHO@': cchain(D['ch']['o']),
        '@CAZA@': str(r['z0'][1]), '@CBZA@': str(r['z0'][2]),
        '@CAZB@': str(r['z1'][1]), '@CBZB@': str(r['z1'][2]),
        '@CAPA@': str(r['p0'][1]), '@CBPA@': str(r['p0'][2]),
        '@CAPB@': str(r['p1'][1]), '@CBPB@': str(r['p1'][2]),
        '@CAO@': str(r['o'][1]), '@CBO@': str(r['o'][2]),
        '@NZ0@': str(r['z0'][2]), '@NZ1@': str(r['z1'][2]),
        '@NP0@': '%d*j\'+%d' % (r['p0'][1], r['p0'][2]),
        '@NP1@': '%d*j\'+%d' % (r['p1'][1], r['p1'][2]),
        '@NO@': '%d*j+%d' % (r['o'][1], r['o'][2]),
        '@OVPOST@': clist(ovpost), '@HCLEFT@': hcleft, '@CLOSE@': close,
        '@P0@': str(D['p0']), '@BOOT@': str(D['boot']),
        '@VISHYP@': ('forall p q, q <> StA ->' if D['qh'] else 'forall p q,'),
        '@VISINTRO@': ('intros p q Hq' if D['qh'] else 'intros p q'),
        '@VISA@': ('  - (* StA: quiet -- see the closing theorem *)\n'
                   '    exfalso; exact (Hq eq_refl).' if D['qh'] else ''),
        '@FINAL@': (QH_CLOSE if D['qh'] else NQH_CLOSE).replace('@ID@', ID)
                    .replace('@P0@', str(D['p0'])),
        '@VAL@': D['val'], '@VISITS@': '\n'.join(vis),
    }
    out = HEADER
    for _ in range(3):
        for k, v in reps.items():
            out = out.replace(k, v)
    return out


def coqc(path):
    r = subprocess.run(['coqc', '-native-compiler', 'no', '-Q', 'theories',
                        'BBB4', path], cwd=REPO, capture_output=True, text=True)
    return r.returncode == 0, (r.stderr or r.stdout)[-1500:]


def gray_anchors(spec, T=60000):
    """(st0, tail, p0, far) candidates: scan the run for configurations whose
    near word is [Gp p ++ tail] with the far side fixed, and keep the
    (state, tail, far) whose p-run is longest and consecutive."""
    tab = parse(spec)
    tabw = {}
    for p in range(1, 4096):
        tabw[tuple(Gp(p))] = p
    cfg = (0, (), 0, ())
    hits = {}
    for t in range(T):
        q, l, h, r = cfg
        if h == 0:
            ls, rs = LC.rstrip0(l), LC.rstrip0(r)
            for k in range(0, 4):
                head = ls[:len(ls) - k] if k else ls
                p = tabw.get(tuple(head))
                if p is not None:
                    key = (q, ls[len(ls) - k:] if k else (), rs)
                    hits.setdefault(key, []).append(p)
        try:
            cfg = LC.wstep(tab, False, False, cfg)
        except Halt_:
            break
    out = []
    for (q, tail, far), ps in hits.items():
        run, best, cur = 1, 1, 1
        for i in range(1, len(ps)):
            cur = cur + 1 if ps[i] == ps[i - 1] + 1 else 1
            best = max(best, cur)
        if best >= 8:
            out.append((best, q, tail, min(ps), far))
    out.sort(reverse=True)
    return [(q, tail, p0, far) for (_, q, tail, p0, far) in out[:6]]


def process(spec, do_emit, force=False):
    last = None
    for mirrored in (False, True):
        dspec = mirror_spec(spec) if mirrored else spec
        try:
            cands = gray_anchors(dspec)
        except Exception as e:                                    # noqa: BLE001
            last = '%s: %s' % (type(e).__name__, e)
            continue
        for (st0, tail, p0, far) in cands:
            try:
                D = derive(dspec, st0, tail, max(p0, 2), far)
            except (DeriveError, Halt_) as e:
                last = str(e)
                continue
            except Exception as e:                                # noqa: BLE001
                last = '%s: %s' % (type(e).__name__, e)
                continue
            tag = 'Gp' + ('/mirror' if mirrored else '')
            if not do_emit:
                return dict(spec=spec, ok=True, enc=tag, why='')
            path = os.path.join(OUTDIR, '%s_%s.v' % (PREFIX, mach_id(spec)))
            if os.path.exists(path) and not force:
                return dict(spec=spec, ok=True, enc=tag, file=path,
                            skipped=True, why='')
            try:
                src = render(D)
                if mirrored:
                    src = mirrorize(src, spec, dspec)
            except (DeriveError, RuntimeError) as e:
                last = str(e)
                continue
            open(path, 'w').write(src)
            ok, log = coqc(os.path.relpath(path, REPO))
            if not ok:
                os.remove(path)
                lg = [l for l in log.strip().splitlines() if l.strip()]
                last = 'coqc: ' + (lg[-1] if lg else '?')
                continue
            return dict(spec=spec, ok=True, enc=tag, file=path, why='')
    return dict(spec=spec, ok=False, why=last or 'no Gray anchor')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list')
    ap.add_argument('--spec')
    ap.add_argument('--emit', action='store_true')
    ap.add_argument('--json')
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--force', action='store_true')
    a = ap.parse_args()
    specs = ([a.spec] if a.spec else
             [l.strip() for l in open(a.list) if l.strip()])
    if a.limit:
        specs = specs[:a.limit]
    res, nok = [], 0
    for i, spec in enumerate(specs):
        r = process(spec, a.emit, a.force)
        res.append(r)
        nok += bool(r['ok'])
        print('%5d/%d %-40s %s' % (i + 1, len(specs), spec,
                                   ('OK %s' % r['enc']) if r['ok']
                                   else 'no: %s' % r['why'][:90]), flush=True)
    print('\n%d / %d derived' % (nok, len(specs)))
    if a.json:
        json.dump(res, open(a.json, 'w'), indent=1)


if __name__ == '__main__':
    main()
