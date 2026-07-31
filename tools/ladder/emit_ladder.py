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
               ('Fib' if fam.get('numeration') == 'fibonacci'
                else 'Gray' if fam.get('code') == 'gray' else 'Binary'),
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
From BBB4.Census Require Import TNF_QH.
From BBB4.Counters Require Import WTape LapGlueQuiet.
From BBB4.Checkers Require Import LapDecider LapAvoid LadderKernel LadderFam.
From BBB4.Checkers Require Import LadderCheck.
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


# The (threshold, stride) pairs the arm search tries, cheapest first --
# cheapest meaning FEWEST ARMS, which is [N0 + st] of them.  [N0 = 0] is
# 4i's scheme (a bare residue) and is still tried first; the rows 4i stopped
# on are the ones that need [N0 >= 1], because their materialisation offset
# is at least the stride and so cannot be a residue at all.
ARM_GRID = sorted(((n0, st) for n0 in range(0, 4) for st in range(1, 5)),
                  key=lambda p: (p[0] + p[1], p[0], p[1]))


def blk(P, u, s, W):
    """[LadderCheck.blk]: a side whose repeated block may be EMPTY.  With no
    block, [s_post] has to move into [s_pre] -- no chain step carries a cell
    across the block boundary, so a flat arm stated with a [s_post] has no
    chain at all."""
    v = tuple(u) * s
    if not v:
        return (tuple(P) + tuple(W), (), 0, 0, ())
    return (tuple(P), v, 1, 0, tuple(W))


def _splits(total):
    """How to divide the fill target's guaranteed copies about the block,
    in the order to try them: 4h's normalisation (one copy materialised)
    first, then none, then the rest."""
    return [m for m in [1, 0] + list(range(2, total + 1)) if 0 <= m <= total]


def last_visit(tab, qa, t0):
    """The last configuration index below [t0] at which the machine, from the
    blank tape, is in state [qa] -- the quiet state's LAST visit, which is
    what [QHBound] is stated against.

    UNTRUSTED like everything here: the board re-derives it with
    [LapGlueQuiet.bootvis_chk] and re-checks the window above it with
    [bootquiet_chk], both by [vm_compute]."""
    tape, pos, q, last = {}, 0, 0, None
    for i in range(t0):
        if q == qa:
            last = i
        e = tab.get((q, tape.get(pos, 0)))
        if e is None:
            return last
        w, d, q = e
        tape[pos] = w
        pos += d
    return last


def closure_data(cert, tab):
    """The CLASS arms, the boot and the per-state visits, or NoClosure.

    LADDER_PLAN 4h(a): coverage reduces to a finite case split -- every
    digit string is t^n ++ d :: rest with d <> t, or t^k.  The arms that
    serve those two classes are not the mined arms the certificate carries:
    those are the same rules with every run length but one pinned to its
    lower bound.  Here they are built from the FAMILY, so the arms are one
    per digit below the top and per ARM INDEX, whatever the certificate
    happened to emit.

    The arm index is [LadderCheck]'s one scheme, and 4k's finding is that
    BOTH classes want it: a run of length [n] is served by the arm at [n]
    itself below a threshold [N0] -- flat, stride 0, the whole run concrete
    in s_pre -- and at [N0 + (n - N0) mod st] above it, with the block taken
    [(n - N0) / st] times.  Measured over the live core
    (tools/ladder/core61_armshapes.txt): with a stride on the interior arm
    alone, 3 of 21 rows have both arms; with the threshold and the stride on
    both, 15 do.

    The fill arm is the one that must see the end of the counter, so its
    guaranteed block copies are materialised into s_pre (4h) -- without that
    it has no chain at all.  That is why its threshold is at least 1: the
    arm at index [r] carries [r] concrete copies, and no width is 0.
    """
    fam = cert['family']
    fills = cert.get('fill_by_phase') or [cert['fill']]
    nph = len(fills)
    if fam.get('code') != 'binary':
        raise NoClosure('code %s: LadderCheck states (Binary, 1) only'
                        % fam.get('code'))
    if fam.get('value_step_per_anchor_visit', 1) != 1:
        raise NoClosure('step %d: LadderCheck states (Binary, 1) only'
                        % fam.get('value_step_per_anchor_visit', 1))
    # A weight sequence is not a positional base-b numeration and
    # [LadderFam.fam_value] is [val_pos].  4m's five fibonacci rows read as
    # `code = binary, step = 1` and would otherwise be emitted here with a
    # family whose value the kernel computes differently -- the board would
    # fail [check_arm] rather than produce a wrong theorem, but the reason
    # belongs in the file.
    if fam.get('weights') is not None:
        raise NoClosure('numeration %s: LadderCheck states positional base-b '
                        '(fam_value is val_pos over the digits); a weight '
                        'sequence wants its canonical-form lemma first (4m)'
                        % fam.get('numeration'))
    # The PHASE CYCLE (4l/4n).  [LadderCheck.Inv] carries [ph < NPH] rather
    # than [ph = 0], so a family with more than one terminator is stated
    # here rather than refused: what each phase's fill has to do is land in
    # a phase this family HAS, and it does not have to widen -- a phase-0
    # fill that re-enters the same width in phase 1 is what a terminator
    # cycle IS, and [tops_cofinal] needs tops to recur and nothing more.
    for ph, f in enumerate(fills):
        if not 0 <= f['lands_in_phase'] < nph:
            raise NoClosure('phase %d fills into phase %d, which this family '
                            'does not have' % (ph, f['lands_in_phase']))
        m = len(f['target_prefix']) + len(f['target_suffix'])
        if m > 1 + f['widens_by']:
            raise NoClosure('phase %d fill target names %d digits but widens '
                            'by %d' % (ph, m, f['widens_by']))
    b = fam['base']
    if b < 2:
        raise NoClosure('base %d' % b)

    digs = [tuple(w) for w in fam['digits']]
    pre = tuple(fam['near_head_prefix'])
    tails = [tuple(t) for t in
             (fam.get('terminators_by_phase') or [fam['terminator']])]
    if len(tails) < nph:
        raise NoClosure('%d fill laws but %d terminators' % (nph, len(tails)))
    ph0 = cert['boot'].get('phase', 0)
    if not 0 <= ph0 < nph:
        raise NoClosure('the boot is read in phase %d of %d' % (ph0, nph))
    other = tuple(fam['other_side_cells'])
    q = ord(fam['state']) - 65
    hs = fam['head']
    left = fam['side'] == 'L'
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

    # The interior class arms: t^n ++ d :: rest -> 0^n ++ (d+1) :: rest, one
    # per digit below the top and per ARM INDEX.  The cost of the carry
    # ripple need not be affine in [n] -- measured (4i), four live-core rows
    # walk the run at one cost on even lengths and another on odd -- so the
    # class splits by residue, and (4k) some of those residues need a
    # materialisation offset that is at or above the stride, which is what
    # the threshold buys.  A row whose cost is genuinely quadratic has no
    # (threshold, stride) that works and is refused here; that is the count
    # language of RULE_LADDER 5, not a gap in this emitter.
    el, er = (not left), left

    def interior_at(n0, stride):
        got = []
        for d in range(b - 1):
            for r in range(n0 + stride):
                s = 0 if r < n0 else stride
                c0 = conf(blk(pre + digs[b - 1] * r, digs[b - 1], s, digs[d]))
                c1 = conf(blk(pre + digs[0] * r, digs[0], s, digs[d + 1]))
                try:
                    ch, ca, cb = derive(el, er, c0, c1,
                                        'interior arm d=%d r=%d' % (d, r))
                except NoClosure:
                    return None
                got.append((d, r, s, c0, c1, ch, ca, cb))
        return got

    inter, n0i, sti = None, None, None
    for n0, stride in ARM_GRID:
        got = interior_at(n0, stride)
        if got is not None:
            inter, n0i, sti = got, n0, stride
            break
    if inter is None:
        raise NoClosure('interior arm: no chain at any threshold 0..3 and '
                        'stride 1..4 -- the carry ripple is not affine in the '
                        'run length')

    # The fill arms: t^k -> the fill law's target at width k + s, both tails
    # known empty, with the same two knobs.  The arm at index [r] carries [r]
    # guaranteed copies in s_pre, so its target carries [r + widens_by - m]
    # of them and they divide about the block as [fm1] before and [fm2]
    # after; 4h's normalisation is that at least one should be materialised,
    # so try fm1 = 1 first.
    def fill_at(n0, stride):
        got = []
        for ph, f in enumerate(fills):
            to = f['lands_in_phase']
            mid = f['target_fill_digit']
            mf = len(f['target_prefix']) + len(f['target_suffix'])
            fpre = tuple(x for d in f['target_prefix'] for x in digs[d])
            fsuf = tuple(x for d in f['target_suffix'] for x in digs[d])
            for r in range(1, n0 + stride):
                s = 0 if r < n0 else stride
                fl = conf(blk(pre + digs[b - 1] * r, digs[b - 1], s, tails[ph]))
                total = r + f['widens_by'] - mf
                if total < 0:
                    return None
                hit = None
                for m1 in _splits(total):
                    cand = conf(blk(pre + fpre + digs[mid] * m1, digs[mid], s,
                                    digs[mid] * (total - m1) + fsuf
                                    + tails[to]))
                    try:
                        ch, ca, cb = derive(True, True, fl, cand,
                                            'fill arm r=%d ph=%d' % (r, ph))
                    except NoClosure:
                        continue
                    hit = (r, ph, s, m1, total - m1, fl, cand, ch, ca, cb)
                    break
                if hit is None:
                    return None
                got.append(hit)
        return got

    fill, n0f, stf = None, None, None
    for n0, stride in ARM_GRID:
        if n0 < 1 or n0 + stride < 2:
            continue          # no width is 0, and there must be an arm
        got = fill_at(n0, stride)
        if got is not None:
            fill, n0f, stf = got, n0, stride
            break
    if fill is None:
        raise NoClosure('fill arm: no chain at any threshold 1..3, stride '
                        '1..4 or copy split')

    # the boot, and a chain to every state from each fill arm's anchor
    boot = cert['boot']
    ds0 = list(boot['digits_lsb_first'])
    cells = list(pre)
    for d in ds0:
        cells.extend(digs[d])
    cells.extend(tails[ph0])
    if cells != list(boot['cells']):
        raise NoClosure('boot cells %r are not the family at %r'
                        % (boot['cells'], ds0))
    if not ds0:
        raise NoClosure('boot digit string is empty')

    # Which closer this row wants.  A row whose liveness is ABCD never
    # quasihalts and [board_neverqh] takes it; a row missing exactly one
    # state QUASIHALTS in that state and wants [board_iqh] instead, with the
    # arms additionally shown to avoid it (4k step 2).  [board_neverqh]
    # proves the wrong theorem for the second kind by construction.
    live = (cert.get('liveness') or {}).get('states_infinitely_often')
    if live == ''.join(s[-1] for s in ST):
        qa, sq = None, None
    elif live and len(live) == 3:
        qa = next(i for i in range(4) if ST[i][-1] not in live)
        sq = last_visit(tab, qa, boot['steps_from_blank'])
        if sq is None:
            raise NoClosure('%s never visits %s before the anchor, so it is '
                            'not the quiet state' % (cert['spec'], ST[qa]))
    else:
        raise NoClosure('liveness %r: the closure takes ABCD (never '
                        'quasihalts) or exactly one quiet state' % live)

    # A chain to each state from EACH fill arm's anchor -- the tops the
    # liveness argument lands on are whatever widths the counter reaches, so
    # every arm index has to carry its own visits.  [vis_of_run] wants a
    # chain from the anchor, NOT a prefix of the arm's own chain -- which
    # matters, because a state can sit inside a macro step that no prefix
    # ends on.  So: walk out from every prefix of that arm's derivation.
    # The QUIET state has no such chain, and wanting one is the bug the
    # liveness split above exists to avoid.
    want = [i for i in range(4) if i != qa]

    def visits(fl, fch):
        seen, cand = {}, []
        for i in range(len(fch) + 1):
            base = fch[:i]
            cand.append(base)
            for k in range(0, 31):
                cand.append(base + [('SWin', k)])
                cand.append(base + [('SWinL', k)])
                cand.append(base + [('SWinR', k)])
            for k in range(0, 16):
                for k2 in range(0, 8):
                    cand.append(base + [('SWinL', k), ('SWin', k2)])
                    cand.append(base + [('SWinR', k), ('SWin', k2)])
        for ch in cand:
            if all(i in seen for i in want):
                break
            got = LC.srun(tab, True, True, ch, fl)
            if got:
                seen.setdefault(got[0][0], ch)
        if all(i in seen for i in want):
            return seen

        # A state the arm's own lap does not pass through.  [vis_of_run] wants
        # a chain from the anchor and NOTHING about where it ends, so it may
        # leave the lap entirely -- which a multi-phase counter needs, because
        # a phase whose fill is a lap into the next terminator can be six
        # steps long and pass through two states.  This walks out from the
        # anchor the way the chain search itself explores (at a wall only a
        # cycle or a rotation makes progress), breadth first, and keeps the
        # first chain that lands in each state still wanted.
        front, seenk = [([], fl)], set()
        for _ in range(12):
            if all(i in seen for i in want) or not front:
                break
            nxt = []
            for ch, c in front:
                try:
                    sts = (LC._win_candidates(tab, True, True, c, 120)
                           + LC._cyc_candidates(tab, True, True, c, 120)
                           + LC._rot_candidates(c))
                except LC.Halt:
                    continue
                for st in sts:
                    try:
                        r = LC.sstep(tab, True, True, st, c)
                    except LC.Halt:
                        continue
                    if r is None:
                        continue
                    c2 = r[0]
                    k = (c2[0], c2[1], c2[2], c2[3])
                    if k in seenk:
                        continue
                    seenk.add(k)
                    seen.setdefault(c2[0], ch + [st])
                    nxt.append((ch + [st], c2))
            front = nxt
        return seen

    # The VISIT PHASE.  A fill anchor does not have to reach every recurring
    # state; what the liveness needs is that the anchors which DO reach it
    # keep coming, and [tops_cofinal_at] gives that for the tops of any one
    # phase the cycle returns to.  Measured (4n): on all three two-phase rows
    # the phase whose fill laps into the next terminator WITHOUT widening is
    # a six-step lap whose anchor reaches two states of four, and the other
    # phase's anchor reaches all four.  So: pick a phase that reaches
    # everything at every arm index, and report what each phase missed if
    # none does.
    seen_at = {}
    for (r, ph, _s, _m1, _m2, fl, _fr, fch, _ca, _cb) in fill:
        seen_at[(r, ph)] = visits(fl, fch)
    pv, miss = None, []
    for ph in range(nph):
        bad = []
        for (r, p) in sorted(seen_at):
            if p != ph:
                continue
            gap = [ST[i] for i in want if i not in seen_at[(r, p)]]
            if gap:
                bad.append('r=%d misses %s' % (r, ','.join(gap)))
        if not bad:
            pv = ph
            break
        miss.append('phase %d (%s)' % (ph, '; '.join(bad)))
    if pv is None:
        raise NoClosure('no phase whose fill anchors reach every recurring '
                        'state: %s' % ' | '.join(miss))
    vis = {r: {i: seen_at[(r, pv)][i] for i in want}
           for (r, p) in seen_at if p == pv}

    # ...and that the phase cycle returns to it from every phase, with the
    # number of fills it takes -- the kernel's [Hcyc], discharged per phase.
    def kto(ph):
        cur = ph
        for k in range(nph + 1):
            if cur == pv:
                return k
            cur = fills[cur]['lands_in_phase']
        return None
    kcyc = [kto(ph) for ph in range(nph)]
    if any(k is None for k in kcyc):
        raise NoClosure('the phase cycle does not reach phase %d from every '
                        'phase' % pv)

    return dict(b=b, el=el, er=er, nph=nph, ph0=ph0, pv=pv, kcyc=kcyc,
                inter=inter, n0i=n0i, sti=sti,
                fill=fill, n0f=n0f, stf=stf,
                ds0=ds0, t0=boot['steps_from_blank'], vis=vis,
                want=want, qa=qa, sq=sq)


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
    from the FAMILY rather than mined: interior arms for the digits below the
    top, and fill arms.  Every certificate arm above is one of these with its
    run lengths pinned to their lower bounds, which is why %(nc)d of them
    collapse to %(na)d here.

    Both classes are indexed by [LadderCheck]'s ONE arm scheme -- flat below
    a threshold, residue-and-stride at or above it.  The interior class runs
    at threshold %(n0i)d stride %(sti)d, the fill class at threshold %(n0f)d
    stride %(stf)d.

    [board_neverqh] consumes them, the boot, and one chain per state per fill
    arm, and returns the machine-level theorem. *)
'''

CLOSURE_IARM = '''Definition iarm%(d)d_%(r)d_%(mid)s : LRule :=
  mkLRule (%(lhs)s)
          (%(rhs)s) %(ca)d %(cb)d.
Definition ch_iarm%(d)d_%(r)d_%(mid)s : list rstep := %(ch)s.
Lemma ok_iarm%(d)d_%(r)d_%(mid)s :
  check_arm tm %(el)s %(er)s rules iarm%(d)d_%(r)d_%(mid)s
            ch_iarm%(d)d_%(r)d_%(mid)s = true.
Proof. vm_compute. reflexivity. Qed.

'''

CLOSURE_IDISP = '''Definition iarm_%(mid)s (d r : nat) : LRule :=
  match d, r with
  %(br)s
  | _, _ => iarm0_0_%(mid)s   (* unreachable: only d < b-1 and r < N0 + st *)
  end.

'''

CLOSURE_FARM = '''Definition farm%(r)d_%(ph)d_%(mid)s : LRule :=
  mkLRule (%(lhs)s)
          (%(rhs)s) %(ca)d %(cb)d.
Definition ch_farm%(r)d_%(ph)d_%(mid)s : list rstep := %(ch)s.
Lemma ok_farm%(r)d_%(ph)d_%(mid)s :
  check_arm tm true true rules farm%(r)d_%(ph)d_%(mid)s
            ch_farm%(r)d_%(ph)d_%(mid)s = true.
Proof. vm_compute. reflexivity. Qed.

'''

CLOSURE_FDISP = '''(** The fill arms, one per arm index and PHASE.  Both tails are known
    empty -- they are the only arms that see the end of the counter -- and
    the arm at index [r] has [r] guaranteed block copies materialised into
    [s_pre], without which it has no chain at all.  [fm1]/[fm2] say how the
    fill target's own guaranteed copies divide about the block.

    The phase is the second index because the fill arm is the ONLY one that
    sees a terminator: it leaves from the terminator of its own phase and
    lands on the terminator of the phase its law names.  The interior arms
    keep the terminator in the opaque tail and are phase-free. *)
Definition farm_%(mid)s (r ph : nat) : LRule :=
  match r, ph with
  %(br)s
  | _, _ => farm%(r0)d_%(ph0)d_%(mid)s  (* unreachable: 0 < r < N0 + st *)
  end.

Definition fm1_%(mid)s (r ph : nat) : nat :=
  match r, ph with %(b1)s | _, _ => 0 end.
Definition fm2_%(mid)s (r ph : nat) : nat :=
  match r, ph with %(b2)s | _, _ => 0 end.

'''

CLOSURE_VIS = '''(** One chain per RECURRING state per fill arm, at the VISIT PHASE %(pv)d.
    [vis_of_run] turns each into a visit, and [tops_cofinal_at] says the tops
    of that phase keep coming -- which is all the liveness needs, and is why
    the arms of the other phases carry no visits at all. *)
Definition vis_%(mid)s (r : nat) (q : St) : list lstep :=
  match r, q with
  %(vb)s
  | _, _ => []
  end.

'''

CLOSURE_THM = '''Lemma iarm_sound_%(mid)s : forall d r,
  d < fm_b FAM - 1 -> r < %(n0i)d + %(sti)d ->
  RuleSound tm (negb (fm_left FAM)) (fm_left FAM) (iarm_%(mid)s d r).
Proof.
  intros d r Hd Hr. vm_compute in Hd.
%(bsound)s  exfalso; lia.
Qed.

Lemma iarm_lhs_%(mid)s : forall d r,
  d < fm_b FAM - 1 -> r < %(n0i)d + %(sti)d ->
  lr_lhs (iarm_%(mid)s d r)
    = cls_conf FAM (cls_side FAM [] (fm_b FAM - 1) r
                      (astride %(n0i)d %(sti)d r) [d]).
Proof.
  intros d r Hd Hr. vm_compute in Hd.
%(bcomp)s  exfalso; lia.
Qed.

Lemma iarm_rhs_%(mid)s : forall d r,
  d < fm_b FAM - 1 -> r < %(n0i)d + %(sti)d ->
  lr_rhs (iarm_%(mid)s d r)
    = cls_conf FAM (cls_side FAM [] 0 r (astride %(n0i)d %(sti)d r) [S d]).
Proof.
  intros d r Hd Hr. vm_compute in Hd.
%(bcomp)s  exfalso; lia.
Qed.

Lemma iarm_cb_%(mid)s : forall d r,
  d < fm_b FAM - 1 -> r < %(n0i)d + %(sti)d -> 0 < lr_cb (iarm_%(mid)s d r).
Proof.
  intros d r Hd Hr. vm_compute in Hd.
%(blia)s  exfalso; lia.
Qed.

Lemma farm_sound_%(mid)s : forall r ph, 0 < r -> r < %(n0f)d + %(stf)d ->
  ph < %(nph)d -> RuleSound tm true true (farm_%(mid)s r ph).
Proof.
  intros r ph H0 Hr Hph.
%(fsound)s  exfalso; lia.
Qed.

Lemma farm_lhs_%(mid)s : forall r ph, 0 < r -> r < %(n0f)d + %(stf)d ->
  ph < %(nph)d ->
  lr_lhs (farm_%(mid)s r ph)
    = cls_conf FAM (run_side FAM (fm_b FAM - 1) r (astride %(n0f)d %(stf)d r)
                      0 ph [] []).
Proof.
  intros r ph H0 Hr Hph.
%(fcomp)s  exfalso; lia.
Qed.

Lemma farm_rhs_%(mid)s : forall r ph, 0 < r -> r < %(n0f)d + %(stf)d ->
  ph < %(nph)d ->
  lr_rhs (farm_%(mid)s r ph)
    = cls_conf FAM (run_side FAM (f_mid (fam_fill FAM ph)) (fm1_%(mid)s r ph)
                      (astride %(n0f)d %(stf)d r) (fm2_%(mid)s r ph)
                      (f_to (fam_fill FAM ph))
                      (f_pre (fam_fill FAM ph)) (f_suf (fam_fill FAM ph))).
Proof.
  intros r ph H0 Hr Hph.
%(fcomp)s  exfalso; lia.
Qed.

Lemma farm_cb_%(mid)s : forall r ph, 0 < r -> r < %(n0f)d + %(stf)d ->
  ph < %(nph)d -> 0 < lr_cb (farm_%(mid)s r ph).
Proof.
  intros r ph H0 Hr Hph.
%(flia)s  exfalso; lia.
Qed.

Lemma fm12_%(mid)s : forall r ph, 0 < r -> r < %(n0f)d + %(stf)d ->
  ph < %(nph)d ->
  fm1_%(mid)s r ph + fm2_%(mid)s r ph
  + (length (f_pre (fam_fill FAM ph)) + length (f_suf (fam_fill FAM ph)))
  = r + f_s (fam_fill FAM ph).
Proof.
  intros r ph H0 Hr Hph.
%(flia)s  exfalso; lia.
Qed.

Lemma boot_%(mid)s :
  csteps tm %(t0)d c0 = Some (fam_cfg FAM (%(ds0)s, 0, %(ph0)d)).
Proof. vm_compute. reflexivity. Qed.

'''

CLOSURE_NQH = '''Lemma vis_ok_%(mid)s : forall r q, 0 < r ->
  r < %(n0f)d + %(stf)d ->
  srun_st tm true true (vis_%(mid)s r q) (lr_lhs (farm_%(mid)s r %(pv)d))
    = Some q.
Proof.
  intros r q H0 Hr.
%(fvis)s  exfalso; lia.
Qed.

(** The machine-level theorem.  Every argument is either a [RuleSound] the
    Stage-B kernel discharged, or an equation two [vm_compute]s decide. *)
Theorem nqh_%(mid)s : NeverQuasiHaltsSt tm.
Proof.
  apply (boardph_neverqh tm FAM %(nph)d iarm_%(mid)s %(n0i)d %(sti)d
                         farm_%(mid)s %(n0f)d %(stf)d
                         fm1_%(mid)s fm2_%(mid)s %(pv)d vis_%(mid)s
                         %(ds0)s %(ph0)d %(t0)d).
%(args)s  - exact vis_ok_%(mid)s.
Qed.
'''

CLOSURE_QH = '''Lemma vis_ok_%(mid)s : forall r q, q <> %(qa)s -> 0 < r ->
  r < %(n0f)d + %(stf)d ->
  srun_st tm true true (vis_%(mid)s r q) (lr_lhs (farm_%(mid)s r %(pv)d))
    = Some q.
Proof.
  intros r q Hq H0 Hr.
%(fvis)s  exfalso; lia.
Qed.

(** *** The arms avoid the quiet state

    Recomputed from the SAME chains the kernel already replays
    ([LadderCheck.arm_avoid] over [LapAvoid.srun_avoid]): a chain whose trace
    touches [%(qa)s] evaluates to [false] and this file fails to compile. *)
%(avarms)s
Lemma iarm_avoid_%(mid)s : forall d r,
  d < fm_b FAM - 1 -> r < %(n0i)d + %(sti)d ->
  RuleAvoid tm (negb (fm_left FAM)) (fm_left FAM) %(qa)s (iarm_%(mid)s d r).
Proof.
  intros d r Hd Hr. vm_compute in Hd.
%(bav)s  exfalso; lia.
Qed.

Lemma farm_avoid_%(mid)s : forall r ph, 0 < r -> r < %(n0f)d + %(stf)d ->
  ph < %(nph)d -> RuleAvoid tm true true %(qa)s (farm_%(mid)s r ph).
Proof.
  intros r ph H0 Hr Hph.
%(fav)s  exfalso; lia.
Qed.

(** *** The quiet state's last visit, and the window from it to the anchor *)
Lemma qvis_%(mid)s : VisitsAt tm %(qa)s %(sq)d.
Proof. apply bootvis_chk_sound. vm_compute. reflexivity. Qed.

Lemma qwin_%(mid)s : forall n c, %(sq)d < n < %(t0)d ->
  stepn tm n InitES = Some c -> fst c <> %(qa)s.
Proof.
  intros n c Hn Hstep.
  exact (bootquiet_chk_sound tm %(qa)s %(sq1)d %(win)d
           ltac:(vm_compute; reflexivity) n c ltac:(lia) Hstep).
Qed.

(** The machine-level theorem.  This row QUASIHALTS in %(qa)s: the counter
    laps forever and every other state recurs, but %(qa)s stops firing after
    index %(sq)d.  [board_iqh] returns the exact bound and it is weakened to
    the census tier's 2000. *)
Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\\ QHBound 2000 tm /\\ QuasiHaltsSt tm.

Theorem iqh_%(mid)s : iqh tm.
Proof.
  assert (H : NonHalt tm /\\ QHBound (S %(sq)d) tm /\\ QuasiHaltsSt tm).
  { apply (boardph_iqh tm FAM %(nph)d iarm_%(mid)s %(n0i)d %(sti)d
                       farm_%(mid)s %(n0f)d %(stf)d
                       fm1_%(mid)s fm2_%(mid)s %(pv)d
                       %(ds0)s %(ph0)d %(t0)d %(qa)s %(sq)d vis_%(mid)s).
%(args)s    - exact iarm_avoid_%(mid)s.
    - exact farm_avoid_%(mid)s.
    - exact vis_ok_%(mid)s.
    - exact qvis_%(mid)s.
    - exact qwin_%(mid)s. }
  destruct H as (Hn & Hb & Hq).
  split; [exact Hn | split; [| exact Hq]].
  apply (qhbound_mono (S %(sq)d) 2000); [lia | exact Hb].
Qed.
'''


AVOID_ARM = '''Lemma av_%(nm)s_%(mid)s :
  RuleAvoid tm %(el)s %(er)s %(qa)s %(nm)s_%(mid)s.
Proof. eapply arm_avoid; [exact ok_%(nm)s_%(mid)s | vm_compute; reflexivity]. Qed.

'''


def _rbranches(n, body, dead='  exfalso; lia.\n', lo=0):
    """[destruct r] down to [n], one brace-delimited branch per index, the
    indices below [lo] and at or above [n] dead."""
    out = []
    for r in range(n):
        out.append('  destruct r as [|r].\n  { %s }\n'
                   % (dead.strip() if r < lo else body(r)))
    return ''.join(out)


def emit_closure(cert, tab, mid):
    """The Coq for LadderCheck.boardph_neverqh, or a note on what stopped it."""
    try:
        cd = closure_data(cert, tab)
    except NoClosure as e:
        return CLOSURE_NONE % e, None

    b = cd['b']
    n0i, sti, n0f, stf = cd['n0i'], cd['sti'], cd['n0f'], cd['stf']
    nph, ph0, pv = cd['nph'], cd['ph0'], cd['pv']
    nA, nF = n0i + sti, n0f + stf
    L = [CLOSURE_HEAD % dict(nc=len(cert['arms']),
                             na=len(cd['inter']) + len(cd['fill']),
                             n0i=n0i, sti=sti, n0f=n0f, stf=stf, nph=nph)]
    el, er = (cd['el'], cd['er'])
    for d, r, _s, c0, c1, ch, ca, cb in cd['inter']:
        L.append(CLOSURE_IARM % dict(
            d=d, r=r, mid=mid, lhs=coq_conf(c0), rhs=coq_conf(c1), ca=ca,
            cb=cb, ch=coq_chain(ch), el=str(el).lower(), er=str(er).lower()))
    L.append(CLOSURE_IDISP % dict(
        mid=mid,
        br='\n  '.join('| %d, %d => iarm%d_%d_%s' % (d, r, d, r, mid)
                       for d, r, _s, _0, _1, _c, _a, _b in cd['inter'])))
    for r, ph, _s, _m1, _m2, fl, fr, fch, fca, fcb in cd['fill']:
        L.append(CLOSURE_FARM % dict(
            r=r, ph=ph, mid=mid, lhs=coq_conf(fl), rhs=coq_conf(fr), ca=fca,
            cb=fcb, ch=coq_chain(fch)))
    r0, p0 = cd['fill'][0][0], cd['fill'][0][1]
    L.append(CLOSURE_FDISP % dict(
        mid=mid, r0=r0, ph0=p0,
        br='\n  '.join('| %d, %d => farm%d_%d_%s' % (r, ph, r, ph, mid)
                       for r, ph, *_ in cd['fill']),
        b1=' '.join('| %d, %d => %d' % (r, ph, m1)
                    for r, ph, _s, m1, *_ in cd['fill']),
        b2=' '.join('| %d, %d => %d' % (r, ph, m2)
                    for r, ph, _s, _m1, m2, *_ in cd['fill'])))
    L.append(CLOSURE_VIS % dict(
        mid=mid, pv=pv,
        vb='\n  '.join('| %d, %s => %s' % (r, ST[i], coq_chain_l(ch))
                       for r in sorted(cd['vis'])
                       for i, ch in sorted(cd['vis'][r].items()))))

    def ibranches(body):
        """One brace-delimited branch per (digit, arm index); rest is dead."""
        out = []
        for d in range(b - 1):
            rb = []
            for r in range(nA):
                rb.append('    destruct r as [|r].\n    { %s. }\n'
                          % (body % dict(d=d, r=r, mid=mid)))
            out.append('  destruct d as [|d].\n  {\n%s    exfalso; lia.\n  }\n'
                       % ''.join(rb))
        return ''.join(out)

    def fbranches(body):
        """One per (fill arm index, PHASE); index 0 and anything past the last
        of either is dead."""
        out = []
        for r in range(nF):
            if r < 1:
                out.append('  destruct r as [|r].\n  { exfalso; lia. }\n')
                continue
            pb = []
            for ph in range(nph):
                pb.append('    destruct ph as [|ph].\n    { %s. }\n'
                          % (body % dict(r=r, ph=ph, mid=mid)))
            out.append('  destruct r as [|r].\n  {\n%s    exfalso; lia.\n  }\n'
                       % ''.join(pb))
        return ''.join(out)

    def pharg(body):
        """A board argument that is quantified over the PHASE: one branch per
        phase, the rest dead.  At [nph = 1] it is the old one-liner with a
        [destruct] around it."""
        out = ['  - intros ph Hph.\n']
        for _ in range(nph):
            out.append('    destruct ph as [|ph].\n    { %s. }\n' % body)
        out.append('    exfalso; lia.\n')
        return ''.join(out)

    L.append(CLOSURE_THM % dict(
        mid=mid, t0=cd['t0'], ds0=clist(cd['ds0'], str), ph0=ph0, nph=nph,
        n0i=n0i, sti=sti, n0f=n0f, stf=stf,
        bsound=ibranches('eapply arm_sound; [exact rules_sound_%(mid)s '
                         '| exact ok_iarm%(d)d_%(r)d_%(mid)s]'),
        bcomp=ibranches('vm_compute; reflexivity'),
        blia=ibranches('vm_compute; lia'),
        fsound=fbranches('eapply arm_sound; [exact rules_sound_%(mid)s '
                         '| exact ok_farm%(r)d_%(ph)d_%(mid)s]'),
        fcomp=fbranches('vm_compute; reflexivity'),
        flia=fbranches('vm_compute; lia')))

    # The board's arguments up to [HAfC]; both closers take exactly these.
    # The five the family's own parameters supply are quantified over the
    # phase now, so each is one branch per phase rather than one tactic.
    args = ''.join([
        '  - vm_compute; lia.\n',                        # Hb
        '  - vm_compute; reflexivity.\n',                # Hcode
        '  - vm_compute; reflexivity.\n',                # Hstep
        pharg('vm_compute; repeat constructor'),          # Hfpre
        pharg('vm_compute; repeat constructor'),          # Hfsuf
        pharg('vm_compute; lia'),                         # Hfmid
        pharg('vm_compute; lia'),                         # Hfs
        pharg('vm_compute; lia'),                         # Hfto: the CYCLE
        '  - lia.\n',                                     # Hpv
        ''.join(['  - intros ph Hph.\n']                  # Hcyc
                + ['    destruct ph as [|ph].\n'
                   '    { exists %d; vm_compute; reflexivity. }\n' % k
                   for k in cd['kcyc']]
                + ['    exfalso; lia.\n']),
        '  - exact fm12_%s.\n' % mid,                    # Hfm12
        '  - repeat constructor.\n',                     # Hbnd0
        '  - vm_compute; lia.\n',                        # Hlen0
        '  - lia.\n',                                    # Hph0
        '  - exact boot_%s.\n' % mid,                    # Hboot
        '  - lia.\n',                                    # Hsti
        '  - exact iarm_sound_%s.\n' % mid,
        '  - exact iarm_lhs_%s.\n' % mid,
        '  - exact iarm_rhs_%s.\n' % mid,
        '  - exact iarm_cb_%s.\n' % mid,
        '  - lia.\n',                                    # Hstf
        '  - lia.\n',                                    # HN0f
        '  - exact farm_sound_%s.\n' % mid,
        '  - exact farm_lhs_%s.\n' % mid,
        '  - exact farm_rhs_%s.\n' % mid,
        '  - exact farm_cb_%s.\n' % mid,
    ])

    common = dict(mid=mid, t0=cd['t0'], ds0=clist(cd['ds0'], str),
                  ph0=ph0, nph=nph, pv=pv,
                  n0i=n0i, sti=sti, n0f=n0f, stf=stf, args=args)
    def vbranches(body):
        """The visit lemma is at ONE phase, so its branches are over the arm
        index alone -- the shape it had before the phase cycle."""
        return _rbranches(nF, lambda r: body, lo=1)

    if cd['qa'] is None:
        L.append(CLOSURE_NQH % dict(
            common, fvis=vbranches('destruct q; vm_compute; reflexivity.')))
    else:
        qa, sq = ST[cd['qa']], cd['sq']
        av = []
        for d, r, _s, *_ in cd['inter']:
            av.append(AVOID_ARM % dict(
                nm='iarm%d_%d' % (d, r), mid=mid, qa=qa,
                el='(negb (fm_left FAM))', er='(fm_left FAM)'))
        for r, ph, *_ in cd['fill']:
            av.append(AVOID_ARM % dict(nm='farm%d_%d' % (r, ph), mid=mid,
                                       qa=qa, el='true', er='true'))
        L.append(CLOSURE_QH % dict(
            common, qa=qa, sq=sq, sq1=sq + 1, win=cd['t0'] - sq - 1,
            avarms=''.join(av),
            bav=ibranches('exact av_iarm%(d)d_%(r)d_%(mid)s'),
            fav=fbranches('exact av_farm%(r)d_%(ph)d_%(mid)s'),
            fvis=vbranches('destruct q; '
                           'try (exfalso; apply Hq; reflexivity); '
                           'vm_compute; reflexivity.')))
    return ''.join(L), cd


# ===========================================================================
# The (Gray, 2) path.  LadderCheck section 10 ([boardG_neverqh]) is a
# DIFFERENT closure from section 7's and this builds its arms, so it is kept
# entirely apart from [closure_data] rather than threaded through it: four
# interior classes instead of [b-1] digits, a fill arm indexed by the WIDTH
# with a fixed word at each end, one phase, and the far side read off the
# boot.  Nothing below is shared with the binary path.
# ===========================================================================

def g2c(p, i):
    """[LadderCheck.g2c p i] as (u, t, w, u', t', w').  4i's four classes at
    the family's own parity; at p = 0 they are 4i's table verbatim and at
    p = 1 they are the same four with the two sides exchanged."""
    q = 1 - p
    return [([p, p], 0, [], [q, q], 0, []),
            ([p, q], 1, [], [q, p], 1, []),
            ([q], 0, [1, p], [p], 0, [1, q]),
            ([q], 0, [1, q], [p], 0, [1, p])][i]


def _gray_boot_conf(cert, tab):
    """The anchor's `cconf`, by simulating `CTape.ctape_move` from the blank
    tape to the boot index.

    This is the one place the far side can be read EXACTLY.  `RuleSound` is an
    equation on `cconf` and `ctape_move` does not normalise, so a blank the
    head materialised by stepping back over it is `S0 :: r` and not `r`;
    `valfam`'s `other_side_cells` reads through a run-length view that has
    already dropped a trailing blank run and can be short by exactly those
    cells (LADDER_PLAN 4n).  Same TAPE under `lift`, different `cconf`."""
    l, h, r, q = [], 0, [], 0
    for _ in range(cert['boot']['steps_from_blank']):
        e = tab.get((q, h))
        if e is None:
            return None
        w, d, q2 = e
        if d > 0:
            l, h, r = [w] + l, (r[0] if r else 0), r[1:]
        else:
            r, h, l = [w] + r, (l[0] if l else 0), l[1:]
        q = q2
    return q, tuple(l), h, tuple(r)


def _gray_far_sides(cert, tab):
    """The far sides to try for `fm_other`: the certificate's, and the one the
    machine actually spells at the anchor."""
    fam = cert['family']
    other = tuple(fam['other_side_cells'])
    bc = _gray_boot_conf(cert, tab)
    if bc is None:
        raise NoClosure('the boot index halts')
    q, l, h, r = bc
    if (q, h) != (ord(fam['state']) - 65, fam['head']):
        raise NoClosure('the boot index is not the anchor')
    far = r if fam['side'] == 'L' else l
    n = min(len(far), len(other))
    if far[:n] != other[:n] or any(c != 0 for c in far[n:] + other[n:]):
        raise NoClosure('the boot far side is %r, the family carries %r and '
                        'they differ by more than trailing blanks'
                        % (far, other))
    return [other] if far == other else [other, far]


def _gray_visits(tab, fl, fch, want):
    """A chain from a fill arm's anchor to each state in `want`.

    `vis_of_run` wants a chain from the ANCHOR and nothing about where it
    ends, not a prefix of the arm's own chain -- a state can sit inside a
    macro step that no prefix ends on.  So: walk out from every prefix of the
    arm's derivation, then breadth-first from the anchor if that is not
    enough."""
    seen, cand = {}, []
    for i in range(len(fch) + 1):
        base = fch[:i]
        cand.append(base)
        for k in range(0, 31):
            cand.append(base + [('SWin', k)])
            cand.append(base + [('SWinL', k)])
            cand.append(base + [('SWinR', k)])
        for k in range(0, 16):
            for k2 in range(0, 8):
                cand.append(base + [('SWinL', k), ('SWin', k2)])
                cand.append(base + [('SWinR', k), ('SWin', k2)])
    for ch in cand:
        if all(i in seen for i in want):
            break
        got = LC.srun(tab, True, True, ch, fl)
        if got:
            seen.setdefault(got[0][0], ch)
    if all(i in seen for i in want):
        return seen
    front, seenk = [([], fl)], set()
    for _ in range(12):
        if all(i in seen for i in want) or not front:
            break
        nxt = []
        for ch, c in front:
            try:
                sts = (LC._win_candidates(tab, True, True, c, 120)
                       + LC._cyc_candidates(tab, True, True, c, 120)
                       + LC._rot_candidates(c))
            except LC.Halt:
                continue
            for st in sts:
                try:
                    res = LC.sstep(tab, True, True, st, c)
                except LC.Halt:
                    continue
                if res is None:
                    continue
                c2 = res[0]
                k = (c2[0], c2[1], c2[2], c2[3])
                if k in seenk:
                    continue
                seenk.add(k)
                seen.setdefault(c2[0], ch + [st])
                nxt.append((ch + [st], c2))
        front = nxt
    return seen


def closure_data_gray(cert, tab):
    """The class arms of a one-phase (Gray, 2) family, for LadderCheck 10.

    LADDER_PLAN 4i measured the coverage and 4n re-derived it from the
    machines: four classes of `Class`'s own shape cover every interior string
    of every width, split by the PARITY of the digit sum -- which is the
    value's low bit, and +2 preserves it.  So the arms are one per CLASS and
    arm index, plus one fill arm per WIDTH index; the fill arm's left-hand
    side is the top of the width, [1-p] ++ 0^(k-2) ++ [1], the largest MEMBER
    and not the largest value."""
    fam = cert['family']
    fills = cert.get('fill_by_phase') or [cert['fill']]
    if fam.get('code') != 'gray':
        raise NoClosure('code %s is not gray' % fam.get('code'))
    if fam['base'] != 2:
        raise NoClosure('base %d: LadderCheck states (Gray, 2) at base 2'
                        % fam['base'])
    if fam.get('value_step_per_anchor_visit') != 2:
        raise NoClosure('step %d: LadderCheck states (Gray, 2)'
                        % fam.get('value_step_per_anchor_visit', 1))
    if fam.get('weights') is not None:
        raise NoClosure('numeration %s is not positional base-2'
                        % fam.get('numeration'))
    if len(fills) != 1:
        raise NoClosure('%d phases: the gray board is one-phase (4n measured '
                        'all six gray rows at one)' % len(fills))
    f = fills[0]
    if f['lands_in_phase'] != 0:
        raise NoClosure('the fill lands in phase %d of 1'
                        % f['lands_in_phase'])
    if f['target_fill_digit'] != 0:
        raise NoClosure('the fill digit is %d: with a fill digit of 1 the '
                        "target's digit sum alternates with the width, so the "
                        'parity is not an invariant at all'
                        % f['target_fill_digit'])
    tails = [tuple(t) for t in
             (fam.get('terminators_by_phase') or [fam['terminator']])]
    if cert['boot'].get('phase', 0) != 0:
        raise NoClosure('the boot is read in phase %d of 1'
                        % cert['boot'].get('phase', 0))
    live = (cert.get('liveness') or {}).get('states_infinitely_often')
    if live != ''.join(s[-1] for s in ST):
        raise NoClosure('liveness %r: the gray board is board_neverqh only '
                        '(no gray core row quasihalts)' % live)

    digs = [tuple(w) for w in fam['digits']]
    pre = tuple(fam['near_head_prefix'])
    q = ord(fam['state']) - 65
    hs = fam['head']
    left = fam['side'] == 'L'
    el, er = (not left), left

    boot = cert['boot']
    ds0 = list(boot['digits_lsb_first'])
    if len(ds0) < 2:
        raise NoClosure('the boot digit string %r is shorter than two digits, '
                        'and the top of a width needs two to spell' % ds0)
    p = sum(ds0) % 2
    cells = list(pre)
    for d in ds0:
        cells.extend(digs[d])
    cells.extend(tails[0])
    if cells != list(boot['cells']):
        raise NoClosure('boot cells %r are not the family at %r'
                        % (boot['cells'], ds0))
    fpar = (sum(f['target_prefix']) + sum(f['target_suffix'])) % 2
    if fpar != p:
        raise NoClosure("the fill target's digit sum has parity %d and the "
                        "family's members have parity %d, so the fill leaves "
                        'the family' % (fpar, p))

    fpre, fsuf = list(f['target_prefix']), list(f['target_suffix'])
    mid = f['target_fill_digit']
    mf = len(fpre) + len(fsuf)

    def cellsof(ds):
        out = []
        for d in ds:
            out.extend(digs[d])
        return tuple(out)

    def conf(other, sd):
        OT = (other, (), 0, 0, ())
        return (q, sd, hs, OT) if left else (q, OT, hs, sd)

    def derive(e0, e1, c0, c1, what):
        ch = LC.derive_chain(tab, e0, e1, c0, c1, maxdepth=32, nmax=120,
                             lift=True)
        if ch is None:
            raise NoClosure('%s: no chain' % what)
        got = LC.srun(tab, e0, e1, ch, c0)
        if got is None or got[0] != c1:
            raise NoClosure('%s: chain lands off the rhs' % what)
        if got[2] == 0:
            raise NoClosure('%s: zero-step rule' % what)
        return ch, got[1], got[2]

    def interior_at(other, n0, stride):
        got = []
        for i in range(4):
            u, t, w, u2, t2, w2 = g2c(p, i)
            for r in range(n0 + stride):
                s = 0 if r < n0 else stride
                c0 = conf(other, blk(pre + cellsof(u) + digs[t] * r,
                                     digs[t], s, cellsof(w)))
                c1 = conf(other, blk(pre + cellsof(u2) + digs[t2] * r,
                                     digs[t2], s, cellsof(w2)))
                if c0 == c1:
                    return None
                try:
                    ch, ca, cb = derive(el, er, c0, c1,
                                        'interior class %d r=%d' % (i, r))
                except NoClosure:
                    return None
                got.append((i, r, s, c0, c1, ch, ca, cb))
        return got

    def fill_at(other, n0, stride):
        got = []
        for r in range(2, n0 + stride):
            s = 0 if r < n0 else stride
            run = r - 2
            total = r + f['widens_by'] - mf
            if total < 0:
                return None
            hit = None
            for w1 in _splits(run):
                lhs = conf(other, blk(pre + cellsof([1 - p]) + digs[0] * w1,
                                      digs[0], s,
                                      digs[0] * (run - w1) + cellsof([1])
                                      + tails[0]))
                for m1 in _splits(total):
                    rhs = conf(other,
                               blk(pre + cellsof(fpre) + digs[mid] * m1,
                                   digs[mid], s,
                                   digs[mid] * (total - m1) + cellsof(fsuf)
                                   + tails[0]))
                    if lhs == rhs:
                        continue
                    try:
                        ch, ca, cb = derive(True, True, lhs, rhs,
                                            'fill r=%d' % r)
                    except NoClosure:
                        continue
                    hit = (r, s, w1, run - w1, m1, total - m1, lhs, rhs,
                           ch, ca, cb)
                    break
                if hit:
                    break
            if hit is None:
                return None
            got.append(hit)
        return got

    best = None
    for other in _gray_far_sides(cert, tab):
        inter = n0i = sti = None
        for n0, stride in ARM_GRID:
            hit = interior_at(other, n0, stride)
            if hit is not None:
                inter, n0i, sti = hit, n0, stride
                break
        fill = n0f = stf = None
        for n0, stride in ARM_GRID:
            if n0 < 2 or n0 + stride < 3:
                continue      # no width is below 2, and there must be an arm
            hit = fill_at(other, n0, stride)
            if hit is not None:
                fill, n0f, stf = hit, n0, stride
                break
        score = (inter is not None) + (fill is not None)
        if best is None or score > best[0]:
            best = (score, other, inter, n0i, sti, fill, n0f, stf)
        if score == 2:
            break
    _sc, other, inter, n0i, sti, fill, n0f, stf = best
    if inter is None:
        raise NoClosure('interior class arm: no chain at any threshold 0..3 '
                        'and stride 1..4')
    if fill is None:
        raise NoClosure('fill arm: no chain at any threshold 2..3, stride '
                        '1..4 or copy split')

    want = list(range(4))
    vis = {}
    for (r, _s, _w1, _w2, _m1, _m2, lhs, _rhs, fch, _ca, _cb) in fill:
        seen = _gray_visits(tab, lhs, fch, want)
        gap = [ST[i] for i in want if i not in seen]
        if gap:
            raise NoClosure('the fill anchor at width index %d reaches no %s'
                            % (r, ','.join(gap)))
        vis[r] = {i: seen[i] for i in want}

    return dict(gray=True, p=p, el=el, er=er, other=list(other),
                inter=inter, n0i=n0i, sti=sti,
                fill=fill, n0f=n0f, stf=stf, nph=1,
                ds0=ds0, t0=boot['steps_from_blank'], vis=vis, want=want,
                qa=None, sq=None, pv=0, ph0=0, kcyc=[0], b=2)


CLOSURE_G_HEAD = '''
(** ** The closure: from the RULES to [NeverQuasiHaltsSt], at [(Gray, 2)]

    The arms below are the case split of [LadderCheck.gray_split], built from
    the FAMILY rather than mined: one interior arm per CLASS (there are four,
    LADDER_PLAN 4i) and per arm index, and one fill arm per WIDTH index.
    Every certificate arm above is one of these with its run lengths pinned to
    their lower bounds, which is why %(nc)d of them collapse to %(na)d here.

    The family's parity is %(p)d.  That is not a choice: it is the digit sum
    of the boot, it is the value's low bit, [+2] preserves it, and it is what
    makes "member of this width" a predicate rather than "every string of this
    width".  The four classes and the top's shape are read off it.

    The interior class runs at threshold %(n0i)d stride %(sti)d, the fill
    class at threshold %(n0f)d stride %(stf)d.  [boardG_neverqh] consumes
    them, the boot, and one chain per state per fill arm. *)
'''

CLOSURE_G_IARM = '''Definition iarm%(i)d_%(r)d_%(mid)s : LRule :=
  mkLRule (%(lhs)s)
          (%(rhs)s) %(ca)d %(cb)d.
Definition ch_iarm%(i)d_%(r)d_%(mid)s : list rstep := %(ch)s.
Lemma ok_iarm%(i)d_%(r)d_%(mid)s :
  check_arm tm %(el)s %(er)s rules iarm%(i)d_%(r)d_%(mid)s
            ch_iarm%(i)d_%(r)d_%(mid)s = true.
Proof. vm_compute. reflexivity. Qed.

'''

CLOSURE_G_FARM = '''Definition farm%(r)d_%(mid)s : LRule :=
  mkLRule (%(lhs)s)
          (%(rhs)s) %(ca)d %(cb)d.
Definition ch_farm%(r)d_%(mid)s : list rstep := %(ch)s.
Lemma ok_farm%(r)d_%(mid)s :
  check_arm tm true true rules farm%(r)d_%(mid)s ch_farm%(r)d_%(mid)s = true.
Proof. vm_compute. reflexivity. Qed.

'''

CLOSURE_G_DISP = '''Definition iarm_%(mid)s (i r : nat) : LRule :=
  match i, r with
  %(ibr)s
  | _, _ => iarm0_0_%(mid)s   (* unreachable: i < 4 and r < N0i + sti *)
  end.

(** The fill arms, indexed by the WIDTH.  Both tails are known empty -- they
    are the only arms that see the end of the counter -- and the left-hand
    side is the top of the width: [%(top)d], then a run of zeros, then [1].
    That is the largest MEMBER and not the largest value ([2^k - 1] has the
    wrong parity and is not a member at all), which is why it has a fixed word
    at each end.  [fw1]/[fw2] say how the top's concrete copies of the run
    divide about the block and [fm1]/[fm2] the fill target's. *)
Definition farm_%(mid)s (r : nat) : LRule :=
  match r with
  %(fbr)s
  | _ => farm%(r0)d_%(mid)s   (* unreachable: 2 <= r < N0f + stf *)
  end.

Definition fw1_%(mid)s (r : nat) : nat := match r with %(b1)s | _ => 0 end.
Definition fw2_%(mid)s (r : nat) : nat := match r with %(b2)s | _ => 0 end.
Definition fm1_%(mid)s (r : nat) : nat := match r with %(b3)s | _ => 0 end.
Definition fm2_%(mid)s (r : nat) : nat := match r with %(b4)s | _ => 0 end.

(** One chain per state per fill arm.  [vis_of_run] turns each into a visit
    and [topsG_cofinal] says the tops keep coming, which is all the liveness
    needs. *)
Definition vis_%(mid)s (r : nat) (q : St) : list lstep :=
  match r, q with
  %(vb)s
  | _, _ => []
  end.

'''

CLOSURE_G_THM = '''Lemma iarm_sound_%(mid)s : forall i r,
  i < 4 -> r < %(n0i)d + %(sti)d ->
  RuleSound tm (negb (fm_left FAM)) (fm_left FAM) (iarm_%(mid)s i r).
Proof.
  intros i r Hi Hr.
%(isound)s  exfalso; lia.
Qed.

Lemma iarm_lhs_%(mid)s : forall i r, i < 4 -> r < %(n0i)d + %(sti)d ->
  lr_lhs (iarm_%(mid)s i r)
    = cls_conf FAM (cls_side FAM (cs_u (g2c %(p)d i)) (cs_t (g2c %(p)d i)) r
                      (astride %(n0i)d %(sti)d r) (cs_w (g2c %(p)d i))).
Proof.
  intros i r Hi Hr.
%(icomp)s  exfalso; lia.
Qed.

Lemma iarm_rhs_%(mid)s : forall i r, i < 4 -> r < %(n0i)d + %(sti)d ->
  lr_rhs (iarm_%(mid)s i r)
    = cls_conf FAM (cls_side FAM (cs_u' (g2c %(p)d i)) (cs_t' (g2c %(p)d i)) r
                      (astride %(n0i)d %(sti)d r) (cs_w' (g2c %(p)d i))).
Proof.
  intros i r Hi Hr.
%(icomp)s  exfalso; lia.
Qed.

Lemma iarm_cb_%(mid)s : forall i r, i < 4 -> r < %(n0i)d + %(sti)d ->
  0 < lr_cb (iarm_%(mid)s i r).
Proof.
  intros i r Hi Hr.
%(ilia)s  exfalso; lia.
Qed.

Lemma farm_sound_%(mid)s : forall r, 2 <= r -> r < %(n0f)d + %(stf)d ->
  RuleSound tm true true (farm_%(mid)s r).
Proof.
  intros r H2 Hr.
%(fsound)s  exfalso; lia.
Qed.

Lemma farm_lhs_%(mid)s : forall r, 2 <= r -> r < %(n0f)d + %(stf)d ->
  lr_lhs (farm_%(mid)s r)
    = cls_conf FAM (run_side FAM 0 (fw1_%(mid)s r)
                      (astride %(n0f)d %(stf)d r) (fw2_%(mid)s r) 0
                      [1 - %(p)d] [1]).
Proof.
  intros r H2 Hr.
%(fcomp)s  exfalso; lia.
Qed.

Lemma farm_rhs_%(mid)s : forall r, 2 <= r -> r < %(n0f)d + %(stf)d ->
  lr_rhs (farm_%(mid)s r)
    = cls_conf FAM (run_side FAM (f_mid (fam_fill FAM 0)) (fm1_%(mid)s r)
                      (astride %(n0f)d %(stf)d r) (fm2_%(mid)s r) 0
                      (f_pre (fam_fill FAM 0)) (f_suf (fam_fill FAM 0))).
Proof.
  intros r H2 Hr.
%(fcomp)s  exfalso; lia.
Qed.

Lemma farm_cb_%(mid)s : forall r, 2 <= r -> r < %(n0f)d + %(stf)d ->
  0 < lr_cb (farm_%(mid)s r).
Proof.
  intros r H2 Hr.
%(flia)s  exfalso; lia.
Qed.

Lemma fw_%(mid)s : forall r, 2 <= r -> r < %(n0f)d + %(stf)d ->
  fw1_%(mid)s r + fw2_%(mid)s r + 2 = r.
Proof.
  intros r H2 Hr.
%(flia)s  exfalso; lia.
Qed.

Lemma fm12_%(mid)s : forall r, 2 <= r -> r < %(n0f)d + %(stf)d ->
  fm1_%(mid)s r + fm2_%(mid)s r
  + (length (f_pre (fam_fill FAM 0)) + length (f_suf (fam_fill FAM 0)))
  = r + f_s (fam_fill FAM 0).
Proof.
  intros r H2 Hr.
%(flia)s  exfalso; lia.
Qed.

Lemma boot_%(mid)s :
  csteps tm %(t0)d c0 = Some (fam_cfg FAM (%(ds0)s, 0, 0)).
Proof. vm_compute. reflexivity. Qed.

Lemma vis_ok_%(mid)s : forall r q, 2 <= r -> r < %(n0f)d + %(stf)d ->
  srun_st tm true true (vis_%(mid)s r q) (lr_lhs (farm_%(mid)s r)) = Some q.
Proof.
  intros r q H2 Hr.
%(fvis)s  exfalso; lia.
Qed.

(** The machine-level theorem.  Every argument is either a [RuleSound] the
    Stage-B kernel discharged, or an equation two [vm_compute]s decide -- and
    the PARITY, which is one more of the second kind. *)
Theorem nqh_%(mid)s : NeverQuasiHaltsSt tm.
Proof.
  apply (boardG_neverqh tm FAM %(p)d iarm_%(mid)s %(n0i)d %(sti)d
                        farm_%(mid)s %(n0f)d %(stf)d
                        fw1_%(mid)s fw2_%(mid)s fm1_%(mid)s fm2_%(mid)s
                        vis_%(mid)s %(ds0)s %(t0)d).
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - lia.
  - vm_compute; repeat constructor.
  - vm_compute; repeat constructor.
  - vm_compute; lia.
  - vm_compute; lia.
  - vm_compute; reflexivity.
  - intros k Hk.
    rewrite (filled_parity FAM 0 k ltac:(vm_compute; reflexivity)).
    vm_compute; reflexivity.
  - repeat constructor.
  - vm_compute; lia.
  - vm_compute; reflexivity.
  - exact boot_%(mid)s.
  - lia.
  - exact iarm_sound_%(mid)s.
  - exact iarm_lhs_%(mid)s.
  - exact iarm_rhs_%(mid)s.
  - exact iarm_cb_%(mid)s.
  - lia.
  - lia.
  - exact fw_%(mid)s.
  - exact fm12_%(mid)s.
  - exact farm_sound_%(mid)s.
  - exact farm_lhs_%(mid)s.
  - exact farm_rhs_%(mid)s.
  - exact farm_cb_%(mid)s.
  - exact vis_ok_%(mid)s.
Qed.
'''


def emit_closure_gray(cert, tab, mid):
    """The Coq for LadderCheck.boardG_neverqh, or a note on what stopped it."""
    try:
        cd = closure_data_gray(cert, tab)
    except NoClosure as e:
        return CLOSURE_NONE % e, None

    p = cd['p']
    n0i, sti, n0f, stf = cd['n0i'], cd['sti'], cd['n0f'], cd['stf']
    nA, nF = n0i + sti, n0f + stf
    el, er = cd['el'], cd['er']
    L = [CLOSURE_G_HEAD % dict(nc=len(cert['arms']),
                               na=len(cd['inter']) + len(cd['fill']),
                               p=p, n0i=n0i, sti=sti, n0f=n0f, stf=stf)]
    for i, r, _s, c0, c1, ch, ca, cb in cd['inter']:
        L.append(CLOSURE_G_IARM % dict(
            i=i, r=r, mid=mid, lhs=coq_conf(c0), rhs=coq_conf(c1), ca=ca,
            cb=cb, ch=coq_chain(ch), el=str(el).lower(), er=str(er).lower()))
    for r, _s, _w1, _w2, _m1, _m2, lhs, rhs, ch, ca, cb in cd['fill']:
        L.append(CLOSURE_G_FARM % dict(
            r=r, mid=mid, lhs=coq_conf(lhs), rhs=coq_conf(rhs), ca=ca, cb=cb,
            ch=coq_chain(ch)))
    L.append(CLOSURE_G_DISP % dict(
        mid=mid, top=1 - p, r0=cd['fill'][0][0],
        ibr='\n  '.join('| %d, %d => iarm%d_%d_%s' % (i, r, i, r, mid)
                        for i, r, *_ in cd['inter']),
        fbr='\n  '.join('| %d => farm%d_%s' % (r, r, mid)
                        for r, *_ in cd['fill']),
        b1=' '.join('| %d => %d' % (r, w1) for r, _s, w1, *_ in cd['fill']),
        b2=' '.join('| %d => %d' % (r, w2)
                    for r, _s, _w1, w2, *_ in cd['fill']),
        b3=' '.join('| %d => %d' % (r, m1)
                    for r, _s, _w1, _w2, m1, *_ in cd['fill']),
        b4=' '.join('| %d => %d' % (r, m2)
                    for r, _s, _w1, _w2, _m1, m2, *_ in cd['fill']),
        vb='\n  '.join('| %d, %s => %s' % (r, ST[i], coq_chain_l(ch))
                       for r in sorted(cd['vis'])
                       for i, ch in sorted(cd['vis'][r].items()))))

    def ibranches(body):
        """One brace-delimited branch per (class index, arm index)."""
        out = []
        for i in range(4):
            rb = []
            for r in range(nA):
                rb.append('    destruct r as [|r].\n    { %s. }\n'
                          % (body % dict(i=i, r=r, mid=mid)))
            out.append('  destruct i as [|i].\n  {\n%s    exfalso; lia.\n  }\n'
                       % ''.join(rb))
        return ''.join(out)

    def fbranches(body):
        """One per fill arm index; 0 and 1 are dead, no width is below 2."""
        return _rbranches(nF, lambda r: (body % dict(r=r, mid=mid)) + '.',
                          lo=2)

    L.append(CLOSURE_G_THM % dict(
        mid=mid, p=p, t0=cd['t0'], ds0=clist(cd['ds0'], str),
        n0i=n0i, sti=sti, n0f=n0f, stf=stf,
        isound=ibranches('eapply arm_sound; [exact rules_sound_%(mid)s '
                         '| exact ok_iarm%(i)d_%(r)d_%(mid)s]'),
        icomp=ibranches('vm_compute; reflexivity'),
        ilia=ibranches('vm_compute; lia'),
        fsound=fbranches('eapply arm_sound; [exact rules_sound_%(mid)s '
                         '| exact ok_farm%(r)d_%(mid)s]'),
        fcomp=fbranches('vm_compute; reflexivity'),
        flia=fbranches('vm_compute; lia'),
        fvis=fbranches('destruct q; vm_compute; reflexivity')))
    return ''.join(L), cd



# ===========================================================================
# The (Fib, 1) path.  LadderCheck section 11 ([boardF_neverqh]) is a THIRD
# closure and this builds its arms, kept apart from the other two for the same
# reason they are kept apart from each other: two interior classes split on the
# LOW DIGIT, a fill arm indexed by the WIDTH whose left-hand side is a BARE run
# (the top of a width is 1^k), one phase, and MEMBERSHIP where the gray path
# has a parity.
#
# The numeration is FIBONACCI (LADDER_PLAN 4p): digit i carries weight
# 1, 1, 2, 3, 5, 8, ... and the widths spell 2, 3, 5, 8, 13, 21 members rather
# than 2^k.  The certificate's own `code` says "binary" on all five of these
# rows and that is the lie 4p caught -- what selects this path is `numeration`
# and the `weights` beside it, never `code`.
# ===========================================================================

def f1c(i):
    """[LadderCheck.f1c i] as (u, t, w, u', t', w').  4p's two classes: the
    increment at low digit 0, the carry at low digit 1."""
    return [([0], 0, [], [1], 0, []),
            ([], 1, [1, 0], [], 0, [1, 1])][i]


def fib_member(ds):
    """[LadderCheck.fibokb false]: at every 0, an EVEN number of 1s above it.

    Equivalently -- and this is how 4p states it -- an optional leading 1 then
    a concatenation of the blocks [0] and [1;1], LSB-first.  Checked against
    the orbit read off all five machines by tools/ladder/fibmem.py."""
    return all(sum(ds[i + 1:]) % 2 == 0 for i in range(len(ds)) if ds[i] == 0)


def closure_data_fib(cert, tab):
    """The class arms of a one-phase (Fib, 1) family, for LadderCheck 11.

    LADDER_PLAN 4p measured the coverage over all 2,284 interior members of
    the five rows -- overlap 0, uncovered 0, wrong successor 0 -- and measured
    both class arms deriving at threshold 0..1 and stride 1.  So the arms are
    one per CLASS and arm index, plus one fill arm per WIDTH index; the fill
    arm's left-hand side is the top of the width, 1^k, which is the largest
    MEMBER and here also the largest VALUE (fibsum k), unlike either of the
    other two codes."""
    fam = cert['family']
    fills = cert.get('fill_by_phase') or [cert['fill']]
    if fam.get('numeration') != 'fibonacci':
        raise NoClosure('numeration %r is not fibonacci'
                        % fam.get('numeration'))
    w = fam.get('weights')
    if not w or list(w[:6]) != [1, 1, 2, 3, 5, 8]:
        raise NoClosure('weights %r are not the fibonacci weights' % (w,))
    if fam['base'] != 2:
        raise NoClosure('base %d: LadderCheck states (Fib, 1) at base 2'
                        % fam['base'])
    if fam.get('value_step_per_anchor_visit', 1) != 1:
        raise NoClosure('step %d: LadderCheck states (Fib, 1)'
                        % fam.get('value_step_per_anchor_visit', 1))
    cf = fam.get('canonical_form') or {}
    if [list(b) for b in (cf.get('blocks') or [])] != [[0], [1, 1]]:
        raise NoClosure('canonical blocks %r are not [[0],[1,1]]'
                        % (cf.get('blocks'),))
    if len(fills) != 1:
        raise NoClosure('%d phases: the fibonacci board is one-phase (4p '
                        'measured all five rows at one)' % len(fills))
    f = fills[0]
    if f['lands_in_phase'] != 0:
        raise NoClosure('the fill lands in phase %d of 1'
                        % f['lands_in_phase'])
    # [filled_fib0] discharges "the fill target is a member" for exactly this
    # shape: the all-zero string of any width is a member.  Anything else
    # would need the target's own membership proved per width.
    if (list(f['target_prefix']) or list(f['target_suffix'])
            or f['target_fill_digit'] != 0):
        raise NoClosure('the fill target is %r ++ %d^n ++ %r; [filled_fib0] '
                        'discharges membership for a bare run of 0 only'
                        % (f['target_prefix'], f['target_fill_digit'],
                           f['target_suffix']))
    tails = [tuple(t) for t in
             (fam.get('terminators_by_phase') or [fam['terminator']])]
    if cert['boot'].get('phase', 0) != 0:
        raise NoClosure('the boot is read in phase %d of 1'
                        % cert['boot'].get('phase', 0))
    # The liveness picks the closer.  All five fibonacci rows read BCD (4p):
    # A is entered once, at step 0, and nothing targets it, so the row
    # QUASIHALTS in A and [boardF_neverqh] would prove the wrong theorem.
    live = (cert.get('liveness') or {}).get('states_infinitely_often') or ''
    missing = [i for i in range(4) if ST[i][-1] not in live]
    if len(missing) > 1:
        raise NoClosure('liveness %r leaves %d states finite; the board names '
                        'ONE quiet state' % (live, len(missing)))

    digs = [tuple(w) for w in fam['digits']]
    pre = tuple(fam['near_head_prefix'])
    q = ord(fam['state']) - 65
    hs = fam['head']
    left = fam['side'] == 'L'
    el, er = (not left), left

    boot = cert['boot']
    ds0 = list(boot['digits_lsb_first'])
    if not ds0:
        raise NoClosure('the boot digit string is empty and a width is not')
    if not fib_member(ds0):
        raise NoClosure('the boot digit string %r is not a MEMBER: some 0 has '
                        'an odd number of 1s above it, so the counter does '
                        'not stand on it' % ds0)
    cells = list(pre)
    for d in ds0:
        cells.extend(digs[d])
    cells.extend(tails[0])
    if cells != list(boot['cells']):
        raise NoClosure('boot cells %r are not the family at %r'
                        % (boot['cells'], ds0))

    fpre, fsuf = list(f['target_prefix']), list(f['target_suffix'])
    mid = f['target_fill_digit']
    mf = len(fpre) + len(fsuf)

    def cellsof(ds):
        out = []
        for d in ds:
            out.extend(digs[d])
        return tuple(out)

    def conf(other, sd):
        OT = (other, (), 0, 0, ())
        return (q, sd, hs, OT) if left else (q, OT, hs, sd)

    def derive(e0, e1, c0, c1, what):
        ch = LC.derive_chain(tab, e0, e1, c0, c1, maxdepth=32, nmax=120,
                             lift=True)
        if ch is None:
            raise NoClosure('%s: no chain' % what)
        got = LC.srun(tab, e0, e1, ch, c0)
        if got is None or got[0] != c1:
            raise NoClosure('%s: chain lands off the rhs' % what)
        if got[2] == 0:
            raise NoClosure('%s: zero-step rule' % what)
        return ch, got[1], got[2]

    def interior_at(other, n0, stride):
        got = []
        for i in range(2):
            u, t, w, u2, t2, w2 = f1c(i)
            for r in range(n0 + stride):
                s = 0 if r < n0 else stride
                c0 = conf(other, blk(pre + cellsof(u) + digs[t] * r,
                                     digs[t], s, cellsof(w)))
                c1 = conf(other, blk(pre + cellsof(u2) + digs[t2] * r,
                                     digs[t2], s, cellsof(w2)))
                if c0 == c1:
                    return None
                try:
                    ch, ca, cb = derive(el, er, c0, c1,
                                        'interior class %d r=%d' % (i, r))
                except NoClosure:
                    return None
                got.append((i, r, s, c0, c1, ch, ca, cb))
        return got

    def fill_at(other, n0, stride):
        got = []
        for r in range(1, n0 + stride):
            s = 0 if r < n0 else stride
            total = r + f['widens_by'] - mf
            if total < 0:
                return None
            hit = None
            for w1 in _splits(r):
                # the top of width r is 1^r: a bare run, no fixed word at
                # either end, which is what [cells_topF] states
                lhs = conf(other, blk(pre + digs[1] * w1, digs[1], s,
                                      digs[1] * (r - w1) + tails[0]))
                for m1 in _splits(total):
                    rhs = conf(other,
                               blk(pre + cellsof(fpre) + digs[mid] * m1,
                                   digs[mid], s,
                                   digs[mid] * (total - m1) + cellsof(fsuf)
                                   + tails[0]))
                    if lhs == rhs:
                        continue
                    try:
                        ch, ca, cb = derive(True, True, lhs, rhs,
                                            'fill r=%d' % r)
                    except NoClosure:
                        continue
                    hit = (r, s, w1, r - w1, m1, total - m1, lhs, rhs,
                           ch, ca, cb)
                    break
                if hit:
                    break
            if hit is None:
                return None
            got.append(hit)
        return got

    best = None
    for other in _gray_far_sides(cert, tab):
        inter = n0i = sti = None
        for n0, stride in ARM_GRID:
            hit = interior_at(other, n0, stride)
            if hit is not None:
                inter, n0i, sti = hit, n0, stride
                break
        fill = n0f = stf = None
        for n0, stride in ARM_GRID:
            if n0 < 1:
                continue      # the fill arm index range starts at 1
            hit = fill_at(other, n0, stride)
            if hit is not None:
                fill, n0f, stf = hit, n0, stride
                break
        score = (inter is not None) + (fill is not None)
        if best is None or score > best[0]:
            best = (score, other, inter, n0i, sti, fill, n0f, stf)
        if score == 2:
            break
    _sc, other, inter, n0i, sti, fill, n0f, stf = best
    if inter is None:
        raise NoClosure('interior class arm: no chain at any threshold 0..3 '
                        'and stride 1..4')
    if fill is None:
        raise NoClosure('fill arm: no chain at any threshold 1..3, stride '
                        '1..4 or copy split')

    qa, sq = None, None
    if missing:
        qa = missing[0]
        sq = last_visit(tab, qa, boot['steps_from_blank'])
        if sq is None:
            raise NoClosure('%s never enters %s below the boot anchor, so it '
                            'is not the quiet state' % (cert['spec'], ST[qa]))
    want = [i for i in range(4) if i != qa]
    vis = {}
    for (r, _s, _w1, _w2, _m1, _m2, lhs, _rhs, fch, _ca, _cb) in fill:
        seen = _gray_visits(tab, lhs, fch, want)
        gap = [ST[i] for i in want if i not in seen]
        if gap:
            raise NoClosure('the fill anchor at width index %d reaches no %s'
                            % (r, ','.join(gap)))
        vis[r] = {i: seen[i] for i in want}

    return dict(fib=True, el=el, er=er, other=list(other),
                inter=inter, n0i=n0i, sti=sti,
                fill=fill, n0f=n0f, stf=stf, nph=1,
                ds0=ds0, t0=boot['steps_from_blank'], vis=vis, want=want,
                qa=qa, sq=sq, pv=0, ph0=0, kcyc=[0], b=2)


CLOSURE_F_HEAD = '''
(** ** The closure: from the RULES to [NeverQuasiHaltsSt], at [(Fib, 1)]

    The arms below are the case split of [LadderCheck.fib_split], built from
    the FAMILY rather than mined: one interior arm per CLASS (there are two,
    LADDER_PLAN 4p) and per arm index, and one fill arm per WIDTH index.
    Every certificate arm above is one of these with its run lengths pinned to
    their lower bounds, which is why %(nc)d of them collapse to %(na)d here.

    The numeration is FIBONACCI: the digit at index [i] carries weight
    1, 1, 2, 3, 5, 8, ... and this width spells [fibsum k + 1] members, not
    [2^k].  It is REDUNDANT -- the first two weights are both 1 -- so which
    string of a width the counter stands on is a MEMBERSHIP predicate and not
    an arithmetic fact, and that predicate is what [fibokb] is.  The two
    classes split on the LOW DIGIT and the top of a width is [1^k].

    The interior class runs at threshold %(n0i)d stride %(sti)d, the fill
    class at threshold %(n0f)d stride %(stf)d.  [boardF_neverqh] consumes
    them, the boot, and one chain per state per fill arm. *)
'''

CLOSURE_F_DISP = '''Definition iarm_%(mid)s (i r : nat) : LRule :=
  match i, r with
  %(ibr)s
  | _, _ => iarm0_0_%(mid)s   (* unreachable: i < 2 and r < N0i + sti *)
  end.

(** The fill arms, indexed by the WIDTH.  Both tails are known empty -- they
    are the only arms that see the end of the counter -- and the left-hand
    side is the top of the width, which here is a BARE run of [1]s.  That is
    both the largest MEMBER and the largest value ([fibsum k]), so unlike
    either other code it needs no fixed word at either end.  [fw1]/[fw2] say
    how the top's concrete copies of the run divide about the block and
    [fm1]/[fm2] the fill target's. *)
Definition farm_%(mid)s (r : nat) : LRule :=
  match r with
  %(fbr)s
  | _ => farm%(r0)d_%(mid)s   (* unreachable: 1 <= r < N0f + stf *)
  end.

Definition fw1_%(mid)s (r : nat) : nat := match r with %(b1)s | _ => 0 end.
Definition fw2_%(mid)s (r : nat) : nat := match r with %(b2)s | _ => 0 end.
Definition fm1_%(mid)s (r : nat) : nat := match r with %(b3)s | _ => 0 end.
Definition fm2_%(mid)s (r : nat) : nat := match r with %(b4)s | _ => 0 end.

(** One chain per state per fill arm.  [vis_of_run] turns each into a visit
    and [topsF_cofinal] says the tops keep coming, which is all the liveness
    needs. *)
Definition vis_%(mid)s (r : nat) (q : St) : list lstep :=
  match r, q with
  %(vb)s
  | _, _ => []
  end.

'''

CLOSURE_F_THM = '''Lemma iarm_sound_%(mid)s : forall i r,
  i < 2 -> r < %(n0i)d + %(sti)d ->
  RuleSound tm (negb (fm_left FAM)) (fm_left FAM) (iarm_%(mid)s i r).
Proof.
  intros i r Hi Hr.
%(isound)s  exfalso; lia.
Qed.

Lemma iarm_lhs_%(mid)s : forall i r, i < 2 -> r < %(n0i)d + %(sti)d ->
  lr_lhs (iarm_%(mid)s i r)
    = cls_conf FAM (cls_side FAM (cs_u (f1c i)) (cs_t (f1c i)) r
                      (astride %(n0i)d %(sti)d r) (cs_w (f1c i))).
Proof.
  intros i r Hi Hr.
%(icomp)s  exfalso; lia.
Qed.

Lemma iarm_rhs_%(mid)s : forall i r, i < 2 -> r < %(n0i)d + %(sti)d ->
  lr_rhs (iarm_%(mid)s i r)
    = cls_conf FAM (cls_side FAM (cs_u' (f1c i)) (cs_t' (f1c i)) r
                      (astride %(n0i)d %(sti)d r) (cs_w' (f1c i))).
Proof.
  intros i r Hi Hr.
%(icomp)s  exfalso; lia.
Qed.

Lemma iarm_cb_%(mid)s : forall i r, i < 2 -> r < %(n0i)d + %(sti)d ->
  0 < lr_cb (iarm_%(mid)s i r).
Proof.
  intros i r Hi Hr.
%(ilia)s  exfalso; lia.
Qed.

Lemma farm_sound_%(mid)s : forall r, 1 <= r -> r < %(n0f)d + %(stf)d ->
  RuleSound tm true true (farm_%(mid)s r).
Proof.
  intros r H1 Hr.
%(fsound)s  exfalso; lia.
Qed.

Lemma farm_lhs_%(mid)s : forall r, 1 <= r -> r < %(n0f)d + %(stf)d ->
  lr_lhs (farm_%(mid)s r)
    = cls_conf FAM (run_side FAM 1 (fw1_%(mid)s r)
                      (astride %(n0f)d %(stf)d r) (fw2_%(mid)s r) 0 [] []).
Proof.
  intros r H1 Hr.
%(fcomp)s  exfalso; lia.
Qed.

Lemma farm_rhs_%(mid)s : forall r, 1 <= r -> r < %(n0f)d + %(stf)d ->
  lr_rhs (farm_%(mid)s r)
    = cls_conf FAM (run_side FAM (f_mid (fam_fill FAM 0)) (fm1_%(mid)s r)
                      (astride %(n0f)d %(stf)d r) (fm2_%(mid)s r) 0
                      (f_pre (fam_fill FAM 0)) (f_suf (fam_fill FAM 0))).
Proof.
  intros r H1 Hr.
%(fcomp)s  exfalso; lia.
Qed.

Lemma farm_cb_%(mid)s : forall r, 1 <= r -> r < %(n0f)d + %(stf)d ->
  0 < lr_cb (farm_%(mid)s r).
Proof.
  intros r H1 Hr.
%(flia)s  exfalso; lia.
Qed.

Lemma fw_%(mid)s : forall r, 1 <= r -> r < %(n0f)d + %(stf)d ->
  fw1_%(mid)s r + fw2_%(mid)s r = r.
Proof.
  intros r H1 Hr.
%(flia)s  exfalso; lia.
Qed.

Lemma fm12_%(mid)s : forall r, 1 <= r -> r < %(n0f)d + %(stf)d ->
  fm1_%(mid)s r + fm2_%(mid)s r
  + (length (f_pre (fam_fill FAM 0)) + length (f_suf (fam_fill FAM 0)))
  = r + f_s (fam_fill FAM 0).
Proof.
  intros r H1 Hr.
%(flia)s  exfalso; lia.
Qed.

Lemma boot_%(mid)s :
  csteps tm %(t0)d c0 = Some (fam_cfg FAM (%(ds0)s, 0, 0)).
Proof. vm_compute. reflexivity. Qed.

'''


CLOSURE_F_NQH = '''Lemma vis_ok_%(mid)s : forall r q, 1 <= r ->
  r < %(n0f)d + %(stf)d ->
  srun_st tm true true (vis_%(mid)s r q) (lr_lhs (farm_%(mid)s r)) = Some q.
Proof.
  intros r q H1 Hr.
%(fvis)s  exfalso; lia.
Qed.

(** The machine-level theorem.  Every argument is either a [RuleSound] the
    Stage-B kernel discharged, or an equation two [vm_compute]s decide -- and
    the boot's MEMBERSHIP, which is one more of the second kind. *)
Theorem nqh_%(mid)s : NeverQuasiHaltsSt tm.
Proof.
  apply (boardF_neverqh tm FAM iarm_%(mid)s %(n0i)d %(sti)d
                        farm_%(mid)s %(n0f)d %(stf)d
                        fw1_%(mid)s fw2_%(mid)s fm1_%(mid)s fm2_%(mid)s
                        vis_%(mid)s %(ds0)s %(t0)d).
%(args)s  - exact vis_ok_%(mid)s.
Qed.
'''


CLOSURE_F_QH = '''Lemma vis_ok_%(mid)s : forall r q, q <> %(qa)s -> 1 <= r ->
  r < %(n0f)d + %(stf)d ->
  srun_st tm true true (vis_%(mid)s r q) (lr_lhs (farm_%(mid)s r)) = Some q.
Proof.
  intros r q Hq H1 Hr.
%(fvis)s  exfalso; lia.
Qed.

(** *** The arms avoid the quiet state

    Recomputed from the SAME chains the kernel already replays
    ([LadderCheck.arm_avoid] over [LapAvoid.srun_avoid]): a chain whose trace
    touches [%(qa)s] evaluates to [false] and this file fails to compile. *)
%(avarms)s
Lemma iarm_avoid_%(mid)s : forall i r,
  i < 2 -> r < %(n0i)d + %(sti)d ->
  RuleAvoid tm (negb (fm_left FAM)) (fm_left FAM) %(qa)s (iarm_%(mid)s i r).
Proof.
  intros i r Hi Hr.
%(bav)s  exfalso; lia.
Qed.

Lemma farm_avoid_%(mid)s : forall r, 1 <= r -> r < %(n0f)d + %(stf)d ->
  RuleAvoid tm true true %(qa)s (farm_%(mid)s r).
Proof.
  intros r H1 Hr.
%(fav)s  exfalso; lia.
Qed.

(** *** The quiet state's last visit, and the window from it to the anchor *)
Lemma qvis_%(mid)s : VisitsAt tm %(qa)s %(sq)d.
Proof. apply bootvis_chk_sound. vm_compute. reflexivity. Qed.

Lemma qwin_%(mid)s : forall n c, %(sq)d < n < %(t0)d ->
  stepn tm n InitES = Some c -> fst c <> %(qa)s.
Proof.
  intros n c Hn Hstep.
  exact (bootquiet_chk_sound tm %(qa)s %(sq1)d %(win)d
           ltac:(vm_compute; reflexivity) n c ltac:(lia) Hstep).
Qed.

(** The machine-level theorem.  This row QUASIHALTS in %(qa)s: the counter
    laps forever over the fibonacci numeration and every other state recurs,
    but %(qa)s stops firing after index %(sq)d -- it is entered once, at step
    0, and nothing targets it (4p).  [boardF_iqh] returns the exact bound and
    it is weakened to the census tier's 2000. *)
Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\\ QHBound 2000 tm /\\ QuasiHaltsSt tm.

Theorem iqh_%(mid)s : iqh tm.
Proof.
  assert (H : NonHalt tm /\\ QHBound (S %(sq)d) tm /\\ QuasiHaltsSt tm).
  { apply (boardF_iqh tm FAM iarm_%(mid)s %(n0i)d %(sti)d
                      farm_%(mid)s %(n0f)d %(stf)d
                      fw1_%(mid)s fw2_%(mid)s fm1_%(mid)s fm2_%(mid)s
                      %(ds0)s %(t0)d %(qa)s %(sq)d vis_%(mid)s).
%(args)s    - exact iarm_avoid_%(mid)s.
    - exact farm_avoid_%(mid)s.
    - exact vis_ok_%(mid)s.
    - exact qvis_%(mid)s.
    - exact qwin_%(mid)s. }
  destruct H as (Hn & Hb & Hq).
  split; [exact Hn | split; [| exact Hq]].
  apply (qhbound_mono (S %(sq)d) 2000); [lia | exact Hb].
Qed.
'''


def emit_closure_fib(cert, tab, mid):
    """The Coq for LadderCheck.boardF_neverqh, or a note on what stopped it."""
    try:
        cd = closure_data_fib(cert, tab)
    except NoClosure as e:
        return CLOSURE_NONE % e, None

    n0i, sti, n0f, stf = cd['n0i'], cd['sti'], cd['n0f'], cd['stf']
    nA, nF = n0i + sti, n0f + stf
    el, er = cd['el'], cd['er']
    L = [CLOSURE_F_HEAD % dict(nc=len(cert['arms']),
                               na=len(cd['inter']) + len(cd['fill']),
                               n0i=n0i, sti=sti, n0f=n0f, stf=stf)]
    for i, r, _s, c0, c1, ch, ca, cb in cd['inter']:
        L.append(CLOSURE_G_IARM % dict(
            i=i, r=r, mid=mid, lhs=coq_conf(c0), rhs=coq_conf(c1), ca=ca,
            cb=cb, ch=coq_chain(ch), el=str(el).lower(), er=str(er).lower()))
    for r, _s, _w1, _w2, _m1, _m2, lhs, rhs, ch, ca, cb in cd['fill']:
        L.append(CLOSURE_G_FARM % dict(
            r=r, mid=mid, lhs=coq_conf(lhs), rhs=coq_conf(rhs), ca=ca, cb=cb,
            ch=coq_chain(ch)))
    L.append(CLOSURE_F_DISP % dict(
        mid=mid, r0=cd['fill'][0][0],
        ibr='\n  '.join('| %d, %d => iarm%d_%d_%s' % (i, r, i, r, mid)
                        for i, r, *_ in cd['inter']),
        fbr='\n  '.join('| %d => farm%d_%s' % (r, r, mid)
                        for r, *_ in cd['fill']),
        b1=' '.join('| %d => %d' % (r, w1) for r, _s, w1, *_ in cd['fill']),
        b2=' '.join('| %d => %d' % (r, w2)
                    for r, _s, _w1, w2, *_ in cd['fill']),
        b3=' '.join('| %d => %d' % (r, m1)
                    for r, _s, _w1, _w2, m1, *_ in cd['fill']),
        b4=' '.join('| %d => %d' % (r, m2)
                    for r, _s, _w1, _w2, _m1, m2, *_ in cd['fill']),
        vb='\n  '.join('| %d, %s => %s' % (r, ST[i], coq_chain_l(ch))
                       for r in sorted(cd['vis'])
                       for i, ch in sorted(cd['vis'][r].items()))))

    def ibranches(body):
        """One brace-delimited branch per (class index, arm index)."""
        out = []
        for i in range(2):
            rb = []
            for r in range(nA):
                rb.append('    destruct r as [|r].\n    { %s. }\n'
                          % (body % dict(i=i, r=r, mid=mid)))
            out.append('  destruct i as [|i].\n  {\n%s    exfalso; lia.\n  }\n'
                       % ''.join(rb))
        return ''.join(out)

    def fbranches(body):
        """One per fill arm index; 0 is dead, no width is 0."""
        return _rbranches(nF, lambda r: (body % dict(r=r, mid=mid)) + '.',
                          lo=1)

    args = ''.join([
        '  - vm_compute; reflexivity.\n',                 # fm_b = 2
        '  - vm_compute; reflexivity.\n',                 # fm_code = Fib
        '  - vm_compute; reflexivity.\n',                 # fm_step = 1
        '  - vm_compute; repeat constructor.\n',          # f_pre bounded
        '  - vm_compute; repeat constructor.\n',          # f_suf bounded
        '  - vm_compute; lia.\n',                         # f_mid < 2
        '  - vm_compute; lia.\n',                         # the fill spells
        '  - vm_compute; reflexivity.\n',                 # f_to = 0
        '  - intros k Hk. apply (filled_fib0 FAM 0 k);\n'
        '      vm_compute; reflexivity.\n',               # the target is a member
        '  - repeat constructor.\n',                      # ds0 bounded
        '  - vm_compute; lia.\n',                         # 0 < |ds0|
        '  - vm_compute; reflexivity.\n',                 # ds0 is a MEMBER
        '  - exact boot_%s.\n' % mid,
        '  - lia.\n',                                     # 0 < sti
        '  - exact iarm_sound_%s.\n' % mid,
        '  - exact iarm_lhs_%s.\n' % mid,
        '  - exact iarm_rhs_%s.\n' % mid,
        '  - exact iarm_cb_%s.\n' % mid,
        '  - lia.\n',                                     # 0 < stf
        '  - lia.\n',                                     # 1 <= N0f
        '  - exact fw_%s.\n' % mid,
        '  - exact fm12_%s.\n' % mid,
        '  - exact farm_sound_%s.\n' % mid,
        '  - exact farm_lhs_%s.\n' % mid,
        '  - exact farm_rhs_%s.\n' % mid,
        '  - exact farm_cb_%s.\n' % mid,
    ])

    L.append(CLOSURE_F_THM % dict(
        mid=mid, t0=cd['t0'], ds0=clist(cd['ds0'], str),
        n0i=n0i, sti=sti, n0f=n0f, stf=stf,
        isound=ibranches('eapply arm_sound; [exact rules_sound_%(mid)s '
                         '| exact ok_iarm%(i)d_%(r)d_%(mid)s]'),
        icomp=ibranches('vm_compute; reflexivity'),
        ilia=ibranches('vm_compute; lia'),
        fsound=fbranches('eapply arm_sound; [exact rules_sound_%(mid)s '
                         '| exact ok_farm%(r)d_%(mid)s]'),
        fcomp=fbranches('vm_compute; reflexivity'),
        flia=fbranches('vm_compute; lia')))

    common = dict(mid=mid, t0=cd['t0'], ds0=clist(cd['ds0'], str),
                  n0i=n0i, sti=sti, n0f=n0f, stf=stf, args=args)
    if cd['qa'] is None:
        L.append(CLOSURE_F_NQH % dict(
            common, fvis=fbranches('destruct q; vm_compute; reflexivity')))
    else:
        qa, sq = ST[cd['qa']], cd['sq']
        av = []
        for i, r, _s, *_ in cd['inter']:
            av.append(AVOID_ARM % dict(
                nm='iarm%d_%d' % (i, r), mid=mid, qa=qa,
                el='(negb (fm_left FAM))', er='(fm_left FAM)'))
        for r, *_ in cd['fill']:
            av.append(AVOID_ARM % dict(nm='farm%d' % r, mid=mid,
                                       qa=qa, el='true', er='true'))
        L.append(CLOSURE_F_QH % dict(
            common, qa=qa, sq=sq, sq1=sq + 1, win=cd['t0'] - sq - 1,
            avarms=''.join(av),
            bav=ibranches('exact av_iarm%(i)d_%(r)d_%(mid)s'),
            fav=fbranches('exact av_farm%(r)d_%(mid)s'),
            fvis=fbranches('destruct q; '
                           'try (exfalso; apply Hq; reflexivity); '
                           'vm_compute; reflexivity')))
    return ''.join(L), cd


def emit(cert, out):
    spec = cert['spec']
    mid = mach_id(spec)
    tab = parse_tm(spec)

    # The GRAY closure may need the far side the machine SPELLS at the anchor
    # rather than the one the certificate carries (LADDER_PLAN 4n): the same
    # tape under [lift], a different [cconf], and every arm is stated on
    # [cconf].  Which one it is is decided while the arms are derived, so the
    # gray closure runs FIRST and the [Fam] record below is written from what
    # it chose.  The binary path is untouched and still runs last.
    # The FIBONACCI rows say [code: binary] in the certificate and that is the
    # lie LADDER_PLAN 4p caught: their numeration is weighted and no positional
    # code denotes their successor.  What selects the third closure is
    # [numeration] and the [weights] beside it, never [code].
    gray = cert['family'].get('code') == 'gray'
    fib = cert['family'].get('numeration') == 'fibonacci'
    if fib:
        closure, cd = emit_closure_fib(cert, tab, mid)
    elif gray:
        closure, cd = emit_closure_gray(cert, tab, mid)
    else:
        closure, cd = None, None
    if (gray or fib) and cd is not None:
        cert['family']['other_side_cells'] = list(cd['other'])
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

    if not (gray or fib):
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
             'BUILT (%d interior at N0=%d st=%d + %d fill at N0=%d st=%d)'
             % (len(cd['inter']), cd['n0i'], cd['sti'],
                len(cd['fill']), cd['n0f'], cd['stf']) if cd
             else 'not built'))
    for nm, e in bad:
        print('  %-8s %s' % (nm, e))
    return 0


if __name__ == '__main__':
    sys.exit(main())
