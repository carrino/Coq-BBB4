#!/usr/bin/env python3
"""Generate a shadow's board from its core row's board.  UNTRUSTED.

A SHADOW writes the blank on its first transition, so it runs an all-blank
prefix of length `t` and thereafter IS its re-root [TM_swap StA q*] started
fresh -- and that re-root is some CORE row with non-start states relabelled
and possibly mirrored.  Boarding it is two transports composed, and BOTH are
already proved in general:

    Census/Reroot.neverqh_reroot   across the blank prefix
    Census/RerootSwap.neverqh_swap / neverqh_mirror   across the relabelling

so a shadow board carries NO new argument.  Since #105 it carries almost no
TEXT either: [Census/ShadowBoard.shadow_nqh] packages the whole thing as one
lemma over three booleans, so an emitted board is one literal table, three
numbers, an op chain, and three [vm_compute]s -- the sentence *the first t
steps write only blanks, and what is left is that machine, which is proved.*
The kernel checks every one.  A wrong op order, a wrong re-root state, a
wrong prefix length or too small a fuel makes the emitted file fail to
compile, never a false theorem.

WHY THIS EXISTS.  NEXT_SESSION (2026-07-31, John) decided to hand-write
shadow boards "until it is earning", with the revisit trigger: "when a shadow
does NOT fall in the same session as its core row".  The generator is the
answer to that trigger; `RRNQ_0RB0RD_1RC____1RD1LC_0LC1RA.v` is the
hand-written original this reproduces as a regression.

SCOPE.  Never-quasihalting core rows only (`kind = nqh` in frozen_map.tsv).
A core row boarded as `iqh` transports through [Reroot.qhbound_reroot]
instead, which shifts the bound by the prefix length and carries a
`B + t <= B_board` side condition -- refused here rather than guessed at.

Usage:
    gen_shadow.py --harvest              board every shadow whose partner has
                                         BOARDED -- the one that runs in
                                         `make closeout`; see below
    gen_shadow.py --all                  every row in shadow_rows.tsv
    gen_shadow.py --spec SPEC            one row from shadow_rows.tsv
    gen_shadow.py --spec SPEC --qs B --t 1 --partner SPEC --ops swap:B:C,swap:C:D
                                         explicit (used for the regression)
    ... [--out DIR] [--check]            --check compiles what it wrote

--harvest IS THE ONE THAT MATTERS, and --all cannot replace it.  A row sits in
`shadow_rows.tsv` only while its partner is DEFERRED; the moment the partner
boards, the row leaves that file -- which is the moment its board becomes
buildable.  So `--all`, whose input is that file, is by construction blind to
every row that is ready, and #104 had to drive two of them by hand off the
previous git revision of the table.  `--harvest` recomputes the relation
against the boarded set (shadowlib.classify) and so sees exactly those rows.
`make closeout` runs it between two inventory passes, so a shadow now falls in
the same regen as its core row with nobody typing anything.
"""
import argparse
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import shadowlib  # noqa: E402

STATES = 'ABCD'

# [ShadowBoard.all_visited_b] re-runs [csteps] from [c0] per index, so it is
# quadratic in the fuel.  Every shadow in the tree needs <= 9; anything much
# larger is a row worth looking at rather than generating.
FUEL_CAP = 64


class ShadowGenError(Exception):
    pass


class Unbuilt(Exception):
    """`coqc` could not resolve `BBB4.*` -- the tree is not built, so a
    compile result means nothing in either direction."""


def parse(spec):
    """bbchallenge spec -> 8 slots, None for an undefined transition."""
    slots = []
    for pair in spec.split('_'):
        for t in (pair[:3], pair[3:]):
            slots.append(None if t == '---' else (t[0], t[1], t[2]))
    if len(slots) != 8:
        raise ShadowGenError('%s: %d slots, want 8' % (spec, len(slots)))
    return tuple(slots)


def modname(spec):
    """Module-safe name: each `-` becomes `_`, so `1RC---_1RD` -> `1RC____1RD`.

    NOT `'---' -> '____'`: that adds an underscore, because the `_` field
    separator after the dashes is already there.  Checked against the names
    in the tree (`NLAP_1RB____1RC1LB_…`, `LDR_1RB____0LB1RC_…`).
    """
    return spec.replace('-', '_')


def coq_table(slots, mk):
    """The eight arms of a `fun q s => match q, s with ... end` body."""
    out = []
    for i in range(0, 8, 2):
        st = STATES[i // 2]
        cells = []
        for s in (0, 1):
            t = slots[i + s]
            cells.append('| St%s, S%d => %s' % (st, s, 'None' if t is None else
                         '%s S%s D%s St%s' % (mk, t[0], t[1], t[2])))
        out.append('  ' + ' '.join(cells))
    return '\n'.join(out)


def step(slots, st, tape, pos):
    """One raw step on a dict tape.  Returns (st, pos) or None if undefined."""
    t = slots[STATES.index(st) * 2 + tape.get(pos, 0)]
    if t is None:
        return None
    tape[pos] = int(t[0])
    return t[2], pos + (1 if t[1] == 'R' else -1)


def first_visits(slots, cap=4000):
    """Step index at which each state is first entered (StA is 0)."""
    seen = {'A': 0}
    st, tape, pos = 'A', {}, 0
    for n in range(1, cap + 1):
        r = step(slots, st, tape, pos)
        if r is None:
            break
        st, pos = r
        seen.setdefault(st, n)
        if len(seen) == 4:
            break
    missing = [q for q in STATES if q not in seen]
    if missing:
        raise ShadowGenError('states %s not visited within %d steps'
                             % (','.join(missing), cap))
    return seen


def blank_prefix(slots):
    """(q*, t): the first 1-writing state and the all-blank prefix length."""
    st, pos, n = 'A', 0, 0
    while n < 16:
        t = slots[STATES.index(st) * 2 + 0]
        if t is None:
            raise ShadowGenError('undefined transition inside the blank prefix')
        if t[0] == '1':
            return st, n
        st, pos, n = t[2], pos + (1 if t[1] == 'R' else -1), n + 1
    raise ShadowGenError('no 1 written in 16 steps -- not a shadow shape')


def load_map():
    p = os.path.join(ROOT, 'tools', 'closeout', 'frozen_map.tsv')
    if not os.path.exists(p):
        raise ShadowGenError('frozen_map.tsv missing -- run inventory.py first')
    out = {}
    with open(p) as f:
        next(f)
        for line in f:
            c = line.rstrip('\n').split('\t')
            if len(c) >= 5:
                out[c[0]] = {'kind': c[1], 'vfile': c[2], 'thm': c[3],
                             'const': c[4]}
    return out


def load_unproven():
    p = os.path.join(ROOT, 'tools', 'closeout', 'frozen_unproven.txt')
    if not os.path.exists(p):
        raise ShadowGenError('frozen_unproven.txt missing -- run inventory.py first')
    return [l.strip() for l in open(p) if l.strip()]


def freed_shadows():
    """Rows that STOPPED being shadows because their partner boarded.

    These are the actionable ones and the whole reason this generator exists:
    a shadow becomes buildable at exactly the moment it falls out of
    `shadow_rows.tsv`, so anything that reads only that file can never see
    one.  See shadowlib.classify.
    """
    fmap = load_map()
    _core, _shadows, freed = shadowlib.classify(
        load_unproven(), {k: v['kind'] for k, v in fmap.items()})
    return freed, fmap


def load_shadows():
    p = os.path.join(ROOT, 'tools', 'closeout', 'shadow_rows.tsv')
    rows = []
    with open(p) as f:
        head = next(f).rstrip('\n').split('\t')
        for line in f:
            c = line.rstrip('\n').split('\t')
            if len(c) == len(head):
                rows.append(dict(zip(head, c)))
    return rows


def apply_ops_coq(const, ops):
    """The core constant wrapped in its op chain, innermost last.

    shadowlib emits ops in APPLICATION order, so the Coq term nests in
    reverse: ops [a, b] means `a (b core)`.  Wrong order fails to compile.
    """
    term = const
    for op in reversed(ops):
        if op[0] == 'mirror':
            term = 'mirror_tm (%s)' % term
        else:
            term = 'TM_swap St%s St%s (%s)' % (op[1], op[2], term)
    return term


def parse_ops(s):
    ops = []
    for tok in [x for x in s.split(',') if x]:
        if tok == 'mirror':
            ops.append(('mirror',))
        elif tok.startswith('swap:'):
            _, u, v = tok.split(':')
            ops.append(('swap', u, v))
        else:
            raise ShadowGenError('unknown op %r' % tok)
    return ops


def nqh_chain(ops, core_thm):
    """Tactic script taking the core theorem through the op chain."""
    lines = []
    for op in ops:
        if op[0] == 'mirror':
            lines.append('    apply neverqh_mirror.')
        else:
            lines.append('    apply neverqh_swap; [discriminate | discriminate |].')
    lines.append('    exact %s.' % core_thm)
    return '\n'.join(lines)


def emit(spec, qs, t, partner, ops, fmap, fuel=None):
    core = fmap.get(partner)
    if core is None:
        raise ShadowGenError('core row %s has no board in frozen_map.tsv' % partner)
    if core['kind'] != 'nqh':
        raise ShadowGenError('core row %s is boarded as %s; only nqh is '
                             'supported (see the SCOPE note)'
                             % (partner, core['kind']))
    for op in ops:
        if op[0] == 'swap' and ('A' in (op[1], op[2])):
            raise ShadowGenError('op %r moves the start state' % (op,))

    name = modname(spec)
    slots = parse(spec)
    # the re-root: swap StA with q*
    rr = shadowlib.swap_uv(slots, 'A', qs)
    # [ShadowBoard.all_visited_b] searches steps 0..f-1 for each state, so the
    # fuel is the last first-visit plus one.  Tight on purpose: a fuel that is
    # too small fails at [vm_compute] instead of proving something weaker.
    fuel = fuel or max(first_visits(rr).values()) + 1
    if fuel > FUEL_CAP:
        raise ShadowGenError('re-root needs fuel %d (> %d) to visit every '
                             'state; all_visited_b is quadratic in the fuel, '
                             'so check this row by hand' % (fuel, FUEL_CAP))
    core_mod = os.path.splitext(os.path.basename(core['vfile']))[0]
    # ...and the PACKAGE it lives in.  Boards are not all under
    # [Machines/Counters]: LADDER boards are under [Machines/Ladder], and a
    # shadow whose core row is a ladder board imported the wrong module and
    # failed to compile with the path hard-coded here.  [frozen_map.tsv]
    # already carries the file, so read the package off it.
    core_pkg = (os.path.dirname(core['vfile'])
                .replace('theories', 'BBB4', 1).replace('/', '.'))
    mk = 'mk_' + name

    txt = '''(** * SH_%(name)s: machine %(spec)s, boarded by RE-ROOT off a boarded core row.

    GENERATED by [tools/closeout/gen_shadow.py] -- do not edit; regenerate.

    This row is a SHADOW of the core row [%(partner)s]: its first
    transition writes the blank, so its first %(t)d step(s) leave the tape all
    blank, and from state [St%(qs)s] onward it IS its re-root
    [TM_swap StA St%(qs)s] started fresh -- which is that core row relabelled
    (%(opstr)s).  A shadow satisfies the [skipped] disjunct only while its
    core row is still DEFERRED, so once the core row boards this row needs a
    board of its own.  It needs no new ARGUMENT, though: every step of the
    reasoning is general and proved once elsewhere, so the whole board is the
    sentence you would say out loud --

      the first %(t)d step(s) write only blanks, and what is left is
      %(partner)s, which is proved.

    [Census/ShadowBoard.shadow_nqh] is that sentence as one lemma; the three
    bullets below are its three booleans, each a [vm_compute] the kernel
    re-runs, and the fourth is the neighbouring board's own theorem carried
    across the relabelling ([RerootSwap.neverqh_swap] / [neverqh_mirror]).
    Nothing here is per-machine except the table, the numbers and the op
    chain -- and a wrong one of any of those fails to compile.

    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift] and
    [ShadowBoard.tm_eqb_spec]). *)
From Coq Require Import List.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From BBB4.Census Require Import TNF_QH Reroot RerootSwap ShadowBoard.
From %(core_pkg)s Require Import %(core_mod)s.
Import ListNotations.

Definition %(mk)s (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := %(mk)s.

(** %(spec)s *)
Definition tm_%(name)s : TM := fun q s => match q, s with
%(table)s end.
Local Notation tm := tm_%(name)s.

Theorem nqh_%(name)s : NeverQuasiHaltsSt tm.
Proof.
  apply (shadow_nqh tm (%(applied)s) St%(qs)s %(t)d %(fuel)d).
  - (* the first %(t)d step(s) leave the tape blank, in St%(qs)s *)
    vm_compute; reflexivity.
  - (* ...and from there it IS %(partner)s, relabelled *)
    vm_compute; reflexivity.
  - (* which visits every state, within %(fuel)d steps *)
    vm_compute; reflexivity.
  - (* ...and never quasihalts, which is the core row's own theorem *)
%(chain)s
Qed.

Theorem nonhalt_%(name)s : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_%(name)s. Qed.
''' % dict(name=name, spec=spec, partner=partner, t=t, qs=qs, fuel=fuel,
           opstr=', '.join(':'.join(o) for o in ops) or 'no ops',
           core_pkg=core_pkg, core_mod=core_mod, mk=mk,
           table=coq_table(slots, 'mk'),
           applied=apply_ops_coq(core['const'], ops),
           chain=nqh_chain(ops, core['thm']))
    return 'SH_%s.v' % name, txt


"""The regression fixture: the one shadow that has already boarded.

`RRNQ_0RB0RD_1RC____1RD1LC_0LC1RA.v` was written by hand before this
generator existed, so reproducing it is a real differential test -- and the
three corruptions below are the corruption-test tradition of
`theories/Tests/*_Corruption.v` applied to the generator: if a wrong op
order, a wrong prefix length or a wrong re-root state still compiled, the
kernel would not be checking what this file claims it checks.
"""
FIXTURE_VO = 'theories/Machines/Counters/' \
             'RRNQ_0RB0RD_1RC____1RD1LC_0LC1RA.vo'
FIXTURE = dict(spec='0RB0RD_1RC---_1RD1LC_0LC1RA', qs='B', t=1,
               partner='1RB---_1RC1LB_0LB1RD_0RA0RC',
               ops='swap:B:C,swap:C:D')
CORRUPTIONS = [
    ('op order reversed', dict(ops='swap:C:D,swap:B:C')),
    ('prefix length off by one', dict(t=2)),
    ('wrong re-root state', dict(qs='C')),
    # #105's packaged form introduces one new way to be wrong: the fuel for
    # [ShadowBoard.all_visited_b].  Too small must FAIL, not silently prove
    # something weaker -- so it is a control like the other three.
    ('fuel too short', dict(_fuel=1)),
]


def _build_and_compile(cfg, fmap, outdir):
    fn, txt = emit(cfg['spec'], cfg['qs'], cfg['t'], cfg['partner'],
                   parse_ops(cfg['ops']), fmap, fuel=cfg.get('_fuel'))
    p = os.path.join(outdir, fn)
    with open(p, 'w') as f:
        f.write(txt)
    try:
        r = subprocess.run(['coqc', '-R', 'theories', 'BBB4',
                            os.path.relpath(p, ROOT)],
                           cwd=ROOT, capture_output=True, text=True)
        if r.returncode == 0:
            return True
        # An UNBUILT library is not a rejected board.  Without this the three
        # corruptions below all report `rejected` on a tree where nothing has
        # been compiled -- vacuously, because every file fails the same way --
        # and the regression's corruption half says nothing at all.
        if 'Cannot find a physical path bound to logical path' in \
                (r.stderr or '') + (r.stdout or ''):
            raise Unbuilt(os.path.relpath(p, ROOT))
        return False
    finally:
        # p ends in '.v'; drop the source and every build product it made, so
        # the regression leaves the tree exactly as it found it.
        for q in (p, p + 'o', p + 'ok', p + 'os', p[:-2] + '.glob'):
            if os.path.exists(q):
                os.remove(q)


def regress():
    """Reproduce the hand-written board, then break it three ways."""
    fmap = load_map()
    outdir = os.path.join(ROOT, 'theories', 'Machines', 'Counters')
    ok = True

    try:
        good = _build_and_compile(FIXTURE, fmap, outdir)
        print('%-28s %s' % ('reproduces RRNQ',
                            'COMPILES' if good else 'FAILS  <-- regression'))
        ok &= good

        for label, patch in CORRUPTIONS:
            cfg = dict(FIXTURE)
            cfg.update(patch)
            bad = _build_and_compile(cfg, fmap, outdir)
            print('%-28s %s' % (label, 'compiles <-- NOT REJECTED' if bad
                                else 'rejected'))
            ok &= not bad
    except Unbuilt as e:
        print('GEN_SHADOW REGRESSION: INCONCLUSIVE -- the library is not '
              'built, so %s cannot be compiled either way.\n'
              '  Build the fixture first:\n'
              '    make -f Makefile.coq -j3 %s' % (e, FIXTURE_VO))
        return 2

    print('GEN_SHADOW REGRESSION: %s' % ('OK' if ok else 'FAILED'))
    return 0 if ok else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--all', action='store_true')
    ap.add_argument('--harvest', action='store_true',
                    help='board every shadow whose partner has BOARDED -- the '
                         'rows shadow_rows.tsv can no longer see')
    ap.add_argument('--spec')
    ap.add_argument('--qs')
    ap.add_argument('--t', type=int)
    ap.add_argument('--partner')
    ap.add_argument('--ops', default='')
    ap.add_argument('--out', default='theories/Machines/Counters')
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--regress', action='store_true',
                    help='reproduce the hand-written RRNQ board and its three '
                         'corruption controls, then delete what it wrote')
    a = ap.parse_args()

    if a.regress:
        return regress()

    if a.harvest:
        freed, fmap = freed_shadows()
        if not freed:
            print('gen_shadow --harvest: nothing freed '
                  '(no shadow has a boarded partner)')
            return 0
        jobs = [(f['spec'], f['qs'], f['t'], f['partner'], f['ops'])
                for f in freed]
        print('gen_shadow --harvest: %d shadow(s) freed by a boarded partner'
              % len(jobs))
    else:
        fmap = load_map()
        jobs = []
        if a.spec and a.partner:
            qs, t = a.qs, a.t
            if qs is None or t is None:
                qs, t = blank_prefix(parse(a.spec))
            jobs.append((a.spec, qs, t, a.partner, parse_ops(a.ops)))
        else:
            for r in load_shadows():
                if a.spec and r['machine'] != a.spec:
                    continue
                jobs.append((r['machine'], r['qstar'], int(r['prefix']),
                             r['partner'], parse_ops(r['ops'])))
            if not jobs:
                raise SystemExit('gen_shadow: nothing to do (no matching shadow)')

    outdir = os.path.join(ROOT, a.out)
    wrote, skipped = [], []
    for spec, qs, t, partner, ops in jobs:
        try:
            fn, txt = emit(spec, qs, t, partner, ops, fmap)
        except ShadowGenError as e:
            skipped.append((spec, str(e)))
            continue
        p = os.path.join(outdir, fn)
        with open(p, 'w') as f:
            f.write(txt)
        wrote.append(p)

    for p in wrote:
        print('WROTE  %s' % os.path.relpath(p, ROOT))
    for spec, why in skipped:
        print('SKIP   %s: %s' % (spec, why))

    rc = 0
    if a.check:
        for p in wrote:
            r = subprocess.run(['coqc', '-R', 'theories', 'BBB4',
                                os.path.relpath(p, ROOT)],
                               cwd=ROOT, capture_output=True, text=True)
            if r.returncode == 0:
                print('COMPILES  %s' % os.path.relpath(p, ROOT))
            else:
                rc = 1
                print('FAILS     %s' % os.path.relpath(p, ROOT))
                print(r.stdout[-2000:], r.stderr[-2000:])
    return rc


if __name__ == '__main__':
    sys.exit(main())
