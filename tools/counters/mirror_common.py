#!/usr/bin/env python3
"""Mirror-route support shared by emit_shape1.py / emit_shape4.py.

A growth=R counter is proved by running the WHOLE template on the MIRRORED
table (where the counter grows left, matching the templates) and transferring
the conclusion back through Mirror.mirror_never_qh -- the route the wave-9
ILCM_ boards used, no new theory.  The emitters derive/validate/emit against
the mirrored spec; [mirrorize] then rewrites the generated source so that

  - tm_<id>  is the REAL machine and tmm_<id> its mirror (the proof body's
    [tm] notation points at tmm);
  - mirror_ok_<id> : mirror_tm tm_<id> = tmm_<id> (functional_extensionality);
  - the glue theorem becomes nqhm_<id> on the mirror, and nqh_<id> /
    nonhalt_<id> for the REAL machine close via mirror_never_qh.

UNTRUSTED like everything under tools/: the kernel re-checks every board.
"""
import re

from emit_interleave import mach_id, coq_table


def mirror_spec(spec):
    """mirror_tm at the level of the SPEC string: flip every move."""
    out = []
    for part in spec.split('_'):
        t = ''
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            t += e if e == '---' else e[0] + ('L' if e[1] == 'R' else 'R') + e[2]
        out.append(t)
    return '_'.join(out)


def mirrorize(src, rspec, mspec):
    """Rewrite a direct-template source (generated against [mspec]) into the
    mirror-transfer form for the real machine [rspec]."""
    rid, mid = mach_id(rspec), mach_id(mspec)
    src = src.replace(mspec, rspec)
    src = src.replace(mid, rid)

    old_tm = ('Definition tm_%s : TM := fun q s => match q, s with\n'
              '%s end.\nLocal Notation tm := tm_%s.'
              % (rid, coq_table(mspec), rid))
    new_tm = ('(** %s -- the real machine (its counter grows RIGHT). *)\n'
              'Definition tm_%s : TM := fun q s => match q, s with\n'
              '%s end.\n\n'
              '(** Its mirror %s: the same counter grown leftward.  Every\n'
              '    lemma below runs on the MIRRORED table;\n'
              '    [Mirror.mirror_never_qh] transfers the conclusion back. *)\n'
              'Definition tmm_%s : TM := fun q s => match q, s with\n'
              '%s end.\nLocal Notation tm := tmm_%s.\n\n'
              'Lemma mirror_ok_%s : mirror_tm tm_%s = tmm_%s.\n'
              'Proof.\n'
              '  apply functional_extensionality; intro q;\n'
              '    apply functional_extensionality; intro b; '
              'destruct q, b; reflexivity.\nQed.'
              % (rspec, rid, coq_table(rspec), mspec, rid, coq_table(mspec),
                 rid, rid, rid, rid))
    if old_tm not in src:
        raise RuntimeError('mirrorize: tm definition block not found')
    src = src.replace(old_tm, new_tm)

    pat = re.compile(
        r'Theorem nqh_%s : NeverQuasiHaltsSt tm\.\n'
        r'Proof\. apply \(glue_neverqh tm Cc (\d+)\)\.(.*?)Qed\.\n\n'
        r'Theorem nonhalt_%s : NonHalt tm\.\n'
        r'Proof\. apply never_qh_nonhalt, nqh_%s\. Qed\.'
        % (re.escape(rid), re.escape(rid), re.escape(rid)), re.DOTALL)
    m = pat.search(src)
    if m is None:
        return _mirrorize_qh(src, rid)
    new_close = (
        'Theorem nqhm_%s : NeverQuasiHaltsSt tm.\n'
        'Proof. apply (glue_neverqh tm Cc %s).%sQed.\n\n'
        'Theorem nqh_%s : NeverQuasiHaltsSt tm_%s.\n'
        'Proof. apply (mirror_never_qh tm_%s). rewrite mirror_ok_%s. '
        'exact nqhm_%s. Qed.\n\n'
        'Theorem nonhalt_%s : NonHalt tm_%s.\n'
        'Proof. apply never_qh_nonhalt, nqh_%s. Qed.'
        % (rid, m.group(1), m.group(2), rid, rid, rid, rid, rid,
           rid, rid, rid))
    src = pat.sub(lambda _: new_close, src, count=1)

    src = src.replace(
        'From BBB4 Require Import BBB4_Statement CTape.\n',
        'From BBB4 Require Import BBB4_Statement CTape Mirror.\n'
        'From Coq Require Import FunctionalExtensionality.\n')
    return src


# ---------------------------------------------------------------------------
# The QUASI-HALTING close.
#
# WAVE13_FINDINGS.md section 6 records the 47 machines whose StA is targeted
# by nothing, so [LapGlueQH.glue_qh] bounds its quiet time outright -- and
# records that they were "blocked in practice on ... mirrorize not knowing the
# QH closing shape".  This is that shape.  It needs NO new Coq: [mirror_nonhalt]
# and [mirror_qh] are in Mirror.v and [qhbound_mirror] is already in
# Census/TNF_QH.v, which every board imports anyway.
# ---------------------------------------------------------------------------

_QH_PAT = re.compile(
    r'Theorem iqh_(?P<id>\S+) : iqh tm\.\n'
    r'Proof\.\n(?P<body>.*?)Qed\.\n\n'
    r'Theorem nonhalt_(?P=id) : NonHalt tm\.\n'
    r'Proof\. apply \(proj1 iqh_(?P=id)\)\. Qed\.', re.DOTALL)


def _mirrorize_qh(src, rid):
    m = _QH_PAT.search(src)
    if not m or m.group('id') != rid:
        raise RuntimeError('mirrorize: closing theorems not found')
    new_close = (
        'Theorem iqhm_%s : iqh tmm_%s.\n'
        'Proof.\n%sQed.\n\n'
        '(** Transfer to the REAL machine.  [mirror_nonhalt] and [mirror_qh]\n'
        '    are Mirror.v; [qhbound_mirror] is Census/TNF_QH.v. *)\n'
        'Theorem iqh_%s : iqh tm_%s.\n'
        'Proof.\n'
        '  destruct iqhm_%s as (Hn & Hb & Hq).\n'
        '  rewrite <- mirror_ok_%s in Hn, Hb, Hq.\n'
        '  split; [exact (mirror_nonhalt _ Hn)\n'
        '         | split; [exact (qhbound_mirror _ _ Hb)\n'
        '                  | exact (mirror_qh _ Hq)]].\n'
        'Qed.\n\n'
        'Theorem nonhalt_%s : NonHalt tm_%s.\n'
        'Proof. apply (proj1 iqh_%s). Qed.'
        % (rid, rid, m.group('body'), rid, rid, rid, rid, rid, rid, rid))
    src = _QH_PAT.sub(lambda _: new_close, src, count=1)
    src = src.replace(
        'From BBB4 Require Import BBB4_Statement CTape.\n',
        'From BBB4 Require Import BBB4_Statement CTape Mirror.\n'
        'From Coq Require Import FunctionalExtensionality.\n')
    return src
