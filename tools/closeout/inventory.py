#!/usr/bin/env python3
"""Inventory for the route-A closeout: map every frozen deferred row
(tools/census_residue.txt + tools/census_holdouts_kept.txt, 5,156 specs)
to an in-tree Coq theorem, or mark it UNPROVEN.

Scans ALL of theories/Machines/**/*.v.  For each file it
  - parses every `Definition <c> : TM := fun q s => match q, s with ...`
    body into a spec string (bbchallenge order A0A1_B0B1_C0C1_D0D1,
    `---` for None) -- the BODY is ground truth, names are not trusted;
  - collects theorems of the shapes
      Theorem/Lemma <t> : NeverQuasiHaltsSt <c>.          (kind nqh)
      Theorem/Lemma <t> : iqh <c>. / pqhs <c>.            (kind iqh)
    resolving a bare `tm` through `Local Notation tm := <c>`;
  - for iqh/pqhs files, verifies the predicate is literally
      NonHalt _ /\ QHBound 2000 _ /\ QuasiHaltsSt _.

Output: tools/closeout/frozen_map.tsv  (spec kind vfile theorem const)
        tools/closeout/frozen_unproven.txt
Everything here is UNTRUSTED bookkeeping: the generated stage files
re-verify each (row, theorem) pair in the kernel (an 8-way case split
that fails to compile on any mismatch).
"""
import collections
import glob
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if not os.path.isdir(os.path.join(ROOT, 'theories')):
    ROOT = '/home/user/Coq-BBB4'

TMDEF_RE = re.compile(
    r'Definition\s+(\w+)\s*:\s*TM\s*:=\s*fun\s+q\s+s\s*=>\s*'
    r'match\s+q\s*,\s*s\s+with(.*?)end\s*\.', re.S)
ARM_RE = re.compile(
    r'\|\s*St([ABCD])\s*,\s*S([01])\s*=>\s*'
    r'(None|mk\s+S([01])\s+D([LR])\s+St([ABCD])|'
    r'Some\s*\(\s*mkTrans\s+S([01])\s+D([LR])\s+St([ABCD])\s*\))')
THM_RE = re.compile(
    r'(?:Theorem|Lemma)\s+(\w+)\s*:\s*(NeverQuasiHaltsSt|iqh|pqhs)\s+\(?(\w+)\)?\s*\.')
NOTA_RE = re.compile(r'Local\s+Notation\s+tm\s*:=\s*(\w+)')
IQH_OK_RE = re.compile(
    r'Definition\s+(?:iqh|pqhs)\s*\(\s*tm\s*:\s*TM\s*\)\s*:\s*Prop\s*:=\s*'
    r'NonHalt\s+tm\s*/\\\s*QHBound\s+2000\s+tm\s*/\\\s*QuasiHaltsSt\s+tm\s*\.')

# Explicit-bound quasihalt boards (kind iqhle:<B>): admitted only up to the
# closeout bound B_board (CloseoutKit.v) -- the previous champion's score.
THMLE_RE = re.compile(
    r'(?:Theorem|Lemma)\s+(\w+)\s*:\s*iqh_le\s+(\d+)\s+\(?(\w+)\)?\s*\.')
IQHLE_OK_RE = re.compile(
    r'Definition\s+iqh_le\s*\(\s*B\s*:\s*nat\s*\)\s*\(\s*tm\s*:\s*TM\s*\)'
    r'\s*:\s*Prop\s*:=\s*'
    r'NonHalt\s+tm\s*/\\\s*QHBound\s+B\s+tm\s*/\\\s*QuasiHaltsSt\s+tm\s*\.')
B_BOARD = 66349

# The CHAMPION's board (kind iqhch): a quasihalter at 32,779,478, which is
# above B_board and so lands in [boarded]'s THIRD disjunct
# ([CloseoutKit.covers_iqh_champ_at], gate [B <= B_champ]).  It cannot state
# its bound as a decimal literal the way the iqhle boards do -- 32,779,478 is
# left as [Nat.of_num_uint], opaque to lia and ruinous to vm_compute -- so the
# bound rides in the DEFINITION, in Horner form, and the regex checks that
# definition rather than a number in the theorem statement.
CHAMP_THM_RE = re.compile(
    r'(?:Theorem|Lemma)\s+(\w+)\s*:\s*iqh_champ\s+\(?(\w+)\)?\s*\.')
CHAMP_OK_RE = re.compile(
    r'Definition\s+iqh_champ\s*\(\s*tm\s*:\s*TM\s*\)\s*:\s*Prop\s*:=\s*'
    r'NonHalt\s+tm\s*/\\\s*QHBound\s+champ_score\s+tm\s*/\\\s*QuasiHaltsSt\s+tm\s*\.')
# and the Horner form [champ_score] must actually BE 32,779,478.  The kernel
# re-checks this in the stage (the [lia] gate), so this is hygiene, not proof.
CHAMP_SCORE_RE = re.compile(
    r'Definition\s+champ_score\s*:\s*nat\s*:=\s*([-()*+ 0-9\n]+?)(?:%nat)?\s*\.')
B_CHAMP = 32779478

SLOT = {('A', '0'): 0, ('A', '1'): 1, ('B', '0'): 2, ('B', '1'): 3,
        ('C', '0'): 4, ('C', '1'): 5, ('D', '0'): 6, ('D', '1'): 7}


def parse_tm_defs(txt):
    """{const: spec} for every fully-parsed TM definition in the file."""
    out = {}
    for m in TMDEF_RE.finditer(txt):
        const, body = m.group(1), m.group(2)
        slots = [None] * 8
        seen = 0
        for a in ARM_RE.finditer(body):
            idx = SLOT[(a.group(1), a.group(2))]
            if slots[idx] is not None:
                seen = -99  # duplicate arm: refuse
                break
            if a.group(3) == 'None':
                slots[idx] = '---'
            elif a.group(4):
                slots[idx] = a.group(4) + a.group(5) + a.group(6)
            else:
                slots[idx] = a.group(7) + a.group(8) + a.group(9)
            seen += 1
        if seen != 8 or any(s is None for s in slots):
            continue
        out[const] = '_'.join(slots[i] + slots[i + 1] for i in (0, 2, 4, 6))
    return out


def main():
    frozen = [l.strip() for l in open(os.path.join(ROOT, 'tools/census_residue.txt'))]
    frozen += [l.strip() for l in open(os.path.join(ROOT, 'tools/census_holdouts_kept.txt'))]
    frozen = [f for f in frozen if f]
    fset = set(frozen)
    assert len(frozen) == len(fset)

    # spec -> list of (kind, vfile, theorem, const); kind nqh preferred
    hits = collections.defaultdict(list)
    files = sorted(glob.glob(os.path.join(ROOT, 'theories/Machines/**/*.v'),
                             recursive=True))
    nfiles = nthm = 0
    for path in files:
        txt = open(path).read()
        if 'NeverQuasiHaltsSt' not in txt and 'iqh' not in txt and 'pqhs' not in txt:
            continue
        defs = parse_tm_defs(txt)
        if not defs:
            continue
        nota = NOTA_RE.findall(txt)
        iqh_ok = bool(IQH_OK_RE.search(txt))
        vfile = os.path.relpath(path, ROOT)
        nfiles += 1
        for thm, pred, const in THM_RE.findall(txt):
            if const == 'tm':
                if len(nota) != 1:
                    continue  # ambiguous notation: skip, mirror files state explicitly
                const = nota[0]
            spec = defs.get(const)
            if spec is None or spec not in fset:
                continue
            if pred == 'NeverQuasiHaltsSt':
                kind = 'nqh'
            elif iqh_ok:
                kind = 'iqh'
            else:
                continue  # iqh/pqhs with unexpected definition: refuse
            hits[spec].append((kind, vfile, thm, const))
            nthm += 1
        if IQHLE_OK_RE.search(txt):
            for thm, bound, const in THMLE_RE.findall(txt):
                if const == 'tm':
                    if len(nota) != 1:
                        continue
                    const = nota[0]
                spec = defs.get(const)
                if spec is None or spec not in fset:
                    continue
                if int(bound) > B_BOARD:
                    continue  # above the closeout bound: refuse
                hits[spec].append(('iqhle:%s' % bound, vfile, thm, const))
                nthm += 1
        if CHAMP_OK_RE.search(txt):
            ms = CHAMP_SCORE_RE.search(txt)
            try:
                score = eval(ms.group(1), {'__builtins__': {}}, {}) if ms else None
            except Exception:
                score = None
            if score == B_CHAMP:
                for thm, const in CHAMP_THM_RE.findall(txt):
                    if const == 'tm':
                        if len(nota) != 1:
                            continue
                        const = nota[0]
                    spec = defs.get(const)
                    if spec is None or spec not in fset:
                        continue
                    hits[spec].append(('iqhch', vfile, thm, const))
                    nthm += 1

    chosen = {}
    for spec, cands in hits.items():
        cands.sort(key=lambda c: (c[0] != 'nqh', c[1], c[2]))
        chosen[spec] = cands[0]

    unproven = [s for s in frozen if s not in chosen]

    outdir = os.path.join(ROOT, 'tools/closeout')
    with open(os.path.join(outdir, 'frozen_map.tsv'), 'w') as f:
        f.write('machine\tkind\tvfile\ttheorem\tconst\n')
        for spec in sorted(chosen, key=lambda s: (chosen[s][1], chosen[s][2])):
            k, v, t, c = chosen[spec]
            f.write('%s\t%s\t%s\t%s\t%s\n' % (spec, k, v, t, c))
    with open(os.path.join(outdir, 'frozen_unproven.txt'), 'w') as f:
        for s in unproven:
            f.write(s + '\n')

    fam = collections.Counter()
    for spec, (k, v, t, c) in chosen.items():
        d = v.split('/')[2] if v.count('/') >= 2 else v
        fam[(d if not d.endswith('.v') else re.sub(r'_?\d*\.v$', '', d), k)] += 1
    print('frozen: %d   proven: %d   unproven: %d   (files scanned: %d, thms matched: %d)'
          % (len(frozen), len(chosen), len(unproven), nfiles, nthm))
    for (d, k), n in sorted(fam.items(), key=lambda x: -x[1]):
        print('  %-24s %-4s %5d' % (d, k, n))


if __name__ == '__main__':
    main()
