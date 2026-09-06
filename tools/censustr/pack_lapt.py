#!/usr/bin/env python3
"""Pack individually kernel-validated LAPT boards (Machines/CountersTr/
LAPT_<ID>.v, one machine each) into files of N machines.

Each board becomes a [Section B_<ID>. ... End B_<ID>.] block -- its
[Local Notation]s ([mk], [tm], [Cc]) are section-local, so bodies do not
collide, and every Definition/Theorem keeps its <ID>-suffixed name -- under
ONE header whose imports are the union of the boards' imports.  The proof
text is unchanged; the packed file is re-checked by coqc before the
singles are removed (UNTRUSTED bookkeeping; the kernel decides).

Usage: pack_lapt.py --per N [--outdir DIR] [--keep] [--dry-run] BOARD.v...
"""
import argparse
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
IMPORT_RE = re.compile(r'^(From \S+ Require (?:Import|Export) .*?\.)\s*$', re.M | re.S)


def split_board(path):
    """-> (header comment, list of import statements, body)"""
    t = open(path).read()
    i = t.index('\nFrom Coq Require Import')
    head, rest = t[:i + 1], t[i + 1:]
    # imports run until the first blank-line-separated non-import statement
    imports, pos = [], 0
    for m in re.finditer(r'From [^\n]+?(?:\n [^\n]+)*\.\n', rest):
        if m.start() != pos:
            break
        imports.append(m.group(0).strip())
        pos = m.end()
    body = rest[pos:]
    body = body.replace('\nImport ListNotations.\n', '\n', 1)
    return head.strip(), imports, body.strip('\n')


def merge_imports(all_imports):
    """Union of [From X Require Import A B C.] lines, per prefix X."""
    per = {}
    order = []
    for imp in all_imports:
        m = re.match(r'From (\S+) Require Import (.*)\.$', imp, re.S)
        if not m:
            raise SystemExit('unrecognised import: %r' % imp)
        pre, mods = m.group(1), m.group(2).split()
        if pre not in per:
            per[pre] = []
            order.append(pre)
        for x in mods:
            if x not in per[pre]:
                per[pre].append(x)
    return '\n'.join('From %s Require Import %s.' % (p, ' '.join(per[p])) for p in order)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--per', type=int, default=50)
    ap.add_argument('--outdir', default=os.path.join(REPO, 'theories', 'Machines', 'CountersTr'))
    ap.add_argument('--keep', action='store_true', help='do not delete the singles')
    ap.add_argument('--dry-run', action='store_true')
    ap.add_argument('--start', type=int, default=0, help='first pack index')
    ap.add_argument('boards', nargs='+')
    a = ap.parse_args()
    boards = sorted(a.boards)
    npack = a.start
    for ci in range(0, len(boards), a.per):
        chunk = boards[ci:ci + a.per]
        heads, imps, bodies, ids = [], [], [], []
        for b in chunk:
            h, im, body = split_board(b)
            m = re.search(r'\(\*\* \* (?:LAPT|LAPC|NLAP|PEEL|LAPQ)_(\w+): '
                          r'(?:TRANSITION-LEVEL board for )?machine (\S+),', h)
            if not m:
                raise SystemExit('no board header in %s' % b)
            ids.append((m.group(1), m.group(2)))
            imps += im
            bodies.append('Section B_%s.\n\n%s\n\nEnd B_%s.' % (m.group(1), body, m.group(1)))
        name = 'LAPTP_%03d' % npack
        out = os.path.join(a.outdir, name + '.v')
        text = ('(** * %s: %d TRANSITION-LEVEL lap-certificate boards, packed.\n\n'
                '    Each [Section B_<ID>] is one machine\'s board exactly as\n'
                '    tools/counters/emit_lapcert.py --tr emitted and coqc validated it\n'
                '    (tools/censustr/pack_lapt.py only concatenates).  Machines:\n%s *)\n'
                '%s\nImport ListNotations.\n\n%s\n'
                % (name, len(chunk),
                   '\n'.join('      %s' % spec for _, spec in ids),
                   merge_imports(imps), '\n\n'.join(bodies)))
        if a.dry_run:
            print('%s <- %d boards' % (out, len(chunk)))
            npack += 1
            continue
        open(out, 'w').write(text)
        r = subprocess.run(['coqc', '-native-compiler', 'no', '-Q', 'theories', 'BBB4',
                            os.path.relpath(out, REPO)], cwd=REPO, capture_output=True, text=True)
        if r.returncode != 0:
            os.remove(out)
            sys.exit('PACK FAILED %s:\n%s' % (out, (r.stderr or r.stdout)[-2000:]))
        print('%s OK (%d boards)' % (out, len(chunk)))
        if not a.keep:
            for b in chunk:
                for ext in ('.v', '.vo', '.vos', '.vok', '.glob'):
                    p = os.path.splitext(b)[0] + ext
                    if os.path.exists(p):
                        os.remove(p)
                aux = os.path.join(os.path.dirname(b), '.' + os.path.basename(os.path.splitext(b)[0]) + '.aux')
                if os.path.exists(aux):
                    os.remove(aux)
        npack += 1


if __name__ == '__main__':
    main()
