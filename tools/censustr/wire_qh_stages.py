#!/usr/bin/env python3
"""Wire every unwired theories/CensusTr/ProvTr_QH_NN.v into the census
(UNTRUSTED tooling; the kernel checks the result when RunTr compiles).

For each stage file not yet imported by CensusTr/RunTr.v it
  * appends the stage to the `From BBB4.CensusTr Require Import ...
    ProvTr_QH_..` line,
  * appends `++ pqh_NN` to [provqh_tr],
  * adds `exact pqh_NN_qhtr` to the [provqh_tr_all] closer,
  * lists the file in _CoqProject after the last ProvTr_QH entry.
Idempotent: a second run changes nothing.  Exits 0 and prints the stages
it wired (possibly none).

Usage: wire_qh_stages.py [--repo DIR]
"""
import argparse
import glob
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--repo', default=REPO)
    a = ap.parse_args()
    run = os.path.join(a.repo, 'theories', 'CensusTr', 'RunTr.v')
    cp = os.path.join(a.repo, '_CoqProject')
    src = open(run).read()
    stages = sorted(os.path.splitext(os.path.basename(p))[0]
                    for p in glob.glob(os.path.join(a.repo, 'theories', 'CensusTr', 'ProvTr_QH_*.v')))
    wired = set(re.findall(r'\bProvTr_QH_(\d+)\b', src))
    new = [s for s in stages if s[len('ProvTr_QH_'):] not in wired]
    if not new:
        print('wire_qh_stages: nothing to wire')
        return
    for s in new:
        nn = s[len('ProvTr_QH_'):]
        # the import line: "  ProvTr_QH_00 ProvTr_QH_01 ProvTr_QH_02."
        src, k = re.subn(r'^(  ProvTr_QH_\d+(?: ProvTr_QH_\d+)*)\.$',
                         lambda m: m.group(1) + ' ' + s + '.', src, count=1, flags=re.M)
        if k != 1:
            sys.exit('wire_qh_stages: cannot find the ProvTr_QH import line in RunTr.v')
        # the list
        src, k = re.subn(r'^(Definition provqh_tr : list TM := pqh_\d+(?: \+\+ pqh_\d+)*)\.$',
                         lambda m: m.group(1) + ' ++ pqh_' + nn + '.', src, count=1, flags=re.M)
        if k != 1:
            sys.exit('wire_qh_stages: cannot find [provqh_tr] in RunTr.v')
        # the closer: "    first [exact pqh_00_qhtr | ... | exact pqh_02_qhtr]."
        src, k = re.subn(r'(first \[exact pqh_\d+_qhtr(?: \| exact pqh_\d+_qhtr)*)\]\.',
                         lambda m: m.group(1) + ' | exact pqh_' + nn + '_qhtr].', src, count=1)
        if k != 1:
            sys.exit('wire_qh_stages: cannot find the [provqh_tr_all] closer in RunTr.v')
    open(run, 'w').write(src)
    lines = open(cp).read().split('\n')
    have = set(lines)
    for s in new:
        entry = 'theories/CensusTr/%s.v' % s
        if entry in have:
            continue
        last = max(i for i, l in enumerate(lines) if l.startswith('theories/CensusTr/ProvTr_QH_'))
        lines.insert(last + 1, entry)
        have.add(entry)
    open(cp, 'w').write('\n'.join(lines))
    print('wire_qh_stages: wired %s' % ' '.join(new))


if __name__ == '__main__':
    main()
