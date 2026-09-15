#!/usr/bin/env python3
"""Wire every unwired theories/CensusTr/ProvTr_QH_NN.v (and
ProvTr_Lap_NN.v) into the census (UNTRUSTED tooling; the kernel checks
the result when RunTr compiles).

For each QH stage file not yet imported by CensusTr/RunTr.v it
  * appends the stage to the `From BBB4.CensusTr Require Import ...
    ProvTr_QH_..` line,
  * appends `++ pqh_NN` to [provqh_tr],
  * adds `exact pqh_NN_qhtr` to the [provqh_tr_all] closer,
  * lists the file in _CoqProject after the last ProvTr_QH entry;
for a lap stage the same with the ProvTr_Lap import line, `++ ptl_NN`
in [prov_tr] and `exact ptl_NN_nqhtr` in the [prov_tr_all] closer.
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
    # (stage prefix, list name, closer lemma suffix, list definition, closer's first lemma)
    kinds = [('ProvTr_QH_', 'pqh_', '_qhtr', 'provqh_tr', r'exact pqh_\d+_qhtr'),
             ('ProvTr_Lap_', 'ptl_', '_nqhtr', 'prov_tr', r'exact prov_tr_irtr_all')]
    new_all = []
    for pre, lst, suf, defn, first in kinds:
        stages = sorted(os.path.splitext(os.path.basename(p))[0]
                        for p in glob.glob(os.path.join(a.repo, 'theories', 'CensusTr', pre + '*.v')))
        wired = set(re.findall(r'\b' + pre + r'(\d+)\b', src))
        new = [s for s in stages if s[len(pre):] not in wired]
        for s in new:
            nn = s[len(pre):]
            # the import line: "  ProvTr_QH_00 ProvTr_QH_01 ProvTr_QH_02."  /
            # "  ProvTr_Lap_00 ... ProvTr_Lap_11"
            src, k = re.subn(r'^(  ' + pre + r'\d+(?: ' + pre + r'\d+)*)(\.?)$',
                             lambda m: m.group(1) + ' ' + s + m.group(2), src, count=1, flags=re.M)
            if k != 1:
                sys.exit('wire_qh_stages: cannot find the %s import line in RunTr.v' % pre)
            # the list: "... ++ ptl_11 ++ ptc_00 ..." keeps its order: insert after the last ptl_/pqh_
            src, k = re.subn(r'(Definition ' + defn + r' : list TM :=[^.]*?' + lst + r'\d+)(?![^.]*' + lst + r'\d)',
                             lambda m: m.group(1) + ' ++ ' + lst + nn, src, count=1, flags=re.S)
            if k != 1:
                sys.exit('wire_qh_stages: cannot find [%s] in RunTr.v' % defn)
            # the closer: "first [exact ... | exact ptl_11_nqhtr | exact ptc_00_nqhtr ...]"
            src, k = re.subn(r'(first \[' + first + r'(?: \| exact \w+)*? \| exact ' + lst + r'\d+' + suf + r')(?![^\]]*' + lst + r'\d)',
                             lambda m: m.group(1) + ' | exact ' + lst + nn + suf, src, count=1, flags=re.S)
            if k != 1:
                src, k = re.subn(r'(first \[' + first + r'(?: \| exact ' + lst + r'\d+' + suf + r')*)',
                                 lambda m: m.group(1) + ' | exact ' + lst + nn + suf, src, count=1)
            if k != 1:
                sys.exit('wire_qh_stages: cannot find the [%s_all] closer in RunTr.v' % defn)
        new_all += new
    if not new_all:
        print('wire_qh_stages: nothing to wire')
        return
    open(run, 'w').write(src)
    lines = open(cp).read().split('\n')
    have = set(lines)
    for s in new_all:
        entry = 'theories/CensusTr/%s.v' % s
        if entry in have:
            continue
        pre = s[:s.rindex('_') + 1]
        last = max(i for i, l in enumerate(lines) if l.startswith('theories/CensusTr/' + pre))
        lines.insert(last + 1, entry)
        have.add(entry)
    open(cp, 'w').write('\n'.join(lines))
    print('wire_qh_stages: wired %s' % ' '.join(new_all))


if __name__ == '__main__':
    main()
