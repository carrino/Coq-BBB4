#!/usr/bin/env python3
"""List the machines in the transition-level proven tier (UNTRUSTED
bookkeeping) and, optionally, subtract them from a deferred list.

Sources, all read from the committed stage files so the list can only
name machines the kernel already certified:
  - CensusTr/RunTr.v      prov_tr_irtr  (tm_<ID> names, XXX = hole)
  - CensusTr/ProvTr_Lap_*.v   LAPT_<ID> board imports (____ = hole)
  - CensusTr/ProvTr_QH_*.v    LAPQ_<ID> board imports (same), and the
                              (* <spec> ... *) rows of the other QH conveyors
  - CensusTr/ProvTr_TC_*.v, ProvTr_RW_*.v, ProvTr_IR_*.v, ProvTr_RK_*.v, ProvTr_QH_*.v
    the (* <spec> ... *) row comments

Usage: proven_specs.py [--minus DEFERRED.txt] > out.txt
  without --minus: the sorted proven specs (bbchallenge text, --- = hole)
  with    --minus: DEFERRED minus the proven specs, order preserved
"""
import argparse
import glob
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
CT = os.path.join(REPO, 'theories', 'CensusTr')


def proven():
    out = set()
    s = open(os.path.join(CT, 'RunTr.v')).read()
    m = re.search(r'Definition prov_tr_irtr : list TM :=\s*\[(.*?)\]\.', s, re.S)
    if m:
        for nm in re.findall(r'tm_([0-9A-Z_]+)', m.group(1)):
            out.add(nm.replace('XXX', '---'))
    # the lap boards: ProvTr_Lap_NN import LAPT_<ID> (never-QH), ProvTr_QH_NN
    # from gen_provtr_lapqh.py import LAPQ_<ID> (quasihalting side); neither
    # carries (* spec *) rows, the spec is the board name
    for pat in ('ProvTr_Lap_*.v', 'ProvTr_QH_*.v'):
        for f in glob.glob(os.path.join(CT, pat)):
            for nm in re.findall(r'Require Import LAP[TQ]_([0-9A-Z_]+)\.', open(f).read()):
                # board names write a hole as ___ (a trailing hole) or ____
                # (hole + the group separator)
                out.add(re.sub(r'___$', '---', nm.replace('____', '---_')))
    for pat in ('ProvTr_TC_*.v', 'ProvTr_RW_*.v', 'ProvTr_IR_*.v', 'ProvTr_RK_*.v', 'ProvTr_QH_*.v'):
        for f in glob.glob(os.path.join(CT, pat)):
            # (?=\s), not \b: a spec whose last transition is a hole ends in
            # '-', a non-word character, and \b would not match after it
            for sp in re.findall(r'^\(\* ([0-9A-Z\-]{6}(?:_[0-9A-Z\-]{6}){3})(?=\s)', open(f).read(), re.M):
                out.add(sp)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--minus')
    a = ap.parse_args()
    pv = proven()
    if not a.minus:
        for sp in sorted(pv):
            print(sp)
        sys.stderr.write('proven_specs: %d machines\n' % len(pv))
        return
    kept = removed = 0
    for line in open(a.minus):
        sp = line.strip()
        if not sp:
            continue
        if sp in pv:
            removed += 1
        else:
            kept += 1
            print(sp)
    sys.stderr.write('proven_specs: %d proven; %s: %d removed, %d kept\n'
                     % (len(pv), a.minus, removed, kept))


if __name__ == '__main__':
    main()
