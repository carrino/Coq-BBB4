#!/usr/bin/env python3
"""Split a `tailcert.py --out` scan into one row list per gate label.

`tools/counters/buckets31/*.txt` were assembled by hand, so the next wave could
read the lists but not re-derive them. This does it from the JSON, which means a
bucket table and the row lists behind it can be regenerated at any commit --
the wave-31 section 11 constraint, applied to the lists as well as the counts.

Writes `<outdir>/<slug>.txt` per label, plus `<outdir>/GATETABLE.md` with the
table in the form the findings documents use.

Usage
  tailcert.py --list tools/closeout/core_rows.txt --out scan.json
  buckets.py --json scan.json --out tools/counters/buckets32
"""
import argparse
import collections
import json
import os
import re
import sys


def slug(label):
    """`no interior j=0 chain at octave parity 0` -> the buckets31 spelling."""
    s = label.replace('j=0', 'j0').replace('j=S j', 'jS_j')
    s = re.sub(r'[^0-9A-Za-z]+', '_', s).strip('_')
    return s


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--json', required=True)
    ap.add_argument('--out', required=True)
    a = ap.parse_args()
    rows = json.load(open(a.json))
    os.makedirs(a.out, exist_ok=True)
    by = collections.defaultdict(list)
    nok = 0
    for r in rows:
        if r.get('ok'):
            nok += 1
            continue
        why = r['why']
        # the validate diagnostics carry a machine-specific configuration dump;
        # bucket them under the assertion that produced them.
        if 'inner fill ->' in why:
            why = 'inner fill lands off the endpoint'
        elif re.match(r'^p=\d+ boot ->', why):
            why = 'boot lands off the endpoint'
        elif re.match(r'^p=\d+ branch:', why):
            why = 'branch lands off the next anchor'
        by[why].append(r['spec'])
    tab = sorted(by.items(), key=lambda kv: (-len(kv[1]), kv[0]))
    lines = ['    %d / %d fully derived' % (nok, len(rows)), '',
             '| n | furthest gate |', '|--:|---|']
    for label, specs in tab:
        path = os.path.join(a.out, '%s.txt' % slug(label))
        with open(path, 'w') as f:
            f.write(''.join(s + '\n' for s in sorted(specs)))
        lines.append('| %d | `%s` |' % (len(specs), label))
        print('%5d  %-52s %s' % (len(specs), label, os.path.basename(path)))
    with open(os.path.join(a.out, 'GATETABLE.md'), 'w') as f:
        f.write('\n'.join(lines) + '\n')
    print('\n%d derived, %d rows over %d buckets -> %s'
          % (nok, len(rows) - nok, len(tab), a.out))
    return 0


if __name__ == '__main__':
    sys.exit(main())
