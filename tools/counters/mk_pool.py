#!/usr/bin/env python3
"""Compute the unproven pool: frozen deferred 5156 minus proven machines
(manifest rows + spec-named board files)."""
import glob
import os
import re
import sys

ROOT = '/home/user/Coq-BBB4'

# ---- decode the frozen deferred list from theories/Census/Deferred_*.v
def rows_to_specs():
    specs = []
    rowre = re.compile(r'\[(t[^\]]*)\]')
    for f in sorted(glob.glob(ROOT + '/theories/Census/Deferred_0*.v')):
        for m in rowre.finditer(open(f).read()):
            slots = m.group(1).split(';')
            if len(slots) != 8:
                continue
            ent = []
            for s in slots:
                s = s.strip()
                if s == 'tN':
                    ent.append('---')
                else:
                    assert len(s) == 4 and s[0] == 't', s
                    ent.append(s[1:])
            spec = '_'.join(ent[2*i] + ent[2*i+1] for i in range(4))
            specs.append(spec)
    return specs

def proven():
    out = set()
    for f in glob.glob(ROOT + '/tools/*manifest*.tsv'):
        for i, line in enumerate(open(f)):
            if i == 0:
                continue
            m = line.split('\t')[0].strip()
            if m:
                out.add(m)
    # spec-named boards (waves 8-12): filename embeds mach_id(spec)
    ids = {}
    for f in (glob.glob(ROOT + '/theories/Machines/Counters/*.v')
              + glob.glob(ROOT + '/theories/Counters/*.v')
              + glob.glob(ROOT + '/theories/Machines/**/*.v', recursive=True)):
        ids[os.path.basename(f)[:-2]] = 1
    return out, ids

def mach_id(spec):
    return re.sub(r'[^0-9A-Za-z]', '_', spec)

def main():
    specs = rows_to_specs()
    man, ids = proven()
    unproven = []
    for s in sorted(set(specs)):
        if s in man:
            continue
        mid = mach_id(s)
        if any(k.endswith('_' + mid) or k.endswith(mid) and mid in k
               for k in ids if k.endswith(mid)):
            continue
        unproven.append(s)
    print('deferred %d unique %d manifests %d unproven %d'
          % (len(specs), len(set(specs)), len(man), len(unproven)),
          file=sys.stderr)
    for s in unproven:
        print(s)

if __name__ == '__main__':
    main()
