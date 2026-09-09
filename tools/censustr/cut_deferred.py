#!/usr/bin/env python3
"""Cut the next transition-level deferred list and regenerate its tables
(UNTRUSTED tooling; a wrong list only changes which machines the walk
defers, and the walk's queue-empty check fails if it is too small).

  cut_deferred.py OLD.txt NEW.txt

  * NEW = OLD minus every machine some ProvTr stage proves
    (tools/censustr/proven_specs.py --minus), OLD is deleted (git tracks
    the rename),
  * theories/CensusTr/DeferredTr_NN.v + DeferredTr_Data.v are regenerated
    from NEW (gen_deferredtr.py); shards the smaller list no longer needs
    are deleted and dropped from _CoqProject,
  * Makefile's LISTBURN_SRC default is pointed at NEW.
Refuses to run if NEW exists or nothing would be removed.
"""
import glob
import os
import re
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    old, new = sys.argv[1], sys.argv[2]
    if os.path.exists(new):
        sys.exit('cut_deferred: %s exists, refusing to overwrite' % new)
    if not os.path.exists(old):
        sys.exit('cut_deferred: %s missing' % old)
    r = subprocess.run([sys.executable, os.path.join(HERE, 'proven_specs.py'), '--minus', old],
                       capture_output=True, text=True, cwd=REPO)
    if r.returncode != 0:
        sys.exit('cut_deferred: proven_specs failed:\n' + r.stderr)
    sys.stderr.write(r.stderr)
    kept = [l for l in r.stdout.split('\n') if l.strip()]
    nold = sum(1 for l in open(old) if l.strip())
    if len(kept) >= nold:
        sys.exit('cut_deferred: nothing removed (%d rows), no cut' % nold)
    open(new, 'w').write('\n'.join(kept) + '\n')
    os.remove(old)
    outdir = os.path.join(REPO, 'theories', 'CensusTr')
    before = set(glob.glob(os.path.join(outdir, 'DeferredTr_[0-9][0-9].v')))
    r = subprocess.run([sys.executable, os.path.join(HERE, 'gen_deferredtr.py'), new, outdir],
                       capture_output=True, text=True, cwd=REPO)
    if r.returncode != 0:
        sys.exit('cut_deferred: gen_deferredtr failed:\n' + r.stderr)
    sys.stderr.write(r.stderr)
    data = open(os.path.join(outdir, 'DeferredTr_Data.v')).read()
    used = set(re.findall(r'\bDeferredTr_(\d\d)\b', data))
    cp = os.path.join(REPO, '_CoqProject')
    lines = open(cp).read().split('\n')
    for p in sorted(before):
        nn = os.path.basename(p)[len('DeferredTr_'):-2]
        if nn not in used:
            os.remove(p)
            for ext in ('.vo', '.vos', '.vok', '.glob'):
                if os.path.exists(p[:-2] + ext):
                    os.remove(p[:-2] + ext)
            lines = [l for l in lines if l != 'theories/CensusTr/DeferredTr_%s.v' % nn]
            sys.stderr.write('cut_deferred: dropped stale shard DeferredTr_%s\n' % nn)
    open(cp, 'w').write('\n'.join(lines))
    mk = os.path.join(REPO, 'Makefile')
    src = open(mk).read()
    src, k = re.subn(r'^LISTBURN_SRC \?= .*$', 'LISTBURN_SRC ?= ' + os.path.basename(new), src, count=1, flags=re.M)
    if k != 1:
        sys.exit('cut_deferred: LISTBURN_SRC not found in Makefile')
    open(mk, 'w').write(src)
    print('cut_deferred: %s -> %s: %d removed, %d kept' % (old, new, nold - len(kept), len(kept)))


if __name__ == '__main__':
    main()
