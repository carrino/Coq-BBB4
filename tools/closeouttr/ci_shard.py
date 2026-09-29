#!/usr/bin/env python3
"""Split the closeout batches across CI shards (UNTRUSTED scheduler).

The `closeout-shard` matrix job of .github/workflows/ci.yml builds one
slice of the batches theories/CloseoutTr/CBT_*.vo per runner; the
`closeout-final` job then builds CloseoutTr.vo on top of all the slices.
This script decides the slices.  It is pure scheduling: nothing it says is
trusted.  The final job's `make -q` fails if any batch did not arrive, and
coqc compiles CloseoutTr.vo, which Requires every batch, there.  A bad
split can only cost time or fail the run, never pass a wrong one.

    python3 tools/closeouttr/ci_shard.py K N      targets of shard K of N (0-based), one per line
    python3 tools/closeouttr/ci_shard.py --check N   self-check: the N slices partition CBT_*.v
    python3 tools/closeouttr/ci_shard.py --plan N    per-shard load table
    python3 tools/closeouttr/ci_shard.py --merge TAR...  unpack shard output (final job)
    python3 tools/closeouttr/ci_shard.py --costs LOG...  cost table from TIMED=1 logs

The split is longest-processing-time-first over a recorded per-batch cost,
where a shard's load is max(total / JOBS, its longest batch): make -j4
runs four batches at once, so slow batches may share a shard as long as
that does not make it the long pole.  The cost is read from
tools/closeouttr/ci_costs.tsv (`batch<TAB>seconds`: the batch's own compile
plus the boards only it imports, one core of a hosted runner).  Batches
not in the table cost DEFAULT_COST.  It depends only on the committed tree,
so every shard computes the same split.  Ties go to the lower batch name
and the lower shard index.

When you add a batch that takes more than a minute to compile, record it
in ci_costs.tsv, or it may land beside another slow one and make its shard
the long pole.  Refresh the table from the shard logs (every shard runs
`make TIMED=1` and uploads its log): `ci_shard.py --costs LOG...` prints
it (it reads .Makefile.coq.d, so run any `make -f Makefile.coq` first).
"""
import glob
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
COSTS = os.path.join(HERE, 'ci_costs.tsv')
# Same pattern as gen_closeout_tr.py: exactly the files CloseoutTr.v imports.
BATCH_RE = re.compile(r'^CBT_([A-Z][A-Z0-9]{0,7})_(\d\d)\.v$')
DEFAULT_COST = 20.0   # seconds; most batches (boards included) take 5-40 s
JOBS = 4              # the shard's make -j (ci.yml)


def batches():
    names = [os.path.basename(p)[:-2] for p in
             glob.glob(os.path.join(REPO, 'theories', 'CloseoutTr', 'CBT_*.v'))]
    return sorted(n for n in names if BATCH_RE.match(n + '.v'))


def read_costs():
    costs = {}
    with open(COSTS) as f:
        for line in f:
            line = line.split('#', 1)[0].strip()
            if not line:
                continue
            name, secs = line.split('\t')
            costs[name] = float(secs)
    return costs


def estimate(costs):
    """A shard's wall-clock estimate: make -j JOBS spreads its batches over
    JOBS cores, but no batch is split, so the longest is a floor."""
    return max(sum(costs) / JOBS, max(costs, default=0.0))


def plan(n):
    """Return [(estimate, [batch, ...]) for each shard]: longest first, each
    batch onto the shard whose estimate grows least (then the lower index)."""
    costs = read_costs()
    cost = lambda b: costs.get(b, DEFAULT_COST)  # noqa: E731
    work = sorted(batches(), key=lambda b: (-cost(b), b))
    shards = [[] for _ in range(n)]
    for b in work:
        k = min(range(n), key=lambda i: (
            estimate([cost(x) for x in shards[i] + [b]]),
            estimate([cost(x) for x in shards[i]]), i))
        shards[k].append(b)
    return [(estimate([cost(x) for x in bs]), sorted(bs)) for bs in shards]


def target(b):
    return 'theories/CloseoutTr/%s.vo' % b


def check(n):
    every = batches()
    seen = {}
    for k, (_, bs) in enumerate(plan(n)):
        for b in bs:
            if b in seen:
                sys.exit('ci_shard: %s in shards %d and %d' % (b, seen[b], k))
            seen[b] = k
        if not bs:
            sys.exit('ci_shard: shard %d of %d is empty' % (k, n))
    missing = sorted(set(every) - set(seen))
    extra = sorted(set(seen) - set(every))
    if missing or extra:
        sys.exit('ci_shard: missing %s, unknown %s' % (missing, extra))
    stale = sorted(set(read_costs()) - set(every))
    if stale:
        sys.exit('ci_shard: ci_costs.tsv names batches that do not exist: %s'
                 % ' '.join(stale))
    print('ci_shard: %d batches, each in exactly one of %d shards'
          % (len(every), n))


def read_deps():
    """The .vo -> .vo edges of the generated .Makefile.coq.d."""
    deps = {}
    edge = re.compile(r'^(\S+\.vo) [^:]*:(.*)$')
    with open(os.path.join(REPO, '.Makefile.coq.d')) as f:
        for line in f:
            m = edge.match(line)
            if m:
                deps[m.group(1)] = [d for d in m.group(2).split()
                                    if d.endswith('.vo')]
    return deps


def closure(deps, t):
    seen, todo = set(), [t]
    while todo:
        for d in deps.get(todo.pop(), []):
            if d not in seen:
                seen.add(d)
                todo.append(d)
    return seen


def costs_from_logs(paths):
    """Per-batch cost from `make TIMED=1` logs: the batch's own real time
    plus that of every dependency no other batch needs (its boards)."""
    # search, not match: a GitHub job log prefixes every line with a stamp
    time_re = re.compile(r'(theories/\S+\.vo) \(real: ([0-9.]+),')
    secs = {}
    for p in paths:
        with open(p, errors='replace') as f:
            for line in f:
                m = time_re.search(line)
                if m:
                    secs[m.group(1)] = float(m.group(2))
    deps = read_deps()
    clo = {b: closure(deps, target(b)) for b in batches()}
    users = {}
    for b, c in clo.items():
        for d in c:
            users[d] = users.get(d, 0) + 1
    out = {}
    for b, c in clo.items():
        if target(b) not in secs:
            continue
        out[b] = secs[target(b)] + sum(secs.get(d, 0.0) for d in c
                                       if users[d] == 1)
    return out


def merge(tars):
    """Unpack the shard tarballs into the tree.  A file two shards both
    built (a shared glue file or board) must be byte-identical: coqc is
    deterministic for the same source, binary and dependencies, and
    anything else would be caught at Require time anyway ("compiled
    library ... makes inconsistent assumptions"), so a mismatch fails
    here, early and with a name.  Every merged file then gets ONE mtime,
    later than the checkout: no .vo is newer than another .vo, and none
    is older than its .v, so make sees all of them up to date."""
    import tarfile
    import time
    got = set()
    dup = 0
    for t in tars:
        with tarfile.open(t) as tf:
            for m in tf.getmembers():
                if not m.isfile():
                    continue
                if not re.match(r'^theories/[^\0]*\.(vo|glob)$', m.name) \
                        or '..' in m.name.split('/'):
                    sys.exit('ci_shard: %s: unexpected member %s' % (t, m.name))
                path = os.path.join(REPO, m.name)
                data = tf.extractfile(m).read()
                if m.name in got:
                    dup += 1
                    with open(path, 'rb') as f:
                        if f.read() != data:
                            sys.exit('ci_shard: %s differs between shards'
                                     % m.name)
                    continue
                if os.path.exists(path):
                    sys.exit('ci_shard: %s already in the tree' % m.name)
                os.makedirs(os.path.dirname(path), exist_ok=True)
                with open(path, 'wb') as f:
                    f.write(data)
                got.add(m.name)
    now = time.time()
    for name in got:
        os.utime(os.path.join(REPO, name), (now, now))
    vo = sum(1 for n in got if n.endswith('.vo'))
    print('ci_shard: merged %d files (%d .vo) from %d shards; %d duplicate '
          'copies (files built by more than one shard)'
          % (len(got), vo, len(tars), dup))


def main(argv):
    if len(argv) == 2 and argv[0] == '--check':
        check(int(argv[1]))
    elif len(argv) == 2 and argv[0] == '--plan':
        n = int(argv[1])
        costs = read_costs()
        for k, (load, bs) in enumerate(plan(n)):
            top = sorted(bs, key=lambda b: -costs.get(b, DEFAULT_COST))[:3]
            print('shard %d: %3d batches, %7.0f s  (heaviest: %s)'
                  % (k, len(bs), load, ', '.join(top)))
    elif len(argv) >= 2 and argv[0] == '--merge':
        merge(argv[1:])
    elif len(argv) >= 2 and argv[0] == '--costs':
        for b, s in sorted(costs_from_logs(argv[1:]).items()):
            print('%s\t%.0f' % (b, s))
    elif len(argv) == 2:
        k, n = int(argv[0]), int(argv[1])
        if not 0 <= k < n:
            sys.exit('ci_shard: shard %d out of range 0..%d' % (k, n - 1))
        for b in plan(n)[k][1]:
            print(target(b))
    else:
        sys.exit(__doc__)


if __name__ == '__main__':
    main(sys.argv[1:])
