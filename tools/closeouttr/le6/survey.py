#!/usr/bin/env python3
"""LE6 survey (untrusted): what the tape does at its extent records.

For each row: run rec.c for N steps; per side the record times, the
per-record time ratio r (a base-b counter that grows a digit cell per
overflow has r ~ b^(1/w)), the extent exponent a (ext ~ t^a), the number
of runs (blocks) at the last records, the best periodic cover u v^n w of
the last record tape, and the diff between consecutive same-side record
tapes.

    python3 tools/closeouttr/le6/survey.py ROWS OUT.jsonl [--steps N] [--jobs J]
"""
import json, math, os, re, subprocess, sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
REC = '/tmp/claude-0/rec'


def build():
    if not os.path.exists(REC):
        subprocess.check_call(['gcc', '-O2', '-o', REC, os.path.join(HERE, 'rec.c')])


def runs(s):
    s = re.sub('[A-D]', '', s)
    return len(re.findall(r'0+|1+', s))


def strip(s):
    return re.sub('[A-D]', '', s)


def period_cover(s):
    """best u v^n w (|v| <= 16, n >= 3) by covered length"""
    best = (0, '', 0, 0)
    L = len(s)
    for p in range(1, 17):
        i = 0
        while i + p <= L:
            j = i
            while j + 2 * p <= L and s[j + p:j + 2 * p] == s[j:j + p]:
                j += p
            n = (j - i) // p + 1
            if n >= 3 and n * p > best[0]:
                best = (n * p, s[i:i + p], n, i)
            i += max(1, (j - i) if j > i else 1)
    return best


def one(args):
    spec, N = args
    out = subprocess.run([REC, spec, str(N), '8'], capture_output=True, text=True, timeout=600).stdout
    R = []; T = []; info = {}
    for l in out.splitlines():
        f = l.split()
        if f[0] == 'R':
            R.append((int(f[1]), int(f[2]), int(f[3])))
        elif f[0] == 'T':
            T.append((int(f[1]), int(f[2]), f[3]))
        elif f[0] in ('HALT', 'OUT', 'N'):
            info[f[0]] = f[1:]
    d = dict(spec=spec)
    if not R:
        d['kind'] = 'no records'
        return d
    tN = int(info['N'][0])
    d['records'] = int(info['N'][1])
    d['ext'] = R[-1][2]
    # extent exponent between t/16 and t
    def ext_at(t):
        e = 1
        for (tt, sd, ex) in R:
            if tt <= t:
                e = ex
        return e
    e1, e2 = ext_at(tN // 16), ext_at(tN)
    d['alpha'] = round(math.log(max(e2, 1) / max(e1, 1)) / math.log(16), 3)
    for sd, nm in ((0, 'L'), (1, 'R')):
        ts = [t for (t, s, _) in R if s == sd]
        late = [t for t in ts if t > tN // 64]
        d['n' + nm] = len(late)
        if len(ts) >= 6:
            k = min(10, len(ts) - 1)
            d['r' + nm] = round((ts[-1] / ts[-1 - k]) ** (1.0 / k), 3)
    d['grows'] = ''.join(nm for sd, nm in ((0, 'L'), (1, 'R')) if d['n' + nm] >= 2)
    if T:
        last = strip(T[-1][2])
        d['last'] = T[-1][2][:300]
        d['runs'] = [runs(x[2]) for x in T]
        pc = period_cover(last)
        d['period'] = dict(cov=pc[0], v=pc[1], n=pc[2], at=pc[3], frac=round(pc[0] / max(1, len(last)), 2))
    return d


def main():
    a = sys.argv[1:]
    rows = open(a[0]).read().split()
    N = int(a[a.index('--steps') + 1]) if '--steps' in a else 100000000
    J = int(a[a.index('--jobs') + 1]) if '--jobs' in a else 4
    build()
    done = set()
    if os.path.exists(a[1]):
        done = {json.loads(l)['spec'] for l in open(a[1])}
    todo = [(r, N) for r in rows if r not in done]
    with open(a[1], 'a') as fo, Pool(J) as P:
        for d in P.imap_unordered(one, todo):
            fo.write(json.dumps(d) + '\n'); fo.flush()


if __name__ == '__main__':
    main()
