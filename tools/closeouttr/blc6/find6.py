#!/usr/bin/env python3
"""BLC6: block lists through ListGlueRngTr (UNTRUSTED; SCOPING_INSTR.md §7.4.BLC6).

    python3 tools/closeouttr/blc6/find6.py find ROWS.txt OUT.jsonl [--jobs 2] [--timeout 1800]
    python3 tools/closeouttr/blc6/find6.py one SPEC [--out OUT.jsonl]
    python3 tools/closeouttr/blc6/find6.py batch OUT.jsonl --tag BLC6 [--chunk 4]

MP's language (mp_find.get_lang: learn4 with F the anchors' local language
and the far end from a long run; cached in $MP_CACHE) with a far-end depth
count in the right states (lang_mp.Lang4D, MP_DEPTH, default 4 here), and
BLC4's exploration whose mins voids are RANGE voids local to the unfold
path (rng6.X6, ListGlueRngTr's URng).  The liveness is lx5's (additive,
else lexicographic); the batch uses lgr_sound or lgrx_sound.
"""
import argparse
import collections
import json
import os
import signal
import sys
import time
from multiprocessing import Pool

os.environ.setdefault('MP_DEPTH', '4')
HERE = os.path.dirname(os.path.abspath(__file__))
for d in ('.', '..', '../blc3', '../blc4', '../blc5', '../mp'):
    sys.path.insert(0, os.path.join(HERE, d))
import cert6                                        # noqa: E402
import lg_batch as G                                # noqa: E402
import lx5                                          # noqa: E402
import mp_find                                      # noqa: E402
import rng6                                         # noqa: E402
import ti_batch as T                                # noqa: E402


def find_dir(spec, lang, t0, mir=False, plist=G.PLIST):
    X, pins, boot = rng6.explore_row(spec, lang, t0, mir)
    tab = T.parse(spec)
    if mir:
        tab = T.mirror(tab)
    cert = cert6.assemble(X, X.t0, pins)
    cert['mir'] = mir
    tabw = X.tabw
    err = G.c_fams_ok(cert, tabw)
    if err:
        return dict(err='fams: ' + err, nfam=len(cert['fams']))
    err = G.c_boot_ok(cert, tab, tabw)
    if err:
        return dict(err=err)
    fired = [G.leaf_fired(tabw, lf) for lf in cert['leaves']]
    last = None
    for P in plist:
        lv = lx5.live_search(cert, fired, P)
        if isinstance(lv, dict):
            cert.update(lv)
            err = lx5.c_checkx(cert, tab)
            if err:
                return dict(err='check: ' + err)
            cert['nfam'] = len(cert['fams'])
            cert['nrng'] = sum(1 for F in cert['fams'] for nd in F['utree'] if nd[0] == 'rng')
            return cert
        last = lv
    return dict(err='norank %s' % (last,), nfam=len(cert['fams']))


LANG = os.environ.get('BLC6_LANG', 'mp')


def get_lang(spec):
    """mp: MP's language (local F, long-run far end, Lang4D); l4: BLC4's
    learner as it is (for regression tests on boarded rows)"""
    if LANG == 'l4':
        import learn4
        import lang_mp
        lang, mir, info = learn4.learn(spec)
        if lang_mp.DEPTH > 0:
            lang = lang_mp.with_depth(lang)
        return lang, mir, info
    return mp_find.get_lang(spec)


def find_row(spec, t0s=(20000, 100000)):
    t = time.time()
    rng6.STATS.clear()
    lang, mir, info = get_lang(spec)
    errs = []
    if info.get('tboot') and info['tboot'] > 20000:
        t0s = (info['tboot'],) + tuple(x for x in t0s if x < info['tboot'])
    for t0 in t0s:
        try:
            r = find_dir(spec, lang, t0, mir=mir)
        except T.Fail as e:
            r = dict(err=str(e))
        if 'err' not in r:
            r.update(spec=spec, learn=info, secs=round(time.time() - t, 1), t0=r.get('t0', t0))
            return r
        errs.append('t%d %s' % (t0, r['err']))
    return dict(spec=spec, err=' / '.join(errs), learn=info, secs=round(time.time() - t, 1),
                stats=dict(rng6.STATS))


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()


def find(spec, timeout=0):
    if timeout:
        signal.signal(signal.SIGALRM, _alarm)
        signal.alarm(timeout)
    try:
        return find_row(spec)
    except T.Fail as e:
        return dict(spec=spec, err=str(e))
    except Timeout:
        return dict(spec=spec, err='timeout', stats=dict(rng6.STATS))
    except RecursionError:
        return dict(spec=spec, err='recursion')
    finally:
        if timeout:
            signal.alarm(0)


def _find1(args):
    return find(*args)


def cmd_find(a):
    specs = [l.split()[0] for l in open(a.rows) if l.strip() and not l.startswith('#')]
    done = set()
    if os.path.exists(a.out):
        done = set(json.loads(l)['spec'] for l in open(a.out))
    todo = [(s, a.timeout) for s in specs if s not in done]
    stats = collections.Counter()
    with open(a.out, 'a') as f, Pool(a.jobs, maxtasksperchild=1) as pool:
        for r in pool.imap_unordered(_find1, todo):
            f.write(json.dumps(G.jsonable(r)) + '\n')
            f.flush()
            stats['ok' if 'err' not in r else 'fail'] += 1
            print(r['spec'], r.get('err', 'OK')[:200], flush=True)
    print(dict(stats))


def cmd_one(a):
    r = find(a.spec, a.timeout)
    print(json.dumps({k: v for k, v in G.jsonable(r).items()
                      if k in ('spec', 'err', 'secs', 'nfam', 'nrng', 'stats')})[:3000])
    if a.out:
        with open(a.out, 'a') as f:
            f.write(json.dumps(G.jsonable(r)) + '\n')


def cmd_batch(a):
    from cbt import next_free, write_batch
    rem = T.remaining()
    certs, seen = [], set()
    for p in a.found:
        for line in open(p):
            c = json.loads(line)
            s = c['spec']
            if 'err' in c or s not in rem or s in seen or s in a.skip:
                continue
            seen.add(s)
            certs.append(lx5.detuplex(c))
    nn = next_free(a.tag)
    made = []
    for i in range(0, len(certs), a.chunk):
        chunk = certs[i:i + a.chunk]
        entries = [(c['spec'], cert6.renderx_r(c)) for c in chunk]
        made.append(write_batch(a.tag, nn, ['From BBB4.Checkers Require Import LapDecider.',
                                            'From BBB4.Counters Require Import TriGlueTr ListGlue2Tr '
                                            'ListGlueLexTr ListGlueRngTr ListGlueRngLexTr.'],
                                entries, 'multi-cell block lists with range voids '
                                         '(ListGlueRngTr, lgr_check / lgrx_check)'))
        nn += 1
    print('%d rows -> %d batch file(s): %s' % (len(certs), len(made),
          ' '.join(os.path.relpath(p, T.REPO) for p in made)))


def main():
    if os.environ.get('PYTHONHASHSEED') != '0':
        os.environ['PYTHONHASHSEED'] = '0'
        os.execv(sys.executable, [sys.executable] + sys.argv)
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest='cmd', required=True)
    p = sp.add_parser('find')
    p.add_argument('rows')
    p.add_argument('out')
    p.add_argument('--jobs', type=int, default=2)
    p.add_argument('--timeout', type=int, default=1800)
    p = sp.add_parser('one')
    p.add_argument('spec')
    p.add_argument('--timeout', type=int, default=0)
    p.add_argument('--out')
    p = sp.add_parser('batch')
    p.add_argument('found', nargs='+')
    p.add_argument('--tag', default='BLC6')
    p.add_argument('--chunk', type=int, default=4)
    p.add_argument('--skip', action='append', default=[])
    a = ap.parse_args()
    {'find': cmd_find, 'one': cmd_one, 'batch': cmd_batch}[a.cmd](a)


if __name__ == '__main__':
    main()
