#!/usr/bin/env python3
"""MP: the multi-cell / carry-like block lists (UNTRUSTED; SCOPING_INSTR.md §7.4.MP).

    python3 tools/closeouttr/mp/mp_find.py find ROWS.txt OUT.jsonl [--jobs 2] [--timeout 1200]
    python3 tools/closeouttr/mp/mp_find.py one SPEC                    # verbose, one row
    python3 tools/closeouttr/mp/mp_find.py batch OUT.jsonl --tag MP [--chunk 4]

blc5/lx5.py (BLC4's learner and exploration, ListGlue2Tr's additive or
ListGlueLexTr's lexicographic liveness) with the language's far end learned
from a long run (learn_mp.extend).  Learned languages are cached in
$MP_CACHE (default /tmp/mp_cache) as pickles, so a rerun skips the learner.
"""
import argparse
import collections
import json
import os
import pickle
import signal
import sys
import time
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..'))
sys.path.insert(0, os.path.join(HERE, '..', 'blc3'))
sys.path.insert(0, os.path.join(HERE, '..', 'blc4'))
sys.path.insert(0, os.path.join(HERE, '..', 'blc5'))
import learn4 as L4                                 # noqa: E402
import lang_mp                                      # noqa: E402
import learn_mp                                     # noqa: E402
import lg_batch as G                                # noqa: E402
import lx5                                          # noqa: E402
import ti_batch as T                                # noqa: E402

CACHE = os.environ.get('MP_CACHE', '/tmp/mp_cache')
EXTEND = os.environ.get('MP_EXTEND', '1') == '1'
FKIND = os.environ.get('MP_F', 'local')         # 'local' (learn_mp.fit_local) or 'bps' (learn4's)


def get_lang(spec):
    os.makedirs(CACHE, exist_ok=True)
    p = os.path.join(CACHE, 'lang_%s%s%s.pkl' % (spec, '_x' if EXTEND else '',
                                                 '_loc' if FKIND == 'local' else ''))
    if os.path.exists(p):
        lang, mir, info = pickle.load(open(p, 'rb'))
    else:
        if FKIND == 'local':
            lang, mir, info = learn_mp.learn_local(spec)
            info = dict(info, F='local')
        else:
            lang, mir, info = L4.learn(spec)
        if EXTEND:
            lang, st = learn_mp.extend(spec, lang, mir, info)
            info = dict(info, extend=st)
        pickle.dump((lang, mir, info), open(p, 'wb'))
    if lang_mp.DEPTH > 0:
        lang = lang_mp.with_depth(lang)
        info = dict(info, depth=lang_mp.DEPTH)
    return lang, mir, info


def find_row(spec, t0s=(20000, 100000)):
    t = time.time()
    lang, mir, info = get_lang(spec)
    tl = time.time() - t
    errs = []
    if info.get('tboot') and info['tboot'] > 20000:
        t0s = (info['tboot'],) + tuple(t for t in t0s if t < info['tboot'])
    for t0 in t0s:
        try:
            r = lx5.find_dir(spec, lang, t0, mir=mir)
        except T.Fail as e:
            r = dict(err=str(e))
        if 'err' not in r:
            r['spec'] = spec
            r['learn'] = info
            r['secs'] = round(time.time() - t, 1)
            return r
        errs.append('t%d %s' % (t0, r['err']))
    return dict(spec=spec, err=' / '.join(errs), learn=info, secs=round(time.time() - t, 1),
                tlearn=round(tl, 1))


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
        return dict(spec=spec, err='timeout')
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
                      if k in ('spec', 'err', 'learn', 'secs', 'tlearn')})[:3000])
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
        entries = [(c['spec'], lx5.renderx(c)) for c in chunk]
        made.append(write_batch(a.tag, nn, ['From BBB4.Checkers Require Import LapDecider.',
                                            'From BBB4.Counters Require Import TriGlueTr ListGlue2Tr '
                                            'ListGlueLexTr.'],
                                entries, 'multi-cell block lists whose far end is learned from '
                                         'a long run (ListGlueLexTr, lgx_check)'))
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
    p.add_argument('--timeout', type=int, default=1200)
    p = sp.add_parser('one')
    p.add_argument('spec')
    p.add_argument('--timeout', type=int, default=0)
    p.add_argument('--out')
    p = sp.add_parser('batch')
    p.add_argument('found', nargs='+')
    p.add_argument('--tag', default='MP')
    p.add_argument('--chunk', type=int, default=4)
    p.add_argument('--skip', action='append', default=[])
    a = ap.parse_args()
    {'find': cmd_find, 'one': cmd_one, 'batch': cmd_batch}[a.cmd](a)


if __name__ == '__main__':
    main()
