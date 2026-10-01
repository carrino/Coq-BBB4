"""BLC6: the language of mp/learn_mp (local F, long-run END table) with the
LEFT automaton and the right tails' alternative forms learned from a LONG
run (UNTRUSTED; SCOPING_INSTR.md §7.4.BLC6)."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
for d in ('..', '../blc3', '../blc4', '../mp'):
    sys.path.insert(0, os.path.join(HERE, d))
import learn4 as L4                                 # noqa: E402
import learn_mp                                     # noqa: E402

T1 = int(os.environ.get('BLC6_T1', '100000000'))
EVERY = int(os.environ.get('BLC6_EVERY', '2477'))


def learn(spec, t1=T1, every=EVERY, F='local'):
    old = L4.fit_F
    L4.fit_F = {'local': learn_mp.fit_local, 'free': learn_mp.fit_free}.get(F, old)
    try:
        lang, mir, info = L4.learn(spec, t1=t1, every=every)
    finally:
        L4.fit_F = old
    info = dict(info, F=F, t1=t1, every=every)
    lang, st = learn_mp.extend(spec, lang, mir, info)
    return lang, mir, dict(info, extend=st)


if __name__ == '__main__':
    import time
    t = time.time()
    lang, mir, info = learn(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else T1)
    print({k: v for k, v in info.items() if k != 'seps'}, round(time.time() - t, 1))
    print('lstart', len(lang.lstart), 'lfwd', len(lang.lfwd))
    for x in lang.lstart: print('  S', x)
    for k, v in lang.lfwd.items(): print('  ', k, '->', v)
