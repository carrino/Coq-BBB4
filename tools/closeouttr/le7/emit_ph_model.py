#!/usr/bin/env python3
"""UNTRUSTED emitter wrapper (SCOPING_INSTR 7.4.LE7): LE5's `emit_ph.py`
([LadderCheckPhRunTr]) over a phase MODEL given directly in the input record
(`model`: l, D, pre, T, phases [{key, W, V}], mvT, mvE), not read by
`phrun2.py`.  The boot is the first anchor visit past the quiet window that
parses in some phase with a nonempty x (phases tried in order).

LE7's use: the marker-run rows whose top word steps through a few values and
whose LAST value is the run word itself (`0RB1LA_0LC1RD_0RD1LD_1RB0LA`:
`x ++ W_p ++ (01)^m`, W over `1`, `11`, `10`, `01`), which LE5's beam reader
cannot parse (the last phase word and the run are the same cells) and
`LadderCheckRun3Tr` cannot state (its narrowing resets the top word).

    python3 emit_ph_model.py SPEC MODELS.jsonl -o OUT.v [--qh]
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'le5'))
sys.path.insert(0, os.path.join(HERE, '..', 'le3'))
import emit_ph as EPH  # noqa: E402
import termrun_detect as TD  # noqa: E402


def parse(st, md, p):
    """(x, m) for phase p with the FEWEST run words, or None; st padded with
    up to l blanks"""
    l, D, pre, T = md['l'], md['D'], md['pre'], md['T']
    W, V = md['phases'][p]['W'], md['phases'][p]['V']
    for k in range(0, l + len(W) + len(V) + 1):
        s = st + '0' * k
        if not s.startswith(pre):
            return None
        b = s[len(pre):]
        if V:
            if not b.endswith(V):
                continue
            b = b[:len(b) - len(V)]
        m = 0
        while True:
            if b.endswith(W) and (len(b) - len(W)) % l == 0:
                xs = b[:len(b) - len(W)]
                ws = [xs[i:i + l] for i in range(0, len(xs), l)]
                if all(w in D for w in ws):
                    return [D.index(w) for w in ws], m
            if not T or not b.endswith(T):
                break
            b, m = b[:len(b) - len(T)], m + 1
    return None


def boot(spec, md, lastf, steps=300000):
    q0, s0, side, _o = md['phases'][0]['key']
    for t, st in visits(spec, q0, s0, side, steps):
        if t <= lastf:
            continue
        for p in range(len(md['phases'])):
            r = parse(st, md, p)
            if r is not None and r[0]:
                return t, tuple(r[0]), p, r[1]
    raise EPH.NoClosure('no boot past %d' % lastf)


def visits(spec, q0, s0, side, steps):
    tm = TD.parse(spec)
    tape, h, q = {}, 0, 0
    for t in range(steps):
        s = tape.get(h, 0)
        if q == q0 and s == s0:
            cs = [i for i, v in tape.items() if v]
            if side == 'R' and (not cs or min(cs) >= h):
                yield t, ''.join(str(tape.get(i, 0)) for i in range(h + 1, max(cs + [h]) + 1))
            elif side == 'L' and (not cs or max(cs) <= h):
                yield t, ''.join(str(tape.get(i, 0)) for i in range(h - 1, min(cs + [h]) - 1, -1))
        w, d, nq = tm[(q, s)]
        tape[h] = w
        h += d
        q = nq


def model_given(spec, det, lastf):
    md = dict(det['model'], spec=spec)
    md['mvT'] = {int(k): tuple(v) for k, v in md['mvT'].items()}
    md['mvE'] = {int(k): tuple(v) for k, v in md['mvE'].items()}
    md['boot'] = boot(spec, md, lastf)
    return md


EPH.model_phrun = model_given

# LE7: carries from index 1 ([LadderCheckPhRun1Tr]): the template, the carry
# search (index 1 up, threshold >= 1) and the carry lemma bodies (r = 0
# refuted), each patched from emit_ph's own source
EPH.TM = os.path.join(HERE, 'emit_ph1_tmpl.txt')


def _patch(fn, subs):
    import inspect
    import textwrap
    src = textwrap.dedent(inspect.getsource(fn))
    for a, b in subs:
        assert src.count(a) == 1, (fn.__name__, a)
        src = src.replace(a, b)
    exec(compile(src, EPH.__file__, 'exec'), EPH.__dict__)


_patch(EPH.closure_data, [
    ("        gg = tmove_at('TC', 0)(n0, st)",
     "        if n0 < 1:\n            continue\n        gg = tmove_at('TC', 1)(n0, st)")])
_patch(EPH.emit_closure, [
    ("lambda p, r: reach('carm_%d_%d' % (p, r)), n0c + stc)",
     "lambda p, r: reach('carm_%d_%d' % (p, r)), n0c + stc, 1)"),
    ("ccomp=ph_body('T', 'TC', lambda p, r: cmp, n0c + stc)",
     "ccomp=ph_body('T', 'TC', lambda p, r: cmp, n0c + stc, 1)"),
    ("lambda p, r: fire, n0c + stc, extra=lambda p: fT[p])",
     "lambda p, r: fire, n0c + stc, 1, extra=lambda p: fT[p])")])

if __name__ == '__main__':
    sys.exit(EPH.main())
