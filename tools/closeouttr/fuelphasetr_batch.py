#!/usr/bin/env python3
"""Untrusted parity-indexed n-gram search for FuelPhaseTr.

Track absolute cell positions modulo two in the tail grammar sets and
carry head parity in each refined FuelWide node. The finite closure and
per-instruction rank/measure certificates are independently replayed,
then the emitted Coq batch checks the parity-aware successors in kernel.
Only the blank anchor is supported; use --warmups 0. Other CLI arguments
are the same as fueltr_batch.py. NumPy/SciPy are needed only if search
reaches the optional weighted-measure fallback.
"""
import sys
import fuelmixtr_batch as fm
ft = fm.ft

def successors(tbl, n, modulus, lset, rset, a):
    b, p = a
    q, s, lw, rw = b
    tr = tbl[q, s]
    if tr is None:
        return None
    w, d, nq = tr
    if d == 'R':
        return [((nq, rw[0], (w,) + lw[:-1], rw[1:] + (x,)), (p + 1) % modulus) for x in (0, 1) if ((p + 2) % modulus, rw[1:] + (x,)) in rset]
    return [((nq, lw[0], lw[1:] + (x,), (w,) + rw[:-1]), (p - 1) % modulus) for x in (0, 1) if ((p - 2) % modulus, lw[1:] + (x,)) in lset]

def closure(tbl, n, modulus, t=0, cap=100000):
    tape, pos, q = ft.gf.sim_tape(tbl, t)
    p = pos % modulus
    l = lambda i: tape.get(pos - 1 - i, 0)
    r = lambda i: tape.get(pos + 1 + i, 0)
    win = lambda f, d: tuple((f(d + i) for i in range(n)))
    extent = max([abs(x - pos) for x in tape] + [0]) + n + modulus + 2
    lset = {((p - 1 - d) % modulus, win(l, d)) for d in range(1, extent)}
    rset = {((p + 1 + d) % modulus, win(r, d)) for d in range(1, extent)}
    a0 = ((q, tape.get(pos, 0), win(l, 0), win(r, 0)), p)
    for _ in range(400):
        seen = set()
        todo = [a0]
        while todo:
            a = todo.pop()
            if a in seen:
                continue
            seen.add(a)
            if len(seen) > cap:
                return None
            out = successors(tbl, n, modulus, lset, rset, a)
            if out is None:
                return None
            todo.extend(out)
        nl = {((p - 1) % modulus, b[2]) for b, p in seen if tbl[b[:2]][1] == 'R'}
        nr = {((p + 1) % modulus, b[3]) for b, p in seen if tbl[b[:2]][1] == 'L'}
        if nl <= lset and nr <= rset:
            break
        lset |= nl
        rset |= nr
    else:
        return None
    lc = min(sum((v == 1 for x, v in tape.items() if x < pos)), 2)
    rc = min(sum((v == 1 for x, v in tape.items() if x > pos)), 2)
    start = (a0[0], lc, rc, a0[1])
    seen = set()
    todo = [start]
    adj = {}
    while todo:
        a = todo.pop()
        if a in seen:
            continue
        seen.add(a)
        if len(seen) > cap:
            return None
        b, fl, fr, p = a
        fl2, fr2 = ft.gf.fw_upd(tbl, b)(fl, fr)
        out = [(b2, fl2, fr2, p2) for b2, p2 in successors(tbl, n, modulus, lset, rset, (b, p))]
        adj[a] = out
        todo.extend(out)
    return (seen, adj, lset, rset, start)

def find_one(spec, n0, n_extra, warmups, max_pattern=4):
    if 0 not in warmups:
        raise ValueError('phase checker requires the blank anchor (warmup 0)')
    first_fail = None
    for modulus in (2,):
        for mirrored in (True, False):
            tbl = ft.bp.parse(ft.gf.mirror_mtext(spec) if mirrored else spec)
            for n in range(n0, n0 + n_extra + 1):
                for t in (0,):
                    result = closure(tbl, n, modulus, t)
                    if result is None:
                        continue
                    seen, adj, lset, rset, start = result
                    targets = sorted({a[0][:2] for a in seen} | ft.warmup_fires(tbl, t))
                    delta = ft.make_pattern_delta(tbl, n)
                    cands = ft.pattern_candidates(n, max_pattern)
                    cert = {}
                    for target in targets:
                        found = ft.instruction_procedure(tbl, n, adj, seen, target, cands, delta)
                        if found is None or not ft.instruction_check(tbl, n, adj, seen, target, *found):
                            first_fail = first_fail or dict(n=n, t=t, mirrored=mirrored, target=list(target), contexts=len(seen), modulus=modulus)
                            break
                        cert[target] = found
                    else:
                        return dict(spec=spec, status='found', n=n, t=t, mirrored=mirrored, contexts=len(seen), modulus=modulus, fuel=8 * len(seen) + 64, left_grams=[sorted((w for p, w in lset if p == k)) for k in (0, 1)], right_grams=[sorted((w for p, w in rset if p == k)) for k in (0, 1)], cert=fm.emit_cert(cert))
    return dict(spec=spec, status='no certificate', first_fail=first_fail)
base_fenc = ft.gf.fenc
ft.gf.fenc = lambda a: 2 * base_fenc(a[:3]) + a[3]

def emit_grams(grams):
    return '[' + '; '.join((ft.gf.gb.coq_patt(w) for w in grams)) + ']'

def write_records(tag, nn, indexed, overwrite=False):
    entries, preamble = ([], [])
    for idx, rec in indexed:
        assert rec['t'] == 0 and rec['modulus'] == 2
        name = 'fuelphase_%s_%02d_%04d' % (tag, nn, idx)
        preamble.append('Definition %s : Instr -> list fmxcomp * list positive :=\n%s.' % (name, rec['cert']))
        grams = rec['left_grams'] + rec['right_grams']
        names = []
        for suffix, words in zip(('l0', 'l1', 'r0', 'r1'), grams):
            gn = name + '_' + suffix
            names.append(gn)
            preamble.append('Definition %s : list (list Sym) := %s.' % (gn, emit_grams(words)))
        proof = 'apply coversTr_nqh. '
        if rec['mirrored']:
            proof += 'apply neverqhtr_mirror. '
        proof += 'apply (ngram_check_neverqh_phase2tr_sound _ %d %d %s %s). ' % (rec['n'], rec['fuel'], ' '.join(names), name)
        proof += 'vm_compute. reflexivity.'
        entries.append((rec['spec'], proof))
    print(ft.write_batch(tag, nn, ['From BBB4.Checkers Require Import NGram FuelMixTr FuelPhaseTr.', 'From BBB4.CensusTr Require Import TNF_QHTr.'], entries, 'parity-indexed tail grammars and fuel certificates (FuelPhaseTr)', overwrite=overwrite, preamble='\n\n'.join(preamble)))
ft.find_one, ft.write_records = (find_one, write_records)
if __name__ == '__main__':
    ft.main()
