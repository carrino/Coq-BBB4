#!/usr/bin/env python3
"""UNTRUSTED TNF canonicalizer for (4,2) machines (wave-7).

Reconstructs the bbchallenge / Coq-BB5 Tree-Normal-Form (TNF) state
relabeling so a per-machine lookup into mxdys' BB4_verified_enumeration.csv
covers ALL residue/holdouts, not just the strings that already match.

The TNF rule (Coq-BB5 TNF_Enumeration): the enumeration tree fills an
undefined transition only with a next-state that is either an ALREADY-USED
state or the SINGLE next-unused state.  Equivalently, the canonical labels
are assigned to states in the order each state is first *referenced as a
transition target* during the blank-tape simulation from the start state A.
Simulation-order labelling is behaviour-defined, so any relabelled copy of a
machine normalizes to the SAME string.

This is UNTRUSTED tooling: it only picks which oracle row (and hence which
params) to try; the Coq kernel still re-checks every emitted certificate.
"""
import sys

STATES = "ABCDE"   # E only appears transiently for (5,2); (4,2) uses A..D

def decode(mstr):
    g = mstr.strip().split('_')
    n = len(g)
    tm = {}
    for si, grp in enumerate(g):
        st = STATES[si]
        tm[st] = {}
        for b in (0, 1):
            c = grp[b*3:b*3+3]
            tm[st][b] = None if c == '---' else (int(c[0]), c[1], c[2])
    return tm, n

def encode(tm, n):
    def cell(tr):
        if tr is None:
            return '---'
        w, d, nx = tr
        return '{}{}{}'.format(w, d, nx)
    return '_'.join(cell(tm[STATES[i]][0]) + cell(tm[STATES[i]][1]) for i in range(n))

def canon(mstr, sim_limit=100000):
    """Return (canonical_string, relabel_map, reached_all).

    relabel_map: original_state_char -> canonical_state_char.
    reached_all: whether blank-tape simulation referenced every state before
    the sim ended (halt/undefined) -- diagnostic only.
    """
    tm, n = decode(mstr)
    label = {'A': 0}
    order = ['A']
    # blank-tape simulation; states are tracked in first-reference order.
    left = []       # left[0] is cell just left of head, growing outward
    right = []      # right[0] is cell just right of head
    head = 0
    s = 'A'
    steps = 0
    while steps < sim_limit and len(order) < n:
        tr = tm[s][head]
        if tr is None:
            break                      # undefined/halt reached: stop
        w, d, nx = tr
        # write + move
        if d == 'R':
            left.append(w)
            head = right.pop() if right else 0
        else:
            right.append(w)
            head = left.pop() if left else 0
        if nx not in label:
            label[nx] = len(order)
            order.append(nx)
        s = nx
        steps += 1
    reached_all = (len(order) == n)
    # states never referenced keep their relative original order at the tail
    for st in STATES[:n]:
        if st not in label:
            label[st] = len(order)
            order.append(st)
    # inverse: canonical index i is held by original state order[i]
    # build the relabelled machine: canonical state i inherits order[i]'s row,
    # with every next-state pointer remapped through `label`.
    inv = {i: order[i] for i in range(n)}
    newtm = {}
    for i in range(n):
        cst = STATES[i]
        orig = inv[i]
        newtm[cst] = {}
        for b in (0, 1):
            tr = tm[orig][b]
            if tr is None:
                newtm[cst][b] = None
            else:
                w, dr, nx = tr
                newtm[cst][b] = (w, dr, STATES[label[nx]])
    relabel = {STATES[i]: STATES[label[STATES[i]]] for i in range(n)}
    return encode(newtm, n), relabel, reached_all

if __name__ == '__main__':
    for m in sys.argv[1:]:
        c, rel, ra = canon(m)
        print("{}\t->\t{}\treached_all={}".format(m, c, ra))
