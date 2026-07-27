#!/usr/bin/env python3
"""Minimal (4,2) TM simulator + tape utilities shared by the holdout probes."""
LAB = "ABCD"

def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3*yi:3*yi+3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab

class Sim:
    def __init__(self, spec):
        self.tab = parse(spec); self.spec = spec
        self.tape = {}; self.pos = 0; self.q = 0; self.t = 0
        self.lo = 0; self.hi = 0
    def read(self):
        return self.tape.get(self.pos, 0)
    def step(self):
        tr = self.tab.get((self.q, self.read()))
        if tr is None: return None
        w, d, nq = tr
        key = (self.q, self.read())
        self.tape[self.pos] = w
        self.pos += d; self.q = nq; self.t += 1
        if self.pos < self.lo: self.lo = self.pos
        if self.pos > self.hi: self.hi = self.pos
        return key
    def tape_str(self, lo=None, hi=None):
        lo = self.lo if lo is None else lo
        hi = self.hi if hi is None else hi
        return ''.join(str(self.tape.get(i, 0)) for i in range(lo, hi+1))
    def conf(self):
        """Canonical (state, left-list-nearest-first, head, right-list) trimmed."""
        lo, hi = self.lo, self.hi
        L = [self.tape.get(i,0) for i in range(self.pos-1, lo-1, -1)]
        R = [self.tape.get(i,0) for i in range(self.pos+1, hi+1)]
        while L and L[-1]==0: L.pop()
        while R and R[-1]==0: R.pop()
        return (self.q, tuple(L), self.read(), tuple(R))
