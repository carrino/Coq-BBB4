#!/usr/bin/env python3
"""Minimal constant-coefficient linear recurrence (C-finite certificate).

Used by sn_scan.py to test mxdys' "the usage count ... is a simple function"
claim on the (4,2) holdouts; see docs/HOLDOUTS_MXDYS_SN.md.

A sequence is a 'simple function' of n in mxdys' sense iff it satisfies a
short linear recurrence with constant rational coefficients; the closed form
is then sum_i p_i(n) r_i^n over the characteristic roots.  We find the
MINIMAL such recurrence exactly over Q, and require at least `slack` terms
of the sequence beyond what the fit consumes, so a fit is a prediction that
was checked, not an interpolation.
"""
from fractions import Fraction

def solve(M):
    """Exact RREF solve of M (rows = equations, last col = rhs). Returns
    a particular solution or None if inconsistent."""
    M=[[Fraction(x) for x in r] for r in M]
    rows=len(M); cols=len(M[0])-1
    piv=[]; r=0
    for c in range(cols):
        p=None
        for i in range(r,rows):
            if M[i][c]!=0: p=i;break
        if p is None: continue
        M[r],M[p]=M[p],M[r]
        pv=M[r][c]; M[r]=[x/pv for x in M[r]]
        for i in range(rows):
            if i!=r and M[i][c]!=0:
                f=M[i][c]; M[i]=[a-f*b for a,b in zip(M[i],M[r])]
        piv.append(c); r+=1
        if r==rows: break
    for i in range(r,rows):
        if all(M[i][c]==0 for c in range(cols)) and M[i][cols]!=0: return None
    sol=[Fraction(0)]*cols
    for i,c in enumerate(piv): sol[c]=M[i][cols]
    return sol

def find_rec(a, maxd=6, slack=3):
    """Return (d, coeffs) for the minimal recurrence
       a[n+d] = sum_{i=1..d} c_i a[n+d-i], validated on >= slack extra terms."""
    n=len(a)
    for d in range(0, maxd+1):
        if n < 2*d + slack: break
        eqs=[[a[k+d-i-1] for i in range(d)]+[a[k+d]] for k in range(n-d)]
        if d==0:
            if all(x==0 for x in a): return 0,[]
            continue
        sol=solve(eqs[:d*2] if len(eqs)>=d*2 else eqs)
        if sol is None: continue
        ok=all(sum(sol[i]*a[k+d-i-1] for i in range(d))==a[k+d] for k in range(n-d))
        if ok: return d,sol
    return None,None

def roots_desc(d,c):
    """Human description of the characteristic polynomial x^d - c1 x^(d-1) - ..."""
    if d==0: return 'zero'
    terms=' - '.join('%s*x^%d'%(c[i], d-i-1) for i in range(d) if c[i]!=0)
    return 'x^%d = %s'%(d, terms if terms else '0')
