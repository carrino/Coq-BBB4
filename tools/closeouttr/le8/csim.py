"""LE8 helpers (UNTRUSTED): concrete runs on (q, left, head, right) configurations,
sides nearest-first, blank beyond the lists."""


def parse(spec):
    tab = {}
    for q, t in enumerate(spec.split('_')):
        for s in range(2):
            x = t[3 * s:3 * s + 3]
            tab[(q, s)] = None if x[2] in '-Z' else (int(x[0]), x[1], 'ABCD'.index(x[2]))
    return tab


def step(tab, c):
    q, L, h, R = c
    e = tab[(q, h)]
    if e is None:
        return None
    w, d, nq = e
    if d == 'R':
        L = (w,) + L
        h, R = (R[0], R[1:]) if R else (0, ())
    else:
        R = (w,) + R
        h, L = (L[0], L[1:]) if L else (0, ())
    return (nq, L, h, R)


def norm(c):
    q, L, h, R = c
    L, R = list(L), list(R)
    while L and L[-1] == 0:
        L.pop()
    while R and R[-1] == 0:
        R.pop()
    return (q, tuple(L), h, tuple(R))


def run_until(tab, c, pred, maxn=10 ** 6, skip=0):
    """the first configuration after `skip` steps (>= 1 step) satisfying pred; (n, c)"""
    c = (c[0], tuple(c[1]), c[2], tuple(c[3]))
    for n in range(1, maxn):
        c = step(tab, c)
        if c is None:
            return None
        if n > skip and pred(c):
            return n, c
    return None


def show(c):
    q, L, h, R = c
    return ''.join(map(str, reversed(L))) + '[' + 'ABCD'[q] + str(h) + ']' + ''.join(map(str, R))
