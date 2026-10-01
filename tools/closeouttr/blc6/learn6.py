"""BLC6: MP's language (learn4 with F the anchors' local language, the far
end from a long run) whose LEFT automaton is learned from every round's
TURN tape over a long run (UNTRUSTED; SCOPING_INSTR.md §7.4.BLC6).

learn4.fit_left2 aligns left samples (the elements left of the head, in
their left spelling) with the anchor list they were swept from.  learn4's
samples are lsnap's periodic snapshots with the head deep enough, which on
the ratio-4 lists are rare: ~85 on 0RB0LD_1RC1LB_1LA1RA_1LA0LD, all from
short carries, and the left digits of a long carry (-2, -3 at `111111`)
never appear; the real run (lg_batch's data pass) then cannot fold its left
side at all (558 left-fold misses in 6,000 leaves, against 2 on the right).
Here the samples are blc6/turns.c's: one per round, at the round's
rightmost step, over T1 (default 1e8) steps.
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
for d in ('..', '../blc3', '../blc4', '../mp'):
    sys.path.insert(0, os.path.join(HERE, d))
import learn3 as L3                                 # noqa: E402
import learn4 as L4                                 # noqa: E402
import learn_mp                                     # noqa: E402

T1 = int(os.environ.get('BLC6_T1', '100000000'))
TURNS = os.path.join(os.environ.get('MP_BIN', '/tmp'), 'blc6_turns')


def turns_bin():
    if not os.path.exists(TURNS):
        subprocess.check_call(['cc', '-O2', '-o', TURNS, os.path.join(HERE, 'turns.c')])
    return TURNS


def turn_rows(spec, t0, t1):
    out = subprocess.run([turns_bin(), spec, str(t0), str(t1), '0'],
                         capture_output=True, text=True, timeout=3600).stdout
    return [L4.Row(line) for line in out.splitlines()]


def _left_part_keep_head(orig):
    """learn4.left_part on a cut tape whose last cell is the head's: a 0
    there is stripped by learn3.strip_cells and the head token lost (lsnap's
    samples rarely end at the head; a turn sample always does).  A 1 cell
    right of the head keeps it; left_part reads only the elements wholly
    left of the head."""
    def lp(cells, pos, WL, pseps, seps):
        cut, i = [], 0
        for s_, ln in cells:
            if i > pos:
                break
            cut.append((s_, min(ln, pos + 1 - i)))
            i += ln
        if i >= pos + 1 and cut and cut[-1][0] == 0:
            cut.append((1, 1))
        return orig(cut, pos, WL, pseps, seps)
    return lp


def learn(spec, t1=T1, F='local'):
    """learn4.learn (F local or free), its deep samples replaced by the turn
    tapes, then learn_mp.extend's long-run far end"""
    old_fit, old_snaps = L4.fit_F, L4.snaps
    L4.fit_F = {'local': learn_mp.fit_local, 'free': learn_mp.fit_free}.get(F, old_fit)

    def snaps(sp, a, b, every, k=0):
        if k:
            return turn_rows(sp, a, t1)
        return old_snaps(sp, a, b, every, k)
    old_lp = L4.left_part
    L4.snaps = snaps
    L4.left_part = _left_part_keep_head(old_lp)
    try:
        lang, mir, info = L4.learn(spec)
    finally:
        L4.fit_F, L4.snaps, L4.left_part = old_fit, old_snaps, old_lp
    info = dict(info, F=F, tturn=t1)
    lang, st = learn_mp.extend(spec, lang, mir, info)
    return lang, mir, dict(info, extend=st)


if __name__ == '__main__':
    import time
    t = time.time()
    lang, mir, info = learn(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else T1)
    print({k: v for k, v in info.items() if k not in ('seps', 'extend')}, round(time.time() - t, 1))
    print('lstart', len(lang.lstart), 'lfwd', len(lang.lfwd))
    for x in lang.lstart:
        print('  S', x)
    for k, v in sorted(lang.lfwd.items(), key=str):
        print('  ', k, '->', v)
