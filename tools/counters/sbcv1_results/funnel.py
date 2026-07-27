"""Where does each machine fall out of the SBCv1 shape?"""
import re, sys, glob, collections
def stages(files):
    n = collections.Counter(); tot = 0
    for f in files:
        for line in open(f):
            if '\t' not in line: continue
            tot += 1
            if 'SBCV1' in line: n['HIT'] += 1; continue
            # a machine clears a stage if EITHER orientation clears it
            best = (0, 0, 0, 0)
            for m in re.finditer(r'(?:fwd|mir):(\S+)', line):
                d = dict(kv.split('=') for kv in m.group(1).split(','))
                best = tuple(max(b, int(d.get(k, 0)))
                             for b, k in zip(best, ('rc', 'lc', 'part', 's0')))
            rc, lc, part, s0 = best
            if s0: n['4 reached S0, cert rejected'] += 1
            elif part: n['3 join ok, never reaches S0'] += 1
            elif rc and lc: n['2 both sweeps, join empty'] += 1
            elif lc: n['1 left sweep only'] += 1
            elif rc: n['1 right sweep only'] += 1
            else: n['0 no shift rule at all'] += 1
    return tot, n
for label, pat in (('C_residue', 'sbcout_*.tsv'),
                   ('A_boarded', 'sbc_boarded.tsv'),
                   ('B_holdout', 'sbc_holdout.tsv')):
    files = sorted(glob.glob(sys.argv[1] + '/' + pat))
    if not files: continue
    tot, n = stages(files)
    print('%s  n=%d' % (label, tot))
    for k in sorted(n): print('    %-32s %5d  (%.1f%%)' % (k, n[k], 100.0*n[k]/max(tot,1)))
