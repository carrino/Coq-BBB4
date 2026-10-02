"""LE6: group extent records into growth EVENTS (records within 1% of each
other's time) per side; time ratio between consecutive events and cells per
event, over the last events.  Adds 'ev' to survey.jsonl lines."""
import json, subprocess, sys
REC = '/tmp/claude-0/rec'

def events(spec, N=100000000):
    out = subprocess.run([REC, spec, str(N), '1'], capture_output=True, text=True).stdout
    R = [tuple(map(int, l.split()[1:])) for l in out.splitlines() if l.startswith('R ')]
    res = {}
    for sd in (0, 1):
        ts = [t for (t, s, e) in R if s == sd]
        ev = []
        for t in ts:
            if ev and t <= ev[-1][0] * 1.01 + 50:
                ev[-1][1] += 1
            else:
                ev.append([t, 1])
        ev = [e for e in ev if e[0] > N // 1000]
        if len(ev) >= 4:
            rat = [ev[i + 1][0] / ev[i][0] for i in range(len(ev) - 1)][-8:]
            res['LR'[sd]] = dict(n=len(ev), rat=[round(x, 3) for x in rat], cells=[e[1] for e in ev][-8:])
    return res

if __name__ == '__main__':
    D = [json.loads(l) for l in open(sys.argv[1])]
    from multiprocessing import Pool
    with Pool(4) as P:
        evs = P.map(events, [d['spec'] for d in D])
    with open(sys.argv[2], 'w') as f:
        for d, e in zip(D, evs):
            d['ev'] = e; f.write(json.dumps(d) + '\n')
