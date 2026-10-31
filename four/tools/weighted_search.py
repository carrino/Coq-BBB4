"""Search weighted recurrence certificates; every result still requires Coq replay.

The LP producer uses floating point only to propose integer coefficients. The
kernel checker rechecks positivity and every abstract edge with exact integers.
"""
import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import signal
import time

ROOT = Path(__file__).resolve().parents[1]
SHARED = ROOT.parent/'tools/multisymbol/weighted_certificates.py'
spec = importlib.util.spec_from_file_location('weighted_producer', SHARED)
shared = importlib.util.module_from_spec(spec)
spec.loader.exec_module(shared)

class BudgetExpired(Exception):
    pass

def solve(graph, target, allow_binary):
    ms = graph['symbols']
    nodes = graph['nodes']
    edges = [(i,j) for i, adjacent in enumerate(graph['edges']) for j in adjacent
             if nodes[i][0]*ms+nodes[i][2] != target and nodes[j][0]*ms+nodes[j][2] != target]
    components = []
    for _ in range(64):
        if not edges:
            return components
        groups = shared.scc(len(nodes), edges)
        cross = [(groups[i],groups[j]) for i,j in edges if groups[i] != groups[j]]
        ranks = {group:0 for group in groups}
        for _ in range(len(ranks)):
            for left,right in cross:
                ranks[left] = max(ranks[left],ranks[right]+1)
        components.append({'kind':'rank','rank':[int(ranks[group]) for group in groups]})
        edges = [(i,j) for i,j in edges if groups[i] == groups[j]]
        if not edges:
            return components
        progress = False
        remaining = []
        for group in sorted(set(groups)):
            local = [(i,j) for i,j in edges if groups[i] == group]
            if not local:
                continue
            for kind in ['linear','w'] if allow_binary else ['linear']:
                answer = shared.lp(graph,target,local,kind,1)
                if answer is None:
                    continue
                rest,values = answer
                components.append({'kind':kind,'values':shared.integerize(values),
                                   'active':sorted({v for edge in local for v in edge})})
                progress = True
                local = rest
                break
            remaining += local
        if not progress:
            return None
        edges = remaining
    return None

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--graphs',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--report',type=Path,required=True)
    parser.add_argument('--node-limit',type=int,default=512)
    parser.add_argument('--wall-width',type=int,default=4)
    parser.add_argument('--timeout',type=float,default=3)
    args = parser.parse_args()
    if args.node_limit<1 or args.wall_width<0 or not 0<args.timeout<float('inf'):
        parser.error('positive finite budgets required')
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(BudgetExpired()))
    counts = Counter()
    done = set()
    started = time.monotonic()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    with args.output.open('w') as output, args.graphs.open() as source:
        for graph in map(json.loads,source):
            if graph['machine'] in done:
                counts['already_candidate'] += 1
                continue
            counts['graphs'] += 1
            if len(graph['nodes'])>args.node_limit:
                counts['node_budget'] += 1
                continue
            signal.setitimer(signal.ITIMER_REAL,args.timeout)
            try:
                certs = {}
                for target in range(graph['states']*graph['symbols']):
                    if target in graph['ranked']:
                        continue
                    width = next((k for k in range(1,args.wall_width+1)
                                  if shared.wall(graph,target,k)),None)
                    components = solve(graph,target,width is not None)
                    if components is None:
                        counts['no_certificate'] += 1
                        break
                    wall = shared.wallcert(graph,target,width) if width else {'k':0,'guards':[],'inside':[]}
                    certs[target] = {**wall,'components':components}
                else:
                    done.add(graph['machine'])
                    counts['candidate_machines'] += 1
                    output.write(json.dumps({'graph':graph,'certs':certs},separators=(',',':'))+'\n')
                    output.flush()
            except BudgetExpired:
                counts['timeout'] += 1
            finally:
                signal.setitimer(signal.ITIMER_REAL,0)
            if counts['graphs']%100 == 0:
                print(json.dumps(dict(counts),sort_keys=True),flush=True)
    import scipy
    report = {'status':'Untrusted LP candidates; no proof or census discharge claim.',
              'input_sha256':sha(args.graphs),'output_sha256':sha(args.output),
              'sources_sha256':{str(p.relative_to(ROOT.parent)):sha(p) for p in [Path(__file__),SHARED]},
              'scipy_version':scipy.__version__,'counts':dict(counts),
              'parameters':{'node_limit':args.node_limit,'wall_width':args.wall_width,'timeout':args.timeout},
              'seconds':round(time.monotonic()-started,3)}
    args.report.parent.mkdir(parents=True,exist_ok=True)
    args.report.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(counts),sort_keys=True),flush=True)

if __name__=='__main__':
    main()
