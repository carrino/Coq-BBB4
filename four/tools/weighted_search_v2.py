"""Untrusted SCC-local weighted search with exact post-LP inequality checks.

The Coq checker remains authoritative. This producer preserves a checked closed
graph even if the ordinary ranking search exhausted its orientation time budget.
"""
import argparse
from collections import Counter
from contextlib import contextmanager
from fractions import Fraction
from functools import reduce
import hashlib
import json
from math import gcd, lcm
from pathlib import Path
import signal
import time

from weighted_search import shared, BudgetExpired
from weighted_codec_v2 import pack

alarm_active=False


def install_budget():
    def handler(*_):
        if alarm_active:raise BudgetExpired()
    signal.pthread_sigmask(signal.SIG_BLOCK,{signal.SIGALRM})
    signal.signal(signal.SIGALRM,handler)


@contextmanager
def budget(seconds):
    global alarm_active
    try:
        signal.pthread_sigmask(signal.SIG_UNBLOCK,{signal.SIGALRM})
        signal.pthread_sigmask(signal.SIG_BLOCK,{signal.SIGALRM})
        alarm_active=True
        signal.setitimer(signal.ITIMER_REAL,seconds)
        signal.pthread_sigmask(signal.SIG_UNBLOCK,{signal.SIGALRM})
        yield
    finally:
        alarm_active=False
        signal.pthread_sigmask(signal.SIG_BLOCK,{signal.SIGALRM})
        signal.setitimer(signal.ITIMER_REAL,0)


def inequalities(graph, edges, kind):
    nodes=graph['nodes']; count=len(nodes)
    rows=[]; edge_rows=[]; active={v for edge in edges for v in edge}
    def row(pairs,edge=False):
        result={}
        for index,value in pairs:result[index]=result.get(index,0)+value
        rows.append(result)
        if edge:edge_rows.append(result)
    if kind=='w':
        for left in range(4):
            for right in range(4):
                row([(left,-1),(8+right,-1),(8+left,2)])
                row([(4+left,-1),(12+right,-2),(12+left,1)])
        row([(8,1)]);row([(12,1)])
        for i in active:
            _,left,_,right=nodes[i]
            row([(8+left[0],-1),(12+right[0],-1),(16+i,-1)])
        for i,j in edges:
            q,left,head,right=nodes[i]
            write,direction,_=graph['trans'][4*q+head]
            if direction==-1:row([(left[0],-1),(4+write,1),(16+j,1),(16+i,-2)],True)
            else:row([(write,1),(4+right[0],-1),(16+j,2),(16+i,-1)],True)
    else:
        for i,j in edges:
            q,left,head,right=nodes[i]
            write,direction,_=graph['trans'][4*q+head]
            pairs=[(write,1),(head,-1),(12+j,1),(12+i,-1)]
            pairs+=([(4+left[0],-1),(8+write,1)] if direction==-1 else
                    [(4+write,1),(8+right[0],-1)])
            row(pairs,True)
    return rows,edge_rows


def exact_lp(graph,target,edges,kind,diagnostics):
    answer=shared.lp(graph,target,edges,kind,1)
    if answer is None:return None
    _,floats=answer
    rows,edge_rows=inequalities(graph,edges,kind)
    for denominator in (1000,100000,10000000):
        fractions=[Fraction(float(x)).limit_denominator(denominator) for x in floats]
        common=lcm(*(x.denominator for x in fractions))
        values=[int(x*common) for x in fractions]
        divisor=reduce(gcd,values) or 1
        values=[x//divisor for x in values]
        if max(map(abs,values),default=0).bit_length()>4096:continue
        if kind=='linear' and (any(x<0 for x in values) or any(values[i] for i in (0,4,8))):continue
        if kind=='w' and values[4]!=0:continue
        if any(sum(values[i]*v for i,v in row.items())>0 for row in rows):continue
        deltas=[sum(values[i]*v for i,v in row.items()) for row in edge_rows]
        if not any(delta<0 for delta in deltas):continue
        return [edge for edge,delta in zip(edges,deltas) if delta==0],values
    diagnostics['lp_integerization_rejected']+=1
    return None


def solve(graph,target,allow_binary,diagnostics):
    nodes=graph['nodes']
    edges=[(i,j) for i,adjacent in enumerate(graph['edges']) for j in adjacent
           if nodes[i][0]*4+nodes[i][2]!=target and nodes[j][0]*4+nodes[j][2]!=target]
    components=[]
    for _ in range(64):
        if not edges:return components
        groups=shared.scc(len(nodes),edges)
        cross={(int(groups[i]),int(groups[j])) for i,j in edges if groups[i]!=groups[j]}
        ranks={int(group):0 for group in groups}
        for _ in range(len(ranks)):
            changed=False
            for left,right in cross:
                value=ranks[right]+1
                if ranks[left]<value:ranks[left]=value;changed=True
            if not changed:break
        components.append({'kind':'rank','rank':[ranks[int(group)] for group in groups]})
        edges=[(i,j) for i,j in edges if groups[i]==groups[j]]
        if not edges:return components
        buckets={}
        for edge in edges:buckets.setdefault(int(groups[edge[0]]),[]).append(edge)
        progress=False;remaining=[]
        for group,local in sorted(buckets.items()):
            for kind in ('linear','w') if allow_binary else ('linear',):
                answer=exact_lp(graph,target,local,kind,diagnostics)
                if answer is None:continue
                rest,values=answer
                components.append({'kind':kind,'values':values,
                                   'active':sorted({v for edge in local for v in edge})})
                progress=True;local=rest;break
            remaining+=local
        if not progress:return None
        edges=remaining
    diagnostics['lex_round_budget']+=1
    return None


def solve_graph(graph,wall_width,diagnostics):
    certs={}
    for target in range(8):
        if target in graph['ranked']:continue
        width=next((k for k in range(1,wall_width+1) if shared.wall(graph,target,k)),None)
        components=solve(graph,target,width is not None,diagnostics)
        if components is None:
            diagnostics['failed_target_'+str(target)]+=1
            diagnostics['failed_with_wall' if width else 'failed_without_wall']+=1
            return None
        wall=shared.wallcert(graph,target,width) if width else {'k':0,'guards':[],'inside':[]}
        certs[target]={**wall,'components':components}
    return {'graph':graph,'certs':certs}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--graphs',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--report',type=Path,required=True)
    parser.add_argument('--node-limit',type=int,default=2048)
    parser.add_argument('--wall-width',type=int,default=16)
    parser.add_argument('--timeout',type=float,default=3)
    args=parser.parse_args()
    if args.node_limit<1 or args.wall_width<0 or not 0<args.timeout<float('inf'):parser.error('Invalid budget')
    install_budget()
    counts=Counter();done=set();start=time.monotonic()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    with args.graphs.open() as stream,args.output.open('w') as output:
        for event in map(json.loads,stream):
            counts[event['status']]+=1
            if event['machine'] in done:continue
            graph=event.get('graph')
            if not graph:continue
            counts['graphs']+=1
            if len(graph['nodes'])>args.node_limit:counts['node_budget']+=1;continue
            try:
                with budget(args.timeout):row=solve_graph(graph,args.wall_width,counts)
                if row is not None:
                    counts['weighted_candidate']+=1;done.add(graph['machine'])
                    output.write(json.dumps(pack(row),separators=(',',':'))+'\n');output.flush()
                else:counts['no_certificate']+=1
            except BudgetExpired:counts['lp_timeout']+=1
    report={'status':'Untrusted search only; no checked or census-linked claims.',
            'input_sha256':hashlib.sha256(args.graphs.read_bytes()).hexdigest(),
            'output_sha256':hashlib.sha256(args.output.read_bytes()).hexdigest(),
            'parameters':{'node_limit':args.node_limit,'wall_width':args.wall_width,'timeout':args.timeout},
            'counts':dict(counts),'seconds':round(time.monotonic()-start,3)}
    args.report.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,sort_keys=True),flush=True)


if __name__=='__main__':main()
