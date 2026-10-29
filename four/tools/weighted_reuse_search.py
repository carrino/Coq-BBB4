"""Untrusted recurring-closure template selection for BBB24.

No source proof is inferred from a sampled tail. The recurring instruction mask
comes from an explicit weighted closure, and every selected target is replayed
through wc_graph_check with that supplied graph and ranking.
"""
import copy
from collections import defaultdict
import group_families as grouping
from generate_pipeline_examples import codes


def table(machine,mirror):
    return [c^2 if mirror and c<16 else c for c in codes(machine)]


def configurations(machine,mirror,boots):
    tm=table(machine,mirror);tape={};head=0;state=0
    for t in range(max(boots)+1):
        if t in boots:yield t,tape,head,state
        tr=tm[4*state+tape.get(head,0)]
        if tr==16:break
        write=tr//4
        if write:tape[head]=write
        else:tape.pop(head,None)
        state=tr%2;head+=1 if (tr//2)%2 else -1


def grams(tape,head,side,width):
    extent=max([0]+[(p-head)*side for p in tape if (p-head)*side>0])
    return {tuple(tape.get(head+side*(d+i+1),0) for i in range(width)) for d in range(1,extent+2)}


def node(c,p,swap):
    q,l,h,r=c
    return [q^swap,[p[x] for x in l],p[h],[p[x] for x in r]]


def transform(source,p,swap):
    """Transform symbols/states, leaving orientation to the replay mirror flag."""
    row=copy.deepcopy(source);g=row['graph']
    g['nodes']=[node(c,p,swap) for c in g['nodes']]
    certs={}
    for target,cert in row['certs'].items():
        target=int(target);newtarget=4*((target//4)^swap)+p[target%4]
        cert['guards']=[[p[x] for x in word] for word in cert['guards']]
        cert['inside']=[node(c,p,swap) for c in cert['inside']]
        for comp in cert['components']:
            if comp['kind']=='rank':continue
            old=comp['values'][:];count=12 if comp['kind']=='linear' else 16
            for block in range(0,count,4):
                for symbol in range(4):comp['values'][block+p[symbol]]=old[block+symbol]
        certs[str(newtarget)]=cert
    row['certs']=certs
    return row


def original_sets(row):
    g=row['graph'];width=g['n'];tm=table(g['machine'],g['mirror'])
    _,tape,head,_=next(configurations(g['machine'],g['mirror'],{g['t']}))
    left=grams(tape,head,-1,width);right=grams(tape,head,1,width)
    for q,l,h,r in g['nodes']:
        if (tm[4*q+h]//2)%2:left.add(tuple(l))
        else:right.add(tuple(r))
    return left,right


def select(sources,machines,max_boot=4096):
    index=defaultdict(lambda:defaultdict(list));templates={}
    for i,source in enumerate(sources):
        g=source['graph'];left,right=original_sets(source)
        used={4*c[0]+c[2] for c in g['nodes']}
        partial=tuple(t if j in used else '---' for j,t in enumerate(grouping.parse(g['machine'])))
        for p in grouping.PERMS:
            for swap in (False,True):
                identity=(i,''.join(map(str,p[1:])),swap)
                ns={tuple([c[0],tuple(c[1]),c[2],tuple(c[3])]) for c in (node(c,p,swap) for c in g['nodes'])}
                ls={tuple(p[x] for x in word) for word in left};rs={tuple(p[x] for x in word) for word in right}
                templates[identity]=(g['n'],ns,ls,rs)
                for reflection in (False,True):
                    image=grouping.rename(partial,p,mirror=reflection,swap=swap)
                    if image[0] not in ('---','1LB'):continue
                    mask=grouping.defined_mask(image)
                    part=tuple(t for j,t in enumerate(image) if mask>>j&1)
                    index[mask][part].append((*identity,bool(g['mirror'])^reflection))
    pairs=[];known={r['graph']['machine'] for r in sources}
    for machine in machines:
        if machine in known:continue
        parsed=grouping.parse(machine);available=grouping.defined_mask(parsed)
        for mask,patterns in index.items():
            if mask&~available:continue
            for template in patterns.get(tuple(t for j,t in enumerate(parsed) if mask>>j&1),[]):
                pairs.append((machine,template))
    selected=[];found=set();boots={0,1,2};power=4
    while power<=max_boot:boots.add(power);power*=2
    boots.add(max_boot)
    for machine,(i,p,swap,mirror) in pairs:
        if machine in found:continue
        width,nodes,left,right=templates[i,p,swap]
        for boot,tape,head,state in configurations(machine,mirror,boots):
            center=(state,tuple(tape.get(head-1-k,0) for k in range(width)),tape.get(head,0),tuple(tape.get(head+1+k,0) for k in range(width)))
            if center not in nodes:continue
            if not grams(tape,head,-1,width)<=left or not grams(tape,head,1,width)<=right:continue
            selected.append([machine,i,p,swap,mirror,boot]);found.add(machine);break
    return sorted(selected),dict(candidate_pairs=len(pairs),candidate_cores=len({m for m,_ in pairs}),
                                 selected_cores=len(selected),used_templates=len({tuple(r[1:4]) for r in selected}),max_boot=max_boot)
