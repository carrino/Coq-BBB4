"""Memory-bounded untrusted matching of recurring weighted templates.

Only live instruction masks and compact transition tables are indexed eagerly.
Original closure graphs/gram sets are loaded lazily, and target boots are
inverse-renamed against those originals. Ranking vectors stay packed until
certificate generation. No source x target x permutation scan is performed.
"""
from collections import defaultdict
from functools import lru_cache

import group_families as grouping
from weighted_reuse_search import configurations,grams,original_sets


def graph(row):
    if 'graph' in row:return row['graph']
    width=row['n']
    nodes=[]
    for encoded in row['nodes']:
        digits=tuple(map(int,encoded[1:]))
        nodes.append([ord(encoded[0])-65,list(digits[:width]),digits[width],list(digits[width+1:])])
    return dict(machine=row['machine'],mirror=row['mirror'],n=width,t=row['t'],nodes=nodes)


def header(row):
    return row['graph'] if 'graph' in row else row


def used_slots(row):
    if 'graph' in row:return {4*c[0]+c[2] for c in row['graph']['nodes']}
    width=row['n']
    return {4*(ord(c[0])-65)+int(c[width+1]) for c in row['nodes']}


class TemplateIndex:
    def __init__(self,rows,cache_size=128):
        self.rows=rows;self.patterns=defaultdict(lambda:defaultdict(list))
        self.known={header(r)['machine'] for r in rows}
        self.inverse={''.join(map(str,p[1:])):tuple(p.index(i) for i in range(4)) for p in grouping.PERMS}
        for i,row in enumerate(rows):
            h=header(row);used=used_slots(row)
            partial=tuple(t if j in used else '---' for j,t in enumerate(grouping.parse(h['machine'])))
            for permutation in grouping.PERMS:
                p=''.join(map(str,permutation[1:]))
                for swap in (False,True):
                    for reflection in (False,True):
                        image=grouping.rename(partial,permutation,mirror=reflection,swap=swap)
                        if image[0] not in ('---','1LB'):continue
                        mask=grouping.defined_mask(image)
                        key=tuple(t for j,t in enumerate(image) if mask>>j&1)
                        self.patterns[mask][key].append((i,p,swap,bool(h['mirror'])^reflection))
        @lru_cache(maxsize=cache_size)
        def context(index):
            g=graph(self.rows[index]);left,right=original_sets({'graph':g})
            nodes={(q,tuple(l),h,tuple(r)) for q,l,h,r in g['nodes']}
            return g['n'],nodes,left,right
        self.context=context

    def candidates(self,machine):
        parsed=grouping.parse(machine);available=grouping.defined_mask(parsed);result=[]
        for mask,patterns in self.patterns.items():
            if mask&~available:continue
            result.extend(patterns.get(tuple(t for j,t in enumerate(parsed) if mask>>j&1),()))
        return result

    def match(self,machine,candidates,boots):
        # Simulate the actual machine once. Reflection swaps its two half-tapes,
        # so it needs no separate run. Prefer the earliest usable target boot.
        for boot,tape,head,state in configurations(machine,False,boots):
            windows={};normalized_nodes={};seed={};normalized_seed={}
            for index,p,swap,mirror in candidates:
                width=header(self.rows[index])['n']
                identity=width,p,mirror
                if identity not in normalized_nodes:
                    if width not in windows:
                        windows[width]=(tuple(tape.get(head-1-k,0) for k in range(width)),
                                        tape.get(head,0),tuple(tape.get(head+1+k,0) for k in range(width)))
                    left,center,right=windows[width]
                    if mirror:left,right=right,left
                    inverse=self.inverse[p]
                    normalized_nodes[identity]=(tuple(inverse[x] for x in left),inverse[center],tuple(inverse[x] for x in right))
                _,nodes,ls,rs=self.context(index)
                left,center,right=normalized_nodes[identity]
                if (state^swap,left,center,right) not in nodes:continue
                if identity not in normalized_seed:
                    if width not in seed:seed[width]=(grams(tape,head,-1,width),grams(tape,head,1,width))
                    left_seed,right_seed=seed[width]
                    if mirror:left_seed,right_seed=right_seed,left_seed
                    inverse=self.inverse[p]
                    normalized_seed[identity]=(
                        {tuple(inverse[x] for x in word) for word in left_seed},
                        {tuple(inverse[x] for x in word) for word in right_seed})
                left_seed,right_seed=normalized_seed[identity]
                if left_seed<=ls and right_seed<=rs:return [machine,index,p,swap,mirror,boot]
        return None


def select(rows,machines,max_boot=4096,excluded=(),cache_size=128):
    index=TemplateIndex(rows,cache_size=cache_size);excluded=set(excluded)
    boots={0,1,2};power=4
    while power<=max_boot:boots.add(power);power*=2
    boots.add(max_boot)
    result=[];pairs=0;cores=0
    for machine in machines:
        if machine in index.known or machine in excluded:continue
        candidates=index.candidates(machine)
        if not candidates:continue
        cores+=1;pairs+=len(candidates)
        match=index.match(machine,candidates,boots)
        if match:result.append(match)
    cache=index.context.cache_info()
    return sorted(result),dict(candidate_pairs=pairs,candidate_cores=cores,selected_cores=len(result),
                              source_templates=len(rows),source_masks=len(index.patterns),
                              pattern_keys=sum(len(p) for p in index.patterns.values()),max_boot=max_boot,
                              context_cache_limit=cache_size,context_cache_hits=cache.hits,context_cache_misses=cache.misses,
                              used_templates=len({tuple(r[1:4]) for r in result}))
