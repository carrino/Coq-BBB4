#!/usr/bin/env python3
"""Reproduce the M-core frontier and B1-wall certificates (untrusted).

The frontier search keeps eight nearest left cells and an exact right
stack with an explicit bottom marker. It stops at B0 on that bottom;
only the two frontier prefixes 01001 and 01101101 are accepted there.
The B1-wall search forgets the left stack entirely and stops at B1.
Backward pushdown saturation, then subset determinization, produces
137 and six right-word states respectively. Coq checks their local
closure independently; this script is never a proof oracle.

Only the generated table regions are updated. The positive return,
finite macros, and glue proofs are handwritten in the Coq files.
"""
from __future__ import annotations
import argparse
from itertools import product
from pathlib import Path

TABLE = [(0,"R",1),(1,"L",3),(1,"R",2),(0,"R",2),
         (1,"L",0),(1,"R",0),(1,"R",0),(0,"L",3)]
BEGIN = "(* BEGIN GENERATED FINITE CERTIFICATE *)"
END = "(* END GENERATED FINITE CERTIFICATE *)"


def certificate(frontier):
    k = 8 if frontier else 0
    controls = [(q,h,left) for q in range(4) for h in range(2)
                for left in product(range(2), repeat=k)
                if frontier or (q,h)!=(1,1)]
    index = {c:i for i,c in enumerate(controls)}
    final = len(controls)
    size = final+1
    epsilon = [1<<i for i in range(size)]
    symbols = [[0]*size for _ in range(3 if frontier else 2)]
    pushes, bottom = [], []
    guards = [(0,1,0,0,1),(0,1,1,0,1,1,0,1)]
    for (q,h,left),i in index.items():
        write,direction,next_q = TABLE[2*q+h]
        if frontier and (q,h)==(1,0):
            if not any(left[:len(g)]==g for g in guards):
                symbols[2][i] |= 1<<final
        if direction=="R":
            if not frontier:
                epsilon[i] |= 1<<final
            for read in range(2):
                target=(next_q,read,((write,)+left)[:k])
                if target in index:
                    symbols[read][i] |= 1<<index[target]
            target=(next_q,0,((write,)+left)[:k])
            if frontier and (q,h)!=(1,0):
                bottom.append((i,index[target]))
        else:
            for far in range(2):
                target=(next_q,left[0],left[1:]+(far,)) if k else (next_q,far,())
                if target in index:
                    pushes.append((i,write,index[target]))
    while True:
        for j in range(size):
            mask,row=1<<j,epsilon[j]
            for i in range(size):
                if epsilon[i]&mask:
                    epsilon[i] |= row
        paths=[[0]*size for _ in symbols]
        for a in range(len(symbols)):
            for i in range(size):
                pending,middle=epsilon[i],0
                while pending:
                    bit=pending&-pending
                    pending-=bit
                    middle |= symbols[a][bit.bit_length()-1]
                while middle:
                    bit=middle&-middle
                    middle-=bit
                    paths[a][i] |= epsilon[bit.bit_length()-1]
        changed=False
        for i,a,j in pushes:
            expanded=epsilon[i]|paths[a][j]
            if expanded!=epsilon[i]:
                epsilon[i]=expanded
                changed=True
        for i,j in bottom:
            expanded=symbols[2][i]|paths[2][j]
            if expanded!=symbols[2][i]:
                symbols[2][i]=expanded
                changed=True
        if not changed:
            break
    empty_paths=paths[2] if frontier else epsilon
    empty=sum(1<<i for i in range(size) if empty_paths[i]&(1<<final))
    states=[empty]
    indices={empty:0}
    edges=[]
    for subset in states:
        row=[]
        for a in range(2):
            predecessor=sum(1<<i for i in range(size) if paths[a][i]&subset)
            if predecessor not in indices:
                indices[predecessor]=len(states)
                states.append(predecessor)
            row.append(indices[predecessor])
        edges.append(row)
    assert len(states)==(137 if frontier else 6)
    return controls,states,edges


def strong_text(data):
    controls,states,edges=data
    nodes=[("leaf",False),("leaf",True)]
    node_ids={v:i for i,v in enumerate(nodes)}
    def tree(bits):
        if all(b==bits[0] for b in bits):
            return int(bits[0])
        half=len(bits)//2
        node=("node",tree(bits[:half]),tree(bits[half:]))
        if node not in node_ids:
            node_ids[node]=len(nodes)
            nodes.append(node)
        return node_ids[node]
    rows=[]
    for subset in states:
        rows.append([tree([not((subset>>(qh*256+i))&1) for i in range(256)])
                     for qh in range(8)])
    out=["Inductive ms_dfa:="+"|".join(f"MS{i}" for i in range(137))+".",
         "Definition ms_states:list ms_dfa:=["+";".join(f"MS{i}" for i in range(137))+"].",
         "Lemma ms_states_complete:forall s,In s ms_states.",
         "Proof. intro s;destruct s;vm_compute;tauto. Qed.",
         "Inductive ms_tree:=ms_leaf(bool_value:bool)|ms_node(left right:ms_tree).",
         "Fixpoint ms_eval(t:ms_tree)(L:list Sym):bool:=match t with ms_leaf b=>b|ms_node l r=>match L with []=>false|S0::U=>ms_eval l U|S1::U=>ms_eval r U end end."]
    for i,node in enumerate(nodes):
        value=("ms_leaf "+str(node[1]).lower()) if node[0]=="leaf" else f"ms_node ms_t{node[1]} ms_t{node[2]}"
        out.append(f"Definition ms_t{i}:ms_tree:={value}.")
    out.append("Definition ms_trees(s:ms_dfa):list ms_tree:=match s with")
    out.extend(f"|MS{i}=>["+";".join(f"ms_t{j}"for j in row)+"]" for i,row in enumerate(rows))
    out.extend(["end.","Definition ms_cons(a:Sym)(s:ms_dfa):ms_dfa:=match a,s with"])
    out.extend(f"|S0,MS{i}=>MS{a}|S1,MS{i}=>MS{b}"for i,(a,b)in enumerate(edges))
    out.extend(["end.",
      "Fixpoint ms_fold(R:list Sym):ms_dfa:=match R with []=>MS0|a::R=>ms_cons a(ms_fold R)end.",
      "Definition ms_ok(q:St)(h:Sym)(L:list Sym)(s:ms_dfa):bool:=",
      " ms_eval(nth(match q,h with StA,S0=>0|StA,S1=>1|StB,S0=>2|StB,S1=>3|StC,S0=>4|StC,S1=>5|StD,S0=>6|StD,S1=>7 end)(ms_trees s)ms_t0)L."])
    return "\n".join(out)


def wall_text(data):
    controls,states,edges=data
    out=["Inductive mw_state:=W0|W1|W2|W3|W4|W5.",
         "Definition mw_cons(a:Sym)(s:mw_state):mw_state:=match a,s with"]
    out.extend(f"|S0,W{i}=>W{a}|S1,W{i}=>W{b}"for i,(a,b)in enumerate(edges))
    out.extend(["end.","Fixpoint mw_fold(R:list Sym):mw_state:=match R with []=>W0|a::R=>mw_cons a(mw_fold R)end.",
                "Definition mw_ok(q:St)(h:Sym)(s:mw_state):bool:=match q,h,s with"])
    for j,subset in enumerate(states):
        for i,(q,h,_) in enumerate(controls):
            out.append(f"|St{'ABCD'[q]},S{h},W{j}=>"+("false" if subset&(1<<i) else "true"))
    out.append("|StB,S1,_=>true end.")
    return "\n".join(out)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true")
    args=parser.parse_args()
    root=Path(__file__).resolve().parents[2]
    for name,frontier,render in [("BlockCoreMStrongTr",True,strong_text),("BlockCoreMWallTr",False,wall_text)]:
        path=root/"theories"/"Counters"/(name+".v")
        text=path.read_text()
        before,rest=text.split(BEGIN,1)
        _,after=rest.split(END,1)
        expected=before+BEGIN+"\n"+render(certificate(frontier))+"\n"+END+after
        if args.check:
            if text!=expected:
                raise SystemExit(f"stale certificate: {path}")
            print(f"{name}: certificate reproducible",flush=True)
        else:
            path.write_text(expected)
            print(f"{name}: certificate regenerated",flush=True)


if __name__=="__main__":
    main()
