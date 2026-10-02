#!/usr/bin/env python3
"""Reproduce the C1 potential certificate and combine independent windows.

    python3 tools/closeouttr/fuelpotentialtr_targets.py find certificates.jsonl
    python3 tools/closeouttr/fuelpotentialtr_targets.py batch certificates.jsonl --number 95

NumPy/SciPy are required only for finding certificates.
"""
import argparse
import json
import re
from pathlib import Path
from cbt import write_batch
import fuelmixtr_batch as fm
from fuelpotentialtr_batch import choose_mix
from paired_carry_batch import find as find_partial

SPEC = "1RB0LA_0RC1RB_0RD1RC_1LD1LA"

def compact_ranks(record):
    """Share rank maps through exact finite patches; replay every map."""
    r=dict(record)
    maps=[];defs=[];sizes=[]
    pat=re.compile(r'FMRankE\s*(\[[^\]]*\])')
    def replacement(match):
     lit=match.group(1);entries=[(int(k),int(v))for k,v in re.findall(r'\((\d+)%positive,\s*(\d+)\)',lit)];assert len(entries)==lit.count('%positive')
     cur=dict(entries);assert len(cur)==len(entries);i=len(maps);best=(len(entries),None,entries)
     for j,old in enumerate(maps):
      patch=[(k,cur.get(k,0))for k in sorted(old.keys()|cur.keys())if old.get(k,0)!=cur.get(k,0)]
      if len(patch)<best[0]:best=len(patch),j,patch
     num,j,patch=best
     # Independent reconstruction: final map lookup is last binding, default0.
     replay={}if j is None else dict(maps[j]);replay.update(patch)
     assert all(replay.get(k,0)==cur.get(k,0)for k in replay.keys()|cur.keys())
     rhs='potential_decode ['+';\n '.join('(%d%%positive,%d%%N)'%kv for kv in patch)+']'
     if j is not None:rhs='potential_patch potential_rank_%d ('%j+rhs+')'
     defs.append('Definition potential_rank_%d:list(positive*nat):=\n%s.'%(i,rhs));maps.append(cur);sizes.append((len(entries),num,j))
     return 'FMRankE potential_rank_%d'%i
    r['cert']=pat.sub(replacement,r['cert']);r['preamble']='''Definition potential_decode (xs:list(positive*N)):list(positive*nat):=
     map(fun kv=>(fst kv,N.to_nat(snd kv)))xs.
    Definition potential_patch (base patch:list(positive*nat)) : list(positive*nat) :=
     let keys:=psete_of(map fst patch) in
     filter(fun kv=>negb(Nat.eqb(snd kv)0))
      (filter(fun kv=>negb(PositiveSet.mem(fst kv)keys))base++patch).

    '''+ '\n\n'.join(defs)
    r["preamble"] = "\n".join(line.rstrip() for line in r["preamble"].splitlines())
    return r

def find():
    small = find_partial(SPEC, 6, target_state=2)
    ft = fm.ft
    table = ft.bp.parse(ft.gf.mirror_mtext(SPEC))
    n = 10
    _, left, right, initial, _ = ft.bp.build_closure(table, n, 0)
    seen = ft.gf.build_fw_closure(table, left, right, (initial, 0, 0))
    adjacent = ft.gf.fw_adj(table, left, right, seen)
    procedure = ft.instruction_procedure.func
    cert = procedure(table, n, adjacent, seen, (2, 1),
                     ft.pattern_candidates(n, n+1), ft.make_pattern_delta(table,n),
                     mix_finder=choose_mix)
    if cert is None or not ft.instruction_check(table,n,adjacent,seen,(2,1),*cert):
        raise RuntimeError("C1 potential search did not pass exact replay")
    big = dict(spec=SPEC,n=n,contexts=len(seen),mirrored=True,t=0,
               targets={"(2, 1)":True},fuel=8*len(seen)+64,
               rounds=len(left)+len(right)+4,cert=fm.emit_cert({(2,1):cert}))
    return [small,compact_ranks(big)]

def batch(records, number, overwrite):
    small,big = records
    if any(r["spec"]!=SPEC or not r["mirrored"] for r in records):
        raise ValueError("unsupported target certificate")
    suffix = "AST_%02d_0000" % number
    row = "r_"+suffix
    skip = "skip_"+suffix
    only = "only_"+suffix
    preamble = ("Definition %s(q:Instr):bool:=match q with(StC,S1)=>true|_=>false end.\n"
                "Definition %s(q:Instr):bool:=negb(%s q).\n") % (skip,only,skip)
    proof = "apply coversTr_nqh,neverqhtr_mirror.\n"
    for i,(rec,selector) in enumerate([(small,skip),(big,only)]):
        preamble += rec.get("preamble","") + "\n"
        cert = "cert%d_" % i + suffix
        preamble += "Definition %s:Instr->list fmxcomp*list positive:=\n%s.\n\n" % (cert,rec["cert"].rstrip("."))
        args = "(mirror_tm(row_to_tm %s)) %d %d %d %d %s %s" % (row,rec["n"],rec["t"],rec["fuel"],rec["rounds"],selector,cert)
        proof += ("assert(H%d:ngram_check_fuelmix_target_fast %s=true)by(vm_compute;reflexivity).\n"
                  "  pose proof(ngram_check_fuelmix_target_fast_sound %s H%d)as R%d.\n") % (i,args,args,i,i)
    proof += "intros[q s]Hf N. destruct q,s;first[apply R0;[reflexivity|exact Hf]|apply R1;[reflexivity|exact Hf]]."
    write_batch("AST",number,
        ["From Coq Require Import Bool.","From BBB4 Require Import Mirror PosEnc.",
         "From BBB4.Checkers Require Import NGram FuelMixTr FuelMixPartialTr FuelMixTargetTr FuelMixTargetFastTr.",
         "From BBB4.CensusTr Require Import TNF_QHTr."],[(SPEC,proof)],
        "independent target windows and partial weighted-potential certificates",
        overwrite=overwrite,preamble=preamble)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    commands=parser.add_subparsers(dest="command",required=True)
    finder=commands.add_parser("find");finder.add_argument("output",type=Path)
    emitter=commands.add_parser("batch");emitter.add_argument("certificates",type=Path)
    emitter.add_argument("--number",type=int,default=95)
    emitter.add_argument("--overwrite",action="store_true")
    args=parser.parse_args()
    if args.command=="find":
        args.output.write_text("".join(json.dumps(r,sort_keys=True)+"\n" for r in find()))
    else:
        batch([json.loads(line)for line in args.certificates.read_text().splitlines()if line.strip()],args.number,args.overwrite)

if __name__=="__main__":
    main()
