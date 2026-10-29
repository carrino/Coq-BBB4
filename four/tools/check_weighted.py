"""Replay weighted certificates, assemble a completion board, and audit its kernel proofs.

Generated Coq modules stay in an ignored build directory. A successful search
is never counted as checked until coqc and recursive coqchk both succeed.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

from weighted_render import render

ROOT=Path(__file__).resolve().parents[1]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def source_hashes():
    pending=[ROOT/'tools/check_weighted.py',ROOT/'tools/weighted_render.py',
             ROOT/'theories/WeightedCensus.v',ROOT/'theories/WeightedRegression.v',
             ROOT/'theories/CertifiedBoard.v',ROOT/'theories/CycleCensus.v']
    files=set()
    imports=re.compile(r'From BBB24(?:\.([\w.]+))? Require (?:Import|Export)\s+([^.]*)\.')
    while pending:
        path=pending.pop()
        if path in files:continue
        files.add(path)
        if path.suffix=='.v':
            for prefix,modules in imports.findall(path.read_text()):
                pending += [ROOT/'theories'/Path(*filter(None,prefix.split('.')))/(module+'.v') for module in modules.split()]
    return {str(p.relative_to(ROOT)):sha(p) for p in sorted(files)}

def board_source(namespace,names):
    source='From Coq Require Import List NArith.\nFrom BBB24 Require Import Statement Bounds Closeout CertifiedBoard.\n'
    if names:source+=f'From {namespace} Require Import '+' '.join(names)+'.\n'
    source+='Import ListNotations.\nDefinition weighted_families:list(CertifiedFamily 4096%N 4096%N):=['+';'.join(f'mkCertifiedFamily 4096%N 4096%N {n}.family {n}.family_run' for n in names)+'].\n'
    source+='Definition weighted_board:=certified_board 4096%N 4096%N weighted_families.\n'
    source+='Theorem weighted_board_nonhalt:forall tm,In tm weighted_board->NonHalt tm.\nProof. apply certified_board_nonhalt. Qed.\n'
    source+='Theorem weighted_board_sound:BoardSound 4096%N 4096%N weighted_board.\nProof. apply certified_board_sound. Qed.\nPrint Assumptions weighted_board_sound.\n'
    return source

def run(command,log,timeout):
    with log.open('w') as output:
        try:return subprocess.run(command,stdout=output,stderr=subprocess.STDOUT,timeout=timeout,check=False).returncode
        except subprocess.TimeoutExpired:return 124

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificates',type=Path,required=True)
    parser.add_argument('--output-dir',type=Path,required=True)
    parser.add_argument('--report',type=Path,required=True)
    parser.add_argument('--namespace',default='BBB24Weighted')
    parser.add_argument('--timeout',type=int,default=120)
    parser.add_argument('--check',action='store_true',help='Validate saved hashes without rerunning proofs')
    args=parser.parse_args()
    if not re.fullmatch(r'[A-Z][A-Za-z0-9_]*(\.[A-Z][A-Za-z0-9_]*)*',args.namespace) or args.timeout<1:
        parser.error('Invalid namespace or timeout')
    rows=[json.loads(s) for s in args.certificates.read_text().splitlines()]
    machines=[r['graph']['machine'] for r in rows]
    if not rows or len(set(machines))!=len(machines):parser.error('Empty or duplicate machine inventory')
    version=subprocess.run(['coqc','--version'],capture_output=True,text=True,check=True).stdout.splitlines()[0]
    manifest={'certificates_sha256':sha(args.certificates),'source_sha256':source_hashes(),
              'coq_version':version,'namespace':args.namespace,'rows':len(rows),'state_bound':4096,'instruction_bound':4096}
    args.output_dir.mkdir(parents=True,exist_ok=True)
    saved=args.output_dir/'manifest.json'
    if saved.exists() and json.loads(saved.read_text())!=manifest:
        raise ValueError('Inputs or sources changed; select a new output directory')
    if args.check:
        report=json.loads(args.report.read_text())
        if report['manifest']!=manifest:raise ValueError('Saved report manifest differs')
        for name,digest in report['artifacts_sha256'].items():
            if sha(args.output_dir/name)!=digest:raise ValueError('Changed/missing proof artifact: '+name)
        for i,row in enumerate(rows):
            if (args.output_dir/f'Weighted{i:04d}.v').read_text()!=render(row):raise ValueError('Generated certificate source differs')
        checked=[r for r in report['results'] if r['status']=='coq_checked']
        if (args.output_dir/'WeightedBoard.v').read_text()!=board_source(args.namespace,[r['module'] for r in checked]):raise ValueError('Board differs')
        print(f"Validated saved audit of {len(checked)} checked families.")
        return
    saved.write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
    results=[]
    old={}
    if args.report.exists():
        previous=json.loads(args.report.read_text())
        if previous['manifest']==manifest:old={r['machine']:r for r in previous['results']}
    flags=['-Q',str(ROOT/'theories'),'BBB24','-Q',str(args.output_dir.resolve()),args.namespace]
    for i,row in enumerate(rows):
        name=f'Weighted{i:04d}'
        path=args.output_dir/(name+'.v')
        source=render(row)
        digest=hashlib.sha256(source.encode()).hexdigest()
        prior=old.get(machines[i])
        path.write_text(source)
        if prior and prior['status']=='coq_checked' and prior['source_sha256']==digest and sha(path.with_suffix('.vo'))==prior['vo_sha256']:
            results.append(prior);continue
        start=time.monotonic()
        code=run(['coqc','-native-compiler','no',*flags,str(path)],path.with_suffix('.log'),args.timeout)
        result={'machine':machines[i],'module':name,'mirror':row['graph']['mirror'],
                'status':'coq_checked' if code==0 else 'timeout' if code==124 else 'rejected',
                'source_sha256':digest,'seconds':round(time.monotonic()-start,3)}
        if code==0:result['vo_sha256']=sha(path.with_suffix('.vo'))
        results.append(result)
        if (i+1)%25==0:print(i+1,dict(Counter(r['status'] for r in results)),flush=True)
    checked=[r for r in results if r['status']=='coq_checked']
    board=args.output_dir/'WeightedBoard.v'
    board.write_text(board_source(args.namespace,[r['module'] for r in checked]))
    if run(['coqc','-native-compiler','no',*flags,str(board)],board.with_suffix('.log'),args.timeout)!=0:
        raise RuntimeError('Board compilation failed; report not published')
    if run(['coqchk','-silent','-bytecode-compiler','yes',*flags,args.namespace+'.WeightedBoard','BBB24.WeightedRegression'],args.output_dir/'coqchk.log',args.timeout*max(1,len(rows)))!=0:
        raise RuntimeError('Kernel audit failed; report not published')
    (args.output_dir/'machines.txt').write_text(''.join(r['machine']+'\n' for r in checked))
    artifacts=[saved,board,board.with_suffix('.vo'),args.output_dir/'machines.txt']
    for i in range(len(rows)):artifacts.append(args.output_dir/f'Weighted{i:04d}.v')
    for row in checked:artifacts.append(args.output_dir/(row['module']+'.vo'))
    report={'manifest':manifest,'validation':'coqc vm_compute plus recursive coqchk',
            'counts':dict(Counter(r['status'] for r in results)),'results':results,
            'census_linked':0,'artifacts_sha256':{p.name:sha(p) for p in artifacts}}
    args.report.parent.mkdir(parents=True,exist_ok=True)
    args.report.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report['counts'],sort_keys=True),flush=True)

if __name__=='__main__':main()
