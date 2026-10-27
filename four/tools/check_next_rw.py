"""Replay the frozen RW queue using supplied graphs and ranks, one worker.

First create the immutable queue input with --select; --produce N extracts
witnesses for a representative prefix (0 means all), each with a native time
limit. --replay checks saved witnesses, exact inventory and original pending
membership in Coq, then recursively audits the aggregate before publication.
No discovery output is a proof. Existing campaign artifacts are read-only.
"""
import argparse, base64, csv, hashlib, json, resource, shutil, subprocess, time, zlib
from pathlib import Path
from collections import Counter
import check_closure_wave as closure
from generate_pipeline_examples import codes
from check_state_repwl_batch import pack
from check_shadow_links import dependency_hashes
from kernel_audit_cache import audit, fresh_paths
ROOT=Path(__file__).resolve().parents[1]
BUILD=ROOT/'build/next-rw'
INPUT=ROOT/'research/next-rw-input.json'
NS='BBB24NextRW'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def compact(p,data):
    raw=json.dumps(data,sort_keys=True,separators=(',',':')).encode()
    p.write_text(json.dumps(dict(encoding='zlib-base64',uncompressed_sha256=hashlib.sha256(raw).hexdigest(),data=base64.b64encode(zlib.compress(raw,9)).decode()),indent=2)+'\n')
def load(p):
    d=json.loads(p.read_text())
    if d.get('encoding')=='zlib-base64':
        raw=zlib.decompress(base64.b64decode(d['data'],validate=True))
        if hashlib.sha256(raw).hexdigest()!=d['uncompressed_sha256']:raise ValueError('Packed input hash mismatch')
        return json.loads(raw)
    return d

def select():
    mpath=ROOT/'research/campaign-next-summary.json'; meta=json.loads(mpath.read_text())
    qp=ROOT/meta['outputs']['queued.tsv']['path']
    if sha(qp)!=meta['outputs']['queued.tsv']['sha256']:raise ValueError('Frozen queue differs')
    queue={r['machine']:r for r in csv.DictReader(qp.open(),delimiter='\t') if 'rw.' in r['both_sources']}
    pool={};provenance={str(mpath.relative_to(ROOT)):sha(mpath),str(qp.relative_to(ROOT)):sha(qp)}
    for key,s in sorted(meta['candidate_sources'].items()):
        if not key.startswith('rw.'):continue
        p=ROOT/s['file']
        if sha(p)!=meta['source_files_sha256'][s['file']]:raise ValueError('Candidate source changed')
        provenance[s['file']]=sha(p)
        _,rows=closure.load_input(p)
        for r in rows:
            if r['machine'] in queue and key in queue[r['machine']]['both_sources'].split(','):
                pool.setdefault(r['machine'],{**r,'source':key,'state_already_checked':queue[r['machine']]['state_already_checked']})
    if set(pool)!=set(queue) or len(pool)!=2833:raise ValueError('Incomplete queued RW selection')
    rows=sorted(pool.values(),key=closure.machine_hash)
    # One representative of every parameter set first, followed by hash order.
    representatives={}
    for r in rows:representatives.setdefault(tuple(r[k] for k in ('size','extra','anchor','fuel')),r)
    first=list(representatives.values());chosen={r['machine'] for r in first}
    rows=first+[r for r in rows if r['machine'] not in chosen]
    d=dict(scope='Both bounds for all completions; 125 of these IDs also have an unproved state obligation.',selected_rows=len(rows),state_pending_rows=sum(r['state_already_checked']=='no' for r in rows),selection='First hash-ordered representative of each parameter set, then remaining SHA256 machine order',source_sha256=provenance,rows=rows)
    if INPUT.exists() and load(INPUT)!=d:raise ValueError('Refuse to change existing selection')
    compact(INPUT,d)
    return d

def limits():
    resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3))

def run(cmd,log,timeout,cwd=None):
    start=time.monotonic()
    with log.open('w') as f:
        subprocess.run(cmd,cwd=cwd or ROOT.parent,stdout=f,stderr=subprocess.STDOUT,check=True,timeout=timeout,preexec_fn=limits)
    return round(time.monotonic()-start,3)

def flags():return ['-Q',str(ROOT/'theories'),'BBB24','-Q',str(BUILD),NS]
def coqc(p,timeout):return run(['coqc','-w','-abstract-large-number','-native-compiler','no',*flags(),str(p)],p.with_suffix('.log'),timeout)

def build_producer():
    p=BUILD/'Extract.v'
    p.write_text('From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.\nFrom BBB24 Require Import RepWLCensus.\nExtraction "'+str(BUILD/'checkers.ml')+'" rw_check.\n')
    coqc(p,120)
    shutil.copyfile(ROOT/'tools/next_rw_producer.ml',BUILD/'next_rw_producer.ml')
    for f in ('checkers.mli','checkers.ml'):
        run(['ocamlopt','-w','-A','-I',str(BUILD),'-c',str(BUILD/f)],BUILD/(f+'.log'),120)
    run(['ocamlopt','-w','-A','-I',str(BUILD),'-o',str(BUILD/'producer'),str(BUILD/'checkers.cmx'),str(BUILD/'next_rw_producer.ml')],BUILD/'producer-build.log',120)

def produce(d,args):
    build_producer();out=[];results=[]
    selected=d['rows'][:args.produce or None]
    for i,r in enumerate(selected):
        p=BUILD/f'witness-{hashlib.sha256(r["machine"].encode()).hexdigest()[:16]}.json'
        status='candidate';elapsed=0;start=time.monotonic()
        try:
            elapsed=run([str(BUILD/'producer'),r['machine'],*[str(r[k]) for k in ('bound','size','extra','anchor','fuel')]],p,args.native_timeout)
            w=json.loads(p.read_text());out.append(dict(row=r,**w))
        except subprocess.TimeoutExpired:status='native_timeout'
        except (subprocess.CalledProcessError,json.JSONDecodeError):status='native_failure'
        results.append(dict(machine=r['machine'],status=status,seconds=round(time.monotonic()-start,3)))
        print(json.dumps(dict(native=i+1,total=len(selected),**results[-1])),flush=True)
        if (i+1)%16==0:compact(args.witness,dict(input_sha256=sha(INPUT),attempts=results,witnesses=out))
    compact(args.witness,dict(input_sha256=sha(INPUT),attempts=results,witnesses=out))


def cl(xs):return '['+';'.join(xs)+']'
def sym(x):return 'S'+str(x)
def item(x):w,c,cap=x;return '(mkItem '+cl([sym(s) for s in w])+' '+str(c)+' '+str(cap).lower()+')'
def conf(x):
    q,li,lb,h,rb,ri=x
    return '('+('StA' if q==0 else 'StB')+',('+','.join([cl([item(i) for i in li]),cl([sym(s) for s in lb]),sym(h),cl([sym(s) for s in rb]),cl([item(i) for i in ri])])+'))'
def positive(bits):return str(int(bits,2))+'%positive'
def phi(xs):return cl(['('+positive(p)+','+str(n)+')' for p,n in xs])
def comp(x):
    if x[0]=='rank':return '(RwRankE '+phi(x[1])+')'
    if x[0]=='meas':return '(RwMeasE ('+x[1]+') '+str(x[2])+' '+phi(x[3])+' '+cl([positive(p) for p in x[4]])+')'
    raise ValueError('Bad certificate component')
def row(w):
    r=w['row'];return '(next_rw_row '+cl(list(map(str,codes(r['machine']))))+' '+str(r['size'])+' '+str(r['extra'])+' '+str(r['anchor'])+' '+cl([conf(x) for x in w['graph']])+' '+cl([cl([comp(x) for x in cs]) for cs in w['ranks']])+')'
HEADER='''From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Bounds Census Bootstrap Closeout CertifiedBoard
  Pipeline BoardManifest CensusUnion.
From BBB24.Checkers Require Import RepWL NGram.
From BBB24NextRW Require Import NextRWCertificate.
Import ListNotations.
'''+'From BBB24 Require Import PattCount.\n'
def shard(w):
    bound=w['row']['bound']
    return HEADER+f'''Definition rows : list NextRWRow := [{row(w)}].
Lemma checked : next_rw_batch_check {bound}%N {bound}%N rows = true.
Proof. vm_compute. reflexivity. Qed.
Definition board := next_rw_board rows.
Lemma small_sound : BoardSound {bound}%N {bound}%N board.
Proof. apply next_rw_board_sound; exact checked. Qed.
Lemma sound : BoardSound scoreN scoreN board.
Proof.
  intros family Hin tm Hle. eapply (bounds_weaken {bound}%N {bound}%N scoreN scoreN tm).
  - vm_compute. discriminate.
  - vm_compute. discriminate.
  - exact (small_sound family Hin tm Hle).
Qed.
Lemma nonhalt : forall family, In family board -> NonHalt family.
Proof. apply (next_rw_board_nonhalt {bound}%N {bound}%N); exact checked. Qed.
Lemma pending_checked : forallb (pending_check 9 empty bootstrap) board = true.
Proof. vm_compute. reflexivity. Qed.
Lemma was_pending : forall family, In family board -> bootstrap_pending family.
Proof. intros family Hin. apply pending_check_sound. pose proof pending_checked as H.
  apply forallb_forall with (x:=family) in H; assumption. Qed.
'''

def replay(d,args):
    input_hash=sha(INPUT)
    witness_hash=None if args.direct else sha(args.witness)
    data=(dict(input_sha256=input_hash,attempts=[],witnesses=[dict(row=r) for r in d['rows'][:args.limit or None]])
          if args.direct else load(args.witness))
    if data['input_sha256']!=input_hash:raise ValueError('Witness input mismatch')
    pool={r['machine']:r for r in d['rows']};seen=set()
    for w in data['witnesses']:
        r=w['row'];m=r['machine']
        if pool.get(m)!=r or m in seen:raise ValueError('Witness parameter/identity mismatch')
        seen.add(m)
    paths=[]
    if not args.direct:
        generic=BUILD/'NextRWCertificate.v';shutil.copyfile(ROOT/'tools/next_rw_certificate.v',generic)
        coqc(generic,args.coq_timeout);paths.append(generic)
    results=[];modules=[];accepted=[]
    for i,w in enumerate(data['witnesses']):
        source=closure.shard_source([w['row']]) if args.direct else shard(w)
        m=('DirectRow' if args.direct else 'Row')+hashlib.sha256(w['row']['machine'].encode()).hexdigest()[:16]
        p=BUILD/(m+'.v')
        if p.exists() and p.read_text()!=source:raise ValueError('Refuse to replace an existing proof source')
        p.write_text(source);status='compiled';elapsed=0;start=time.monotonic()
        try:elapsed=coqc(p,args.coq_timeout)
        except subprocess.TimeoutExpired:status='coq_timeout'
        except subprocess.CalledProcessError:status='coq_failure'
        result=dict(machine=w['row']['machine'],status=status,seconds=round(time.monotonic()-start,3),nodes=len(w['graph']) if 'graph' in w else None)
        results.append(result);print(json.dumps(dict(replayed=i+1,total=len(data['witnesses']),**result)),flush=True)
        if status=='compiled':modules.append(m);accepted.append(w['row']);paths.append(p)
        (BUILD/(args.name+'-progress.json')).write_text(json.dumps(results,indent=2)+'\n')
    if not accepted:raise ValueError('No compiled rows')
    aggregate=closure.aggregate_source(modules,NS,4096,len(accepted))
    packed=cl([str(pack(r['machine']))+'%N' for r in accepted])
    aggregate+='\nFrom BBB24 Require Import BoardManifest.\nDefinition inventory : list N := '+packed+'.\nLemma inventory_checked : manifest_check inventory board = true.\nProof. vm_compute. reflexivity. Qed.\nTheorem inventory_exact : manifest_board inventory = board.\nProof. apply manifest_check_sound. exact inventory_checked. Qed.\nPrint Assumptions inventory_exact.\n'
    module=args.name+'All';p=BUILD/(module+'.v');p.write_text(aggregate);coqc(p,args.coq_timeout);paths.append(p)
    receipt,log=fresh_paths(BUILD/'audits',args.name)
    old_limit=resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,old_limit[1]))
    try:
        audit([NS+'.'+module],[p],[(ROOT/'theories','BBB24'),(BUILD,NS)],receipt,log,recursive=True,timeout=args.audit_timeout)
    finally:resource.setrlimit(resource.RLIMIT_AS,old_limit)
    if sha(INPUT)!=input_hash or (witness_hash is not None and sha(args.witness)!=witness_hash):
        raise ValueError('Proof input changed during replay')
    for name,h in d['source_sha256'].items():
        if sha(ROOT/name)!=h:raise ValueError('Frozen source changed during replay: '+name)
    input_path=ROOT/('research/next-rw-'+args.name.lower()+'-board-input.json')
    compact(input_path,dict(columns=closure.FIELDS,rows=[[r[k] for k in closure.FIELDS] for r in accepted]))
    descriptor=dict(id='NextRW'+args.name,module=NS+'.'+module,board='board',sound='sound',small_sound='small_sound',was_pending='was_pending',state_bound=4096,instruction_bound=4096,scope='both',rows=len(accepted),inventories=[dict(path=str(input_path.relative_to(ROOT)),format='columns',order='input')],load_paths=[dict(path='build/next-rw',namespace=NS)])
    sources={**dependency_hashes([p],flags()),**{str(x.relative_to(ROOT)):sha(x) for x in [Path(__file__),ROOT/'tools/next_rw_certificate.v',ROOT/'tools/next_rw_producer.ml',ROOT/'tools/check_closure_wave.py',ROOT/'tools/generate_pipeline_examples.py',ROOT/'tools/check_state_repwl_batch.py',ROOT/'tools/check_shadow_links.py',ROOT/'tools/kernel_audit_cache.py']}}
    report=dict(status='Recursive kernel audit passed; exact inventory and pending membership checked',scope='Both bounds for every completion; original census leaf weights unchanged',checked_families=len(accepted),new_state_families=sum(r['state_already_checked']=='no' for r in accepted),remaining_rw_obligations=2833-len(accepted),method='direct rw_check' if args.direct else 'supplied graph and ranking check',attempted_rows=len(data['witnesses']),unattempted_rows=2833-len(data['witnesses']),budgets=dict(coq_seconds_per_row=args.coq_timeout,audit_seconds=args.audit_timeout,memory_limit_bytes=3*1024**3),queue_input_sha256=input_hash,witness_input=None if args.direct else str(args.witness.relative_to(ROOT)),witness_input_sha256=witness_hash,board_input_sha256=sha(input_path),source_sha256=sources,attempts=results,attempt_counts=dict(Counter(r['status'] for r in results)),native_attempt_counts=dict(Counter(r['status'] for r in data['attempts'])),board_descriptor=descriptor,inventory_theorem=NS+'.'+module+'.inventory_exact',discharge_theorem=NS+'.'+module+'.discharged',audit_receipt=str(receipt.relative_to(ROOT)),audit_receipt_sha256=sha(receipt),audit_log_sha256=sha(log),generated_sha256={str(p.relative_to(ROOT)):sha(p) for p in paths},object_sha256={str(p.with_suffix('.vo').relative_to(ROOT)):sha(p.with_suffix('.vo')) for p in paths})
    (ROOT/('research/next-rw-'+args.name.lower()+'-report.json')).write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(audited=len(accepted),new_state=report['new_state_families'],descriptor=descriptor)),flush=True)

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--select',action='store_true');p.add_argument('--direct',action='store_true');p.add_argument('--limit',type=int,default=32);p.add_argument('--produce',type=int);p.add_argument('--replay',action='store_true');p.add_argument('--name',default='Pilot');p.add_argument('--witness',type=Path,default=ROOT/'research/next-rw-pilot-witnesses.json');p.add_argument('--native-timeout',type=int,default=30);p.add_argument('--coq-timeout',type=int,default=120);p.add_argument('--audit-timeout',type=int,default=1200);a=p.parse_args()
    if not a.name.isidentifier():raise ValueError('Bad module name')
    BUILD.mkdir(parents=True,exist_ok=True);a.witness=a.witness.resolve();d=select() if a.select else load(INPUT)
    for name,h in d['source_sha256'].items():
        if sha(ROOT/name)!=h:raise ValueError('Frozen provenance differs: '+name)
    if a.produce is not None:produce(d,a)
    if a.replay:replay(d,a)
if __name__=='__main__':main()
