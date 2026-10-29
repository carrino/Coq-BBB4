"""Run or summarize a single-worker affine search on a frozen machine queue.

Search output is never proof evidence. Complete runs emit candidate and
not-accepted lists plus a compact, hash-pinned report. --partial reports only
the completed prefix and does not overwrite complete-run output files.
"""
import argparse
import csv
import hashlib
import io
import json
import subprocess
import time
from collections import Counter
from pathlib import Path

from generate_pipeline_examples import codes


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_input(path):
    machines = path.read_text().splitlines()
    if not machines or len(set(machines)) != len(machines):
        raise ValueError('Expected a nonempty, duplicate-free input queue')
    for machine in machines:
        codes(machine)
    return machines


def read_output(path, machines):
    if not path.exists():
        return []
    text = path.read_text()
    if text and not text.endswith('\n'):
        text = text[:text.rfind('\n')+1]
    raw = list(csv.reader(io.StringIO(text)))
    if not raw:
        return []
    expected = ['machine','status','anchor','k0','meta_a','meta_b','kmin','nrules','qh','score']
    if raw[0] != expected:
        raise ValueError('Unexpected affine CSV header')
    rows = raw[1:]
    if len(rows)>len(machines) or any(len(r)<10 or r[0]!=machines[i] for i,r in enumerate(rows)):
        raise ValueError('Search output is not an exact prefix of the input queue')
    if any(r[1] not in ('irules','undecided') for r in rows):
        raise ValueError('Unknown search verdict')
    return rows


def run(args, machines):
    output = args.output/'search.csv'
    completed = read_output(output,machines)
    if completed and not args.resume:
        raise ValueError('Existing search output; use --resume or another output directory')
    metadata = {'input_sha256':sha(args.input),'binary_sha256':sha(args.irules),
                'steps':args.steps,'tape_cells':args.tape_cells}
    manifest = args.output/'process.json'
    if manifest.exists():
        old = json.loads(manifest.read_text())
        if any(old[k]!=v for k,v in metadata.items()):
            raise ValueError('Resume input, binary or search parameters changed')
    if len(completed)==len(machines):
        return
    pending = args.output/'resume-input.txt'
    pending.write_text('\n'.join(machines[len(completed):])+'\n')
    chunk = args.output/'resume-output.csv'
    start = time.monotonic()
    with chunk.open('w') as out, (args.output/'search.log').open('a') as err:
        proc = subprocess.Popen([str(args.irules.resolve()),'--max-steps',str(args.steps),
            '--tape-cells',str(args.tape_cells),'--why','--cert-dir',str((args.output/'certs').resolve()),
            str(pending.resolve())],stdout=out,stderr=err)
        manifest.write_text(json.dumps({**metadata,'pid':proc.pid},indent=2)+'\n')
        result = proc.wait()
    new = read_output(chunk,machines[len(completed):])
    header='machine,status,anchor,k0,meta_a,meta_b,kmin,nrules,qh,score\n'
    buffer=io.StringIO(newline='');writer=csv.writer(buffer,lineterminator='\n')
    writer.writerows(completed+new)
    output.write_text(header+buffer.getvalue())
    (args.output/'finished.json').write_text(json.dumps({'returncode':result,
        'seconds':time.monotonic()-start,'processed_this_run':len(new)},indent=2)+'\n')
    if result:
        raise RuntimeError(f'Affine search exited {result}; completed prefix was preserved')


def summarize(args, machines):
    rows=read_output(args.output/'search.csv',machines)
    complete=len(rows)==len(machines)
    if not complete and not args.partial:
        raise ValueError(f'Incomplete search: {len(rows)}/{len(machines)}')
    candidates=[r[0] for r in rows if r[1]=='irules']
    missed=[r[0] for r in rows if r[1]=='undecided']
    reasons=Counter(r[10].split()[0] if len(r)>10 else 'unspecified'
                    for r in rows if r[1]=='undecided')
    versions=Counter(); multivariable=0
    if complete:
        for machine in candidates:
            path=args.output/'certs'/f'{machine}.cert'
            text=path.read_text();lines=text.splitlines()
            if lines.count('machine '+machine)!=1:
                raise ValueError(f'Missing/mismatched certificate: {machine}')
            versions[lines[0]]+=1
            multivariable+=any(line.startswith('nvar ') for line in lines)
    stem='' if complete else 'partial-'
    candidate_file=args.output/f'{stem}candidates.txt'
    missed_file=args.output/f'{stem}not-accepted.txt'
    candidate_file.write_text('\n'.join(candidates)+ ('\n' if candidates else ''))
    missed_file.write_text('\n'.join(missed)+ ('\n' if missed else ''))
    report={'status':'Complete untrusted search' if complete else 'Incomplete untrusted prefix',
        'input_rows':len(machines),'processed_rows':len(rows),'unprocessed_rows':len(machines)-len(rows),
        'candidate_rows':len(candidates),'not_accepted_rows':len(missed),
        'failure_reasons':dict(sorted(reasons.items())),
        'certificate_versions':dict(sorted(versions.items())),
        'multivariable_candidates':multivariable if complete else None,
        'input_sha256':sha(args.input),'search_csv_sha256':sha(args.output/'search.csv'),
        'candidates_sha256':sha(candidate_file),'not_accepted_sha256':sha(missed_file),
        'parameters':json.loads((args.output/'process.json').read_text()),
        'kernel_checked_rows':0,'census_linked_rows':0,
        'proof_accounting':'Search candidates are not certified discharges. Checked proof waves are recorded separately.'}
    report['parameters'].pop('pid',None)
    target=args.report if args.report and complete else args.output/f'{stem}summary.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('status','processed_rows','candidate_rows','not_accepted_rows','unprocessed_rows')}))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--report',type=Path)
    parser.add_argument('--irules',type=Path)
    parser.add_argument('--steps',type=int,default=4096)
    parser.add_argument('--tape-cells',type=int,default=65536)
    parser.add_argument('--resume',action='store_true')
    parser.add_argument('--partial',action='store_true')
    args=parser.parse_args()
    if args.steps<1 or args.tape_cells<2*args.steps+1:
        raise ValueError('Tape must accommodate every position within the search step budget')
    args.output.mkdir(parents=True,exist_ok=True)
    (args.output/'certs').mkdir(exist_ok=True)
    machines=read_input(args.input)
    if args.irules:
        run(args,machines)
    summarize(args,machines)


if __name__=='__main__':
    main()
