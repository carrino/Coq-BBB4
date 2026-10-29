"""Index repaired affine phases with original recurring masks as heuristics.

The phase writer omits claim metadata. This explicit identity join recovers
only a proposal filter from the original C certificate. Every target still
needs its own unchanged ir_check and later Coq/census proof.
"""
import argparse
import csv
import json
from pathlib import Path
from affine_template_bank import ROOT,REPO,sha,proposal


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--search',type=Path,required=True)
    p.add_argument('--replay',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--profile',type=Path,required=True)
    a=p.parse_args();inputs={str(x.resolve().relative_to(REPO)):sha(x) for x in [a.search,a.replay]}
    originals=list(csv.DictReader(a.search.open(),delimiter='\t'))
    lookup={r['machine']:r for r in originals}
    if len(lookup)!=len(originals):raise ValueError('Repeated source identity')
    rows=[r for r in csv.DictReader(a.replay.open(),delimiter='\t') if r['status']=='replay_true']
    if len(rows)!=len({r['machine'] for r in rows}):raise ValueError('Repeated replay identity')
    seeds=[];skipped=[]
    for row in rows:
        old=lookup[row['machine']]
        original=REPO/old['certificate'];repaired=REPO/row['certificate']
        oldmeta,mask,_,_=proposal(original);meta,_,blocks,identity=proposal(repaired)
        if oldmeta['machine']!=row['machine'] or meta['machine']!=row['machine']:
            raise ValueError('Original/repaired machine differs')
        if not mask:skipped.append(row['machine']);continue
        seeds.append(dict(source=row['machine'],certificate=str(repaired.resolve().relative_to(REPO)),
            certificate_sha256=sha(repaired),template_sha256=identity,mask=mask,has_blocks=bool(blocks),
            inherited_mask_source=str(original.resolve().relative_to(REPO)),inherited_mask_sha256=sha(original)))
    if inputs!={str(x.resolve().relative_to(REPO)):sha(x) for x in [a.search,a.replay]}:
        raise ValueError('Source ledger changed during indexing')
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(dict(seeds=seeds,targets=[]),separators=(',',':'))+'\n')
    reserved=a.output.with_name('source-ids.tsv')
    reserved.write_text('machine\n'+'\n'.join(r['machine'] for r in rows)+'\n')
    report=dict(status='untrusted_repaired_phase_templates',source_replay_true=len(rows),
        indexed_templates=len(seeds),zero_mask_skipped=len(skipped),input_sha256=inputs,
        index_sha256=sha(a.output),reserved_ids_sha256=sha(reserved),
        source_sha256={str(x.resolve().relative_to(REPO)):sha(x) for x in [Path(__file__),ROOT/'tools/affine_template_bank.py']},
        proof_status='Original recurring masks only select candidates. Repaired sources and every new target require independent checker evidence; no family discharge is claimed.')
    a.profile.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ['source_replay_true','indexed_templates','zero_mask_skipped']}))


if __name__=='__main__':main()
