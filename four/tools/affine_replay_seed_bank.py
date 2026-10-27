"""Use successful target replays as new untrusted suffix-template proposals.

The recurring mask is inherited only as a search filter from the old proposal.
It is not claimed to describe the new machine. Every future target must pass
its own unchanged ir_check and independent kernel/census replay.
"""
import argparse
import csv
import hashlib
import json
from pathlib import Path
from affine_template_bank import proposal

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--replay',type=Path,required=True);p.add_argument('--proposal-index',type=Path,required=True)
 p.add_argument('--output',type=Path,required=True);p.add_argument('--profile',type=Path,required=True)
 a=p.parse_args();old=json.loads(a.proposal_index.read_text());lookup={x['certificate']:x for x in old['seeds']}
 rows=[x for x in csv.DictReader(a.replay.open(),delimiter='\t') if x['status']=='replay_true']
 if len(rows)!=len({x['machine'] for x in rows}):raise ValueError('Repeated replay target')
 seeds=[]
 for row in rows:
  prior=lookup[row['source']];path=Path(row['certificate']);path=path if path.is_absolute() else REPO/path
  metadata,_,blocks,identity=proposal(path)
  if metadata['machine']!=row['machine']:raise ValueError('Certificate identity differs')
  seeds.append(dict(source=row['machine'],certificate=str(path.resolve().relative_to(REPO)),
   certificate_sha256=sha(path),template_sha256=identity,mask=prior['mask'],has_blocks=bool(blocks)))
 a.output.parent.mkdir(parents=True,exist_ok=True)
 a.output.write_text(json.dumps(dict(seeds=seeds,targets=[]),separators=(',',':'))+'\n')
 report=dict(status='untrusted_replay_seed_templates',source_replay_true=len(rows),
  source_sha256={str(x.resolve().relative_to(REPO)):sha(x) for x in [Path(__file__),ROOT/'tools/affine_template_bank.py']},
  input_sha256=dict(replay=sha(a.replay),proposal_index=sha(a.proposal_index)),index_sha256=sha(a.output),
  semantics='Inherited recurring masks are heuristic filters only. A new target must independently pass ir_check.')
 a.profile.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
if __name__=='__main__':main()
