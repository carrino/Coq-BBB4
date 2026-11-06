#!/usr/bin/env python3
"""UNTRUSTED G/X/Y control-rank nominations; no Coq or coverage credit.

Usage: python3 wait42/tools/probe_control_ranks.py --input residual.tsv \
         --output wait42/build/control-nominations

Try every nonempty total closed control subset and G/X/Y scales 1..6.
G counts all ones, X left plus head, Y right plus head. Nonnegative control
potentials descend on every target-avoiding transition. Each nominee still
requires exact Coq checking and completion transport. This tool does not
subtract existing proofs; select and fingerprint the intended input first.

Outputs control-nominations.json, outcomes.tsv (including every failure), and
manifest.json. Files are published only after the entire input validates and
its hash is rechecked. Uses only Python's standard library; no simulator or
external solver import. The rank cache and input-row count are bounded; input
snapshots are limited to 128 MiB.
"""
import argparse
from collections import Counter
import csv
import functools
import hashlib
import json
import io
from pathlib import Path
import re
import sys
import tempfile
import time

MAX_INPUT_BYTES = 128 * 1024 * 1024
PATTERN = re.compile(r'(?:---|[01][LR][ABCD]){2}(?:_(?:---|[01][LR][ABCD]){2}){3}')
SUBSETS = tuple(tuple(q for q in range(4) if mask >> q & 1)
                for size in range(1, 5) for mask in range(1, 16)
                if mask.bit_count() == size)
MEASURES = ('G', 'X', 'Y')


def fingerprint(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return {'bytes': Path(path).stat().st_size, 'sha256': digest.hexdigest()}


def parse(machine):
 if PATTERN.fullmatch(machine) is None:raise ValueError('invalid machine '+machine)
 text=machine.replace('_','')
 return tuple(None if text[i:i+3]=='---' else (int(text[i]),text[i+1],ord(text[i+2])-65) for i in range(0,24,3))
def delta(measure,w,d,h):
 return w-h if measure=='G' else (-h if (measure=='X' and d=='L') or (measure=='Y' and d=='R') else w+1-h)
def potentials(nodes,edges):
 if not nodes:return {}
 distances={s:0 for s in nodes}
 for _ in range(len(nodes)+1):
  changed=False
  for s,nxt,weight in edges:
   if distances[s]-weight<distances[nxt]:distances[nxt]=distances[s]-weight;changed=True
  if not changed:
   mn=min(distances.values());return {s:v-mn for s,v in distances.items()}
 return None
@functools.lru_cache(maxsize=50000)
def rank_subset(states,slots,cutoff):
 table={(s,h):slots[2*i+h] for i,s in enumerate(states) for h in (0,1)}
 cert={};fail=[]
 for q in states:
  nodes=tuple(s for s in states if s!=q);choices=[]
  for measure in MEASURES:
   for scale in range(1,7):
    edges=[]
    for s in nodes:
     for h in (0,1):
      w,d,nxt=table[s,h]
      if nxt!=q:edges.append((s,nxt,scale*delta(measure,w,d,h)+1))
    phi=potentials(nodes,edges)
    if phi is not None:
     allphi={s:phi.get(s,0) for s in range(4)}
     choices.append((scale*cutoff+max(allphi.values())+1,MEASURES.index(measure),{'measure':measure,'scale':scale,'phi':allphi}))
     break
  if not choices:fail.append(q)
  else:cert[q]=min(choices,key=lambda x:x[:2])[2]
 return cert,tuple(fail)
def nominate(table,fuel,cutoff=32779478,width_limit=225592668):
 closed=[];ranked=[];fail_targets=Counter()
 for states in SUBSETS:
  if any(table[2*s+h] is None or table[2*s+h][2] not in states for s in states for h in (0,1)):continue
  closed.append(states)
  slots=tuple(table[2*s+h] for s in states for h in (0,1))
  cert,fail=rank_subset(states,slots,cutoff)
  if fail:
   for q in fail:fail_targets[str(q)]+=1
  else:ranked.append((states,cert))
 details={'closed_subsets':len(closed),'rank_feasible_subsets':len(ranked),'failed_target_counts':dict(fail_targets)}
 if not closed:return 'no_closed_control_tail',None,details
 if not ranked:return 'target_no_decreasing_rank',None,details
 ones=set();head=0;state=0
 for t in range(fuel+1):
  choices=[]
  for states,cert in ranked:
   if state not in states:continue
   pertarget={q:1+c['scale']*(len(ones)+cutoff-t)+max(c['phi'].values()) for q,c in cert.items()}
   width=max(pertarget.values())
   if t<=cutoff and width<=width_limit:choices.append((width,len(states),states,cert,pertarget))
  if choices:
   width,_,states,cert,target_bounds=min(choices,key=lambda x:x[:3])
   for q,c in cert.items():
    for s in states:
     for h in (0,1):
      w,d,nxt=table[2*s+h]
      if s!=q and nxt!=q:assert c['scale']*delta(c['measure'],w,d,h)+c['phi'][nxt]<c['phi'][s]
   return 'nominated',{'states':states,'anchor':t,'anchor_state':state,'anchor_ones':len(ones),'cert':cert,'target_width_upper':target_bounds,'width_upper':width},details
  if any(state in states for states,_ in ranked):return 'width_gate',None,details
  if t==fuel:break
  tr=table[2*state+int(head in ones)]
  if tr is None:return 'anchor_halts',None,details
  w,d,state=tr
  if w:ones.add(head)
  else:ones.discard(head)
  head+=1 if d=='R' else -1
 return 'anchor_not_reached',None,details

def read_input_bytes(path):
    with Path(path).open('rb') as stream:
        snapshot = stream.read(MAX_INPUT_BYTES + 1)
    if len(snapshot) > MAX_INPUT_BYTES:
        raise ValueError(f'input byte cap {MAX_INPUT_BYTES} exceeded')
    return snapshot


def validated_rows(source, maximum):
    """Parse one immutable UTF-8 byte snapshot using strict rectangular CSV."""
    snapshot = source if isinstance(source, bytes) else read_input_bytes(source)
    if len(snapshot) > MAX_INPUT_BYTES:
        raise ValueError(f'input byte cap {MAX_INPUT_BYTES} exceeded')
    seen = set()
    try:
        with io.StringIO(snapshot.decode('utf-8'), newline='') as stream:
            reader = csv.DictReader(stream, delimiter='\t', strict=True)
            fields = reader.fieldnames
            if (not fields or len(fields) != len(set(fields))
                    or not {'kind', 'machine', 'ptr'} <= set(fields)
                    or any('\n' in field or '\r' in field for field in fields)):
                raise ValueError('input requires unique single-line kind, machine, ptr columns')
            for index, row in enumerate(reader):
                if None in row or any(value is None for value in row.values()):
                    raise ValueError(f'input row {index}: malformed TSV width')
                if any('\n' in value or '\r' in value for value in row.values()):
                    raise ValueError(f'input row {index}: embedded newline in field')
                if row['kind'] not in ('unknown', 'unknown_edge', 'pending') or row['ptr'] not in ('1', '2', '3', '4'):
                    raise ValueError(f'input row {index}: invalid residual kind or pointer')
                table = parse(row['machine'])
                identity = row['machine'] + '\t' + row['ptr']
                if identity in seen:
                    raise ValueError(f'input row {index}: duplicate machine/pointer identity')
                if index >= maximum:
                    raise ValueError(f'input row cap {maximum} exceeded')
                seen.add(identity)
                yield index, row, table
    except csv.Error as error:
        raise ValueError(f'malformed strict TSV: {error}') from error


def run(input_path, output, anchor_fuel=4096, cutoff=32779478,
        width=225592668, maximum=1000000, expected_sha256=None):
    if not (0 <= anchor_fuel <= 65536 and cutoff >= 0 and width >= 0 and 1 <= maximum <= 1000000):
        raise ValueError('invalid numeric limits')
    input_path, output = Path(input_path), Path(output)
    input_bytes = read_input_bytes(input_path)
    before = {'bytes': len(input_bytes), 'sha256': hashlib.sha256(input_bytes).hexdigest()}
    if expected_sha256 is not None and before['sha256'] != expected_sha256:
        raise ValueError('input SHA256 differs from --expected-input-sha256')
    if input_path.resolve() in { (output / name).resolve() for name in
                                ('control-nominations.json', 'outcomes.tsv', 'manifest.json') }:
        raise ValueError('output must not overwrite input')
    output.parent.mkdir(parents=True, exist_ok=True)
    rank_subset.cache_clear()
    start = time.monotonic()
    counts, sizes, measures, scales, anchors, kinds, failed = (Counter() for _ in range(7))
    total = nominees = max_width = max_anchor = 0
    with tempfile.TemporaryDirectory(prefix='control-rank-probe-', dir=output.parent) as temp:
        temp = Path(temp)
        with (temp / 'control-nominations.json').open('w') as accepted, (temp / 'outcomes.tsv').open('w') as outcomes:
            writer = csv.writer(outcomes, delimiter='\t', lineterminator='\n')
            writer.writerow(['source_index', 'machine', 'ptr', 'status', 'closed_subsets',
                             'rank_feasible_subsets', 'failed_target_counts'])
            accepted.write('[\n')
            for index, row, table in validated_rows(input_bytes, maximum):
                total += 1
                status, certificate, details = nominate(table, anchor_fuel, cutoff, width)
                counts[status] += 1
                failed.update(details['failed_target_counts'])
                writer.writerow([index, row['machine'], row['ptr'], status,
                                 details['closed_subsets'], details['rank_feasible_subsets'],
                                 json.dumps(details['failed_target_counts'], sort_keys=True)])
                if certificate is not None:
                    entry = {'source_index': index, 'machine': row['machine'], 'ptr': row['ptr'],
                             'source_kind': row['kind'], **certificate}
                    accepted.write(('' if nominees == 0 else ',\n') + json.dumps(entry, sort_keys=True))
                    nominees += 1
                    sizes[len(certificate['states'])] += 1
                    kinds['partial' if '---' in row['machine'] else 'full'] += 1
                    anchors[certificate['anchor']] += 1
                    max_width = max(max_width, certificate['width_upper'])
                    max_anchor = max(max_anchor, certificate['anchor'])
                    for cert in certificate['cert'].values():
                        measures[cert['measure']] += 1
                        scales[cert['scale']] += 1
            accepted.write('\n]\n')
        if fingerprint(input_path) != before:
            raise ValueError('input changed during nomination')
        manifest = {'schema_version': 1,
                    'trust': 'UNTRUSTED nominations; exact Coq replay and completion transport required',
                    'coverage_proved': False, 'kernel_credit': 0, 'accepted_proofs': 0,
                    'input': {'path': str(input_path), **before},
                    'tool': fingerprint(Path(__file__)),
                    'cutoff': cutoff, 'maximum_allowed_width': width, 'anchor_fuel': anchor_fuel,
                    'maximum_input_rows': maximum, 'maximum_input_bytes': MAX_INPUT_BYTES,
                    'input_hash_and_rows_share_immutable_snapshot': True,
                    'maximum_rank_cache_entries': 50000,
                    'search': 'all nonempty total closed control subsets, G/X/Y, scales1..6',
                    'quantitative_formula': 'max_q(1+scale_q*(anchor_ones+cutoff-anchor)+max_s(phi_q(s)))',
                    'rows_processed': total, 'unique_input_identities': total,
                    'unique_nominee_identities': nominees, 'status_counts': dict(counts),
                    'failed_target_counts': dict(failed), 'invariant_size_histogram': dict(sizes),
                    'measure_histogram': dict(measures), 'scale_histogram': dict(scales),
                    'anchor_histogram': dict(anchors), 'full_partial_histogram': dict(kinds),
                    'maximum_nominated_width': max_width, 'maximum_anchor': max_anchor,
                    'seconds': round(time.monotonic() - start, 3),
                    'output_fingerprints': {name: fingerprint(temp / name) for name in
                                            ('control-nominations.json', 'outcomes.tsv')},
                    'notes': ['Source indices are zero-based data-row indices in the fingerprinted input.',
                              'No previously proved families are automatically removed or counted as proofs.',
                              'Every rejection remains in outcomes.tsv; no source identity is silently discarded.']}
        (temp / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
        output.mkdir(parents=True, exist_ok=True)
        for name in ('control-nominations.json', 'outcomes.tsv', 'manifest.json'):
            (temp / name).replace(output / name)
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--anchor-fuel', type=int, default=4096)
    parser.add_argument('--cutoff', type=int, default=32779478)
    parser.add_argument('--width', type=int, default=225592668)
    parser.add_argument('--max-input-rows', type=int, default=1000000)
    parser.add_argument('--expected-input-sha256')
    args = parser.parse_args()
    try:
        result = run(args.input, args.output, args.anchor_fuel, args.cutoff,
                     args.width, args.max_input_rows, args.expected_input_sha256)
    except (ValueError, OSError) as error:
        print(f'error: {error}', file=sys.stderr)
        return 2
    print(json.dumps({'rows': result['rows_processed'], 'nominees': result['unique_nominee_identities'],
                      'status_counts': result['status_counts'], 'coverage_proved': False}))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
