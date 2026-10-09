#!/usr/bin/env python3
"""Untrusted RepWL closure/certificate search and source-data emission.

The JSON payload stores a complete closure as delta-coded rconf_enc keys,
shared ranks, and compact lexicographic tables. RepWLStoredTr checks every
decoded successor and ranking edge; neither this emitter nor its decoder
is trusted. Replaying committed JSON never repeats certificate search.

  find MANIFEST STAGE INDEX OUTPUT.json
  pack RAW.json OUTPUT.json          (developer probe interchange)
  compact CERT.json OUTPUT.json      (merge disjoint measure components)
  emit CERT.json OUTPUT.v [--check]
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import rw_cert_find as finder

PARAMS = ('spec', 'L', 'T', 't', 'fuel', 'M')


def chunks(xs, size=128):
    return [xs[i:i+size] for i in range(0, len(xs), size)]


def differences(xs):
    return [v-p for p, v in zip([0]+xs, xs)]


def totals(ds):
    out, value = [], 0
    for d in ds:
        if d <= 0:
            raise ValueError('dictionary differences must be positive')
        value += d
        out.append(value)
    return out


def varint(value):
    if not 0 < value < 8**6:
        raise ValueError('key-index difference exceeds decoder budget')
    digits = ''
    while value >= 8:
        digits += format(8 + value % 8, 'x')
        value //= 8
    return digits + format(value, 'x')


def pack_table(items, key_ids, rank_ids=None):
    result = []
    for block in chunks(items):
        previous, payload = 0, ''
        for item in block:
            key, rank = item if rank_ids is not None else (item, None)
            index = key_ids[key]
            payload += varint(index-previous)
            previous = index
            if rank_ids is not None:
                value = rank_ids[rank]
                if not 0 < value < 65536:
                    raise ValueError('too many distinct ranks')
                payload += f'{value:04x}'
        result.append(payload)
    return result


def unpack_table(payloads, keys, ranks=None):
    out = []
    for payload in payloads:
        offset, previous, count = 0, 0, 0
        while offset < len(payload):
            scale, delta = 1, 0
            for _ in range(6):
                d = int(payload[offset], 16)
                offset += 1
                delta += scale * (d % 8)
                if d < 8:
                    break
                scale *= 8
            else:
                raise ValueError('oversized index difference')
            if delta <= 0:
                raise ValueError('nonpositive index difference')
            previous += delta
            key = keys[previous-1]
            if ranks is None:
                out.append(key)
            else:
                if offset+4 > len(payload):
                    raise ValueError('truncated rank reference')
                rank = int(payload[offset:offset+4], 16)
                offset += 4
                if rank < 1:
                    raise ValueError('invalid rank reference')
                out.append([key, ranks[rank-1]])
            count += 1
        if count > 128:
            raise ValueError('oversized table chunk')
    return out


def decoded(data):
    if data['version'] != 1:
        raise ValueError('unknown stored RepWL format')
    keys = totals([int(d, 16) for d in data['key_deltas']])
    ranks = totals(data['rank_deltas'])
    certs = {}
    for tg, components in data['certs'].items():
        if tg not in [f'{q},{s}' for q in range(4) for s in range(2)]:
            raise ValueError('invalid instruction')
        out = []
        for comp in components:
            if comp[0] == 'rank':
                out.append(['rank', unpack_table(comp[1], keys, ranks)])
            elif comp[0] == 'meas' and comp[1] in finder.MEAS_CTOR and comp[2] >= 0:
                out.append(['meas', comp[1], comp[2],
                            unpack_table(comp[3], keys, ranks),
                            unpack_table(comp[4], keys)])
            else:
                raise ValueError('invalid component')
        certs[tg] = out
    return dict(keys=keys, ranks=ranks, certs=certs)


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True,
                                    separators=(',', ':')).encode()).hexdigest()


def read(path):
    data = json.loads(Path(path).read_text())
    if digest(decoded(data)) != data['decoded_sha256']:
        raise ValueError(f'decoded certificate digest mismatch: {path}')
    return data


def freeze(x):
    return tuple(map(freeze, x)) if isinstance(x, list) else x


def pack(raw):
    keys = sorted(finder.rp.rconf_enc(freeze(a)) for a in raw['pool'])
    if len(keys) != len(set(keys)) or not keys:
        raise ValueError('empty or duplicate closure')
    components = [c for cs in raw['certs'].values() for c in cs]
    ranks = sorted({v for c in components for k, v in
                    (c[1] if c[0] == 'rank' else c[3])})
    key_ids = {k: i+1 for i, k in enumerate(keys)}
    rank_ids = {r: i+1 for i, r in enumerate(ranks)}
    data = {k: raw[k] for k in PARAMS}
    data.update(version=1, key_deltas=[format(d, 'x') for d in differences(keys)],
                rank_deltas=differences(ranks), certs={})
    for tg, cs in raw['certs'].items():
        out = []
        for c in cs:
            if c[0] == 'rank':
                out.append(['rank', pack_table(c[1], key_ids, rank_ids)])
            else:
                out.append(['meas', c[1], c[2],
                            pack_table(c[3], key_ids, rank_ids),
                            pack_table(c[4], key_ids)])
        data['certs'][tg] = out
    # Search returns tuple pairs, while interchange JSON contains lists.
    expected = dict(keys=keys, ranks=ranks,
                    certs=json.loads(json.dumps(raw['certs'])))
    if decoded(data) != expected:
        raise ValueError('certificate packing changed data')
    data['decoded_sha256'] = digest(expected)
    return data


def coalesce_measures(components):
    """Propose shorter certificates; the Coq checker still decides validity.

    Consecutive measure components come from separate cyclic components
    in the finder's SCC pass. Merge equal measures/scales only when all
    gates in that run are disjoint. Rank components remain in place.
    """
    result, run = [], []

    def flush():
        seen = set()
        for comp in run:
            gate = set(comp[4])
            if seen & gate:
                result.extend(run)
                return
            seen.update(gate)
        groups = {}
        for comp in run:
            _, measure, scale, phi, gate = comp
            groups.setdefault((measure, scale), []).append(comp)
        for (measure, scale), group in groups.items():
            if len(group) == 1:
                result.extend(group)
                continue
            phi, gate = {}, set()
            for comp in group:
                local_gate = set(comp[4])
                gate.update(local_gate)
                # Potentials outside a component's gate never affect its
                # value or its checker verdict. Do not combine them.
                phi.update((k, v) for k, v in comp[3] if k in local_gate)
            result.append(['meas', measure, scale,
                           [[k, v] for k, v in sorted(phi.items())], sorted(gate)])

    for comp in components:
        if comp[0] == 'meas':
            run.append(comp)
        else:
            flush()
            run = []
            result.append(comp)
    flush()
    return result


def compact(data):
    old = decoded(data)
    if digest(old) != data['decoded_sha256']:
        raise ValueError('invalid decoded digest')
    key_ids = {key: i+1 for i, key in enumerate(old['keys'])}
    rank_ids = {rank: i+1 for i, rank in enumerate(old['ranks'])}
    certs = {tg: coalesce_measures(cs) for tg, cs in old['certs'].items()}
    result = dict(data, certs={})
    for tg, components in certs.items():
        packed = []
        for comp in components:
            if comp[0] == 'rank':
                packed.append(['rank', pack_table(comp[1], key_ids, rank_ids)])
            else:
                packed.append(['meas', comp[1], comp[2],
                               pack_table(comp[3], key_ids, rank_ids),
                               pack_table(comp[4], key_ids)])
        result['certs'][tg] = packed
    expected = dict(old, certs=certs)
    if decoded(result) != expected:
        raise ValueError('compacted certificate packing changed data')
    result['decoded_sha256'] = digest(expected)
    return result


def search(row):
    start = time.monotonic()
    tbl = finder.rp.parse(row['spec'])
    found = finder.rp.build_closure(tbl, row['L'], row['T'], row['t'], cap=30000)
    if found is None:
        raise ValueError('closure search failed')
    _, pool = found
    if max(map(finder.asz, pool)) > row['M']:
        raise ValueError('closure exceeds original size cut')
    adj = {a: finder.rp.rw_succs(tbl, row['L'], row['T'], a) for a in pool}
    certs = {}
    for tg in sorted({finder.instr(a) for a in pool} | finder.fired_prefix(tbl, row['t'])):
        cs = finder.procedure_tr(tbl, pool, adj, tg, finder.rp.MEAS)
        if cs is None or not finder.lex_check_tr(tbl, adj, pool, tg, cs):
            raise ValueError(f'certificate search failed for {tg}')
        certs[f'{tg[0]},{tg[1]}'] = [finder.enc_comp(c) for c in cs]
    raw = dict(row, pool=sorted(pool), certs=certs)
    print(f'found {len(pool)} nodes in {time.monotonic()-start:.3f} seconds', flush=True)
    return pack(raw)


def uints(values):
    return '['+'; '.join('0x'+v+'%huint' for v in values)+']'


def render(data):
    # Validate even in callers that did not use read().
    if digest(decoded(data)) != data['decoded_sha256']:
        raise ValueError('invalid decoded digest')
    body = ['''(** GENERATED by tools/censustr/rw_stored.py -- DO NOT EDIT.
    Untrusted closure/certificate source data; RepWLStoredTr checks it. *)
From Coq Require Import List Hexadecimal.
From BBB4 Require Import BBB4_Statement BBBT4_Statement.
From BBB4.Checkers Require Import RepWL RepWLStoredTr.
Import ListNotations.
''', f'(* {data["spec"]}; decoded SHA-256 {data["decoded_sha256"]} *)']
    for name, values, fun in [('keys', data['key_deltas'], 'rws_keys'),
                              ('ranks', [format(d, 'x') for d in data['rank_deltas']], 'rws_ranks')]:
        blocks = chunks(values)
        for i, block in enumerate(blocks):
            body.append(f'Local Definition {name}_{i:04d} : list Number.uint := {uints(block)}.')
        body.append(f'Definition {name} := {fun} ['+
                    '; '.join(f'{name}_{i:04d}' for i in range(len(blocks)))+'].')
    for tg, cs in sorted(data['certs'].items()):
        components = []
        for c in cs:
            if c[0] == 'rank':
                components.append('RwsRank '+uints(c[1]))
            else:
                components.append('RwsMeas %s %s %s %s' %
                                  (finder.MEAS_CTOR[c[1]], finder.fmt_nat(c[2]),
                                   uints(c[3]), uints(c[4])))
        body.append(f'Definition cert_{tg.replace(",", "_")} : list rwscomp :=\n  ['+
                    ';\n   '.join(components)+'].')
    body.append('Definition cert (tg : Instr) : list rwscomp := match tg with')
    for tg in sorted(data['certs']):
        q, s = map(int, tg.split(','))
        body.append(f'| (St{chr(65+q)}, S{s}) => cert_{q}_{s}')
    if len(data['certs']) < 8:
        body.append('| _ => []')
    body.append('end.\n')
    return '\n'.join(body)


def smoke_source():
    row = dict(spec='0RB0RB_0LC0LC_0RD0RD_0LA0LA', L=1, T=2, t=0,
               fuel=128, M=8)
    data = search(row)
    return render(data) + '''
From BBB4 Require Import CTape.
''' + finder.tm_lambda('smoke_tm', row['spec']) + '''

Example stored_closure_smoke : NeverQuasiHaltsTr smoke_tm.
Proof. apply (rw_check_stored_tr_sound _ 1 2 0 8 keys ranks cert).
  vm_cast_no_check (eq_refl true). Qed.

Example stored_reject_missing_root :
  rw_check_stored_tr smoke_tm 1 2 0 8 [] ranks cert = false.
Proof. vm_cast_no_check (eq_refl false). Qed.

Example stored_reject_malformed_key :
  rw_check_stored_tr smoke_tm 1 2 0 8 [BinNums.xH] ranks cert = false.
Proof. vm_cast_no_check (eq_refl false). Qed.

Example stored_reject_missing_successor :
  rw_check_stored_tr smoke_tm 1 2 0 8 [rconf_enc (rw_seed 1 2 c0)] ranks cert = false.
Proof. vm_cast_no_check (eq_refl false). Qed.

Example stored_reject_missing_certificate :
  rw_check_stored_tr smoke_tm 1 2 0 8 keys ranks (fun _ => []) = false.
Proof. vm_cast_no_check (eq_refl false). Qed.

Example stored_reject_zero_ranks :
  rw_check_stored_tr smoke_tm 1 2 0 8 keys (map (fun _ => 0) ranks) cert = false.
Proof. vm_cast_no_check (eq_refl false). Qed.
'''


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest='command', required=True)
    find = sub.add_parser('find')
    find.add_argument('manifest', type=Path)
    find.add_argument('stage', type=int)
    find.add_argument('index', type=int)
    find.add_argument('output', type=Path)
    pack_parser = sub.add_parser('pack')
    pack_parser.add_argument('raw', type=Path)
    pack_parser.add_argument('output', type=Path)
    compact_parser = sub.add_parser('compact')
    compact_parser.add_argument('certificate', type=Path)
    compact_parser.add_argument('output', type=Path)
    emit = sub.add_parser('emit')
    emit.add_argument('certificate', type=Path)
    emit.add_argument('output', type=Path)
    emit.add_argument('--check', action='store_true')
    smoke = sub.add_parser('smoke')
    smoke.add_argument('output', type=Path)
    smoke.add_argument('--check', action='store_true')
    args = ap.parse_args()
    if args.command in ['emit', 'smoke']:
        source = render(read(args.certificate)) if args.command == 'emit' else smoke_source()
        if args.check:
            if args.output.read_text() != source:
                raise ValueError(f'stale generated certificate: {args.output}')
        else:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(source)
        return
    if args.command == 'compact':
        data = compact(read(args.certificate))
    elif args.command == 'find':
        from gen_provtr_rw import read_manifest
        row = next(r for r in read_manifest(args.manifest)
                   if (r['stage'], r['index']) == (args.stage, args.index))
        data = search(row)
    else:
        data = pack(json.loads(args.raw.read_text()))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, sort_keys=True, indent=2)+'\n')


if __name__ == '__main__':
    main()
