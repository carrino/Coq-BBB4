#!/usr/bin/env python3
"""Compact large literal certificate tables using the existing Coq decoder.

Only increasing positive-key tables and gates are packed. Every payload is
independently decoded and compared with its input before emission. The Coq
checkers still verify all decoded data; this module supplies no proof premise.
Already compacted source remains canonical and can be expanded for inspection.
"""
from dataclasses import dataclass
from pathlib import Path
import re

MIN_BYTES = 100_000
BEGIN = '(* COMPACT CERTIFICATE TABLES v1 *)'
END = '(* END COMPACT CERTIFICATE TABLES *)'
NAT = r'(?:\d+|\(\d+ \* 1000 \+ \d+\))'
PAIR = re.compile(r'\((\d+)%positive,\s*(' + NAT + r')\)')
TABLE = re.compile(r'\[(?:\(\d+%positive,\s*' + NAT + r'\)(?:;\s*)?)+\]')
NTABLE = re.compile(r'potential_decode\s+\[(?:\(\d+%positive,\s*\d+%N\)(?:;\s*)?)+\]')
GATE = re.compile(r'\[(?:\d+%positive(?:;\s*)?)+\]')
NDECODE = ('Definition potential_decode (xs:list(positive*N)):list(positive*nat):='
           'map(fun kv=>(fst kv,N.to_nat(snd kv)))xs.')


def nat_value(text):
    if text.isdecimal():
        return int(text)
    a, b = text[1:-1].split(' * 1000 + ')
    return int(a) * 1000 + int(b)


def encode(rows):
    chunks = []
    for start in range(0, len(rows), 128):
        previous, payload = 0, ''
        for key, value in rows[start:start + 128]:
            delta = key - previous
            if not 0 < delta < 65536:
                raise ValueError('keys must increase, with 16-bit deltas')
            while delta >= 8:
                payload += format(8 + delta % 8, 'x')
                delta //= 8
            payload += format(delta, 'x')
            if value is not None:
                if not 0 < value < 256:
                    raise ValueError('rank index does not fit eight bits')
                payload += f'{value:02x}'
            previous = key
        chunks.append(payload)
    return chunks


def decode(chunks, pairs):
    rows = []
    for payload in chunks:
        offset, previous, count = 0, 0, 0
        while offset < len(payload):
            scale, delta = 1, 0
            for _ in range(6):
                if offset == len(payload):
                    raise ValueError('truncated key')
                digit = int(payload[offset], 16)
                offset += 1
                delta += scale * (digit & 7)
                if digit < 8:
                    break
                scale *= 8
            else:
                raise ValueError('oversized key')
            if delta == 0:
                raise ValueError('keys must increase')
            previous += delta
            value = None
            if pairs:
                if offset + 2 > len(payload):
                    raise ValueError('truncated rank')
                value = int(payload[offset:offset + 2], 16)
                offset += 2
                if value == 0:
                    raise ValueError('zero rank index')
            rows.append((previous, value))
            count += 1
        if count > 128:
            raise ValueError('oversized chunk')
    return rows


@dataclass
class Literal:
    start: int
    end: int
    rows: list
    pairs: bool


def literals(source):
    result = []
    n_decoder = ('potential_decode' in source and
                 re.sub(r'\s+', '', NDECODE) in re.sub(r'\s+', '', source))
    for pattern, kind in [(TABLE, 'nat'), (NTABLE, 'N'), (GATE, 'gate')]:
        for match in pattern.finditer(source):
            if kind == 'N':
                # This particular decoder is just map N.to_nat. Do not assume
                # arbitrary user-defined functions with this name mean that.
                if not n_decoder:
                    continue
                rows = [(int(k), int(v)) for k, v in
                        re.findall(r'\((\d+)%positive,\s*(\d+)%N\)', match[0])]
            elif kind == 'nat':
                rows = [(int(m[1]), nat_value(m[2])) for m in PAIR.finditer(match[0])]
            else:
                rows = [(int(k), None) for k in re.findall(r'(\d+)%positive', match[0])]
            if len(rows) < 8 or any(a[0] >= b[0] for a, b in zip(rows, rows[1:])):
                continue
            result.append(Literal(match.start(), match.end(), rows, kind != 'gate'))
    result.sort(key=lambda x: x.start)
    if any(a.end > b.start for a, b in zip(result, result[1:])):
        raise ValueError('overlapping certificate tables')
    return result


def rewrite(source, module):
    # Existing hand-packed FuelPhase certificates retain their own format.
    if (BEGIN in source or 'hfd_dphi' in source or 'hfd_dgate' in source
            or len(source.encode()) < MIN_BYTES):
        return source
    if not re.fullmatch(r'CBT_[A-Z][A-Z0-9]*_\d+', module):
        raise ValueError('expected a closeout batch module name')
    tables = literals(source)
    if not tables:
        return source
    keys = sorted({key for table in tables for key, _ in table.rows})
    ranks = sorted({0} | {value for table in tables for _, value in table.rows if value is not None})
    if len(keys) >= 65536 or len(ranks) >= 256:
        return source
    ki = {key: i + 1 for i, key in enumerate(keys)}
    ri = {rank: i + 1 for i, rank in enumerate(ranks)}
    prefix = 'ctp_' + module
    if re.search(r'\b' + prefix + r'\w*\b', source):
        raise ValueError('compact-table name collision')
    output, previous = [], 0
    for table in tables:
        rows = [(ki[key], ri[value] if table.pairs else None) for key, value in table.rows]
        chunks = encode(rows)
        replay = [(keys[key - 1], ranks[value - 1] if table.pairs else None)
                  for key, value in decode(chunks, table.pairs)]
        if replay != table.rows:
            raise ValueError('certificate data changed during packing')
        payload = '[' + ';\n '.join('0x' + c + '%huint' for c in chunks) + ']'
        call = (f'hfd_dphi {prefix}_keys {prefix}_ranks' if table.pairs
                else f'hfd_dgate {prefix}_keys')
        output.extend([source[previous:table.start], f'({call} {payload})'])
        previous = table.end
    output.append(source[previous:])
    text = ''.join(output)
    header = [BEGIN, 'From Coq Require Import NArith Hexadecimal.',
              'From BBB4.Checkers Require Import HexFuelData.']
    header.append(f'Local Definition {prefix}_keys := hfd_pool [' +
                  ';\n '.join(str(key) + '%positive' for key in keys) + '].')
    last, name = 0, '0'
    for i, rank in enumerate(ranks):
        nxt = f'{prefix}_n{i}'
        header.append(f'Local Definition {nxt} : nat := N.to_nat {rank - last}%N + {name}.')
        last, name = rank, nxt
    header.append(f'Local Definition {prefix}_ranks := hfd_pool [' +
                  '; '.join(f'{prefix}_n{i}' for i in range(len(ranks))) + '].')
    header.append(END)
    marker = 'Import ListNotations.\n'
    if marker not in text:
        raise ValueError('missing closeout import header')
    return text.replace(marker, marker + '\n' + '\n'.join(header) + '\n', 1)


def expand(source):
    """Recover literal lists for review; N-decoded tables become nat lists."""
    if BEGIN not in source:
        return source
    start, end = source.index(BEGIN), source.index(END) + len(END)
    header = source[start:end]
    match = re.search(r'Local Definition (ctp_CBT_\w+)_keys := hfd_pool \[(.*?)\]\.', header, re.S)
    if not match:
        raise ValueError('invalid compact-table dictionary')
    prefix = match[1]
    keys = [int(k) for k in re.findall(r'(\d+)%positive', match[2])]
    ranks, previous = [], 0
    for delta in re.findall(r': nat := N.to_nat (\d+)%N \+ \w+\.', header):
        previous += int(delta)
        ranks.append(previous)
    text = source[:start] + source[end:]
    pattern = re.compile(r'\(hfd_d(phi|gate) ' + prefix + r'_keys(?: ' + prefix + r'_ranks)? (\[[^\]]*\])\)')
    def unpack(match):
        pairs = match[1] == 'phi'
        rows = decode(re.findall(r'0x([0-9a-f]+)%huint', match[2]), pairs)
        if pairs:
            return '[' + ';\n '.join(f'({keys[k-1]}%positive, {ranks[v-1]})' for k, v in rows) + ']'
        return '[' + ';\n '.join(f'{keys[k-1]}%positive' for k, _ in rows) + ']'
    return pattern.sub(unpack, text)


if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--expand', action='store_true')
    ap.add_argument('source', type=Path)
    args = ap.parse_args()
    text = args.source.read_text()
    print(expand(text) if args.expand else rewrite(text, args.source.stem), end='')
