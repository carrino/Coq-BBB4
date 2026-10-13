#!/usr/bin/env python3
"""Prove fixed census-bound comparisons through the binary Coq lemma.

Only three known proof shapes are normalized: two-goal QH stages, lap QH
stages' final bound goal, and standalone boolean bound lemmas. Machines,
checker calls, parameters and theorem statements are preserved.
"""
import argparse
from pathlib import Path
import re

REPO = Path(__file__).resolve().parents[2]
IMPORT = 'From BBB4.CensusTr Require Import BoundCheckTr.\n'
CAST = 'vm_cast_no_check (eq_refl true)'
PROOF = re.compile(r'\bProof\.(.*?)\bQed\.', re.S)
STAGE = re.compile(r'\b(?:tcycler_qh_stage(?:_L)?|qh_(?:plain|lex)_stage|rwqh_stage)\b')
DIRECT = re.compile(r'((?:Lemma|Theorem)\s+\w+\s*:\s*\([^\n]*<=\?\s*32779478\)\s*=\s*true\.\s*Proof\.\s*)'
                    + re.escape(CAST) + r'(\.\s*Qed\.)')


def rewrite(source):
    def proof(match):
        body = match[1]
        if STAGE.search(body) and '32779478). all: ' + CAST in body:
            body = body.replace('32779478). all: ' + CAST,
                                '32779478); [' + CAST +
                                ' | apply bound_tr_leb; ' + CAST + ']')
        if ('lap_qh_stage ' in body and '32779478).' in body
                and body.rstrip().endswith('- ' + CAST + '.')):
            head, _, tail = body.rpartition('- ' + CAST + '.')
            body = head + '- apply bound_tr_leb; ' + CAST + '.' + tail
        return 'Proof.' + body + 'Qed.'
    after = PROOF.sub(proof, source)
    after = DIRECT.sub(lambda m: m[1] + 'apply bound_tr_leb; ' + CAST + m[2], after)
    if after != source and IMPORT not in after:
        first_import = re.search(r'^From\b', after, re.M)
        pos = first_import.start() if first_import else 0
        after = after[:pos] + IMPORT + after[pos:]
    return after


def generated_files(repo=REPO):
    paths = []
    for pattern in ['theories/CensusTr/ProvTr_QH_*.v',
                    'theories/Machines/CountersTr/LAPQ_*.v',
                    'theories/Machines/LadderTr/*.v']:
        paths.extend(repo.glob(pattern))
    return {p: rewrite(p.read_text()) for p in sorted(paths)}


def rewrite_file(path):
    path = Path(path)
    source = path.read_text()
    after = rewrite(source)
    if after != source:
        path.write_text(after)


def expand(source):
    """Restore the original unary-bound proofs for review or benchmarking."""
    source = source.replace('; [' + CAST + ' | apply bound_tr_leb; ' + CAST + ']',
                            '. all: ' + CAST)
    source = source.replace('apply bound_tr_leb; ' + CAST, CAST)
    if 'bound_tr_leb' in source:
        raise ValueError('unrecognized use of the bound lemma')
    return re.sub(r'^(?:From BBB4.CensusTr Require (?:Import )?BoundCheckTr\.|'
                  r'Import BoundCheckTr\.)\n', '', source, flags=re.M)


def generate(check=False):
    outputs = generated_files()
    changed = [p for p, text in outputs.items() if p.read_text() != text]
    if check and changed:
        raise ValueError('stale binary bound checks: ' + ', '.join(map(str, changed)))
    if not check:
        for p in changed:
            p.write_text(outputs[p])
    print(f'binary bound checks: {"checked" if check else "wrote"} '
          f'{len(outputs) if check else len(changed)} files')


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--expand', type=Path, help='print a file with its original unary-bound proofs')
    args = ap.parse_args()
    if args.expand:
        print(expand(args.expand.read_text()), end='')
    else:
        generate(args.check)
