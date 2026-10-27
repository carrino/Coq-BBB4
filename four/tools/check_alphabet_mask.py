"""Close additional three-symbol families by masking forbidden writes.

A masked BBB(2,3) machine surviving67 steps cannot halt later. The separate
221-family static-alphabet stage is preserved. --prepare compiles the new
stage without publishing an audited report; the default includes coqchk.
"""
import argparse
import json
from pathlib import Path
import subprocess
import time

from check_alphabet23 import generate, sha, source_tree_digest, SOURCES
from generate_pipeline_examples import codes

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
BUILD = ROOT/'build/alphabet-mask'
BUNDLE = ROOT/'research/alphabet-mask-families.json'
BASE_BUNDLE = ROOT/'research/alphabet23-families.json'
BASE_REPORT = ROOT/'research/alphabet23-checked.json'
REPORT = ROOT/'research/alphabet-mask-checked.json'


def survives(machine, omitted):
    table = codes(machine)
    state = position = 0
    tape = {}
    for _ in range(67):
        transition = table[4*state+tape.get(position, 0)]
        if transition == 16 or transition//4 == omitted:
            return False
        tape[position] = transition//4
        position += 1 if transition//2 % 2 else -1
        state = transition % 2
    return True


def select(source):
    machines = source.read_text().splitlines()
    if len(machines) != len(set(machines)):
        raise ValueError('Repeated original family')
    if any(codes(m)[0]//4 != 1 for m in machines):
        raise ValueError('Class saturation expects normalized inputs whose first write is1')
    baseline = json.loads(BASE_BUNDLE.read_text())
    if sha(source) != baseline['input_sha256']:
        raise ValueError('Mask selection must use the same frozen input cohort')
    old = {r['machine'] for r in baseline['rows']}
    selected = []
    for machine in machines:
        for omitted in (3, 2):
            if survives(machine, omitted):
                selected.append({'machine':machine, 'unused_symbol':omitted})
                break
    if not old <= {r['machine'] for r in selected}:
        raise ValueError('Static alphabet rows must also survive masking')
    return dict(input_families=len(machines), input_sha256=sha(source),
        omitted_symbols_checked=[2,3], normalization='Every input first writes1; blank0 and written1 must remain in any closed three-symbol alphabet.',
        base_bundle_sha256=sha(BASE_BUNDLE), total_mask_survivors=len(selected),
        previously_selected=len(old), rows=[r for r in selected if r['machine'] not in old])


def source(rows):
    text = generate(rows)
    text = text.replace('check_alphabet23.py', 'check_alphabet_mask.py')
    text = text.replace('AlphabetReduction Alphabet23.', 'AlphabetReduction Alphabet23 AlphabetMask.')
    text = text.replace('alphabet_batch_check', 'mask_batch_check')
    text = text.replace('alphabet_board', 'mask_board')
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--select', type=Path)
    parser.add_argument('--prepare', action='store_true')
    parser.add_argument('--refresh', action='store_true')
    parser.add_argument('--timeout', type=int, default=3600)
    args = parser.parse_args()
    if args.select:
        BUNDLE.write_text(json.dumps(select(args.select), separators=(',', ':'))+'\n')
    data = json.loads(BUNDLE.read_text())
    if data['base_bundle_sha256'] != sha(BASE_BUNDLE):
        raise ValueError('Frozen static alphabet bundle changed')
    rows = data['rows']
    machines = [r['machine'] for r in rows]
    old = {r['machine'] for r in json.loads(BASE_BUNDLE.read_text())['rows']}
    if not rows or len(machines) != len(set(machines)) or set(machines)&old:
        raise ValueError('Empty, duplicate, or already selected mask family')
    if any(r['unused_symbol'] not in (2,3) or not survives(r['machine'],r['unused_symbol']) for r in rows):
        raise ValueError('Invalid masked survival candidate')
    if not args.prepare:
        baseline = json.loads(BASE_REPORT.read_text())
        if baseline['bundle_sha256'] != sha(BASE_BUNDLE):
            raise ValueError('Static stage audit does not match the frozen bundle')
        for path, digest in baseline['source_sha256'].items():
            if sha(REPO/path) != digest:
                raise ValueError(f'Audited static source changed: {path}')
    BUILD.mkdir(parents=True, exist_ok=True)
    generated = BUILD/'MaskBoard.v'
    generated.write_text(source(rows))
    members = BUILD/'machines.txt'
    members.write_text('\n'.join(machines)+'\n')
    flags = ['-Q', str(REPO/'small/theories'), 'SmallBB',
             '-Q', str(ROOT/'theories'), 'BBB24', '-Q', str(BUILD), 'BBB24AlphabetMask']
    namespace = 'BBB24AlphabetMask.MaskBoard'
    commands = [
        (['coqc','-native-compiler','no',*flags,str(ROOT/'theories/AlphabetMask.v')], 'transport.log'),
        (['coqc','-native-compiler','no',*flags,str(generated)], 'compile.log'),
    ]
    if not args.prepare:
        commands.append((['coqchk','-silent','-bytecode-compiler','yes',*flags,namespace], 'coqchk.log'))
    start = time.monotonic()
    for command, log in commands:
        with (BUILD/log).open('w') as output:
            subprocess.run(['nice','-n','10',*command],cwd=REPO,stdout=output,stderr=subprocess.STDOUT,
                           check=True,timeout=args.timeout)
    if args.prepare:
        print(json.dumps({'coq_compiled_only':len(rows),'audited_report_written':False}))
        return
    report = dict(families=len(rows), concrete=sum('---' not in m for m in machines),
        partial=sum('---' in m for m in machines), census_linked=len(rows),
        state_bound=59, instruction_bound=67,
        prior_static_families=len(old), total_three_symbol_families=len(old)+len(rows),
        descriptor=dict(module=namespace,board=namespace+'.closed_mask_board',
            sound=namespace+'.closed_mask_board_sound',small_sound=namespace+'.closed_mask_board_small_sound',
            nonhalt=namespace+'.closed_mask_board_nonhalt',was_pending=namespace+'.closed_mask_board_was_pending',
            discharge=namespace+'.alphabet_families_discharged',coverage=namespace+'.bootstrap_alphabet_coverage',
            state_bound=59,instruction_bound=67,members=str(members.relative_to(ROOT)),
            flags=['-Q','small/theories','SmallBB','-Q','four/theories','BBB24',
                   '-Q','four/build/alphabet-mask','BBB24AlphabetMask']),
        bundle_sha256=sha(BUNDLE), base_report_sha256=sha(BASE_REPORT),
        member_ids_sha256=sha(members), generated_source_sha256=sha(generated),
        source_sha256={p:sha(REPO/p) for p in SOURCES+[
            'four/theories/AlphabetMask.v','four/tools/check_alphabet_mask.py']},
        small_theories_source_tree_sha256=source_tree_digest(REPO/'small/theories'),
        validation='Compiled masked transport, every67-step survival and pending check, then recursive coqchk.',
        accounting='Only new original families; all completions covered. Prior221 remain in their separate frozen report.')
    serialized = json.dumps(report,indent=2)+'\n'
    if args.refresh or args.select or not REPORT.exists():
        REPORT.write_text(serialized)
    elif REPORT.read_text() != serialized:
        raise ValueError('Masked alphabet evidence changed')
    print(json.dumps({'checked_families':len(rows),'seconds':round(time.monotonic()-start,2)}))


if __name__ == '__main__':
    main()
