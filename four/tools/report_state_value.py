"""Check and print the completed state BBB(2,4) equality, never a checkpoint.

Value.v is deliberately absent until the exhaustive upper bound is proved.
No success report is available from the champion or individual cases alone.
"""
import argparse
from pathlib import Path
import re
import shlex
import subprocess
import sys

FOUR = Path(__file__).resolve().parents[1]
TARGET = 205770076433044242247860
THEOREM = 'BBB24.Value.BBB24_state_value'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-source', action='store_true',
                        help='Fail early if the final global theorem source is missing')
    args = parser.parse_args()
    if not (FOUR / 'theories/Value.v').is_file():
        print(f'BBB(2,4) = {TARGET}: the final global equality theorem is not assembled.',
              file=sys.stderr)
        print('Missing four/theories/Value.v. Use make proof-2-4-checkpoint to audit '
              'the current partial development.', file=sys.stderr)
        return 2
    if args.check_source:
        return 0

    # Follow the actual project load paths, including future census namespaces.
    tokens = shlex.split((FOUR / '_CoqProject').read_text(), comments=True)
    flags = []
    i = 0
    while i < len(tokens):
        width = {'-Q': 3, '-R': 3, '-I': 2}.get(tokens[i])
        if width:
            flags.extend(tokens[i:i + width])
            i += width
        else:
            i += 1

    build = FOUR / 'build/state-value-report'
    build.mkdir(parents=True, exist_ok=True)
    source = build / 'CheckValue.v'
    source.write_text('''From Coq Require Import NArith.
From BBB24 Require Import Statement Spec ValueSpec.
From BBB24 Require Value.
Definition checked_state_equality :
  BBB24_state_lower_bound score /\\ (forall tm : TM, QHBound score tm) :=
  (BBB24.Value.BBB24_state_value : BBB24.ValueSpec.BBB24_state_statement).
Example checked_numeric_target : scoreN = 205770076433044242247860%N.
Proof. reflexivity. Qed.
Example checked_nat_target : score = N.to_nat 205770076433044242247860%N.
Proof. reflexivity. Qed.
Check BBB24.Value.BBB24_state_value.
Check checked_state_equality.
Print AttainsSt.
Print QHBound.
Print BBB24_state_is.
Print BBB24_state_statement.
Eval vm_compute in scoreN.
Print Assumptions checked_state_equality.
''')
    flags.extend(['-Q', str(build), 'BBB24ValueReport'])
    compile_log = build / 'compile.log'
    with compile_log.open('w') as stream:
        subprocess.run(['coqc', '-native-compiler', 'no', *flags, str(source)],
                       cwd=FOUR, stdout=stream, stderr=subprocess.STDOUT, check=True)
    text = compile_log.read_text()
    if 'Axioms:' in text:
        assumptions = text.split('Axioms:')[-1]
        declarations = re.findall(r"(?m)^([^\s:]+)\s*(?=\n?\s*:)", assumptions)
        if declarations != ['FunctionalExtensionality.functional_extensionality_dep']:
            raise RuntimeError('Unexpected theorem assumptions; inspect ' + str(compile_log))
    elif 'Closed under the global context' not in text:
        raise RuntimeError('Missing Print Assumptions result: ' + str(compile_log))

    audit_log = build / 'coqchk.log'
    with audit_log.open('w') as stream:
        subprocess.run(['coqchk', '-silent', '-bytecode-compiler', 'yes', *flags,
                        'BBB24ValueReport.CheckValue'], cwd=FOUR, stdout=stream,
                       stderr=subprocess.STDOUT, check=True)
    print('=' * 72)
    print(f'BBB(2,4) = {TARGET} -- state based, kernel checked')
    print(f'{THEOREM} : BBB24.ValueSpec.BBB24_state_statement')
    print('The champion attains this score, and every two-state, four-symbol '
          'machine satisfies the upper bound.')
    print(text.rstrip())
    print('Full recursive coqchk: passed. Logs: ' + str(build.relative_to(FOUR)))
    print('=' * 72)
    return 0


if __name__ == '__main__':
    sys.exit(main())
