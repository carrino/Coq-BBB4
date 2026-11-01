"""List or build the complete shared source closure of instruction batches."""
import argparse
import json
import re
import subprocess

from check_campaign import ROOT


def targets():
    summary = json.loads((ROOT / 'research/instruction-burndown-summary.json').read_text())
    result = set()
    for batch in summary['upgrades']:
        report = json.loads((ROOT / 'research' / (batch['name'] + '-checked.json')).read_text())
        for name in report['source_sha256']:
            if name.startswith('theories/'):
                if not re.fullmatch(r'theories/[A-Za-z0-9_/]+\.v', name):
                    raise ValueError('Invalid shared Coq source path: ' + name)
                result.add(name[:-2] + '.vo')
    if not result:
        raise ValueError('Empty shared instruction proof closure')
    return sorted(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build', action='store_true')
    parser.add_argument('--jobs', type=int, default=2)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('Worker count must be positive')
    selected = targets()
    if args.build:
        subprocess.run(['make', '-C', str(ROOT), 'Makefile.coq'], check=True)
        subprocess.run(['make', '-C', str(ROOT), '-f', 'Makefile.coq', '-j' + str(args.jobs), *selected], check=True)
    else:
        print('\n'.join(selected))


if __name__ == '__main__':
    main()
