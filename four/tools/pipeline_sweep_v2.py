"""Run a fresh pipeline sweep with guarded per-row alarms.

All result handling stays in the frozen pipeline_sweep.py. Previous full runs
remain immutable; new manifests additionally pin this wrapper and v2 driver.
"""
from pathlib import Path
import subprocess
import sys

import pipeline_sweep as base

ROOT = base.ROOT
PROBE = ROOT/'build/wave3/pipeline-v2/probe'


def main():
    argv = sys.argv[1:]
    if '--probe' in argv:
        raise ValueError('This wrapper selects its guarded driver explicitly')
    if '--build' in argv:
        argv.remove('--build')
        PROBE.parent.mkdir(parents=True, exist_ok=True)
        for command in [
            ['coqc', '-native-compiler', 'no', '-Q', 'theories', 'BBB24', 'tools/ExtractPipeline.v'],
            ['ocamlopt', '-w', '-a', '-I', 'build/pipeline', '-c', 'build/pipeline/checkers.mli'],
            ['ocamlopt', '-w', '-a', '-I', 'build/pipeline', '-c', 'build/pipeline/checkers.ml'],
            ['ocamlopt', '-w', '-a', '-I', 'build/pipeline', '-c', '-o',
             'build/wave3/pipeline-v2/pipeline_probe_v2.cmx', 'tools/pipeline_probe_v2.ml'],
            ['ocamlopt', '-w', '-a', '-I', 'build/pipeline', 'unix.cmxa',
             'build/pipeline/checkers.cmx', 'build/wave3/pipeline-v2/pipeline_probe_v2.cmx',
             '-o', str(PROBE)],
        ]:
            subprocess.run(command, cwd=ROOT, check=True)
    original_hashes = base.source_hashes
    base.source_hashes = lambda: {
        **original_hashes(),
        'tools/pipeline_probe_v2.ml': base.digest(ROOT/'tools/pipeline_probe_v2.ml'),
        'tools/pipeline_sweep_v2.py': base.digest(Path(__file__)),
    }
    sys.argv = [sys.argv[0]]+argv+['--probe', str(PROBE)]
    base.main()


if __name__ == '__main__':
    main()
