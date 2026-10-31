"""Build hash-pinned, untrusted affine search variants from the upstream source.

These heuristics only propose certificates. Replay in the repository's Coq
checker, census membership and recursive coqchk remain required for a proof.
"""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

UPSTREAM_SHA = 'cdffab331bb1987b9995a538bcfb62616c1e2a83ca62a3f4ca8a61f0392e3796'
THREE_SHA = '7b6f27d59767fcf5f5b5b25014034ad345dee5542d5835feaa8fa8b6aee82f77'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def three_samples(source):
    start = source.index('static int fit5_k(const Samp *const s[5]')
    end = source.index('/* ---------------- v4', start)
    part = source[start:end]
    debug = '''    if (g_dbg) {
        fprintf(stderr, "dbg: fit5 k-series %lld %lld %lld %lld %lld\\n",
                (long long)k[0], (long long)k[1], (long long)k[2],
                (long long)k[3], (long long)k[4]);
    }
'''
    assert part.count(debug) == 1
    part = part.replace(debug, '')
    for old, new in [('[5]', '[3]'), ('[4]', '[2]'), ('j < 5', 'j < 3'),
                     ('i < 5', 'i < 3'), ('i < 4', 'i < 2'),
                     ('if (n < 6)', 'if (n < 4)'), ('n - 5', 'n - 3'), ('n - 9', 'n - 5')]:
        part = part.replace(old, new)
    result = source[:start]+part+source[end:]
    if hashlib.sha256(result.encode()).hexdigest() != THREE_SHA:
        raise ValueError('Three-sample transformation differs from its pinned source')
    return result


def short_cell(source):
    source = source.replace('if (groups[i].nseen < 6)', 'if (groups[i].nseen < 3)')
    start = source.index('static int group_fit(const Group *gr, Tpl *t)')
    end = source.index('/* ---------------- v4', start)
    source = source[:start]+'''static int group_fit(const Group *gr, Tpl *t) {
    const int32_t n = gr->nseen < IR_SAMPLES ? gr->nseen : IR_SAMPLES;
    if (n < 3) return -1;
    const Samp *pick[3];
    for (int32_t stride = 1; stride <= 4; stride++) {
        for (int32_t w = n - 1 - 2*stride; w >= 0; w--) {
            for (int i = 0; i < 3; i++) pick[i] = &gr->s[w + stride*i];
            if (fit5(pick, t) == 0) return 0;
        }
    }
    return -1;
}

'''+source[end:]
    return source.replace('cands[j].enc > cands[i].enc', 'cands[j].enc < cands[i].enc')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--upstream', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--mode', choices=['three-samples', 'short-cell'], required=True)
    args = parser.parse_args()
    source = args.upstream/'src/irules.c'
    if sha(source) != UPSTREAM_SHA:
        raise ValueError('Unsupported upstream affine-search source revision')
    text = three_samples(source.read_text())
    if args.mode == 'short-cell':
        text = short_cell(text)
    args.output.mkdir(parents=True, exist_ok=True)
    generated = args.output/('irules-'+args.mode+'.c')
    binary = generated.with_suffix('')
    generated.write_text(text)
    flags = ['-O3', '-Wall', '-Wextra', '-Werror', '-std=c11']
    subprocess.run(['cc', *flags, '-I', str(args.upstream/'src'), str(generated),
                    str(args.upstream/'src/sim.c'), str(args.upstream/'src/tm.c'),
                    '-o', str(binary)], check=True)
    report = {'mode': args.mode, 'untrusted_search_only': True,
              'generated_source_sha256': sha(generated), 'binary_sha256': sha(binary),
              'builder_sha256': sha(Path(__file__)), 'compiler_flags': flags,
              'compiler': subprocess.check_output(['cc', '--version'], text=True).splitlines()[0],
              'upstream_sources_sha256': {name: sha(args.upstream/'src'/name)
                                         for name in ['irules.c', 'sim.c', 'sim.h', 'tm.c', 'tm.h']}}
    generated.with_suffix('.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
