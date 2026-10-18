#!/usr/bin/env python3
"""Compare the old and sliding-window n-gram seeding with native Coq.

Build the native NGram dependencies first. The committed tier corpus supplies
104 machines from the four n-gram classes and the deep-ladder residue. Both
variants use the same eight rungs, fuel and rounds; the equality check compares
the actual gram sets. Output objects stay outside the production proof tree.
"""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--repeat', type=int, default=10)
    args = parser.parse_args()
    if args.repeat < 1:
        parser.error('--repeat must be positive')
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    if (out / 'metadata.json').exists():
        parser.error('use a new output directory to preserve earlier measurements')
    config = subprocess.check_output(['coqc', '-config'], text=True)
    if 'COQ_NATIVE_COMPILER_DEFAULT=no' in config:
        parser.error('this benchmark requires a native-capable Coq')
    _, hard = resource.getrlimit(resource.RLIMIT_STACK)
    resource.setrlimit(resource.RLIMIT_STACK, (hard, hard))
    corpus = ROOT / 'tools/probes/ProbeTierCost.v'
    text = corpus.read_text()
    data = text[text.index('(* 0RB1RD_1LC1LD_1RB---_1LC1RA *)'):
                text.index('(* counts in the full census')]
    prelude = '''From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement CTape PosEnc.
From BBB4.Checkers Require Import NGram.
Import ListNotations.
'''
    samples = out / 'Samples.v'
    samples.write_text(prelude + data)
    flags = ['-Q', str(ROOT / 'theories'), 'BBB4', '-Q', str(out), 'BenchNGram',
             '-w', '-abstract-large-number,-deprecated-native-compiler-option']
    subprocess.run(['coqc', *flags, '-native-compiler', 'yes', str(samples)], check=True)
    common = prelude + '''From BenchNGram Require Import Samples.
Definition fuel := 200000.
Definition rounds := 512.
Definition samples := grp_N2 ++ grp_N3 ++ grp_N4 ++ grp_N6 ++ grp_RES.
Definition rungs := [(2,100);(3,200);(4,400);(6,800);(3,0);(3,64);(3,256);(3,1024)].
Definition old_seed n l :=
  map (fun d => win (lift_side l) d n) (seq 1 (length l + 1)).
Definition sets (grow : TM -> cconf -> nat -> nat -> gset -> gset -> gset * gset)
    (seed : nat -> list Sym -> list (list Sym)) (tm : TM) (nt : nat * nat) :=
  let '(n,t) := nt in
  match csteps tm t c0 with
  | None => (gempty,gempty)
  | Some cc => let '(_, (l,_,r)) := cc in
    grow tm (ng_start n cc) fuel rounds
      (gadds (seed n l) gempty) (gadds (seed n r) gempty)
  end.
'''
    sources = {'theories/Checkers/NGram.v': ROOT / 'theories/Checkers/NGram.v',
               'corpus': corpus}
    (out / 'metadata.json').write_text(json.dumps({
        'coq': subprocess.check_output(['coqc', '--version'], text=True),
        'repeat': args.repeat,
        'sha256': {k: hashlib.sha256(p.read_bytes()).hexdigest() for k, p in sources.items()},
    }, indent=2) + '\n')
    equality = '''
Example same_gram_sets : forallb (fun tm => forallb (fun nt =>
  let '(a,b) := sets ng_grow old_seed tm nt in
  let '(c,d) := sets ng_grow ng_seed_side tm nt in
  PositiveSet.equal a c && PositiveSet.equal b d) rungs) samples = true.
Proof. native_compute. reflexivity. Qed.
Print Assumptions same_gram_sets.
Print Assumptions ng_seed_side_spec.
Print Assumptions seed_ok_side_spec.
'''
    for name, expression in [
        ('Equality', equality),
        ('Reference', ('ng_grow', 'old_seed')),
        ('Sliding', ('ng_grow', 'ng_seed_side')),
    ]:
        if isinstance(expression, tuple):
            grow, seed = expression
            expression = f'''
Time Eval native_compute in map (fun nt => fold_left Nat.add
  (map (fun tm => let '(a,b) := sets {grow} {seed} tm nt in
    PositiveSet.cardinal a + PositiveSet.cardinal b)
    (flat_map (fun _ => samples) (seq 0 {args.repeat}))) 0) rungs.
'''
        source = out / f'{name}.v'
        source.write_text(common + expression)
        with (out / f'{name}.log').open('w') as log:
            subprocess.run([
                sys.executable, str(ROOT / 'tools/time_command.py'),
                '--log', str(out / 'times.jsonl'), '--phase', name, '--',
                'coqc', *flags, '-native-compiler', 'ondemand', str(source)],
                stdout=log, stderr=subprocess.STDOUT, check=True)
        print(f'{name}: {out / (name + ".log")}', flush=True)


if __name__ == '__main__':
    main()
