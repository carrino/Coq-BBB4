# A sparse A0 return is a binary word counter

The exact census family `1LB2LB3RA3LB_1RB1LA3RA1RA`
(`tr24-2806290152`) has **state and instruction upper bounds zero**. Every
instruction recurs arbitrarily late. The theorem covers every completion and
proves original bootstrap membership and exact board inventory. Displayed with
the first move right, the program is `1RB2RB3LA3RB_1LB1RA3LA1LA`.

The old capacity diagnostics left A0 unresolved. Its sparse finite observations
selected this proof attempt; they are not recurrence evidence. The Coq proof
uses symbolic word macros instead of a simulation cutoff or the old native
seven-target witnesses.

At its main boundaries the machine is in A with a blank head and left tape,
and right word `(12)^m 13 13 12`. An elementary scan turns a run of `12` pairs
into `31` pairs on the reversed left stack. A recursive block macro consumes
one left `31` pair, adds a right `12` pair, and preserves its `13` delimiter.
It takes `H(m) = 16·2^m − 4` steps. The proof handles arbitrary left and right
contexts.

Alternating blank-head and head-one boundary phases changes `m` to `m+2` in
`H(m)+6+H(m+1) = 48·2^m − 2` steps. Coq checks the actual blank-start entry at
step 42 with `m=1`. Induction gives main returns beyond every finite horizon.
The finite startup of every return fires seven instructions; the eighth, A3,
fires at the `13` delimiter after the symbolic scan. Consequently all eight
instructions recur, independently of any saved graph certificate.

The checked source consists of `BoundaryCounter.v`, `Board.v`, and
`Regression.v` under `proof-sources/instruction-sparse-return/`. Regressions
include arbitrary contexts, exact first gaps, off-by-one rejection, a wrong
delimiter, the actual blank prefix, and rare-target returns. The proof adds no
axioms; its only imported assumption is the repository's existing functional
extensionality.

After building the shared instruction dependencies, replay with Coq on PATH:

```sh
python3 four/tools/check_instruction_sparse_return.py
```

The driver reconstructs every source, compiles the exact board and inventory,
and performs a full recursive kernel audit including regressions. Inputs and
reports remain frozen; generated sources and current receipts stay below
`four/build/instruction-sparse-return/`. This is one instruction upgrade and no
new state coverage; it does not establish a global instruction maximum.
