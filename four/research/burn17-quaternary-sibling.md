# Quaternary checksum sibling

The complete machine `1LB2LB0LB1RA_2RB2RA3LB1RB` has a kernel-checked state
quasihalting bound of zero, with both states recurring arbitrarily late.
This registers one exact census family; aggregate integration is separate.

Its base-four digits are encoded, nearest first, as `11`, `21`, `12`, and
`22`. The boundary head is the digit sum modulo three. The blank run reaches
the one-digit maximum at step 3. Incrementing a nonmaximal digit rotates the
head `0→1→2→0`; clearing maximal digits preserves the checksum modulo three.
All-maximal digits therefore force head zero, and overflow produces digits
`1,0^(n-1),2`, also with checksum zero.

With `r` carried digits, increment takes `4*r+2` steps when bumping digit
zero or two, and `4*r+4` when bumping digit one. Overflow with `n` digits
takes `4*n+3` steps. The checksum structure matches the earlier quaternary
counter, while the new machine-specific sweeps are reproved: A3 writes `1`
and stays in A, and B3 writes `1` and stays in B. Its overflow uses a B sweep
across the entire temporary `3` block before returning to A.

The finite digit type, checksum preservation, arbitrary-context macros and
positive chaining establish nonhalting and unbounded A returns. Each main
configuration enters B on its next step, proving B recurrence directly.
The wrong-head overflow is explicitly excluded by the derived checksum and
covered by a regression.

Native controls checked all 21,844 valid main configurations with one through
seven digits. These are provenance only; the universal Coq proofs establish
the result. Eight imported regressions are included in the full recursive
kernel audit.

After building the core, run from the repository root:

```sh
python3 four/tools/check_burn17_quaternary_sibling_native.py --check
python3 four/tools/check_burn17_quaternary_sibling.py --timeout 600 --audit-timeout 3600
```

The checked report `research/burn17-quaternary-sibling-checked.json` pins
sources, objects and the exact inventory. This isolated proof uses core
BBB24 modules only, introduces no new axioms, changes no accepted source or
runner, and makes no instruction-bound claim.
