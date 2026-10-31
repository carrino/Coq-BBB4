# Reusing the paired-digit tail for 21 further families

This board proves state bound 0 and instruction bound 147 for 21 additional
frozen-census families. The bounds hold for every completion. The instruction
bound is a common upper bound; no exact-score claim is made for these rows.

The original score 10 machine has a permanent left marker and seven recurrent
instructions. Its only eventually absent instruction is B1. The new proof imports
that machine's unchanged invariant and recurrence theorems, then proves that:

- Changing B1 cannot alter execution inside the invariant.
- Appending arbitrary dormant cells beyond the left marker preserves every
  future step, because the invariant never moves left beyond that marker.
- Entering a proved source configuration transfers all seven recurrence
  witnesses, even if the target and source entered that configuration at
  different times.

Each target first runs its actual finite blank-start prefix. Reflection and
blank-preserving symbol relabeling normalize the table; optional state exchange
is applied only to the suffix after its checked entry. Coq checks the concrete
prefix and configuration equality, including harmless trailing blank padding.
Source anchors range from 10 to 40; target prefixes range from 16 to 147. The
existing invariant proves B1 exclusion after entry, while the transferred
recurrence witnesses establish the state and instruction bounds.

The deterministic screen tested all 24 images of the seven-transition template
against 31,481 rows (the 31,495-row instruction residual minus 14 audited ternary
families). It found 22 matches. One,
`1LB2LB2LA1RB_2RA1LA3RB2LA`, is handled by the separate exact-conjugacy board and
is excluded here. Every remaining match coalesced with a source configuration,
allowing a dormant suffix. The all-eight-transition pair-capacity template also
matched one exchanged/reflected table, but its prefix did not coalesce within
4,096 steps; that row is excluded and remains unresolved by this package.

From `four/`, after the core theory build:

```sh
python3 tools/check_burn3_tail_invariant.py --timeout 300 --audit-timeout 1200
python3 tools/check_burn5_tail_template.py --timeout 300 --audit-timeout 1200
```

The second command compiles the generic transfer, concrete 21-family board and
exact inventory, then runs full recursive `coqchk`. The board proves its bounds
for all completions and proves each row belongs to the frozen pending census.
Inputs, handwritten and generated sources, replay tooling and current objects
are pinned. Published reports and inventories remain unchanged on reruns.

The bounded discovery commands are:

```sh
python3 tools/screen_burn5_handwritten_templates.py
python3 tools/prepare_burn5_tail_template.py
```

They produce untrusted candidate reports; all accepted entries, invariants,
recurrence transfer and inventory claims are checked independently by Coq.
