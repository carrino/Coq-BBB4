# Adjacent-pair capacity closes one frequent instruction holdout

`1LB2RA3RA0RA_1RA2LA0LB3LA` now has a checked recurrence proof for all eight
instructions. Its state and instruction bounds are both **0**: neither a state
nor an instruction has a last occurrence. This adds **one instruction
obligation and zero state obligations** to the next wave; its state bound was
already known. It is separate from the completed burn2 checkpoint and from the
two capacity-pilot proofs and the B1 tail-invariant proof.

The missing instruction was B3. A saved width-2, 930-node graph anchored at
step 4,096 already supplied recurrence witnesses for the other seven
instructions. A binary ranking also worked algebraically for B3, but its
nonempty-left boundary hypothesis was not established by the earlier wall or
single-symbol capacity checks.

The new [pair-capacity theorem](burn3-pair-capacity/PairCapacity.v) supplies that
hypothesis. Write `Lxy` for the number of adjacent pairs `xy` in the left tape
list, read from the head outward, including the final symbol paired with an
implicit blank. The concrete nonnegative value is

```text
V = 3 * count_left(1) + 2 * count_right(3)
    + L01 + 3 * L02 + 3 * L20 + 2 * L22 + graph_node_bias.
```

The node bias is between 0 and 8. Every one of the 2,528 target-avoiding graph
edges satisfies `delta(V) <= 2 * direction`, where left is -1 and right is +1.
Appending blank cells to the left list leaves `V` unchanged because the blank
pair has score zero. Sufficient blank padding therefore initializes
`V < 2 * length(left)`, and the edge inequalities preserve it until B3 occurs.
Since `V` is nonnegative, the left list cannot become empty. The existing
binary-ranking soundness theorem then proves that B3 must be reached. Applying
the argument from arbitrarily late reachable configurations proves recurrence,
without a simulation cutoff or an assumed upper bound on the return time.

The [closeout](burn3-pair-capacity/Closeout.v) combines B3 with the seven
independent witnesses, covers all completions, and checks membership in the
original pending census. The generated inventory theorem identifies exactly
this one machine. The new theorem is isolated under `research/`; the existing
core theory files remain unchanged.

Replay after `make -C four all`, from the repository root:

```bash
python3 four/tools/check_burn3_pair_capacity.py \
  --timeout 300 --audit-timeout 1200
```

The [input](burn3-pair-capacity-input.json) pins a 10,346-byte compact bundle.
The runner pins all consumed sources, regenerates four Coq files under
`build/burn3-frequent-invariants/proof/`, and preserves published evidence on
replay. It also checks rejection of width 1, zero capacity scale, a nonzero
blank-pair charge, omitted pair terms, and the earlier boundary certificate.

The [checked report](burn3-pair-capacity-checked.json) records 10.308 seconds
for compilation and a full recursive kernel audit of 269 modules with no
reused modules, completed in 40.6 seconds. The only assumption is the existing
functional extensionality assumption. The theorem, runner, exact inventory,
source pins, and audit closure were independently reviewed.

The other frequent-target machine,
`1LB2RA2LA0LB_0RB3RA3RB1LA`, still lacks its A2 recurrence proof. Neither the
saved binary ranking proposals nor a bounded adjacent-pair ranking proposal
closed that case; this result makes no claim about it.
