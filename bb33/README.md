# BB(3,3) lower bounds: Bigfoot and the probable champion

Two 3-state, 3-symbol machines on the BusyBeaverWiki's
[BB(3,3)](https://wiki.bbchallenge.org/wiki/BB(3,3)) page are proved, in
Coq, to run for **more than 119,112,334,170,342,541 steps** -- the step
count of the current BB(3,3) champion `0RB2LA1RA_1LA2RB1RC_1RZ1LB1LC`:

| Machine | Status on the wiki | Theorems | Run proved |
| --- | --- | --- | --- |
| `1RB2RA1LC_2LC1RB2RB_---2LA1LA` ([Bigfoot](https://wiki.bbchallenge.org/wiki/Bigfoot)) | Cryptid, probviously non-halting | `bigfoot_runs_past_champion`, `bigfoot_no_halt_within_champion` | 164,455,975,202,918,183 steps |
| `1RB2LC1RC_2LC---2RB_2LA0LB0RA` ([probable champion](https://wiki.bbchallenge.org/wiki/1RB2LC1RC_2LC---2RB_2LA0LB0RA)) | potential Cryptid, probviously halting | `champion_runs_past_champion`, `champion_no_halt_within_champion` | 119,114,045,079,717,165 steps |

Both statements are about the abstract machine model of the small-machine
development ([`small/theories/Statement.v`](../small/theories/Statement.v)):

```coq
Theorem bigfoot_runs_past_champion :
  exists n c, stepn bigfoot n InitES = Some c /\ N.to_nat bb33_champion_steps <= n.
Theorem bigfoot_no_halt_within_champion :
  forall m, m <= N.to_nat bb33_champion_steps -> stepn bigfoot m InitES <> None.
(* and the same two for champ *)
```

with `bb33_champion_steps : N := 119112334170342541`.  Neither machine is
proved to halt (or not to halt): Bigfoot's halting is an open Collatz-like
problem, and the probable champion's halting, while expected, would require
showing that its forward iteration reaches the halting value
`H = (3^307 - 8282708212) / 13959275` -- see the wiki pages.  What is proved
is the lower bound the two machines would need to beat the champion, which
is the part of the question that is accessible to accelerated simulation.

## Method

Each machine is driven by a small set of **Collatz-like rules** on a family
of tape configurations, taken from the wiki, with **exact step counts**.
The rules are proved symbolically (`theories/Bigfoot.v`,
`theories/Champion.v`): single transitions, "shift rules" that cross a
block of `n` symbols in `n` (or `2n`, `6n`) steps by induction, and the
rules themselves as straight-line compositions of those, with the
polynomial step counts discharged by `lia`/`nia`.  Only the iterated
rules that quantify over the tape are proved by induction; every other
hop is a single `csteps` step checked by conversion.

The rules are then iterated on **binary numbers** (`N`) by `vm_compute`
(`theories/BigfootRun.v`, `theories/ChampionRun.v`): a rule function on
`N`, a soundness bridge to the `nat`-indexed rule lemmas, an iteration
with an accumulated step count, and a `vm_compute` of the trajectory.
No unary number of the order of 10^17 is ever evaluated: the bound is
read off as an `N` comparison and transported with `lia`.

| Machine | Rule system | Rule applications computed | Largest parameter |
| --- | --- | --- | --- |
| Bigfoot | the wiki's six `A(a, 6k+r, c)` rules (from A(2,1,2) at step 69) | 62 | b = 219,012,156 |
| champion | 15 fine-grained rules between dyuan01's families `A1`, `A2`, `B`, plus the accelerated loop `A1(m+2d, b, n+2d) -> A1(m, b+3d, n)` (from A1(0,0,1) at step 2) | 2,808,416 | m = 3,308,039 |

Bigfoot's proof follows the wiki's derivation exactly: the partial
configuration `P(m, n) = 1^m <A 1^n`, its even/odd cases
(`P(m+9, 2k) -> P(m, 2k+11)` in `12k + 43` steps,
`P(m+3, 2k+1) -> P(m, 2k+6)` in `12k + 25` steps), the loop over twelve
1s at a time, and six straight-line tails by `b mod 12`.  The champion's
rules are the wiki's dyuan01 transitions refined to the first
configuration of any family the machine reaches, with step counts fitted
and then proved; the configuration notation is
`A1(m,b,c) = 0^inf 1 2^m <C (22)^b (20)^c 0^inf`,
`A2(m,b,c) = 0^inf 1 2^m <A 2 (22)^b (20)^c 0^inf`,
`B(m,b) = 0^inf 1 2^m <B 0 (20)^b 0^inf`.
Rules whose result differs from the canonical list only by trailing blanks
are stated on the lifted (functional) tapes (`RL` in `Champion.v`).

## Build and check

Stock Coq 8.18 (`apt-get install coq`) is enough; no native compilation.

```sh
make -C bb33              # builds SmallBB.Statement/CTape, then the four theorems
make -C bb33 check        # coqchk on BigfootRun and ChampionRun
make -C bb33 assumptions  # prints the axioms: functional_extensionality_dep only
```

A fresh build takes about half a minute on one core, and `coqchk` about
a minute; the champion's `vm_compute` of 2,808,416 rule applications is the
largest single step (about ten seconds, plus the kernel's re-check at
`Qed`).  `coqchk` needs `-bytecode-compiler yes` (as in the small-machine
development) so that it re-checks those casts with the VM rather than the
lazy reducer.  There are no `Admitted`.

## Trust

The statements import only `Statement.v` (the machine model) and `CTape.v`
(computable configurations and their `lift` to the model) from the
small-machine development.  The machines are written out as transition
tables in `Bigfoot.v` and `Champion.v`; `bigfoot_69` and `champion_2`
check by `vm_compute` that the tables reach the wiki's starting
configurations at the stated steps, which guards against a transcription
error in the table.  Everything else is kernel-checked from source; the
untrusted inputs are the choice of rules and step counts, and a wrong
choice fails to compile rather than proving a false theorem.
