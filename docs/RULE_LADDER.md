# What mxdys is actually doing, and what it says we should build

_Written 2026-07-26 after reading `Inductive.v` properly rather than
benchmarking it.  John's question: **"imagine you are mxdys and you want to
predict forward behaviour 100% — what would you do?"**  This is the answer,
and it reframes our own roadmap._

## 0. The one-sentence version

mxdys is not running a decider; he is computing a **closure in an exact
abstract domain**, and the only reason it terminates is that where ordinary
abstract interpretation would WIDEN and lose precision, he **generalises and
then discharges the generalisation by induction**.  Our `LapDecider` is the
same construction with the ladder collapsed to a single rung — which is why
we have hand-added 25 alphabets and are now hand-building a nested lap.

## 1. The machinery, named

Three functions carry the whole system.

**`find_IH` — generalise by interpolation.**  Given the same rule observed at
two different times (`w0'` and `w0`), find a variable that explains the
difference.  This is the widening step of an abstract interpreter: guess that
the pattern continues.

**`try_ind` — and then PROVE the guess.**  Having conjectured the rule,
substitute `n := n+1` (`subst_ind_S`), and discharge base case and step case
(`solve_ind`) using rules *already in the library*.  If the induction fails,
the generalisation is simply not taken.  So the abstraction never
over-approximates: precision is the product, and widening-without-proof would
destroy it.

**`follow_rule` — compose.**  Apply a known rule to advance the symbolic
configuration, so higher rules are built out of lower ones.

**`hlin_layers` is the LADDER**, and the source comment says it outright:

    u1: Q2 --> Q3
    u0: c0 --> P := w0 u1
    w1_: Q0 --> Q1
    w1: Q1 --> Q2
    w0 := w0_ w1

A level-0 rule is a raw step.  A level-`k+1` rule is proved by an induction
whose step case invokes only levels `<= k`.  That well-foundedness is what
makes the whole tower legal — and it is why `hlin_layers` is a *list*, not a
set.

## 2. What "predict forward behaviour 100%" actually means

**You have modelled a machine exactly iff the set of reachable symbolic
SHAPES is finite and closed under rule application.**  Not "the simulation ran
a long way" — closed.  Everything else is in service of that:

| axis | what it must satisfy | mxdys' answer |
|---|---|---|
| tape language | closed under the machine's writes | `side_binary`, `side_binary_Pos`, `side_3ary_Pos`, `side_binary_dec`, `side_BL` — a constructor added each time a new tape shape appeared |
| count language | closed under rule COMPOSITION | `nat_add`, `nat_mul`, `powsum k`, `powsum2 k` |
| discovery | must terminate | `find_IH` + `try_ind` + the ladder |

The count language is the subtle one, and it is worth being precise about why
those four constructors and not others:

* apply a rule a constant number of times → `nat_add`;
* apply a rule `n` times where `n` is itself a count → `nat_mul`;
* apply a rule a number of times that doubles each round → `powsum k`
  (`powsum 0 x = 2^x - 1`, a geometric sum);
* apply *that* a growing number of times → `powsum2`.

**The count language is exactly the closure of the composition operation.**
It is not a wish-list; each constructor is forced by one more level of the
ladder.

## 3. The correction this forces on `NESTED_LAP_PLAN.md` §0

That document says — correctly — that we do **not** need `powsum` to STATE an
exponential lap, because `LapStep` only asks for `exists n`, so the cost never
has to be written down.  That is true and it is why `NestedLap.v` is 63 lines.

But it is only true for **one** rung.  The moment a rule is applied a symbolic
number of times *inside another rule*, the count must be manipulated
symbolically, and then you need exactly the closure above.  So:

> `exists n` is enough to CLOSE a lap.  It is not enough to COMPOSE laps.

Both readings were right at different levels, and the disagreement between
`MXDYS_DECIDERS_PLAN.md` §1c ("we need powsum") and `NESTED_LAP_PLAN.md` §0
("we do not") dissolves here.  If we ever build rung 3, we will need the count
language after all.

## 4. Closure gives LIVENESS for free — which is the thing John keeps saying

Once the rule system is closed, "which states are hit infinitely often" stops
being a separate problem and becomes a **graph property**:

* the run eventually stays inside one strongly-connected component of the
  rule-application graph;
* every state appearing in the configurations of the rules in that SCC is
  visited once per traversal, hence infinitely often;
* every state outside it is visited finitely often, and its last visit is
  bounded by the (finite) prefix before the SCC is entered.

That is precisely `QHBound` + `QuasiHaltsSt`, and it is why John is right that
the `~halts`-versus-quasihalting distinction is beside the point: **a closed
exact model answers both at once.**  `WHY_NO_HAMMER.md` reached the same
conclusion from the other side — an exact forward model makes liveness free,
and the lossy ones cannot close the q-avoiding subgraph.

It also explains our own `LapGlueAbs` result: the absorbing-set argument is
the SCC argument, done syntactically on the transition digraph instead of on
the rule graph.  It worked for 141 machines because for those the two
coincide.

## 5. So what would mxdys do with OUR residue?

Not build a 26th alphabet.  Not hand-write a nested-lap emitter.  **Build the
second rung, once.**

Our `LapDecider` today:

| | ours | mxdys |
|---|---|---|
| tape shapes | one (`pre ++ rep u (a*j+b) ++ post ++ X`) | seven constructors |
| count language | affine `a*j+b` | add / mul / powsum / powsum2 |
| rules | one (the lap), hand-proved | a library, discovered |
| new shape costs | a hand-written encoding + emitter wave | a constructor, reused by every machine |

`SWin`, `SCycL`, `SCycR`, `SRot`, `SFold` are our level-0 and level-1 rules,
each hand-proved in `WTape.v`.  What is missing is `try_ind`: the ability for
the CHECKER to conjecture and prove its own rule at run time and add it to the
library.

Concretely, the build:

1. **A rule becomes data**: `(lhs : sconf, rhs : sconf, n : count_expr)`.
2. **One soundness theorem** — `rule_sound` — by induction on the rule's
   variable, with the step case permitted to invoke rules earlier in the list.
   This is the same shape as `srun_sound`, one level up: it is the ladder's
   well-foundedness that makes it a single theorem rather than one per rule.
3. **The checker carries a ladder** (a `list rule`) and a single `vm_compute`
   validates the whole ladder.
4. `SCycL`/`SCycR` stop being primitives and become rules the ladder
   *discovers*.

**And the nested lap is exactly rung two.**  Instead of `NestedLap.v` plus a
bespoke inner-family search, a ladder finds it mechanically: observe the
overflow phase at two indices, interpolate (`find_IH`), conjecture "the inner
counter runs to its fill", discharge by induction using the rung-1 lap rule
(`try_ind`).  One `try_ind` call.  That is the difference between ~750
machines costing an emitter each and costing one theorem total.

## 6. The honest limit

There is a genuinely undecidable tail.  A machine whose reachable shape set is
infinite under every finite exact abstraction — a Collatz-like machine — is
out of reach of ANY inductive decider, and no amount of ladder-building
changes that.  mxdys knows this; it is what his holdout list *is*, and his own
statement of the boundary is exact:

> *"my inductive decider can only decide a TM when it can model the forward
> behavior exactly"*

So "100%" is not the goal and never was.  The goal is to make the boundary of
"can model exactly" as wide as the arithmetic allows, and to spend theorems
rather than emitters getting there.

## 7. What this changes about our plan

* `NESTED_LAP_PLAN.md` Stage C (a nested-lap emitter) is worth finishing **only
  if** it is cheaper than rung two.  It is currently blocked on a boot-chain
  search that has resisted two hypotheses; rung two would dissolve that
  problem rather than solve it.
* The 25 alphabets are a symptom.  A ladder plus `alphabet_infer` (which
  already INFERS a family rather than guessing) is the fix.
* The count language becomes necessary exactly when rung three appears — and
  at that point `powsum`/`powsum2` are the right constructors, because they
  are the closure of composition, not a borrowed convenience.
