# S066: a checked entry into a sliding frontier

For `1LB2RA0LB1RB_3RB3LA1LA2RA` (code `4218262960`), both states recur
arbitrarily late. The package proves `NonHalt` and `QHBound 0`, contributing
one state family and zero instruction families. No state has a final visit.

The main configuration is A0 with empty right tape and nearest-first left
word `2211 l`, where the entire tail `l` is arbitrary. A universal 11-step
program returns to A0 with left word `22112 l` and empty right tape. Each
return adds one `2` behind the preserved four-cell prefix and moves the
frontier one cell to the right. Induction gives the exact `11n`-step return
with left word `2211 2^n l` for every `n`. Every main configuration enters B
one step later, so the returns certify unbounded visits to both A and B.

The local slide theorem also preserves an arbitrary right context: starting
at A0 with left `2211 l` and right `r`, it ends at A at the first symbol of
`r`, with left `22112 l`. This is a recurrent main configuration when `r`
is empty. The recurrence proof keeps that boundary guard explicit.
Regressions reject a malformed left prefix and an omitted rightblank guard.

The original blank run reaches the main family at step `1922128`. Coq
computes only a Boolean predicate asserting state A, head 0, empty right tape
and the left prefix `2211`. The remaining left tail is existential and is
not supplied by native output. The selected hypotheses were recorded before
formalization. The checked finite prefix and finite slide are closed under
the global context. Lifted recurrence and census theorems use only the
repository's existing functional extensionality assumption.

An independent sparse simulator checks the original entry and 20 subsequent
11-step frontier returns. There are 2,977 native controls covering both
arbitrary contexts, repeated returns, the B visit and both missing-guard
negatives. Native evidence receives no proof credit. Eight imported
regressions and all universal theorems are included in the recursive audit.

Generated wrappers identify the exact encoded transition table, exact
inventory and original pending census membership. Nonhalting completion
extension proves the state bound for every completion. The full recursive
audit starts at Inventory and includes all five package modules with zero
reused modules. No instruction-family claim is made.

From the repository root with the census Coq environment on PATH:

```sh
python3 four/tools/check_burn28_s066_frontier_native.py --check
python3 four/tools/check_burn28_s066_frontier.py
python3 four/tools/check_burn28_s066_frontier.py --check
```

The report pins hypotheses, proof input, native provenance, templates,
generated sources, objects and the recursive audit receipt. Accepted packages,
trackers and the separate checkpoint-59 publication remain unchanged.
