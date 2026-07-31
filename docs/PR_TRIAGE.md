# Merging work into the closeout

_Four rules and a counting method, learned from the 2026-07-31 PR triage.  The
record of that triage is at the bottom; the rules are the part worth keeping._

## 1. Never hand-resolve a generated closeout file

These files are **generated**.  Every one of them:

```
theories/Closeout/CB_*.v, Closeout.v, CoreRows.v,
CloseoutFinal.v, BBB4_Theorem.v          <- gen_stages.py
the Closeout section of _CoqProject       <- gen_stages.py
tools/closeout/core_rows.txt, frozen_map.tsv,
frozen_unproven.txt, shadow_rows.tsv      <- inventory.py + gen_stages.py
```

Two branches that each board a row will **both** rewrite all of them, so they
conflict on every merge.  Resolving one by hand silently reverts whichever
side's boards the resolver did not notice — and the resolver cannot notice,
because the difference is a renumbered stage file three hundred lines long.

The rule:

> Take either side to get a tree (`git checkout --theirs`), then **re-derive**:
>
> ```
> python3 tools/closeout/inventory.py    # rebuilds frozen_map / core_rows
> python3 tools/closeout/gen_stages.py   # rebuilds CB_*, Closeout, _CoqProject
> python3 tools/closeout/audit.py        # must print CLOSEOUT AUDIT: OK
> ```

The board `.v` files are the source of truth and they **never conflict**,
because two sessions board different machines and so write different files.
Re-deriving makes the merge the *union* of the two board sets, which is what a
merge of two boarding branches means.

This is not hypothetical: PR #100 was cut before #95 and its regenerated
closeout still spoke for a tree without main's two boards.  Twenty-nine files
conflicted, all generated.  Re-derived, the merge came out at 39 core / 14
shadows / 5,103 settled with the audit clean; hand-resolved toward #100 it
would have un-boarded two rows **and the audit would still have passed**,
because the audit checks the partition, not the history.

## 2. A branch that is behind is not just stale, it is destructive

A branch cut before a wave lands does not merely lack that wave — merging it
**reverts** it, because its regenerated closeout names a smaller board set.
`git diff --stat origin/main <branch>` is the check, and a docs-only branch
showing thousands of deleted `.v` lines is the signature.

PR #103 sat two hours and came back 16 commits behind, with a diff that would
have removed ~11,600 lines of the `(Gray, 2)` build.  It was also numbered
`LADDER_PLAN` §4o, which `main` had meanwhile assigned to that build.  Rebuild
on current `main` and renumber; do not merge across a wave.

## 3. Count a row's worth with its shadows, not alone

`tools/closeout/shadow_rows.tsv` column 4 is each shadow's core partner.  The
shadows are not spread evenly, and it changes which bucket is worth working:

```
python3 - <<'EOF'
import collections
sh = collections.Counter()
for ln in open('tools/closeout/shadow_rows.tsv').read().splitlines()[1:]:
    if ln.strip(): sh[ln.split('\t')[3]] += 1
core = [l for l in open('tools/closeout/core_rows.txt').read().split()
        if not l.startswith('#')]
for r in sorted(core, key=lambda r: -sh[r]):
    if sh[r]: print("%-32s +%d" % (r, sh[r]))
EOF
```

At the 2026-07-31 triage, all 14 shadows sat on 12 of the 39 core rows — so
those 12 accounted for 26 of the 53 remaining, and the other 27 were worth one
row each.  Boarding a shadow-carrying row is worth double or triple.

A shadow satisfies `skipped` only while its core row is deferred, so it needs
its own board exactly when its partner boards, and not before.
`tools/closeout/gen_shadow.py` generates it (`--regress` first).

## 4. Read the plan's last section before acting on a prompt

The prompt is older than the plan.  A `NEXT_PROMPT.md` written at the end of
one wave is invalidated by the next, sometimes within hours: §4o's own
next-session prompt pointed at four rows §4p had already measured dead.
`git show origin/main:tools/closeout/core_rows.txt` is one command and costs
nothing.

## 5. The emitter's refusal is in the file, and it is the real exception text

`emit_ladder.py` writes its `NoClosure` message into the `.v` it emits, and
there are exactly two — line 381 (the closure's interior class arm) and line
431 (the fill arm).  Read the file, not the driver's last line, and do not read
the certificate's arm counts as the reason: the certificate's arms and the
closure's CLASS arms are different sets, and a board can have every certificate
arm and still stop.

---

## The triage of 2026-07-31, and what came of it

Four PRs were open against `main` at `3ffa761`, with **42 core + 14 shadows**
(5,100 settled, 98.9%).  Only one moved the number, and only that one had a
conflict.

| PR | what it was | verdict | landed |
|---|---|---|---|
| **#100** | the probe, the phase cycle, three rows | merge first — the only one that moves the count | `0fc5f0b` |
| **#92** | counts + `check_coqproject.py` CI guard | merge second, re-swept to the new count | `6e406e2` |
| **#98** | `RerootSwap.v` + `gen_shadow.py` | merge — fills a real gap, zero axioms | `d07e999` |
| **#99** | five partial ladder boards | merge with an exempt block | `fa1be97` |

The order was forced, not stylistic: #92 *is* the count-sweep PR, so it had to
follow the PR that moved the count; and #99's exempt block lives in a file #92
creates.  #92's new guard caught #99's five unwired `.v` files on the way in,
which is the guard doing its job on its first day.

**The finding that shaped what came next.**  Reading the emitter's refusal line
(rule 5) out of every unregistered partial board put **nine core rows, carrying
five shadows, at the same line** — including #99's five, whose PR body
described them as failing differently.  That was 14 of the 53 rows left, and
every one of those boards predated §4n's far-side fix, which had taken the
identical failure on the gray six from zero-of-six to six-of-six.

Two prompts came out of it, parallel-safe by file ownership (A owned
`theories/Checkers/`, B was forbidden it).  Both ran:

* **Prompt A — build `(gray, 2)`** → PR #104, `LADDER_PLAN` §4o, four rows.
* **Prompt B — re-measure the nine interior-arm rows** → PR #101, §4p: **5 of
  9**, and the bucket was never one bucket.  It also freed two shadows.

The Fibonacci block followed from §4p's measurement → §4r, `(Fib, 1)` built,
the five board.  A separate read of the two bouncer rows is §4q.

Net over the session: **42 + 14 → 30 + 12**, 5,100 → 5,114 settled
(98.9% → 99.2%).  `docs/LADDER_PLAN.md` §4o–§4r are the technical record;
`core_rows.txt` and `audit.py` remain the authority for the count.
