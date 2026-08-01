# Wave-36 prompt: board mxdys's rows 1 and 4 by transcribing one argument

Continue the (4,2) core reduction in `carrino/Coq-BBB4`, on branch
`claude/mxdys-four-<yourid>`, cut from `main`.

**Read `docs/WAVE36_MXDYS_FOUR.md` first — all of it.**  It is short, it is
this wave's whole input, and three of its sections are do-not-retry entries
that each cost a measurement to establish.

## STATE

Nine core rows are open (`tools/closeout/core_rows.txt`), and **four of the
nine are mxdys's four**:

    1RB1LC_0LC0RB_1LA1RD_0LA0RD      (row 1)
    1RB1LC_1LB1RA_0LC0LD_0RA0RD      (row 2)
    1RB1LC_1LC1RA_0LC0LD_0RA0RD      (row 3)
    1RB1LD_1LC1RA_0RB0LC_0RA0LD      (row 4)

All four are never-quasihalters; the target is `NeverQuasiHaltsSt`, not
`iqh`.  Wave 36 boarded none of them and moved no count.

## THE JOB — rows 1 and 4, and the assembly already exists

This is transcription, not discovery.  The closer is already in the tree:

    Checkers/NGramHistExt.v
    Theorem ngramhist_check_neverqh_lex_ext_sound :
      forall tm k n t fuel lset rset cert qext,
      (forall N, exists m, N <= m /\ VisitsAt tm qext m) ->      (* <-- the ONLY hole *)
      ngramhist_check_neverqh_lex_ext tm k n t fuel lset rset cert qext = true ->
      NeverQuasiHaltsSt tm.

and `tools/nghist/reachst_prove.py` already emits every other line of the
board — the table, `lset`, `rset`, `cert`, and the final `apply ... ;
vm_compute; reflexivity`.  On a normal `RST_*` board the hole is filled by
`reach_st_recurs` off a named flavour lemma in `ReachSt.v`.  **On these two
rows that route is dead** (§3: `StD`'s avoid run is `Theta(2^width)` long,
so no `ReachSt` flavour and no measure certificate can ever discharge it),
and the hole is filled by §4 instead.

So:

**Step 1 — get the closure half.**  This half is DONE as a measurement:

    python3 -c "import sys
    sys.path.insert(0,'tools/reachsti'); sys.path.insert(0,'tools/nghist')
    from sweep import closure_certs
    for m in ['1RB1LC_0LC0RB_1LA1RD_0LA0RD','1RB1LD_1LC1RA_0RB0LC_0RA0LD']:
      print(m, ''.join(sorted(closure_certs(m,'ABCD'))))"

reports `ABC` on both rows — the closure discharges every state but `StD`,
which is exactly `qext='D'`.  Confirmed twice (this, and
`tools/reachsti/sweep.py`'s own run).  What is left is to pin `(k, n)` and
run `reachst_prove.emit`, then delete only its `recurC_*` lemma.

**Two traps in that tool, both met and both cheap to avoid.**
`prove_ext` returns a `(result, error)` TUPLE, so `if RP.prove_ext(...)` is
always true and a naive probe reports OK on everything — unpack it.  And it
takes no timeout: call it with the sweep's parameters (`t=200`,
**`fuel=40000`**, `(k,n)` from `[(2,2),(3,2),(2,3)]`) and under
`signal.alarm`, exactly as `tools/reachsti/sweep.py:closure_certs` does.
At `fuel=4000` it does not fail, it hangs.

**Step 2 — prove the hole.**  `forall N, exists m, N <= m /\ VisitsAt tm StD m`.
This is §4 of the findings, and it decomposes as:

* **The half-tape invariant** (§2).  Row 1 keeps everything right of the
  head a bare `1^R`; row 4 keeps everything left of it a bare `1^p`.  Carry
  the configuration as `(StA, (l, s, rep [S1] R))` plus, as proof-level
  data, the frame width `w` with `length l = w - 1 - R`.
* **Four macro lemmas** (§2a), each `csteps tm _ (StA,(l,s,rep [S1] R)) =
  Some (StA,(l',s',rep [S1] R'))`.  They need two scan lemmas first — `B`
  and `D` each eat a run of ones rightward, and both have the shape

      Lemma Bscan : forall n l Z, csteps tm (S n) (StB, (l, S1, rep [S1] n ++ Z))
        = Some (StB, (rep [S0] (S n) ++ l, chd Z, ctl Z)).

  Keep the generic tail `Z`: without it the trailing blank that `B0` writes
  makes the next rule's `cconf` fail to match syntactically.  That is the
  first trap and it will cost an hour if you meet it late.  `WTape.rep`,
  `rep_add` and `rep_shift` are the list algebra; `LinCarry`'s `rep1_cons`/
  `rep1_snoc` are the cons/snoc forms.
* **The measure** (§4a).  On the `cconf` directly, with no frame:

      vall [] = 0        vall (b :: t) = sval b + 2 * vall t
      mu (l,s,R) = 2^R * (2 * vall l + sval s + 1)

  Per-rule deltas, exact: rule 1 `+2`, rule 2 `+2^R`, rule 4 `+2^(R+1)`,
  rule 5 `-(2^(R+1)-1)`.  `mu <= 2^w`, and `w` is preserved by all four
  rules.  Induct on `2^w - mu`.
* **The parity lock** (§4).  `p = length l`.  Rules 1 and 2 send `p` to
  `w-2`, rule 4 preserves parity, only rule 5 sends it to `w-1`; widths stay
  odd.  So once `length l` is odd and `last l = S1`, no widening is enabled
  (`length l = 1` with `last l = S1` IS rule 5's guard) and `2^w - mu`
  strictly decreases — forcing rule 5, which is where `StD` fires.

Both the deltas and the lock were checked over 4000 macro steps with zero
exceptions.  `tools/mxdys4/macro1.py` carries the rules; re-run its
validation after any restatement.

**Step 3 — do row 4 the same way** off §2b's three rules.  Row 4 is *not*
`mirror_tm` of row 1 under any state bijection fixing the start state
(checked exhaustively), so `Mirror.mirror_never_qh` will not transport the
board — but the argument transports and the closure half is identical.

**Then re-run the closeout.**  `make closeout` + `tools/closeout/audit.py`.
Boarding a core row re-roots its `0RB` shadow; both of these rows have one
(`tools/closeout/shadow_rows.tsv`), so the counts should move
9 core -> 7 and the shadows with them.  Iterate the regeneration until the
open list stops changing — two earlier waves got free boards from that pass.

## DO NOT REDO — each of these cost a measurement

1. **Any `ReachSt`/`ReachStI`/measure-certificate attempt at `StD` on rows 1
   or 4.**  §3.  The measure is linear in the tape and the run is
   exponential in it.  This is a growth-rate fact, not a search failure; no
   widening of the certificate class touches it.
2. **Re-deriving the macro systems.**  §2a/§2b, both differentially
   validated (400/400 and 4000/4000 macro steps).  `tools/mxdys4/extract.py`
   re-derives them in seconds if you want to check.
3. **Wider windows or deeper extent caps for rows 2 and 3.**  §5.  `k`-cell
   windows at `k = 1,2,3` and extent caps 2 and 3 were all measured; every
   one still fails on the same spurious node.
4. **`emit_lapcert.py` / the anchor search on any of the four.**  It refuses
   all four with `no cascade`, and that refusal is correct — none of the
   four has a one-parameter anchor family with an affine lap.

## ROWS 2 AND 3 — the sized piece, if you want the harder half

§5.  Their counter is exact and consecutive (base 2, LSB first, two cells
per digit, `0 -> 00`, `1 -> 01`), the carry is `Theta(3^c)`, and — unlike
rows 1 and 4 — **every state recurs on an `O(width)` schedule**, so a
measure certificate is *not* excluded.  What blocks it is one spurious
node: `C` reading `0` with the left half-tape blank, whose `C0 -> 0LC`
self-loop sweeps left forever.  The real orbit never visits it (their `C`
always reads `1` when it reaches the blank region and turns into `D`), but
no bounded window can say so, because the fact needed is "the leftmost `1`
is exactly at the head".

The sized piece is a **suffix-closed regular half-tape invariant** — a
`ReachStI` whose `I` is "the state is allowed AND each half-tape is in a
suffix-closed regular language".  `CTape.ctape_move` supports exactly that
shape and nothing more: `DR` replaces `r` by `ctl r` (a suffix — free if
the language is suffix-closed) and `w :: r` on the other side (one known
cell to check).  Build it as a sibling of `ReachStI.v`, which is only 330
lines and whose `drop_ok`/`mu_reaches`/`reach_sti_recurs_b` skeleton
transfers unchanged.  Search side: `tools/mxdys4/certM.py` already returns
the blocking negative cycle on failure, which is how to tell whether a
candidate language is strong enough before writing any Coq.

## ENVIRONMENT

`apt-get install -y coq` (~1 min, gives 8.18.0 — that is the repo's
version).  `theories/BBB4_Statement.v` + `CTape.v` compile in 4 s, so
iterate on a single file with

    coqc -R theories BBB4 theories/Machines/<...>.v

`Checkers/ReachStI.v` depends only on `BBB4_Statement` and `CTape`;
`NGramHistExt.v` pulls in `NGram`, `NGramHist` and `ReachSt`.  Do NOT touch
`theories/Census/` — editing it forces a census re-walk, which this
container cannot run (PLAYBOOK §1).

**Diff `origin/main` immediately before emitting any board, not just at
session start.**  Four collisions between parallel sessions are logged in
`NEXT_SESSION.md`; every one of them happened inside the session window.
