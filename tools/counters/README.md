# Counters track: untrusted lap-discovery executors

Everything here is UNTRUSTED search/validation tooling (repo rule:
only the Coq checkers carry soundness).  These scripts discover and
differentially validate the phase decomposition of a counter
machine's lap before it is transcribed into a Coq proof under
`theories/Machines/Counters/`.

## The method (validated on mono #10/#26/#31 and spacer #16)

1. **Trace** the machine from its anchor configuration C(a) with
   `trace.py` (turnaround summaries, sweep-boundary snapshots) to
   see the lap's macro structure.
2. **Decompose** the lap in `lapNN.py` as a chain of executor
   combinators, each of which corresponds 1:1 to a Coq lemma:
   - `conc(bl, br, n, lwin, rwin)` = a windowed unit run
     (`wsteps` + `wsteps_frame`/`_l`/`_r` transport);
   - `cycR(ulen, P, k)` = `WTape.cycR` (rightward repetition);
   - `cycL(ulen, rwlen, P, k)` = `WTape.cycL`;
   - marker-carrying left cycles = `WTape.cycLW`.
   The executor DERIVES each unit's endpoints by running the walled
   simulation, asserts wall discipline (a pop past a window fails
   loudly), and asserts unit stability across all laps.
3. **Differentially validate**: `python3 lapNN.py 300` replays the
   symbolic lap against the raw simulator for every counter value —
   step counts, final configurations and next-anchor equality must
   all match, including both carry shapes (interior / overflow).
4. **Transcribe**: the unit dump at the end of a validated run is
   the Coq unit-lemma table; the combinator chain is the lap script
   (`eapply csteps_chain` + the `ph*` phase lemmas + `rep`-algebra
   junction rewrites).  Bootstrap step counts and visit-witness
   offsets are printed by small probes (see the session notes in
   NEXT_SESSION.md).

The trap catalog (off-by-one framings, rotated comb units,
overflow's trailing blank, `cbn [rep]` over-unfolding) lives in the
NEXT_SESSION.md counters section.
