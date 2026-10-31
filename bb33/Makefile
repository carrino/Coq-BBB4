# BB(3,3) lower bounds: Bigfoot and the probable champion both run for
# more than 119,112,334,170,342,541 steps (the current BB(3,3) champion's
# step count).  Reuses the three-state, three-symbol carrier of the
# small-machine development (SmallBB) and needs only stock Coq 8.18.

.PHONY: all check deps assumptions clean

all: deps Makefile.coq
	$(MAKE) -f Makefile.coq

deps:
	$(MAKE) -C ../small Makefile.coq
	$(MAKE) -C ../small -f Makefile.coq theories/Statement.vo theories/CTape.vo

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

# Re-verify the compiled proof terms with the standalone checker.
check: all
	coqchk -silent -bytecode-compiler yes -Q ../small/theories SmallBB -Q theories BB33 BB33.BigfootRun BB33.ChampionRun

# Print the axioms the four theorems rest on (expect functional_extensionality_dep only).
assumptions: all
	@printf 'From BB33 Require Import BigfootRun ChampionRun.\nPrint Assumptions bigfoot_runs_past_champion.\nPrint Assumptions bigfoot_no_halt_within_champion.\nPrint Assumptions champion_runs_past_champion.\nPrint Assumptions champion_no_halt_within_champion.\n' > Assumptions.v
	coqc -Q ../small/theories SmallBB -Q theories BB33 Assumptions.v
	rm -f Assumptions.v Assumptions.vo Assumptions.vos Assumptions.vok Assumptions.glob .Assumptions.aux

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Assumptions.v Assumptions.vo Assumptions.vos Assumptions.vok Assumptions.glob .Assumptions.aux
