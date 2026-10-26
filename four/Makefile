.PHONY: all check clean
all: Makefile.coq
	$(MAKE) -f Makefile.coq
Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@
check: all
	coqchk -silent -bytecode-compiler yes -Q theories BBB24 BBB24.Champion BBB24.Regression BBB24.Bootstrap BBB24.CensusRegression
clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
