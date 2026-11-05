.PHONY: all dependencies proof clean

all: dependencies Makefile.coq
	$(MAKE) -f Makefile.coq

# Build just the existing binary values needed by this development.
# Avoid the (2,3), (3,2), and (4,2) census builds.
dependencies:
	$(MAKE) -C ../small Makefile.coq
	$(MAKE) -C ../small -f Makefile.coq theories/Value12.vo theories/Value22.vo

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

proof: all
	@mkdir -p build
	@echo 'Recursively auditing BBB_wait(1,2) and BBB_wait(2,2)...'
	@coqchk -silent -bytecode-compiler yes -Q ../small/theories SmallBB \
	  -Q theories BBBWait BBBWait.Values BBBWait.Recurrence >build/coqchk.log 2>&1 \
	  || { cat build/coqchk.log; exit 1; }
	@coqc -q -Q ../small/theories SmallBB -Q theories BBBWait theories/Report.v \
	  >build/report.log 2>&1 || { cat build/report.log; exit 1; }
	@cat build/report.log
	@echo 'BBB_wait(1,2) = 0; BBB_wait(2,2) = 3 -- state based, inclusive cutoff.'
	@echo 'Exact upper bounds and minimality proved; full recursive coqchk passed.'

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -rf build
