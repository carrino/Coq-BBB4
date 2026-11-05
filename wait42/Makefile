.PHONY: all foundation lower-bounds dependencies proof proof-foundation search test clean

COQ_PATHS = -Q ../theories BBB4 -Q theories BBBWait42
FOUNDATION = theories/Spec.vo theories/Recurrence.vo theories/Transport.vo theories/Periodic.vo theories/Ranked.vo theories/Census.vo theories/Run.vo theories/Pilot.vo
WITNESSES = theories/LowerBounds.vo
CORE = theories/BBB4_Spec.vo theories/BBBT4_Spec.vo theories/Census/TNF_QH.vo theories/CensusTr/TNF_QHTr.vo theories/Checkers/TCyclerN.vo theories/Checkers/NGram.vo

all: dependencies Makefile.coq
	$(MAKE) -f Makefile.coq $(FOUNDATION) $(WITNESSES)

foundation: dependencies Makefile.coq
	$(MAKE) -f Makefile.coq $(FOUNDATION)

lower-bounds: dependencies Makefile.coq
	$(MAKE) -f Makefile.coq $(WITNESSES)

dependencies:
	$(MAKE) -C .. Makefile.coq
	$(MAKE) -C .. -f Makefile.coq $(CORE)

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

proof-foundation: foundation
	@mkdir -p build
	@echo 'Recursively auditing the four-state waiting definitions and census machinery...'
	@coqchk -silent -bytecode-compiler yes $(COQ_PATHS) BBBWait42.Pilot BBBWait42.Recurrence BBBWait42.Transport >build/foundation-coqchk.log 2>&1 \
	  || { cat build/foundation-coqchk.log; exit 1; }
	@echo 'Four-state waiting foundation checked. No universal waiting upper bound is claimed.'

proof: all
	@mkdir -p build
	@echo 'Recursively auditing waiting foundations and finite lower-bound witnesses...'
	@coqchk -silent -bytecode-compiler yes $(COQ_PATHS) BBBWait42.Pilot BBBWait42.Recurrence BBBWait42.Transport BBBWait42.LowerBounds >build/coqchk.log 2>&1 \
	  || { cat build/coqchk.log; exit 1; }
	@coqc -q $(COQ_PATHS) theories/Report.v >build/report.log 2>&1 \
	  || { cat build/report.log; exit 1; }
	@cat build/report.log
	@echo 'Lower bounds and waiting proof machinery checked; exact (4,2) waiting values remain open.'

build/scan: tools/scan.cpp
	@mkdir -p build
	$(CXX) -O3 -std=c++17 -Wall -Wextra -Werror $< -o $@

search: build/scan
	python3 tools/scan_candidates.py --source ../docs/bbbt4_cull_audit.tsv --source ../docs/bbbt4_horizon_1e10.txt --binary build/scan --output build/rare-state --jobs 2

test:
	python3 -m unittest discover -s tools -p 'test_*.py' -v

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -rf build
