.PHONY: all foundation lower-bounds dependencies proof proof-foundation proof-replay search test clean

COQ_PATHS = -Q ../theories BBB4 -Q theories BBBWait42
FOUNDATION = theories/Spec.vo theories/Recurrence.vo theories/Transport.vo theories/Periodic.vo theories/Ranked.vo theories/Census.vo theories/Run.vo theories/Pilot.vo theories/Batch.vo theories/RankedCompletion.vo theories/RepeatedWord.vo theories/Resume.vo theories/ReplayPilot.vo theories/ReplayCoverage.vo
WITNESSES = theories/LowerBounds.vo
RESIDUAL_REPLAY = theories/ResidualReplay.vo theories/ResidualReplayMore.vo
CORE = theories/BBB4_Spec.vo theories/BBBT4_Spec.vo theories/Census/TNF_QH.vo theories/CensusTr/TNF_QHTr.vo theories/Checkers/TCyclerN.vo theories/Checkers/NGram.vo theories/Checkers/RepWL.vo theories/Census/Deferred_Defs.vo

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
	@coqchk -silent -bytecode-compiler yes $(COQ_PATHS) BBBWait42.ReplayCoverage BBBWait42.Recurrence BBBWait42.Transport >build/foundation-coqchk.log 2>&1 \
	  || { cat build/foundation-coqchk.log; exit 1; }
	@echo 'Four-state waiting foundation checked. No universal waiting upper bound is claimed.'

proof: all
	@mkdir -p build
	@echo 'Recursively auditing waiting foundations and finite lower-bound witnesses...'
	@coqchk -silent -bytecode-compiler yes $(COQ_PATHS) BBBWait42.ReplayCoverage BBBWait42.Recurrence BBBWait42.Transport BBBWait42.LowerBounds >build/coqchk.log 2>&1 \
	  || { cat build/coqchk.log; exit 1; }
	@coqc -q $(COQ_PATHS) theories/Report.v >build/report.log 2>&1 \
	  || { cat build/report.log; exit 1; }
	@cat build/report.log
	@echo 'Lower bounds and waiting proof machinery checked; exact (4,2) waiting values remain open.'

# Small frozen samples reproduce the C-to-Coq boundary without shipping ledgers.
proof-replay: foundation
	$(MAKE) -f Makefile.coq $(RESIDUAL_REPLAY)
	python3 tools/replay_periodic.py --source research/periodic-replay-sample.tsv --output build/periodic-replay-sample --per-stratum 256
	coqc -q $(COQ_PATHS) -Q build/periodic-replay-sample BBBWait42Replay build/periodic-replay-sample/Cases.v >build/periodic-replay-sample/probe.log 2>&1
	python3 tools/replay_periodic.py --output build/periodic-replay-sample --probe-log build/periodic-replay-sample/probe.log --expect-accepted 204
	coqc -q $(COQ_PATHS) -Q build/periodic-replay-sample BBBWait42Replay build/periodic-replay-sample/Checked.v >build/periodic-replay-sample/compile.log 2>&1
	coqchk -silent -bytecode-compiler yes $(COQ_PATHS) -Q build/periodic-replay-sample BBBWait42Replay BBBWait42Replay.Checked >build/periodic-replay-sample/coqchk.log 2>&1
	python3 tools/replay_rank_samples.py --ledger research/rank-replay-sample.tsv --output build/rank-replay-sample --expect-accepted 10 --timeout 180
	coqchk -silent -bytecode-compiler yes $(COQ_PATHS) BBBWait42.ResidualReplay BBBWait42.ResidualReplayMore BBBWait42.ReplayCoverage >build/residual-replay-coqchk.log 2>&1
	coqc -q $(COQ_PATHS) theories/ReplayReport.v >build/replay-report.log 2>&1
	@cat build/replay-report.log
	@echo 'Periodic and n-gram samples plus 25 residual families recursively checked; complete census coverage remains open.'

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
