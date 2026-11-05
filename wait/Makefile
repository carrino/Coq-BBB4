.PHONY: all all-three all-ternary all-complete dependencies three-dependencies ternary-dependencies complete-dependencies proof proof-three proof-ternary proof-all clean

COQ_PATHS = -Q ../theories BBB4 -Q ../small/legacy SmallLegacy -Q ../small/theories SmallBB -Q theories BBBWait
DECISION_ROOTS = BBBWait.Recurrence BBBWait.RecurrenceTr

all: dependencies Makefile.coq
	$(MAKE) -f Makefile.coq theories/Decision.vo theories/Recurrence.vo theories/RecurrenceTr.vo

all-three: all three-dependencies
	$(MAKE) -f Makefile.coq theories/Decision32.vo

all-ternary: all ternary-dependencies
	$(MAKE) -f Makefile.coq theories/Decision23.vo

# One Coq dependency graph prevents concurrent builds of shared modules.
all-complete: complete-dependencies Makefile.coq
	$(MAKE) -f Makefile.coq theories/Decision.vo theories/Decision32.vo theories/Decision23.vo theories/Recurrence.vo theories/RecurrenceTr.vo

dependencies:
	$(MAKE) -C ../small Makefile.coq
	$(MAKE) -C ../small -f Makefile.coq theories/Value12.vo theories/Value22.vo

# The existing instruction BBB(3) theorem uses selected binary recurrence
# proofs; this prerequisite target does not build the full (4,2) census.
three-dependencies: dependencies
	$(MAKE) -C ../small legacy-deps
	$(MAKE) -C ../small -f Makefile.coq theories/Value32.vo

ternary-dependencies: dependencies
	$(MAKE) -C ../small -f Makefile.coq theories/Value23.vo

# Serialize prerequisite sub-builds so shared small theories compile once.
complete-dependencies: three-dependencies
	$(MAKE) -C ../small -f Makefile.coq theories/Value23.vo

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

proof: all
	@mkdir -p build
	@echo 'Recursively auditing state and instruction waits for one and two states...'
	@coqchk -silent -bytecode-compiler yes $(COQ_PATHS) BBBWait.Decision $(DECISION_ROOTS) >build/coqchk.log 2>&1 \
	  || { cat build/coqchk.log; exit 1; }
	@coqc -q $(COQ_PATHS) theories/Report.v >build/report.log 2>&1 \
	  || { cat build/report.log; exit 1; }
	@cat build/report.log
	@echo 'BBB_wait(1,2)/(2,2) = 0 / 3; BBB_wait_tr(1,2)/(2,2) = 0 / 9.'
	@echo 'BBB_qh_decide(1,2)/(2,2) = 1 / 9; instruction horizons = 1 / 17.'
	@echo 'Exact upper bounds and minimality proved; full recursive coqchk passed.'

proof-three: all-three
	@mkdir -p build
	@echo 'Recursively auditing both three-state waiting values...'
	@coqchk -silent -bytecode-compiler yes $(COQ_PATHS) BBBWait.Decision32 $(DECISION_ROOTS) >build/coqchk32.log 2>&1 \
	  || { cat build/coqchk32.log; exit 1; }
	@coqc -q $(COQ_PATHS) theories/Report32.v >build/report32.log 2>&1 \
	  || { cat build/report32.log; exit 1; }
	@cat build/report32.log
	@echo 'BBB_wait(3,2) = 38; BBB_wait_tr(3,2) = 173; total horizons = 93 / 228.'
	@echo 'Exact upper bounds and minimality proved; full recursive coqchk passed.'

proof-ternary: all-ternary
	@mkdir -p build
	@echo 'Recursively auditing both two-state, three-symbol waiting values...'
	@coqchk -silent -bytecode-compiler yes $(COQ_PATHS) BBBWait.Decision23 $(DECISION_ROOTS) >build/coqchk23.log 2>&1 \
	  || { cat build/coqchk23.log; exit 1; }
	@coqc -q $(COQ_PATHS) theories/Report23.v >build/report23.log 2>&1 \
	  || { cat build/report23.log; exit 1; }
	@cat build/report23.log
	@echo 'BBB_wait(2,3) = 32; BBB_wait_tr(2,3) = 693; total horizons = 91 / 760.'
	@echo 'Exact upper bounds and minimality proved; full recursive coqchk passed.'

proof-all: all-complete
	@mkdir -p build
	@echo 'Recursively auditing all eight waiting values and their decision horizons...'
	@echo 'The kernel audit rechecks the exhaustive censuses; this takes longer than native compilation.'
	@coqchk -silent -bytecode-compiler yes $(COQ_PATHS) BBBWait.Decision BBBWait.Decision32 BBBWait.Decision23 $(DECISION_ROOTS) >build/coqchk-all.log 2>&1 \
	  || { cat build/coqchk-all.log; exit 1; }
	@coqc -q $(COQ_PATHS) theories/Report.v >build/report.log 2>&1 \
	  || { cat build/report.log; exit 1; }
	@coqc -q $(COQ_PATHS) theories/Report32.v >build/report32.log 2>&1 \
	  || { cat build/report32.log; exit 1; }
	@coqc -q $(COQ_PATHS) theories/Report23.v >build/report23.log 2>&1 \
	  || { cat build/report23.log; exit 1; }
	@cat build/report.log build/report32.log build/report23.log
	@echo 'State BBB_wait: (1,2)=0; (2,2)=3; (3,2)=38; (2,3)=32.'
	@echo 'Instruction BBB_wait_tr: (1,2)=0; (2,2)=9; (3,2)=173; (2,3)=693.'
	@echo 'State BBB_qh_decide: (1,2)=1; (2,2)=9; (3,2)=93; (2,3)=91.'
	@echo 'Instruction BBB_qh_decide_tr: (1,2)=1; (2,2)=17; (3,2)=228; (2,3)=760.'
	@echo 'All eight exact waiting values and decision horizons proved; full recursive coqchk passed.'

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -rf build
