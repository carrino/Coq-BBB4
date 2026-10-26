.PHONY: all check search clean legacy-deps
all: legacy-deps Makefile.coq
	$(MAKE) -f Makefile.coq

# Reuse only the existing binary certificates needed by the (3,2) census.
# This deliberately avoids rebuilding the full (4,2) exhaustive proof.
legacy-deps:
	$(MAKE) -C .. Makefile.coq
	$(MAKE) -C .. -f Makefile.coq $$(cat legacy/targets.txt)

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

check: all
	coqchk -silent -bytecode-compiler yes -Q ../theories BBB4 -Q legacy SmallLegacy -Q theories SmallBB SmallBB.Value12 SmallBB.Value22 SmallBB.Value23 SmallBB.Value32 SmallBB.Normalized22 SmallBB.Regression

search: all
	mkdir -p build
	coqc -Q theories SmallBB tools/Extract.v
	ocamlopt -I build build/smallbb.mli build/smallbb.ml ../tools/multisymbol/probe.ml -o build/probe
	ocamlopt -I build build/smallbb.cmx ../tools/multisymbol/dump_graphs.ml -o build/dump_graphs
	$(CXX) -O3 -std=c++17 ../tools/multisymbol/survey.cpp -o build/survey

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -rf build
