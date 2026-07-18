all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	rm -f Makefile.coq Makefile.coq.conf

.PHONY: all clean

# The census certification: the per-subtree queue enumerations
# (parallel; each Qed is one native_compute walk) + the assembled
# theorem.  Needs native_compute: eval $(opam env --switch=census).
# Layers: Run_Split (grandchild split) -> Run_Split2 + the 7
# Run_Split_<tag> heavy-grandchild splits -> the GG_1LC / GGH_ great-
# grandchild walks -> the 24 G_ units -> theorem.  ~7h native at -P4;
# raise -P to your core count.
census: all
	coqc -Q theories BBB4 theories/Census/Run_Split.v
	coqc -Q theories BBB4 theories/Census/Run_Split2.v
	ls theories/Census/Run_Split_*.v | xargs -P4 -I{} coqc -Q theories BBB4 {}
	ls theories/Census/Compute/GG_1LC_*.v | xargs -P4 -I{} coqc -Q theories BBB4 {}
	ls theories/Census/Compute/GGH_*.v | xargs -P4 -I{} coqc -Q theories BBB4 {}
	ls theories/Census/Compute/G_*.v | xargs -P4 -I{} coqc -Q theories BBB4 {}
	coqc -Q theories BBB4 theories/Census/Compute/Census_Theorem.v
.PHONY: census

# Resume-friendly census: skips any unit whose .vo already exists, in
# dependency order (base modules -> heavy-grandchild modules -> walks ->
# assemblies -> theorem).  Use this to pick up an interrupted `make
# census` without recompiling finished walks.
census-resume: all
	[ -f theories/Census/Run_Split.vo ]  || coqc -Q theories BBB4 theories/Census/Run_Split.v
	[ -f theories/Census/Run_Split2.vo ] || coqc -Q theories BBB4 theories/Census/Run_Split2.v
	for f in theories/Census/Run_Split_*.v; do [ -f $${f}o ] || coqc -Q theories BBB4 $$f; done
	for f in theories/Census/Compute/GG_1LC_*.v theories/Census/Compute/GGH_*.v; do [ -f $${f}o ] || echo $$f; done | xargs -r -P4 -I{} coqc -Q theories BBB4 {}
	for f in theories/Census/Compute/G_*.v; do [ -f $${f}o ] || echo $$f; done | xargs -r -P4 -I{} coqc -Q theories BBB4 {}
	coqc -Q theories BBB4 theories/Census/Compute/Census_Theorem.v
.PHONY: census-resume
