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
# Layers: Run_Split (grandchild split) -> Run_Split2 (the 1RB/1LC
# grandchild split once more, 16 great-grandchildren GG_1LC_*) ->
# the 24 G_ units (G_1RB_1LC assembles from the GG layer) -> theorem.
census: all
	coqc -Q theories BBB4 theories/Census/Run_Split.v
	coqc -Q theories BBB4 theories/Census/Run_Split2.v
	ls theories/Census/Compute/GG_1LC_*.v | xargs -P4 -I{} coqc -Q theories BBB4 {}
	ls theories/Census/Compute/G_*.v | xargs -P4 -I{} coqc -Q theories BBB4 {}
	coqc -Q theories BBB4 theories/Census/Compute/Census_Theorem.v
.PHONY: census
