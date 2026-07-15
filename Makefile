all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	rm -f Makefile.coq Makefile.coq.conf

.PHONY: all clean

# The census certification: 24 per-grandchild subtree enumerations
# (parallel; each Qed is one native_compute walk) + the assembled
# theorem.  Needs native_compute: eval $(opam env --switch=census).
census: all
	ls theories/Census/Compute/G_*.v | xargs -P4 -I{} coqc -Q theories BBB4 {}
	coqc -Q theories BBB4 theories/Census/Compute/Census_Theorem.v
.PHONY: census
