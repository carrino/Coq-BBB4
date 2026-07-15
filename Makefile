all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	rm -f Makefile.coq Makefile.coq.conf

.PHONY: all clean

# The census computation (heavy: one full enumeration run at Qed).
# Needs native_compute: eval $(opam env --switch=census) first.
census: all
	coqc -Q theories BBB4 theories/Census/Census_Compute.v
.PHONY: census
