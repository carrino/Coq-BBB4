.PHONY: all check check-affine-batch check-affine-closeout check-closure-batch check-shadow-links check-transport check-wave clean
all: Makefile.coq
	$(MAKE) -f Makefile.coq
Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@
check: all
	coqchk -silent -bytecode-compiler yes -Q theories BBB24 \
	  BBB24.Champion BBB24.Regression BBB24.Bootstrap BBB24.CensusRegression \
	  BBB24.AffineExamples BBB24.AffineRegression BBB24.Checkers.IRules.MetaBlkPfxTr \
	  BBB24.TotalCompletion BBB24.NGramRegression BBB24.RepWLRegression \
	  BBB24.FiniteHistoryRegression BBB24.SymmetryRegression \
	  BBB24.AffineCloseout BBB24.PipelineExamples BBB24.AdvancedExamples \
	  BBB24.CertifiedBoard BBB24.ClosureBatch BBB24.FamilyTransport BBB24.CensusUnion
check-affine-batch: all
	python3 tools/check_affine_batch.py
check-affine-closeout: check-affine-batch
	python3 tools/check_affine_closeout.py
check-closure-batch: all
	python3 tools/check_closure_batch.py --resume
check-shadow-links: all
	python3 tools/check_shadow_links.py
check-transport: check-affine-closeout check-closure-batch
	python3 tools/check_family_transport.py
check-wave: check-transport check-shadow-links
	python3 tools/check_wave_closeout.py
clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
