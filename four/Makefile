.PHONY: all check check-affine-batch clean
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
	  BBB24.AffineCloseout BBB24.PipelineExamples
check-affine-batch: all
	python3 tools/check_affine_batch.py
clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
