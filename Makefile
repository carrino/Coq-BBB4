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
#
# The census .vo are committed + hash-guarded (tools/census_cache.py, an
# UNTRUSTED build-hygiene guard -- no proof weight; the Coq kernel is what
# certifies the census).  So `make census' normally SKIPS the walk on a clean
# tree; only an edit to a census .v input (detected by the hash) or a missing
# committed .vo forces the walk.  `make census-verify' forces it unconditionally.

# The raw walk recipe, factored out so `census' (cache-miss) and
# `census-verify' (forced) share the exact same commands.  Internal target.
_census-walk:
	coqc -Q theories BBB4 theories/Census/Run_Split.v
	coqc -Q theories BBB4 theories/Census/Run_Split2.v
	ls theories/Census/Run_Split_*.v | xargs -P4 -I{} coqc -Q theories BBB4 {}
	ls theories/Census/Compute/GG_1LC_*.v | xargs -P4 -I{} coqc -Q theories BBB4 {}
	ls theories/Census/Compute/GGH_*.v | xargs -P4 -I{} coqc -Q theories BBB4 {}
	ls theories/Census/Compute/G_*.v | xargs -P4 -I{} coqc -Q theories BBB4 {}
	coqc -Q theories BBB4 theories/Census/Compute/Census_Theorem.v
.PHONY: _census-walk

# Guarded census: skip the walk when the committed .vo already certify this
# tree (hash matches + all census .vo present); otherwise WARN and walk.
census: all
	@if python3 tools/census_cache.py --check >/dev/null 2>&1; then \
	  echo "census cache VALID -- skipping walk (make census-verify to force a re-walk)"; \
	else \
	  echo "############################################################"; \
	  echo "# census cache INVALID or absent -- WALKING FROM SOURCE.    "; \
	  echo "# This is heavy native_compute (~7h at -P4) and preempts on "; \
	  echo "# this container: run ONLY on STABLE hardware (real Linux /  "; \
	  echo "# WSL2, >=16 GB RAM, no preemption).                         "; \
	  echo "############################################################"; \
	  python3 tools/census_cache.py --check || true; \
	  $(MAKE) _census-walk; \
	fi
.PHONY: census

# Container setup step: verify the committed census .vo still certify this tree
# (--check), then touch them newest so `make'-style timestamp checks skip the
# walk (--touch runs only on --check success).  Run after the base build.
census-cache:
	python3 tools/census_cache.py --check && python3 tools/census_cache.py --touch
.PHONY: census-cache

# Force a re-walk from source (the CORRECTNESS phase; STABLE hardware only).
# Deletes ONLY the committed census .vo (walk units + Run_Split* + the theorem);
# the base build's .vo (Run/Decide/Deferred_*/Proven_*/TNF_QH/...) stay under
# Makefile.coq's control.  After a green walk, refresh + commit the cache.
census-verify: all
	@echo ">>> census-verify: FORCE RE-WALK from source (STABLE hardware only) <<<"
	rm -f theories/Census/Run_Split*.vo theories/Census/Run_Split*.glob
	rm -f theories/Census/Compute/*.vo theories/Census/Compute/*.glob
	$(MAKE) _census-walk
	@echo "------------------------------------------------------------"
	@echo "RE-WALK COMPLETE.  Confirm the census is HONEST, then refresh the cache:"
	@echo "  # In coqtop/Census_Theorem: Print Assumptions census_decided."
	@echo "  #   MUST be exactly: functional_extensionality_dep (nothing else)."
	@echo "  python3 tools/census_cache.py --update    # rewrite CENSUS_VO_HASH"
	@echo "  git add theories/Census CENSUS_VO_HASH && git commit"
	@echo "------------------------------------------------------------"
.PHONY: census-verify

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
