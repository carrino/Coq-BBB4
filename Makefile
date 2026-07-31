all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	rm -f Makefile.coq Makefile.coq.conf
	rm -f theories/Closeout/CloseoutFinal.vo theories/Closeout/CloseoutFinal.glob
	rm -f theories/Closeout/BBB4_Theorem.vo theories/Closeout/BBB4_Theorem.glob

.PHONY: all clean

# ---------------------------------------------------------------------------
# `make proof' -- build and state the top-level BBB(4) result:
#
#   bbb4_target : forall tm,
#     QHBound 32779478 tm \/ NeverQuasiHaltsSt tm \/ Deferred D_remaining tm
#
# Every (4,2) machine either quasihalts with score at most the champion's
# 32,779,478, or never quasihalts -- EXCEPT the undecided residue machines
# (600+; tools/closeout/frozen_unproven.txt), which the report prints as
# SKIPPED.  The champion itself is one of them, so this is NOT yet a proof
# of the BBB(4) value; docs/CLAIMS.md states the claim precisely.
#
# The chain: census_decided (committed census .vo) -> closeout_partial
# (Closeout.vo, from source via `make') -> census_boarded (CloseoutFinal.v)
# -> bbb4_target (BBB4_Theorem.v).  The last two files LOAD the committed
# census .vo, which are toolchain-specific (built with coq-native): compile
# them under the census opam switch (docs/VERIFYING.md).  On a mismatched
# toolchain the load fails with "inconsistent assumptions"; either use the
# census switch or re-derive the census .vo with `make census-verify'.
proof: all
	@python3 tools/census_cache.py --check
	coqc -Q theories BBB4 theories/Closeout/CloseoutFinal.v || \
	  { echo "proof: FAILED loading the committed census .vo -- use the census"; \
	    echo "proof: opam switch (docs/VERIFYING.md) or run make census-verify."; \
	    exit 1; }
	coqc -Q theories BBB4 theories/Closeout/BBB4_Theorem.v
	@python3 tools/proof_report.py
.PHONY: proof

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
#
# RESUMABLE: each unit is skipped when its .vo already exists, so a walk
# that dies mid-layer (OOM, preemption) continues where it stopped instead
# of redoing finished units.  `census-verify' still deletes every census
# .vo FIRST, so a verify walk is always a full from-source walk -- the
# honesty property is unchanged.
#
# WALK_JOBS defaults to 2: four parallel native_compute units OOM-killed a
# 16 GB box on the GG_1LC layer (signal 9, 2026-07-22).  Override with
# `make census-verify WALK_JOBS=4' only if RAM headroom is confirmed.
WALK_JOBS ?= 2

# Walk-stamp: census .vo on disk are trustworthy walk output ONLY if they
# were produced by walking the CURRENT census inputs (a crash-resume).
# .vo restored by git (the committed cache of an OLDER tree) or left over
# from a differently-wired tree satisfy a bare existence check and made the
# resumable walk silently no-op (discovered 2026-07-23: a fresh checkout's
# committed .vo "completed" the walk instantly; loading them then failed
# with "inconsistent assumptions" -- the kernel catches it, but the walk
# must not skip).  Before walking, quarantine any census .vo whose stamp
# does not match the current input hash.
_census-prepare:
	@H=$$(python3 tools/census_cache.py --print-hash); \
	 S=census_probes/walk-stamp; mkdir -p census_probes; \
	 if [ ! -f $$S ] || [ "$$(cat $$S)" != "$$H" ]; then \
	   bdir="census_probes/vo-quarantine-$$(date +%Y%m%d-%H%M%S)"; \
	   mkdir -p "$$bdir"; \
	   mv -f theories/Census/Run_Split*.vo theories/Census/Run_Split*.glob "$$bdir"/ 2>/dev/null || true; \
	   mv -f theories/Census/Compute/*.vo theories/Census/Compute/*.glob "$$bdir"/ 2>/dev/null || true; \
	   echo "$$H" > $$S; \
	   echo ">>> census .vo on disk were NOT produced by walking this tree"; \
	   echo ">>> quarantined to $$bdir -- walking from source"; \
	 else \
	   echo ">>> walk-stamp matches this tree -- resuming, finished units kept"; \
	 fi
.PHONY: _census-prepare

_census-walk: _census-prepare
	[ -f theories/Census/Run_Split.vo ] || coqc -Q theories BBB4 theories/Census/Run_Split.v
	[ -f theories/Census/Run_Split2.vo ] || coqc -Q theories BBB4 theories/Census/Run_Split2.v
	ls theories/Census/Run_Split_*.v | while read f; do [ -f "$${f%.v}.vo" ] || echo "$$f"; done | xargs -r -P$(WALK_JOBS) -I{} coqc -Q theories BBB4 {}
	ls theories/Census/Compute/GG_1LC_*.v | while read f; do [ -f "$${f%.v}.vo" ] || echo "$$f"; done | xargs -r -P$(WALK_JOBS) -I{} coqc -Q theories BBB4 {}
	ls theories/Census/Compute/GGH_*.v | while read f; do [ -f "$${f%.v}.vo" ] || echo "$$f"; done | xargs -r -P$(WALK_JOBS) -I{} coqc -Q theories BBB4 {}
	ls theories/Census/Compute/G_*.v | while read f; do [ -f "$${f%.v}.vo" ] || echo "$$f"; done | xargs -r -P$(WALK_JOBS) -I{} coqc -Q theories BBB4 {}
	[ -f theories/Census/Compute/Census_Theorem.vo ] || coqc -Q theories BBB4 theories/Census/Compute/Census_Theorem.v
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
	@echo ">>> current census .vo are BACKED UP (not deleted) -- see below <<<"
	@bdir="census_probes/vo-backup-$$(date +%Y%m%d-%H%M%S)"; \
	  mkdir -p "$$bdir"; \
	  mv -f theories/Census/Run_Split*.vo theories/Census/Run_Split*.glob "$$bdir"/ 2>/dev/null; \
	  mv -f theories/Census/Compute/*.vo theories/Census/Compute/*.glob "$$bdir"/ 2>/dev/null; \
	  echo ">>> previous walk artifacts moved to $$bdir"; \
	  echo ">>> restore with: mv $$bdir/Run_Split* theories/Census/; mv $$bdir/*.vo $$bdir/*.glob theories/Census/Compute/ 2>/dev/null"
	$(MAKE) _census-walk
	@echo "------------------------------------------------------------"
	@echo "RE-WALK COMPLETE.  Confirm the census is HONEST, then refresh the cache:"
	@echo "  # In coqtop/Census_Theorem: Print Assumptions census_decided."
	@echo "  #   MUST be exactly: functional_extensionality_dep (nothing else)."
	@echo "  python3 tools/census_cache.py --update    # rewrite CENSUS_VO_HASH"
	@echo "  git add theories/Census CENSUS_VO_HASH && git commit"
	@echo "------------------------------------------------------------"
.PHONY: census-verify

# Resume an interrupted walk: NEVER deletes anything; skips every unit
# whose .vo already exists and continues in dependency order.  This is
# the target to reach for after an OOM kill, a preemption, or a Ctrl-C
# -- and it is a no-op on a finished walk.  (Same recipe as the guarded
# walk; parallelism via WALK_JOBS, default 2.)
census-resume: all
	$(MAKE) _census-walk
.PHONY: census-resume

# ---------------------------------------------------------------------------
# The route-A closeout (docs/CLOSEOUT_ROUTE_A.md).  Regenerates the stage
# files from the current boards and recompiles theories/Closeout/, yielding
#
#   closeout_partial : forall tm,
#     Deferred D_census tm -> boarded tm \/ Deferred D_remaining tm
#
# Container-safe: NO census walk, and theories/Census/ is never written.
# Run it after every wave of new boards; D_remaining shrinks by exactly the
# machines boarded.  Requires the boards' own .vo to exist already (they are
# built by `make all`).
#
# The gen_shadow --harvest pass between the two inventory runs is what makes a
# 0RB SHADOW fall in the same regen as its core row.  A shadow rides the
# [skipped] disjunct only while its partner is deferred, so boarding a core row
# turns its shadows into ordinary undecided rows -- which need a board each,
# but no new argument (Census/ShadowBoard.v).  --harvest emits them; the second
# inventory picks them up.  It is a no-op when nothing was freed.
closeout:
	python3 tools/closeout/inventory.py
	python3 tools/closeout/gen_shadow.py --harvest
	python3 tools/closeout/inventory.py
	python3 tools/closeout/gen_stages.py
	python3 tools/closeout/audit.py
	coq_makefile -f _CoqProject -o Makefile.coq
	$(MAKE) -f Makefile.coq theories/Closeout/Closeout.vo
	python3 tools/census_cache.py --check
.PHONY: closeout

# Report what the closeout currently certifies, without rebuilding.
closeout-status:
	python3 tools/closeout/audit.py
.PHONY: closeout-status
