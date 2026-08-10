all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	rm -f Makefile.coq Makefile.coq.conf
	rm -f theories/Closeout/CloseoutFinal.vo theories/Closeout/CloseoutFinal.glob
	rm -f theories/Closeout/BBB4_Theorem.vo theories/Closeout/BBB4_Theorem.glob
	rm -f theories/Closeout/BBB4_Value.vo theories/Closeout/BBB4_Value.glob

.PHONY: all clean

# ---------------------------------------------------------------------------
# `make proof' -- build and state the top-level BBB(4) result:
#
#   BBB4_value : BBB4_statement          (the claim of theories/BBB4_Spec.v)
#
# i.e. BBB(4) = 32,779,478: some state of some (4,2) machine (the champion
# 1RB1LD_1RC1RB_1LC1LA_0RC0RD's StD) scores exactly 32,779,478, and no
# state of any (4,2) machine scores more (theories/Closeout/BBB4_Value.v;
# the residue lists are EMPTY since 2026-08-01).  docs/CLAIMS.md states
# the claim -- and its census trust tier -- precisely.
#
# The chain: census_decided (committed census .vo) -> closeout_partial
# (Closeout.vo, from source via `make') -> census_boarded (CloseoutFinal.v)
# -> bbb4_target (BBB4_Theorem.v) -> BBB4_value (BBB4_Value.v).  The last
# three files LOAD the committed census .vo, which are toolchain-specific
# (built with coq-native): compile them under the census opam switch
# (docs/VERIFYING.md).  On a mismatched toolchain the load fails with
# "inconsistent assumptions"; either use the census switch or re-derive
# the census .vo with `make census-verify'.
proof: all
	@python3 tools/census_cache.py --check
	coqc -Q theories BBB4 theories/Closeout/CloseoutFinal.v || \
	  { echo "proof: FAILED loading the committed census .vo -- use the census"; \
	    echo "proof: opam switch (docs/VERIFYING.md) or run make census-verify."; \
	    exit 1; }
	coqc -Q theories BBB4 theories/Closeout/BBB4_Theorem.v
	coqc -Q theories BBB4 theories/Closeout/BBB4_Value.v
	@python3 tools/proof_report.py
.PHONY: proof

# The census certification: the per-subtree queue enumerations
# (parallel; each Qed is one native_compute walk) + the assembled
# theorem.  Needs native_compute: eval $(opam env --switch=census).
# Layers: Run_Split (grandchild split) -> Run_Split2 + the 7
# Run_Split_<tag> heavy-grandchild splits -> the GG_1LC / GGH_ great-
# grandchild walks -> the 24 G_ units -> theorem.  385 core-min native
# (measured 2026-08-09): 1 h 45 m at WALK_JOBS=4, ~52 m at 8.
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
# WALK_JOBS: how many walk units run at once, computed from THIS machine:
#   min(cores, (available RAM - 2 GB) / WALK_RSS_GB), floor 1
# At the current 2 GB/unit that is the core count on anything from 8 GB
# up.  (It was 7 GB/unit until the units were made lean, and then it was
# the binding constraint: 16 GB -> 2 jobs, 32 GB -> 4.  Four 6.8 GB units
# OOM-killed a 16 GB box on the GG_1LC layer, signal 9, 2026-07-22.)
# Override explicitly with `make census-verify WALK_JOBS=6'.  (`make -j'
# does not parallelize the walk -- WALK_JOBS is the knob.)
#
# WALK_RSS_GB is the per-unit peak this sizing assumes.  It WAS 7, and
# that number is what made this a memory problem: 6.8 GB/unit caps a
# 32 GB box at 4 jobs and 1 h 43 m.  79% of it was the environment each
# unit Required -- the boarded-machine theorems behind [proven_all] --
# which the walk half never looks inside.  Census/Run_Compute.v and the
# lean units removed it: a unit's environment is 0.263 GB (vm) against
# 2.743 GB before, and the native lean measurement of the same walk was
# 0.371 GB against 6.758 GB.
#
# 2 is deliberately conservative -- roughly 3x the measured lean peak --
# and PROVISIONAL until a native walk records the real distribution.
# Every walk writes census_probes/walk-rss.tsv (WALK_RSS below);
# `python3 tools/walk_rss_report.py' prints the max and the jobs it
# supports, and you should set this from that.  Raising it is always
# safe; lowering it below your measured max invites the OOM killer.
#
# At 2 GB/unit the RAM term stops binding at any sane size: a 32 GB box
# gets its core count, and so does a 16 GB one -- which is the point.
# The walk was never supposed to need a big desktop.
WALK_RSS_GB ?= 2
WALK_AUTO := $(shell m=$$(awk -v r=$(WALK_RSS_GB) '/MemAvailable/{print int(($$2/1048576 - 2)/r)}' /proc/meminfo 2>/dev/null); m=$${m:-2}; c=$$(nproc 2>/dev/null || echo 2); [ "$$m" -lt 1 ] && m=1; [ "$$m" -gt "$$c" ] && m=$$c; echo $$m)
WALK_JOBS ?= $(WALK_AUTO)

# WALK_OCAMLRUNPARAM: OCaml GC tuning for the walk units.  Measured
# 2026-08-04 on GG_1LC_1LB (32 GB desktop): untuned the unit ratchets to
# ~11-12 GB peak; 'o=80,O=150' -> 8.19 GB; 'o=40,O=60' -> 6.76 GB, FLAT
# from minute 3 onward, still 99% CPU.  o = GC space-overhead target (%),
# O = compaction threshold (%) -- compaction is the only thing that
# returns major-heap memory to the OS.  Lower peaks => more WALK_JOBS on
# the same RAM (WALK_RSS_GB above assumes this default).  Override or
# disable: `make ... WALK_OCAMLRUNPARAM='.
#
# The rest of that note used to read "so without it each unit's RSS is
# the high-water mark of its worst pop's transient garbage".  That was a
# hypothesis, never measured, and it is wrong by ~20x
# (tools/probes/gen_rss_probe.py, 2026-08-09).  Measured under
# vm_compute, GG_1LC_1LB's real computation walked to an EMPTY queue:
#
#   Require Run + Run_Split + Run_Split2, evaluate nothing   2.743 GB
#     -- of which Census/Proven_Data.vo (the board THEOREMS)  2.650 GB
#   + the whole subtree walked, queue ([],[])                3.667 GB
#   the same walk on data-only lookup tables (ProbeWalkCommon) 0.307 GB
#
# So the decider's transient garbage is ~0.1 GB, `o' multiplies a live
# set that is 75% environment, and 2.65 GB of that environment is proofs
# the walk half of a unit never looks inside.  o is a target for slack
# RELATIVE TO LIVE DATA, so it scales with the environment, not with the
# decider: same unit, one run each,
#
#   untuned 5.474 GB / 137 s   o=80,O=150 4.539 / 136   o=40,O=60 3.667 / 143
#   o=20,O=30 3.323 GB / 157 s   o=10,O=20 2.959 / 187
#
# o=40,O=60 stays the default: tightening further buys 9-19% of RSS for
# 10-30% of CPU, and WALK_JOBS is integer, so on a 32 GB box it does not
# cross a job boundary on its own.  docs/CENSUS_RUNTIME.md has the
# arithmetic and what it would take to cross one.
WALK_OCAMLRUNPARAM ?= o=40,O=60

# WALK_RSS: per-unit peak RSS + wall/user seconds, appended to
# census_probes/walk-rss.tsv (one line per unit, `/usr/bin/time -a').
# The 6.8 GB above is ONE unit measured by hand in July; nothing has ever
# recorded the DISTRIBUTION, and WALK_JOBS is derived entirely from that
# single number.  Recording costs nothing (`/usr/bin/time' wraps the
# existing coqc), touches no census input -- tools/census_cache.py hashes
# the census .v only -- and makes every walk report what the next walk
# should be sized for.  `tools/walk_rss_report.py' summarises it and says
# what WALK_JOBS the measured peak supports on a given box.  Disable with
# `make ... WALK_RSS='; degrades to a plain coqc where /usr/bin/time is
# absent (it lives in the `time' package, not the shell builtin).
WALK_RSS ?= census_probes/walk-rss.tsv
WALK_HAS_TIME := $(shell [ -x /usr/bin/time ] && echo yes)
ifneq ($(WALK_RSS),)
ifeq ($(WALK_HAS_TIME),yes)
WALK_MEASURE = /usr/bin/time -a -o $(WALK_RSS) -f '%M\t%e\t%U\t%C'
endif
endif
WALK_COQC = env OCAMLRUNPARAM='$(WALK_OCAMLRUNPARAM)' $(WALK_MEASURE) \
	    coqc -Q theories BBB4

# WALK_MEMFREE (opt-in, needs GNU parallel): memory-aware launch gate,
# the walk's analogue of the IRules order-only chains.  A new unit is
# started only while at least this much RAM is free (e.g.
# `make census-verify WALK_JOBS=8 WALK_MEMFREE=6G'); if free RAM later
# halves below the gate, GNU parallel suspends-and-requeues the
# youngest unit instead of letting the OOM killer pick one.  WALK_JOBS
# still caps the fan-out.  Unset = plain xargs, exactly as before.
ifeq ($(WALK_MEMFREE),)
WALK_RUN = xargs -r -P$(WALK_JOBS) -I{} $(WALK_COQC) {}
else
WALK_RUN = parallel --will-cite -j$(WALK_JOBS) --memfree $(WALK_MEMFREE) $(WALK_COQC) {}
endif

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
	@echo ">>> walk parallelism: WALK_JOBS=$(WALK_JOBS) (auto = min(cores, (free RAM - 2 GB)/$(WALK_RSS_GB) GB); override with WALK_JOBS=N or WALK_RSS_GB=N), GC: OCAMLRUNPARAM=$(WALK_OCAMLRUNPARAM)"
	@if [ -n "$(WALK_MEASURE)" ]; then mkdir -p census_probes; \
	   [ -f "$(WALK_RSS)" ] || \
	     printf 'peak_rss_kb\twall_s\tuser_s\tcommand\n' > "$(WALK_RSS)"; \
	   echo ">>> per-unit peak RSS -> $(WALK_RSS) (python3 tools/walk_rss_report.py)"; \
	 elif [ -n "$(WALK_RSS)" ]; then \
	   echo ">>> per-unit peak RSS NOT recorded: /usr/bin/time missing (apt-get install time)"; \
	 fi
	[ -f theories/Census/Run_Split.vo ] || $(WALK_COQC) theories/Census/Run_Split.v
	[ -f theories/Census/Run_Split2.vo ] || $(WALK_COQC) theories/Census/Run_Split2.v
	ls theories/Census/Run_Split_*.v | while read f; do [ -f "$${f%.v}.vo" ] || echo "$$f"; done | $(WALK_RUN)
	ls theories/Census/Compute/GG_1LC_*.v | while read f; do [ -f "$${f%.v}.vo" ] || echo "$$f"; done | $(WALK_RUN)
	ls theories/Census/Compute/GGH_*.v | while read f; do [ -f "$${f%.v}.vo" ] || echo "$$f"; done | $(WALK_RUN)
	ls theories/Census/Compute/G_*.v | while read f; do [ -f "$${f%.v}.vo" ] || echo "$$f"; done | $(WALK_RUN)
	[ -f theories/Census/Compute/Census_Theorem.vo ] || $(WALK_COQC) theories/Census/Compute/Census_Theorem.v
.PHONY: _census-walk

# Guarded census: skip the walk when the committed .vo already certify this
# tree (hash matches + all census .vo present); otherwise WARN and walk.
census: all
	@if python3 tools/census_cache.py --check >/dev/null 2>&1; then \
	  echo "census cache VALID -- skipping walk (make census-verify to force a re-walk)"; \
	else \
	  echo "############################################################"; \
	  echo "# census cache INVALID or absent -- WALKING FROM SOURCE.    "; \
	  echo "# This is heavy native_compute (385 core-min) and preempts on "; \
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
