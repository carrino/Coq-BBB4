# STACK_KB: the build raises its own stack limit before compiling.
#
# `coqnative' generates one OCaml module per .vo and the OCaml compiler
# recurses over its structure.  The census data lists
# (Census/Proven_List.v and friends) are 5,270-6,517 machine definitions
# in a file, and on the DEFAULT 8 MB stack that is enough to kill it:
#
#     COQNATIVE theories/Census/Proven_List.vo
#     Fatal error: exception Stack overflow
#     Error: Native compiler exited with status 2 (in case of stack
#            overflow, increasing stack size ... often helps)
#
# Plain `coqc' compiles the same files without complaint, so this is
# invisible on any build without a native compiler -- which is most of
# them, and is why it reached a fresh clone.  It bites under the census
# (native) opam switch, on the very first build, which is exactly the
# path someone takes to verify the proof themselves.  Coq's own hint is
# right; there is no reason to make each person rediscover it.
#
# Measured 2026-08-11 on the census switch: 8192 KB overflows, unlimited
# builds all three lists clean.  A soft-limit raise is allowed up to the
# hard limit; where it is not permitted, this degrades to exactly the
# old behaviour and Coq prints the hint above.  Override with
# `make STACK_KB=262144'.
STACK_KB ?= unlimited
all: Makefile.coq
	@# WARN (never fail) when this coqc has no native compiler.  A plain
	@# `make' is legitimately useful that way -- CI builds on apt Coq and
	@# the default build is all-source -- but the resulting .vo can
	@# neither do the census walk nor load alongside the committed census
	@# .vo, which are OCaml-marshalled by a different compiler.
	@#
	@# This exists because `opam env' lives in the shell and a REBOOT
	@# silently drops you back on /usr/bin/coqc.  Nothing announces it;
	@# the build merely gets 33% faster (2026-08-12: 40m00s native,
	@# 26m39s not) and quietly stops being walk-capable.  Discovered
	@# after ~50 min of builds nobody could use.
	@if [ "$$(coqc -config 2>/dev/null | sed -n 's/^COQ_NATIVE_COMPILER_DEFAULT=//p')" = "no" ]; then \
	   echo ">>> NOTE: this coqc has no native compiler ($$(command -v coqc))."; \
	   echo ">>>   Fine for a plain build.  NOT usable for 'make census-verify'"; \
	   echo ">>>   or 'make proof' -- the .vo will not load with the committed"; \
	   echo ">>>   census .vo.  For those: eval \$$(opam env --switch=census)"; \
	   echo ">>>   then rm -f Makefile.coq && make clean && make."; \
	 fi
	@ulimit -s $(STACK_KB) 2>/dev/null || true; \
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
# At the current 2 GB/unit that is the core count on anything from 10 GB
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
# MEASURED, at last, by a full native walk (2026-08-10, 16 cores /
# 31 GB, tools/walk_rss_report.py over all 154 units):
#
#   peak RSS max / p90 / median / min   6.30 / 2.76 / 0.51 / 0.40 GB
#   GGH        104 lean units   max 0.60 GB
#   GG_1LC      16 lean units   max 0.61 GB
#   G_          24 units        max 2.77 GB  (the 8 assemblers)
#   Run_Split*   9 units        max 2.76 GB
#   Census_Theorem              max 6.30 GB, alone
#
# So 1 GB, not the provisional 2: the lean units top out at 0.61 GB and
# this leaves 64% headroom.  The distribution is bimodal and the two
# modes are sized apart (WALK_ASM_RSS_GB below); a single number would
# have to cover 0.40 GB and 6.30 GB at once, which is what made the old
# knob lie.  Raising it is always safe; lowering it below your measured
# max invites the OOM killer.  Every walk rewrites
# census_probes/walk-rss.tsv, so re-derive it on your own box rather
# than trusting this line.
#
# At 1 GB/unit the RAM term stops binding at any sane size: a 32 GB box
# gets its core count, and so does a 16 GB one -- which is the point.
# The walk was never supposed to need a big desktop.
#
# It is NOT what sets the walk's minimum RAM, though, and this knob will
# happily lie to you about that.  The floor is the single largest file
# run alone: Census_Theorem, MEASURED at 6.30 GB.  Call the floor ~9 GB
# with the 2 GB headroom.  Below that no WALK_JOBS setting saves you --
# the last file in the walk does not fit.  (This was written as ~10 GB
# from a 7.2 GB projection -- 3.706 GB under vm_compute scaled by the
# environment's 1.94x vm/native factor.  The walk measured 6.30 GB.  The
# factor was measured on a unit that EVALUATES; Census_Theorem loads and
# applies [exact]s, so native does not inflate it the same way.)
WALK_RSS_GB ?= 1

# WALK_CORES: PHYSICAL cores, not `nproc'.
#
# nproc counts hardware threads, and the walk is CPU-bound
# native_compute -- two units sharing a core do not go twice as fast,
# they contend for the same execution units and cache and each takes
# longer.  Sizing off nproc oversubscribes 2x on any SMT machine, which
# is most of them.
#
# This bit on the first lean walk: an 8-core/16-thread box reported
# nproc=16, so WALK_JOBS auto-sized to 14 (and would have been 16 once
# WALK_RSS_GB dropped to 1).  Per-unit CPU measured under that
# contention came out at 421 core-min against the pre-lean walk's 385 --
# the units did not get slower, the accounting did.
#
# lscpu's (Core,Socket) pairs are the portable count; fall back to nproc
# where lscpu is absent.  Override with `make ... WALK_CORES=N'.
WALK_CORES ?= $(shell c=$$(lscpu -p=Core,Socket 2>/dev/null | grep -v '^\#' | sort -u | wc -l 2>/dev/null); \
  if [ -z "$$c" ] || [ "$$c" -lt 1 ]; then c=$$(nproc 2>/dev/null || echo 2); fi; echo $$c)

WALK_AUTO := $(shell m=$$(awk -v r=$(WALK_RSS_GB) '/MemAvailable/{print int(($$2/1048576 - 2)/r)}' /proc/meminfo 2>/dev/null); m=$${m:-2}; c=$(WALK_CORES); [ "$$m" -lt 1 ] && m=1; [ "$$m" -gt "$$c" ] && m=$$c; echo $$m)
WALK_JOBS ?= $(WALK_AUTO)

# ---------------------------------------------------------------------
# WALK_ASM_JOBS: the SAME sizing, for the files the lean split did not
# make lean.  15 of the 154 still Require Census/Run.v, because they
# prove [NodeDecided] and that needs [decider_WF] -> [proven_all] -> the
# boards.  A library's environment is loaded whole, so there is no way to
# name [decider_WF] without paying for it: the 7 Census/Run_Split_<tag>.v
# and the 8 Compute/G_* assemblers are irreducibly heavy.
#
# WALK_RSS_GB alone is therefore WRONG for them, and dangerously so: at
# 2 GB/unit a 32 GB box picks 8 jobs, and 8 of these at once is ~43 GB.
# Sizing the whole walk from the lean measurement would have OOM-killed
# the Run_Split_<tag> layer at the START of the walk and the G_ layer at
# the END -- after 120 finished units.  (Introduced when WALK_RSS_GB went
# 7 -> 2 and caught before any walk ran, 2026-08-10.)
#
# MEASURED by the full native walk (2026-08-10): the 8 G_ assemblers
# peak at 2.77 GB and the 7 Run_Split_<tag> at 2.76 GB.  3.5 gives 26%
# headroom over that.
#
# This was 7, from a projection that was wrong in an instructive way.
# The vm measurement here was 2.771 GB, and I scaled it by the 1.94x
# vm/native factor to ~5.4 GB, then rounded up to the 7 every pre-lean
# walk had used.  Natively it is 2.77 GB -- the SAME as vm, no inflation
# at all.  The reason was already written two paragraphs up and not
# applied: these files do not walk, they are environment plus a handful
# of [exact]s.  native_compute inflates EVALUATION, and there is none
# here.  A factor measured on a unit that evaluates does not transfer to
# a file that does not, however similar the two look.
#
# The cost of that error was parallelism, not safety: at 7 GB a 32 GB
# box ran these 15 files 4-wide when 8-wide fits.
WALK_ASM_RSS_GB ?= 3.5
WALK_ASM_AUTO := $(shell m=$$(awk -v r=$(WALK_ASM_RSS_GB) '/MemAvailable/{print int(($$2/1048576 - 2)/r)}' /proc/meminfo 2>/dev/null); m=$${m:-1}; c=$(WALK_CORES); [ "$$m" -lt 1 ] && m=1; [ "$$m" -gt "$$c" ] && m=$$c; echo $$m)
WALK_ASM_JOBS ?= $(WALK_ASM_AUTO)

# A file is heavy iff it imports another Census.Compute module -- i.e. it
# assembles rather than walks.  Tested, not assumed: that predicate picks
# out exactly the 9 Compute files that Require Run (the 8 G_ assemblers
# and Census_Theorem) and none of the 136 lean units.  Deriving it from
# the file instead of a name list means a regenerated tree cannot drift
# out of step with this Makefile.
ASM_PRED = grep -q '^From BBB4.Census.Compute Require'

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
# GNU parallel has to be RUNNABLE, not merely named on PATH.  A
# non-executable file called `parallel' earlier in PATH makes the shell
# say "Permission denied" rather than "not found" -- and it says it at
# WALK time, which is after `census-verify' has already backed up and
# quarantined every census .vo.  You discover it having paid the setup
# cost and with nothing walked (seen 2026-08-10 under WSL2).
#
# So probe it, and degrade to xargs with a notice rather than dying --
# the same contract WALK_RSS has when /usr/bin/time is absent.  Nothing
# is lost but the second belt: WALK_JOBS/WALK_ASM_JOBS are what keep the
# walk inside RAM, and --memfree only re-checks while it runs.
WALK_HAS_PARALLEL := $(shell p=$$(command -v parallel 2>/dev/null); \
  [ -n "$$p" ] && [ -x "$$p" ] && "$$p" --version >/dev/null 2>&1 && echo yes)
ifeq ($(WALK_MEMFREE),)
WALK_RUN = xargs -r -P$(WALK_JOBS) -I{} $(WALK_COQC) {}
WALK_ASM_RUN = xargs -r -P$(WALK_ASM_JOBS) -I{} $(WALK_COQC) {}
else ifneq ($(WALK_HAS_PARALLEL),yes)
WALK_RUN = xargs -r -P$(WALK_JOBS) -I{} $(WALK_COQC) {}
WALK_ASM_RUN = xargs -r -P$(WALK_ASM_JOBS) -I{} $(WALK_COQC) {}
else
WALK_RUN = parallel --will-cite -j$(WALK_JOBS) --memfree $(WALK_MEMFREE) $(WALK_COQC) {}
WALK_ASM_RUN = parallel --will-cite -j$(WALK_ASM_JOBS) --memfree $(WALK_MEMFREE) $(WALK_COQC) {}
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
	@# The walk is native_compute.  On a tree built with the native
	@# compiler disabled, `native_cast_no_check' silently falls back to
	@# VM conversion -- a WARNING, not an error -- and `coqnative' never
	@# runs at all, so such a walk proves nothing about a native one and
	@# native-only failures (the coqnative stack overflow on the flat
	@# data lists, for one) stay structurally invisible.
	@#
	@# _CoqProject carries no -native-compiler flag, so Makefile.coq
	@# inherits it from whichever coq_makefile generated it -- and
	@# regenerating it by hand outside the census switch bakes in `no'.
	@# Measured 2026-08-12: the same tree builds in 40m00s with native
	@# and 26m39s without, and the fast one cannot walk.  Caught by
	@# reading coqc's flags in top; nothing checked it before.
	@# Ask the TOOLCHAIN, not Makefile.coq: coq_makefile emits all three
	@# branches of the COQACTUALNATIVEFLAG conditional, so grepping the
	@# generated file for `no' matches the unused arm every time.
	@if [ "$$(coqc -config 2>/dev/null | sed -n 's/^COQ_NATIVE_COMPILER_DEFAULT=//p')" = "no" ]; then \
	   echo "############################################################"; \
	   echo "# REFUSING TO WALK: this coqc has no native compiler        "; \
	   echo "# (coqc -config says COQ_NATIVE_COMPILER_DEFAULT=no).       "; \
	   echo "# native_cast_no_check would fall back to the VM with only a"; \
	   echo "# warning, and coqnative would never run.  The .vo produced  "; \
	   echo "# would certify nothing about a native walk.                 "; \
	   echo "#                                                            "; \
	   echo "# You are probably outside the census opam switch:           "; \
	   echo "#   which coqc     # want ~/.opam/census/bin/coqc, not /usr  "; \
	   echo "#   eval \$$(opam env --switch=census)                        "; \
	   echo "#   rm -f Makefile.coq && make                               "; \
	   echo "#                                                            "; \
	   echo "# .vo are OCaml-marshalled, so a tree built by apt Coq       "; \
	   echo "# (4.14.1) cannot be mixed with census .vo (4.14.2) either.  "; \
	   echo "############################################################"; \
	   exit 1; \
	 fi
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
	@echo ">>> walk parallelism: WALK_JOBS=$(WALK_JOBS) for the 136 lean units, ONE pool (auto = min(cores, (free RAM - 2 GB)/$(WALK_RSS_GB) GB); override with WALK_JOBS=N or WALK_RSS_GB=N), GC: OCAMLRUNPARAM=$(WALK_OCAMLRUNPARAM)"
	@echo ">>> WALK_ASM_JOBS=$(WALK_ASM_JOBS) for the 15 that still Require Run.v (7 Run_Split_<tag> + 8 G_ assemblers, $(WALK_ASM_RSS_GB) GB each)"
	@if [ -n "$(WALK_MEMFREE)" ] && [ "$(WALK_HAS_PARALLEL)" != "yes" ]; then \
	   echo ">>> WALK_MEMFREE=$(WALK_MEMFREE) IGNORED: no runnable GNU parallel (apt-get install parallel)."; \
	   echo ">>> Using xargs; the job counts above still bound RAM, but nothing re-checks free memory as it runs."; \
	 fi
	@if [ -n "$(WALK_MEASURE)" ]; then mkdir -p census_probes; \
	   [ -f "$(WALK_RSS)" ] || \
	     printf 'peak_rss_kb\twall_s\tuser_s\tcommand\n' > "$(WALK_RSS)"; \
	   echo ">>> per-unit peak RSS -> $(WALK_RSS) (python3 tools/walk_rss_report.py)"; \
	 elif [ -n "$(WALK_RSS)" ]; then \
	   echo ">>> per-unit peak RSS NOT recorded: /usr/bin/time missing (apt-get install time)"; \
	 fi
	[ -f theories/Census/Run_Split.vo ] || $(WALK_COQC) theories/Census/Run_Split.v
	[ -f theories/Census/Run_Split2.vo ] || $(WALK_COQC) theories/Census/Run_Split2.v
	@# HEAVY: these seven Require Run.v.  WALK_ASM_JOBS, not WALK_JOBS.
	ls theories/Census/Run_Split_*.v | while read f; do [ -f "$${f%.v}.vo" ] || echo "$$f"; done | $(WALK_ASM_RUN)
	@# ONE POOL for all 136 lean walk units.  GG_1LC, GGH and the lean
	@# half of G_ used to be three separate `ls | xargs' passes, i.e.
	@# three BARRIERS, and a barrier makes a layer cost its LONGEST unit
	@# rather than its share of the work: GG_1LC is 96 core-min that fits
	@# in 12 minutes across 8 jobs, but GG_1LC_0LD alone runs 15.9.
	@#
	@# The barriers were never a dependency.  Every lean unit imports
	@# exactly TNF_QH/Decide/Run_Compute/Run_Compute_Split -- base-build
	@# modules only: not Run_Split, not Run_Split2, not Run_Split_<tag>,
	@# and not each other.  The first files that consume a walk result
	@# are the 8 G_ assemblers, which still run in their own pass below.
	@#
	@# Merged, the pool's LPT makespan is core-min/jobs to two decimals
	@# (measured on the 2026-08-10 walk: 52.2 against a 52.19 perfect
	@# share), so no unit sets a floor and splitting a heavy one buys
	@# nothing.  61.8 -> 53.8 min at 8 jobs; see
	@# `tools/walk_rss_report.py', which models both schedules.
	@#
	@# The two populations stay on separate passes: the assemblers need
	@# Run.v and peak ~2.8 GB, so WALK_ASM_JOBS still bounds them.
	{ ls theories/Census/Compute/GG_1LC_*.v \
	     theories/Census/Compute/GGH_*.v; \
	  ls theories/Census/Compute/G_*.v | while read f; do \
	     $(ASM_PRED) "$$f" || echo "$$f"; done; } \
	 | while read f; do [ -f "$${f%.v}.vo" ] || echo "$$f"; done \
	 | $(WALK_RUN)
	ls theories/Census/Compute/G_*.v | while read f; do \
	   if [ ! -f "$${f%.v}.vo" ] && $(ASM_PRED) "$$f"; then echo "$$f"; fi; \
	 done | $(WALK_ASM_RUN)
	[ -f theories/Census/Compute/Census_Theorem.vo ] || $(WALK_COQC) theories/Census/Compute/Census_Theorem.v
.PHONY: _census-walk

# `make proof-all' -- the whole claim from source, in one command.
#
# `make proof' compiles the closeout chain over the COMMITTED census
# .vo: base build only, and it asks you to trust 154 files someone
# else walked.
# This target is the rung that does not: base build, RE-DERIVE the
# census (census-verify backs the committed .vo out of the way and
# walks from source), then the same closeout chain and the same
# `Print Assumptions'.
#
# Measured 2026-08-12 on 8 physical cores (16 threads) / 31 GB:
#   base build 40 min (`make -j16', from `git clean -fdx')
#   + walk 42.6 min (WALK_JOBS=8, un-niced)  =  ~83 min end to end.
# Needs the census opam switch (native_compute) and >= 10 GB RAM --
# Compute/Census_Theorem.v runs alone at 6.3 GB.  docs/VERIFYING.md.
#
# WALK_JOBS/WALK_ASM_JOBS pass straight through, e.g.
#   make proof-all WALK_JOBS=8
proof-all: all
	@echo "############################################################"
	@echo "# proof-all: re-deriving the census from source.            "
	@echo "# The committed .vo are NOT trusted here -- census-verify    "
	@echo "# backs them up and walks.  ~83 min total on 8 cores / 32 GB,  "
	@echo "# of which the base build above is about half.               "
	@echo "############################################################"
	$(MAKE) census-verify
	coqc -Q theories BBB4 theories/Closeout/CloseoutFinal.v
	coqc -Q theories BBB4 theories/Closeout/BBB4_Theorem.v
	coqc -Q theories BBB4 theories/Closeout/BBB4_Value.v
	@python3 tools/proof_report.py
	@echo "------------------------------------------------------------"
	@echo "proof-all COMPLETE.  The census above was WALKED on this"
	@echo "machine, not loaded from the committed cache.  The"
	@echo "'Print Assumptions' block is the whole trust surface."
	@echo "------------------------------------------------------------"
.PHONY: proof-all

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
