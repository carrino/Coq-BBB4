.PHONY: all small23-deps check check-affine-batch check-affine-closeout check-closure-batch check-shadow-links check-transport check-wave check-campaign list-campaign check-next-campaign list-next-campaign check-burn2-campaign list-burn2-campaign check-burn3-campaign list-burn3-campaign check-burn4-campaign list-burn4-campaign check-burn5-campaign list-burn5-campaign check-burn6-campaign list-burn6-campaign clean
CAMPAIGN_JOBS ?= 1
PROOF_JOBS ?= 2
all: small23-deps Makefile.coq
	$(MAKE) -f Makefile.coq
# Alphabet reduction reuses the completed (2,3) theorem. Build only that
# dependency, without the unrelated (3,2) legacy or full (4,2) census targets.
small23-deps:
	$(MAKE) -C ../small Makefile.coq
	$(MAKE) -C ../small -f Makefile.coq theories/Value23.vo
Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@
check: all
	coqchk -silent -bytecode-compiler yes -Q theories BBB24 -Q ../small/theories SmallBB \
	  BBB24.Champion BBB24.Regression BBB24.Bootstrap BBB24.CensusRegression \
	  BBB24.AffineExamples BBB24.AffineRegression BBB24.Checkers.IRules.MetaBlkPfxTr \
	  BBB24.TotalCompletion BBB24.NGramRegression BBB24.RepWLRegression \
	  BBB24.FiniteHistoryRegression BBB24.SymmetryRegression \
	  BBB24.AffineCloseout BBB24.PipelineExamples BBB24.AdvancedExamples \
	  BBB24.CertifiedBoard BBB24.ClosureBatch BBB24.FamilyTransport BBB24.CensusUnion \
	  BBB24.AffineWave BBB24.CycleBatchRegression BBB24.CycleNonHalt \
	  BBB24.WeightedRegression BBB24.WeightedReuse BBB24.OneStateReachRegression \
	  BBB24.OneStateBatch BBB24.StatePipelineRegression BBB24.StateRepWLBatch \
	  BBB24.StateRepWLRegression BBB24.OneStateConditionalRegression \
	  BBB24.TransportIndexRegression BBB24.Alphabet23 BBB24.DualCloseout \
	  BBB24.OrbitCloseout BBB24.BoardManifest BBB24.BranchCloseout \
	  BBB24.WeightedSuffix BBB24.AlphabetMask BBB24.AlphabetQuotientState \
	  BBB24.WeightedTailRegression BBB24.WeightedStateRegression \
	  BBB24.BranchPrefix BBB24.FastWall BBB24.FastWallRegression \
	  BBB24.InstructionPortfolio BBB24.MarkerPotential BBB24.MarkerPotentialRegression \
	  BBB24.MarkerState BBB24.MarkerStateRegression BBB24.MarkerTrail \
	  BBB24.MarkerTrailRegression BBB24.MarkerWalls BBB24.MarkerWallsRegression \
	  BBB24.ReadyReuse BBB24.ReadyReuseRegression BBB24.ReadySwap \
	  BBB24.ReadySwapRegression BBB24.RightMarkerFamily BBB24.RightMarkerState \
	  BBB24.StateBranchCloseout BBB24.StateBranchCycles BBB24.StateBranchJoin \
	  BBB24.StateHistoryCertificate BBB24.StateHistoryCertificateRegression BBB24.WeightedCapacity \
	  BBB24.WeightedSuffixRegression BBB24.ChampionCensusNext

# Keep these recursive calls and checkpoint replays sequential even under -j:
# the drivers deliberately share generated prerequisites under build/.
# Complete BBB(2,4) state proof build, currently under verification.
# Reviewed source inputs and preparation hashes are fixed below. Only successful
# type, assumptions and full recursive audits establish the equality. The heavy
# graph stays out of four/_CoqProject/all.
# Paths below are relative to four/. Users can relocate the prepared tree/logs
# to a larger disk by overriding STATE24_PREPARED and STATE24_STATE.
STATE24_PREPARED ?= build/state-value-selected
STATE24_TREE ?= $(STATE24_PREPARED)/tree
STATE24_MANIFEST ?= $(STATE24_PREPARED)/frozen-prepare-manifest.json
STATE24_STATE ?= build/state-value-proof
# Fixed reviewed source hashes; never infer these from an unreviewed file.
STATE24_MANIFEST_SHA256 ?= c55522aa04323eb95f93e0866410c6ab42d987baff167372054724e5aad5a0da
STATE24_PREPARE_SPEC ?= research/state-value-prepare-manifest.json
STATE24_PREPARE_SPEC_SHA256 ?= 8a608c2f1c62ebb4676d0ed0b0a9dd29fcfb0a920e482d74107a1356b6c184ba
STATE24_PREPARER ?= tools/state_value/prepare_global_sources.py
STATE24_PREPARER_SHA256 ?= 6533956d26f878011e6a63a0d25efdd9c6de5e29fa358c84ff9cd8bc6654e49b
STATE24_SOURCE_INPUT ?= ..
STATE24_JOBS ?= $(if $(BUILD_JOBS),$(BUILD_JOBS),8)
STATE24_DISK_RESERVE_GIB ?= 8
STATE24_RESUME ?=

# Keep invocation sequential even if an outer make uses -j.
# Pure preparation uses the hashes independently checked against the source
# graph. It neither invokes Coq nor establishes the global theorem.
proof: proof-state-source-ready
	@test -n "$(STATE24_MANIFEST_SHA256)" || { \
	  echo 'The selected build requires its reviewed source-manifest hash.' >&2; exit 2; }
	python3 tools/build_state_value.py build \
	  --tree "$(STATE24_TREE)" --manifest "$(STATE24_MANIFEST)" \
	  --manifest-sha256 "$(STATE24_MANIFEST_SHA256)" \
	  --state "$(STATE24_STATE)" --jobs "$(STATE24_JOBS)" --disk-reserve-gib "$(STATE24_DISK_RESERVE_GIB)" \
	  $(if $(filter 1,$(STATE24_RESUME)),--resume,)

proof-state-source-ready:
	@test -n "$(STATE24_MANIFEST_SHA256)" -a -n "$(STATE24_PREPARE_SPEC_SHA256)" -a -n "$(STATE24_PREPARER_SHA256)" || { \
	  echo 'The selected build requires all reviewed source-preparation hashes.' >&2; exit 2; }
	python3 tools/prepare_state_value.py \
	  --source-input "$(STATE24_SOURCE_INPUT)" --spec "$(STATE24_PREPARE_SPEC)" \
	  --spec-sha256 "$(STATE24_PREPARE_SPEC_SHA256)" \
	  --preparer "$(STATE24_PREPARER)" --preparer-sha256 "$(STATE24_PREPARER_SHA256)" \
	  --output "$(STATE24_PREPARED)" --frozen-manifest-sha256 "$(STATE24_MANIFEST_SHA256)" \
	  --disk-reserve-gib "$(STATE24_DISK_RESERVE_GIB)" \
	  $(if $(filter 1,$(STATE24_RESUME)),--resume,)

# A separate explicit target reruns the exact statement/assumptions check and
# full recursive kernel audit on the current selected closure.
proof-report:
	python3 tools/report_state_value.py \
	  --tree "$(STATE24_TREE)" --manifest "$(STATE24_MANIFEST)" \
	  --manifest-sha256 "$(STATE24_MANIFEST_SHA256)" --state "$(STATE24_STATE)"

.PHONY: proof proof-report proof-state-source-ready

proof-checkpoint:
	@echo "Checking the BBB(2,4) proof checkpoint; use proof-2-4 for the complete state equality."
	$(MAKE) check -j$(PROOF_JOBS)
	$(MAKE) proof-state-cases
	@echo "Checkpoint verified. This target does not verify the global state equality."

proof-state-cases:
	python3 tools/replay_state_case_proofs.py --jobs $(PROOF_JOBS)
	python3 tools/replay_state_case_proofs.py --checkpoint additional --jobs $(PROOF_JOBS)
	python3 tools/replay_state_case_proofs.py --checkpoint recent --jobs $(PROOF_JOBS)
	python3 tools/check_burn43_s071_far.py
.PHONY: proof proof-checkpoint proof-state-cases

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
check-campaign:
	python3 tools/rebuild_campaign.py --jobs $(CAMPAIGN_JOBS)
list-campaign:
	python3 tools/rebuild_campaign.py --list
check-next-campaign:
	python3 tools/rebuild_campaign.py --plan research/next-campaign-build.json --only next-campaign --jobs $(CAMPAIGN_JOBS) --log-dir build/next-campaign-rebuild
list-next-campaign:
	python3 tools/rebuild_campaign.py --plan research/next-campaign-build.json --only next-campaign --list
check-burn2-campaign:
	python3 tools/rebuild_campaign.py --plan research/burn2-campaign-build.json --only burn2-campaign --jobs $(CAMPAIGN_JOBS) --log-dir build/burn2-campaign-rebuild
list-burn2-campaign:
	python3 tools/rebuild_campaign.py --plan research/burn2-campaign-build.json --only burn2-campaign --list
check-burn3-campaign:
	python3 tools/rebuild_campaign.py --plan research/burn3-campaign-build.json --only burn3-campaign --jobs $(CAMPAIGN_JOBS) --log-dir build/burn3-campaign-rebuild
list-burn3-campaign:
	python3 tools/rebuild_campaign.py --plan research/burn3-campaign-build.json --only burn3-campaign --list
check-burn4-campaign:
	python3 tools/rebuild_campaign.py --plan research/burn4-campaign-build.json --only burn4-campaign --jobs $(CAMPAIGN_JOBS) --log-dir build/burn4-campaign-rebuild
list-burn4-campaign:
	python3 tools/rebuild_campaign.py --plan research/burn4-campaign-build.json --only burn4-campaign --list
check-burn5-campaign:
	python3 tools/rebuild_campaign.py --plan research/burn5-campaign-build.json --only burn5-campaign --jobs $(CAMPAIGN_JOBS) --log-dir build/burn5-campaign-rebuild
list-burn5-campaign:
	python3 tools/rebuild_campaign.py --plan research/burn5-campaign-build.json --only burn5-campaign --list
check-burn6-campaign:
	python3 tools/rebuild_campaign.py --plan research/burn6-campaign-build.json --only burn6-campaign --jobs $(CAMPAIGN_JOBS) --log-dir build/burn6-campaign-rebuild
list-burn6-campaign:
	python3 tools/rebuild_campaign.py --plan research/burn6-campaign-build.json --only burn6-campaign --list
clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
