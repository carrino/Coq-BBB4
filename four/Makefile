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
proof:
	python3 tools/report_state_value.py --check-source
	$(MAKE) proof-checkpoint
	$(MAKE) -f Makefile.coq theories/Value.vo
	python3 tools/report_state_value.py

proof-checkpoint:
	@echo "Checking current BBB(2,4) Coq proofs; the universal upper bound remains open."
	$(MAKE) check -j$(PROOF_JOBS)
	$(MAKE) proof-state-cases
	@echo "Checkpoint verified. The global BBB(2,4) equality is still open."

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
