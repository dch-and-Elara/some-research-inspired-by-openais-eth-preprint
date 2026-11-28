import J6R57ScopeFeeFootprinted

/-! Eliminate opaque scale for the structural part of the selected scope:
only true word widths, two resident row counts, actual atlas census, and
individually charged external producer fees occur. -/
namespace J6R79Numeric
open scoped Polynomial
open J6R16ModeCost J6R21Ancestor J6R51Peak J6R50SourceProducer
open J6R57ScopeFee J6R30ProducedGateRegistry
open J6R17ModeTape J6R27OriginalGate J6R33GeneratedChildSite J6R33PageIndexedBirth
open J6R32StatefulArithmetic J6R34RootAtlas J6R32ChildResidentTransfer

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 18000000
set_option maxRecDepth 4300

structure ScopeSizes (s C edges key prec tw bw page ptr nH nR : ℕ)
    (W : ScopeWordCaps) (atlas K : ℕ) : Prop where
  lambda : Nat.clog 2 s ≤ K
  layers : pathLimit s C ≤ K
  edgesLe : edges ≤ K
  keyLe : key ≤ K
  precLe : prec ≤ K
  timeLe : tw ≤ K
  bodyWordLe : bw ≤ K
  pageLe : page ≤ K
  pointerLe : ptr ≤ K
  headersLe : nH ≤ K
  refsLe : nR ≤ K
  fixedLe : W.fixed ≤ K
  addrLe : W.addr ≤ K
  seedLe : W.seed ≤ K
  initialHeaderLe : W.initialHeader ≤ K
  ownerLe : W.owner ≤ K
  ownerKeyLe : W.ownerKey ≤ K
  seatKeyLe : W.seatKey ≤ K
  ownerRowsLe : W.ownerRows ≤ K
  seatRowsLe : W.seatRows ≤ K
  atlasLe : atlas ≤ K

/-- No instance-dependent costs occur in this univariate polynomial. -/
def structuralScope (K : ℕ) :=
  (4+2*K*(3*K+11+maxAddonFee K K K K K))+
  sidecarGeometry K K K K K K K K K K K+
  entryGeometry K K K K (2*K+2) K+
  atlasWordGeometryCeiling K+shapeFrameFee K+
  J6R51Peak.publicationOverhead K K K K K (K+3*K*(K+(2*K+2))) (2*K) (2*K)+
  twoTailFee K+4

theorem atlasGeometry_mono {U K : ℕ} (h : U ≤ K) :
    atlasWordGeometryCeiling U ≤ atlasWordGeometryCeiling K := by
  unfold atlasWordGeometryCeiling prepareSiteFee requestsGeometryCeiling headerSweepCeiling
    framePayloadFee probeCopyFee slotStride pipelineFee onePageFee
    spanFee requestFee dispatchStride contextCopyFee A1R11.uvWidth denseRecordFee modeBindingFee
    maskSearchStride buildModeInputCap recordStride
  gcongr

theorem derivedScope_le_producers_add_structural
    {s C edges key prec tw bw page ptr nH nR atlas K : ℕ} {W : ScopeWordCaps}
    (G : ScopeSizes s C edges key prec tw bw page ptr nH nR W atlas K)
    (boot demand queries words : ℕ) :
    derivedPerScope s C edges key prec tw bw page ptr nH nR W
      (primitiveAndFootprintBudget boot demand queries words atlas) ≤
        boot+demand+queries+words+structuralScope K := by
  have hDim := G.lambda
  have hDepth := G.layers
  have he := G.edgesLe
  have hk := G.keyLe
  have hp := G.precLe
  have htw := G.timeLe
  have hbw := G.bodyWordLe
  have hPage := G.pageLe
  have hPtr := G.pointerLe
  have hH := G.headersLe
  have hR := G.refsLe
  have hf := G.fixedLe
  have ha := G.addrLe
  have hSeed := G.seedLe
  have hI := G.initialHeaderLe
  have ho := G.ownerLe
  have hok := G.ownerKeyLe
  have hsk := G.seatKeyLe
  have hor := G.ownerRowsLe
  have hsr := G.seatRowsLe
  have hBody : sourceBodyCap s C W.seed ≤ 2*K+2 := by
    unfold sourceBodyCap
    have h : max W.seed (Nat.clog 2 s+2) ≤ K+2 := max_le (by omega) (by omega)
    omega
  have index : uniformIndexGeometry s edges key prec page W ≤
      4+2*K*(3*K+11+maxAddonFee K K K K K) := by
    unfold uniformIndexGeometry maxAddonFee
    gcongr
  have desc : uniformDescSidecar s edges key prec page W ≤
      sidecarGeometry K K K K K K K K K K K := by
    unfold uniformDescSidecar sidecarGeometry locateFee maxAddonFee
    gcongr
  have entry : entryGeometry edges edges W.fixed W.addr (sourceBodyCap s C W.seed) key ≤
      entryGeometry K K K K (2*K+2) K := by
    unfold entryGeometry
    gcongr
  have hMul : 3*edges/29 ≤ 3*K :=
    (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left 3 he)
  have width : liveHeaderWidth edges W.fixed W.addr (sourceBodyCap s C W.seed)
      W.initialHeader ≤ K+3*K*(K+(2*K+2)) := by
    unfold liveHeaderWidth
    apply max_le
    · exact hI.trans (Nat.le_add_right _ _)
    · gcongr
  have pub : Nat.le (livePublicationSetup s C edges key prec tw bw W.fixed W.addr
      (sourceBodyCap s C W.seed) W.initialHeader nH nR)
      (J6R51Peak.publicationOverhead K K K K K (K+3*K*(K+(2*K+2))) (2*K) (2*K)) := by
    have heads : nH+pathLimit s C ≤ 2*K := by omega
    have refs : nR+pathLimit s C ≤ 2*K := by omega
    unfold livePublicationSetup
    refine Nat.le_trans (publication_overhead_mono_offset_counts key prec tw bw
      (liveHeaderWidth edges W.fixed W.addr (sourceBodyCap s C W.seed) W.initialHeader)
      hf heads refs) ?_
    unfold J6R51Peak.publicationOverhead scanByWidth
      headerReadFee locateFee contextCopyFee
    gcongr
  have shape : shapeFrameFee prec ≤ shapeFrameFee K := by unfold shapeFrameFee; omega
  have tail : twoTailFee ptr ≤ twoTailFee K := by unfold twoTailFee; omega
  have atlasFee := atlasGeometry_mono G.atlasLe
  have acquire : max (boot+uniformIndexGeometry s edges key prec page W)
      (demand+queries+uniformDescSidecar s edges key prec page W) ≤
      boot+demand+queries+(4+2*K*(3*K+11+maxAddonFee K K K K K))+
        sidecarGeometry K K K K K K K K K K K := by
    exact max_le (by omega) (by omega)
  unfold derivedPerScope acquisitionCeiling primitiveAndFootprintBudget structuralScope
  dsimp only
  refine Nat.le_trans (Nat.add_le_add acquire
    (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left entry words) atlasFee) shape)
      pub) tail) 4)) ?_
  exact le_of_eq (by ring)

#print axioms atlasGeometry_mono
#print axioms derivedScope_le_producers_add_structural
end J6R79Numeric
