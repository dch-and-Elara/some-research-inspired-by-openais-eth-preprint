import J6R79NumericEnvelope

/-! A single fixed-degree polynomial bound on all structural components
used by the numeric gate. This leaves only the paid producer coefficients
outside the polynomial. -/
namespace J6R79Numeric
open J6R16ModeCost J6R21Ancestor J6R51Peak J6R50SourceProducer J6R57ScopeFee
open J6R30ProducedGateRegistry J6R17ModeTape J6R27OriginalGate
open J6R33GeneratedChildSite J6R33PageIndexedBirth J6R32StatefulArithmetic J6R34RootAtlas
open J6R32ChildResidentTransfer J6R21Leaf J6R57LeafCap J6R57ActiveFee
open J6R68ActiveInputs J6R68ActiveInputs.Sweep J6R67UnifiedRate
open J6R63Active J6R64Active J6R62ActivePrep J6R14LayoutCost J6R52FreshExterior
open J6R19Retained J6R22RootReadout J6R12CollisionEdges J6R12CollisionGraphScore

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option Elab.async false
set_option maxHeartbeats 26000000
set_option maxRecDepth 4900

theorem structural_scope_is_polynomial (K : ℕ) :
    structuralScope K ≤ 2^26*(K+1)^8 := by
  simp only [structuralScope, sidecarGeometry, locateFee, maxAddonFee, entryGeometry,
    atlasWordGeometryCeiling, prepareSiteFee, requestsGeometryCeiling, headerSweepCeiling,
    framePayloadFee, probeCopyFee, slotStride, pipelineFee, onePageFee, spanFee,
    requestFee, dispatchStride, contextCopyFee, A1R11.uvWidth, denseRecordFee,
    modeBindingFee, maskSearchStride, buildModeInputCap, recordStride, shapeFrameFee,
    J6R51Peak.publicationOverhead, scanByWidth, headerReadFee, twoTailFee]
  ring_nf
  omega

theorem terminal_arithmetic_is_polynomial (K : ℕ) :
    terminalArithRoof K ≤ 2^48*(K+1)^12 := by
  unfold terminalArithRoof leafArithmeticScale dimEnvelope
  ring_nf
  omega

private theorem tapeBuild_succ (K : ℕ) :
    buildCap K K K 0 0 K K K ≤ buildCap K K K 0 0 K K (K+1) := by
  have shr : K-1≤K := Nat.sub_le _ _
  have base : K≤K+1 := Nat.le_succ K
  unfold buildCap spanFee keyCap pageCap tileCap weightCap layerCap
  simp only [show K+1-1=K by omega]
  gcongr

private def majorTape (K : ℕ) :=
  ctrlFee K K K K K+3+
    (headerPolynomial K+2*(3*K+1)+buildCap K K K 0 0 K K (K+1)+4)+nthRowAddonPx K

private theorem preparedCentre_le_major (K : ℕ) :
    preparedCentrePx K ≤ majorTape K := by
  unfold preparedCentrePx liveActiveTapeRoof tapePolynomial majorTape
  gcongr
  exact tapeBuild_succ K

private theorem active_le_major (K : ℕ) :
    structuralActive K ≤ activeNodeFixedPrice K (majorTape K) (mountedMaskPx K)
      (sweptSetupPx K (selectedLayoutRoof K+3)) := by
  have h := preparedCentre_le_major K
  unfold structuralActive sweptActivePx activeNodeFixedPrice fixedArithmeticPx fixedCentrePx
  gcongr

theorem structural_active_is_polynomial (K : ℕ) :
    structuralActive K ≤ 2^51*(K+1)^12 := by
  refine (active_le_major K).trans ?_
  simp only [activeNodeFixedPrice, fixedArithmeticPx, fixedCentrePx, fixedProbePx,
    J6R16ModeCost.setupCap, normalizerPx, normalPartPx, slopePx, jetMulPx, jetAddPx,
    jetSubPx, interpolationPx, factorPx, quotientPx, inversePx, oddPx]
  simp only [termPx, coefficientPx, boxPx, boxFee, scalarFee, wordFee, weightPx,
    weightsFoldPx, rowWeightPx, partPx, gatePx, oddPx, subPx, uvPx, addPx, mulPx, tapePx,
    stripPx, mountedMaskPx, majorTape, ctrlFee, precisionFee, taperFee,
    headerPolynomial, buildCap, headerTraffic, keyCap, pageCap, tileCap, weightCap,
    layerCap, spanFee, recordStride, nthRowAddonPx, stockAdmissionPx, heightWordRoof,
    rosterRowBound, commonLossWordRoof, J6R52FreshExterior.wordArithmeticRoof,
    signedDivisionFee, sweptSetupPx, sharedHeaderAndCopyRoof, selectedLayoutRoof,
    labelRoof, selectorStepRoof, selectorWriteRoof, selectionScoreWidth, writeBudget,
    scoreGraphBudget, copyBudget, J6R12CollisionBits.pairBudget, fixedPoly, tagStepCap,
    boxStepCap, scanStepCap, recordTraffic, menuPoly, roundCap, exportTapeCap, headerCap,
    seatStepCap, seatTraffic, show K+1-1=K by omega, Nat.zero_mul]
  ring_nf
  omega

theorem address_is_polynomial (K : ℕ) :
    physicalAddressUnit K ≤ 2^19*(K+1)^6 := by
  unfold physicalAddressUnit
  refine (Nat.add_le_add_right (Nat.div_le_self _ _) 1).trans ?_
  ring_nf
  omega

def sumPrimitiveCoefficients (A : ProducerCoefficients) :=
  A.positiveOwner+A.prep+A.reader+A.selectedLayout+A.boot+A.demand+A.queries+A.sourceWords

theorem sourceCoefficient_polynomial (K : ℕ) (A : ProducerCoefficients) :
    sourceCoefficient K A ≤ sumPrimitiveCoefficients A+2^53*(K+1)^12 := by
  have hs : structuralScope K ≤ 2^26*(K+1)^12 := by
    refine (structural_scope_is_polynomial K).trans ?_
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) (by decide))
  have hp : physicalAddressUnit K ≤ 2^19*(K+1)^12 := by
    refine (address_is_polynomial K).trans ?_
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) (by decide))
  have ha := structural_active_is_polynomial K
  have ht := terminal_arithmetic_is_polynomial K
  unfold sourceCoefficient sumPrimitiveCoefficients
  have h : 2^26*(K+1)^12+2^19*(K+1)^12+2^51*(K+1)^12+2^48*(K+1)^12≤
      2^53*(K+1)^12 := by
    rw [← Nat.add_mul,← Nat.add_mul,← Nat.add_mul]
    exact Nat.mul_le_mul_right _ (by decide)
  omega

#print axioms structural_scope_is_polynomial
#print axioms terminal_arithmetic_is_polynomial
#print axioms structural_active_is_polynomial
#print axioms address_is_polynomial
#print axioms sourceCoefficient_polynomial
end J6R79Numeric
