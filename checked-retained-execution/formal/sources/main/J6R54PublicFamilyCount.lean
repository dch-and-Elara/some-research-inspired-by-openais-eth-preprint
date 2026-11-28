import J6R54PublicFamilyCountSite

/-! Execute the actual ordered readout with one preflight: compute the
shared accepted source/field/register bundle and the root probe bank
once, then use the measured site loop for the unchanged final word. -/
namespace J6R54PublicFamily
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime A1R10 A1R12
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R28GeneratedRootFrame
open J6R34RootAtlas J6R53PublicMount J6R53WordIngress
open J6R14ZeroMode J6R33OriginalJ6 J6R32RootGeneratedRegistryInputs
open J6R36SharedGateway J6R22Active J6R52PublicSlot J6R22RootReadout
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18000000
set_option maxRecDepth 3400
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew rate pad : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (W : Widths m native tc tj tw edgew) (C : Compiled G ell q rr cc dd prec kp bw)
variable (R : PublicJobs W C rate pad)
variable (A : SuppliedProbeBits (rootPreset G ell) f.natDegree)

def finishSharedSlots (sites : J6Recovery.Addr m→Meter (Block C.frame ell)) :
    Meter (A1R10.Word (printedAnswerWidth m base)) :=
  let fits := printed_readout_fits m n base (constantRootWord m)
  countFromMeasuredSlots C.frame fits.1 fits.2.1 m (printedHalf m) n (printedRankWidth m)
    (J6R14LayoutCost.wordCell (J6RecursiveOrientation.diagonal (constantRootWord m))) sites

def allLocationFee : ℕ := ∑ i : J6Recovery.Addr m,familySiteFee W i

theorem actual_count_fold_amount :
    Delta (finishSharedSlots C (measuredFamilySite W C R A))
      (finishSharedSlots C (mountedMeasuredSites G C.hf C.frame C.positive (plainFamily W C R) A))
      (allLocationFee W) := by
  let fits := printed_readout_fits m n base (constantRootWord m)
  exact gather_delta C.frame fits.1 fits.2.1 m (printedHalf m) n (printedRankWidth m)
    (J6R14LayoutCost.wordCell (J6RecursiveOrientation.diagonal (constantRootWord m))) _ _ _
    (paid_site_is_same_word_and_adds_every_address W C R A)

variable (I : SharedInputs G ell q rr cc dd prec kp bw)
variable (jobs : PublicJobs W (prepareShared I).result rate pad)

def runPreparedCount : Meter (A1R10.Word (printedAnswerWidth m base)) :=
  let S := prepareShared I
  let bank := buildRootBitBank G ell
  let out := finishSharedSlots S.result (measuredFamilySite W S.result jobs bank.result)
  ⟨out.result,out.steps+S.steps+bank.steps+4⟩

theorem prepared_count_same_word_and_exact_full_bill :
    let S := prepareShared I
    let orig := runMountedCount G S.result.hf S.result.frame S.result.positive (plainFamily W S.result jobs)
    (runPreparedCount W I jobs).result=orig.result ∧
      (runPreparedCount W I jobs).steps=orig.steps+S.steps+allLocationFee W := by
  let S := prepareShared I
  let bank := buildRootBitBank G ell
  let paid := finishSharedSlots S.result (measuredFamilySite W S.result jobs bank.result)
  let old := finishSharedSlots S.result
    (mountedMeasuredSites G S.result.hf S.result.frame S.result.positive (plainFamily W S.result jobs) bank.result)
  have H := actual_count_fold_amount W S.result jobs bank.result
  refine ⟨H.value,?_⟩
  change paid.steps+S.steps+bank.steps+4=old.steps+bank.steps+4+S.steps+allLocationFee W
  have fee := H.fee
  change paid.steps=old.steps+allLocationFee W at fee
  rw [fee]
  omega

#print axioms actual_count_fold_amount
#print axioms runPreparedCount
#print axioms prepared_count_same_word_and_exact_full_bill
end
end J6R54PublicFamily

