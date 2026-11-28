import J6R118PhysicalGroupBudget
import J6R118CompiledAdmissionRoof
import J6R118ReadyRootClockImage

/-! Assembly over the one returned request image. For each real group
address, the preparer takes the actual held payload; the original
addresses index the result, not a second evaluation. -/
namespace J6R114PrescribedReceipts
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10
open J6Mesh J6OrientedHost J6OrientedHostEval J6R51Ingress
open J6R54PublicFamily J6R57PublicRequest J6R27PrescribedProbe J6R28GeneratedRootFrame
open J6R22RootReadout J6R75OuterTime J6R36SharedGateway J6R33OriginalJ6 J6R34OfficialGateway
open J6R25StableCensus J6R15ModeCost J6R11Repack J6R24MeteredRecursion
open J6R24LegalLayout J6R26StablePreparedRoot J6R31RootResidentTables J1PPrinted
open J6R14ZeroMode J6R19Retained J6R12Blueprint J6R33StatefulArithmeticPage
open J6R34RootAtlas J6R50SourceProducer J6R52FreshExterior J6R111KeptOwnerFlow

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 5200
set_option maxHeartbeats 15000000
set_option maxSynthPendingDepth 10

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew} {I : SharedInputs G ell q rr cc dd prec kp bw}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]


variable (image : RequestImage W I) (Q : PhysicalRetainedImagePlan image)

open J6R118ReadyRootClock J6R57ScopeFee J6R111KeptOwnerFlow
open J6R75OuterTime J6R34OfficialGateway J6R35GatewayPreparation

abbrev SourcePreparationBounds (prepCap : ℕ) : Prop :=
  ∀ (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64),
    let r := sourceRow (W:=W) image.compiled i j g
    let posted := admitTheEmittedRow image.compiled image.tables Q.pad Q.prior Q.sync Q.reserved i j g r rfl
    (Q.acquire i j g r rfl posted.result).steps ≤ prepCap

abbrev OriginalRootContractionBounds (rootCap : ℕ) : Prop :=
  ∀ (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64),
    let r := sourceRow (W:=W) image.compiled i j g
    let posted := admitTheEmittedRow image.compiled image.tables Q.pad Q.prior Q.sync Q.reserved i j g r rfl
    let a := posted.result
    let data := Q.acquire i j g r rfl a
    ∃ (ptr : ℕ) (tails : SavedDirectoryTails ptr)
      (C : ReadyContractionInputs a.payload data.result tails),
      readyRootContractionRoof a.payload data.result C ≤ rootCap

/-- A shared phase certificate built from the compiled admission,
measured source acquisition and original prescribed-root geometry.
There is no hypothesis stating a cap on the complete group execution. -/
def phaseCapsFromTheOriginalReadyRoots
    (prepCap rootCap : ℕ)
    (prep : SourcePreparationBounds image Q prepCap)
    (roots : OriginalRootContractionBounds image Q rootCap) :
    PhysicalGroupPhaseCaps image Q where
  admission := originalCompiledAdmissionRoof image Q
  preparation := prepCap
  contraction := rootCap
  paid := by
    intro i j g
    exact ⟨actual_retained_admission_uses_the_compiled_publication_roof image Q i j g,
      prep i j g, by
        obtain ⟨ptr,tails,certificate,fit⟩ := roots i j g
        exact ready_contraction_on_the_original_posted_row image Q i j g tails rootCap certificate fit⟩

#print axioms phaseCapsFromTheOriginalReadyRoots
end
end J6R114PrescribedReceipts

