import J6R75OuterTimeCount

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 5000
set_option maxHeartbeats 26000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! The measured outer count starts from exactly one real R57 request
image. The continuation receives its returned compiled value and tables,
not a reconstructed type-index or separately installed probe bank. -/
namespace J6R75OuterTime
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath J6R35GatewayPreparation
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R9Recursive J6R50SourceProducer J6R51Online J6R52FreshExterior
open J6R57PublicRequest J6R54PublicFamily J6R22Active
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables J6R28GeneratedRootFrame
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R55CachedLedger J6R56PrintedExponent J6R49Cost J6R16ModeCost J6R10Reachable
open J6R64Active J6R66Active J6R66.BootPeak
open J6R67UnifiedRate J6R68ActiveInputs J6R68ActiveInputs.Sweep
open J6R36SharedGateway J6R19Retained AOracleMachineTimeTape A1R10 A1R12
open J6R34OfficialGateway J6R68AbsolutePrescribed
open J6R33OriginalJ6 J6R25StableCensus J6R22RootReadout J6R11Repack J6OrientedHostEval
open J6R63Active J6R62ActivePrep

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

variable (W : Widths m native tc tj tw edgew)
variable (I : SharedInputs G ell q rr cc dd prec kp bw)
variable (pad : ℕ)
variable (B : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
variable {s C rate cw : ℕ} {cfg : RootBounds s C f}
variable (driver : (image : RequestImage W I) →
  Meter (RawGroupPlans image.compiled image.tables pad B cfg rate cw))
variable (sync : B.synced)
variable (reserve : ∀ image : RequestImage W I,
  ∀ x∈B.headers,x.id.bits.take kp≠image.compiled.mark.bits)

/-- Consume the actual selected image as a variable, not a recomputation of
the compiler for a dependent address or receiving-frame type. -/
def runSelectedImage (image : RequestImage W I)
    (U : RawGroupPlans image.compiled image.tables pad B cfg rate cw) :
    Meter (A1R10.Word (printedAnswerWidth m base)) :=
  runRawOuterCount image.compiled image.tables pad B U sync (reserve image)
    image.compiled.frame image.compiled.positive

theorem selected_image_has_exact_count (image : RequestImage W I)
    (U : RawGroupPlans image.compiled image.tables pad B cfg rate cw)
    (positiveBase : 0<base) (allZero : coreA P (fun _=>false)=true)
    (answer : ℕ) (count : Nat.card {x : Fin m→Bool // coreA P x=true ∧ coreB P x=true}=1+answer) :
    bitsValue (runSelectedImage W I pad B sync reserve image U).result.val=answer :=
  (exact_guarded_count_from_the_actual_outer_runs image.compiled image.tables pad B U
    sync (reserve image) image.compiled.frame image.compiled.positive positiveBase allZero answer count).1

def compileThenRawOuterCount : Meter (A1R10.Word (printedAnswerWidth m base)) :=
  let J := buildRequestImage W I
  let configured := driver J.result
  let Q := runSelectedImage W I pad B sync reserve J.result configured.result
  ⟨Q.result,J.steps+configured.steps+Q.steps+5⟩

theorem one_actual_compilation_and_extraction_fee :
    let J := buildRequestImage W I
    let configured := driver J.result
    let Q := runSelectedImage W I pad B sync reserve J.result configured.result
    compileThenRawOuterCount W I pad B driver sync reserve=
      ⟨Q.result,J.steps+configured.steps+Q.steps+5⟩ := rfl

theorem startup_bills_actual_compiler_shared_cache_and_catalogue :
    let J := buildRequestImage W I
    let c := J.result.compiled
    let configured := driver J.result
    let Q := runSelectedImage W I pad B sync reserve J.result configured.result
    (compileThenRawOuterCount W I pad B driver sync reserve).steps=
      (prepareShared I).steps+(buildCommonRoot c).steps+(emitCatalogue W c.mark).steps+
        configured.steps+Q.steps+13 := by
  let J := buildRequestImage W I
  let c := J.result.compiled
  let configured := driver J.result
  let Q := runSelectedImage W I pad B sync reserve J.result configured.result
  have phase : J.steps=(prepareShared I).steps+(buildCommonRoot c).steps+(emitCatalogue W c.mark).steps+8 :=
    (actual_request_image_retains_paid_compilation W I).2.2.2.2.trans
      (compiled_request_cache_exact_fee W I)
  change J.steps+configured.steps+Q.steps+5=
    (prepareShared I).steps+(buildCommonRoot c).steps+(emitCatalogue W c.mark).steps+
      configured.steps+Q.steps+13
  rw [phase]
  omega

theorem compiled_then_count_has_exact_guarded_value
    (positiveBase : 0<base) (allZero : coreA P (fun _=>false)=true)
    (answer : ℕ) (count : Nat.card {x : Fin m→Bool // coreA P x=true ∧ coreB P x=true}=1+answer) :
    bitsValue (compileThenRawOuterCount W I pad B driver sync reserve).result.val=answer :=
  selected_image_has_exact_count W I pad B sync reserve
    (buildRequestImage W I).result (driver (buildRequestImage W I).result).result positiveBase allZero answer count

#print axioms runSelectedImage
#print axioms selected_image_has_exact_count
#print axioms compileThenRawOuterCount
#print axioms one_actual_compilation_and_extraction_fee
#print axioms startup_bills_actual_compiler_shared_cache_and_catalogue
#print axioms compiled_then_count_has_exact_guarded_value
end
end J6R75OuterTime

