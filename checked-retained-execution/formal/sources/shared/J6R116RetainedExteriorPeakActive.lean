import J6R116RetainedExteriorPeakFirst
import J6R115RetainedPeakPathBound

/-! The first captured entry is the argument passed by the literal
exterior callback. This observer neither reissues the exterior
row nor prepares a different first child. -/
namespace J6R116RetainedExteriorPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6OrientedHost J6R34RootAtlas
open J6Mesh J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R28GeneratedRootFrame J6R34ChildPath J6R37StructuredRoot J6R41StructuredAllPaths
open J6R54TerminalBoot J6R53OldOwner J6R53OldOwnerRoot J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R52CacheSource
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS J6R10Repack J6ActiveSchedule
open J6R50SourceProducer J6R51Online J6R51ParentFrames J6R52CacheWhole J6R64Active J6R66Active
open J6R59Public J6R94HeldOwnerProvider J6R54PeakInput J6R48RawRoute J6R49SourceLayout
open J6R58RequestSource J6R52Dispatch J6R53Dispatch J6R27OriginalGate J6R36ChildFramedRoute
open J6R62ActivePrep J6R82LayoutDebit V8NativeMessage.N2DLabels J6R68ActiveInputs J6R68ActiveInputs.Sweep
open J6R9Recursive J6R22Active J6R49DFS J6R10Reachable
open J6R111KeptOwnerFlow J6R114RetainedPeak J6R115RetainedPeakPath
open J6R52Peak J6R53PeakAddon J6R55SelectedPeak J6R75RawPeak J6R66.BootPeak J6R16ModeCost

set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15500000
set_option maxRecDepth 4900
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate rank : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (boot : FirstSource X M) (E : ExteriorLabels X M boot rank)
variable (on : (printedParams (f:=f) (ell:=ell) s).cutoff<(exteriorChild G ell X.centre X.sample X.group).edges)
variable (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))

local notation "RootCall" => (exteriorChild G ell X.centre X.sample X.group)
local notation "RootPath" => (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
  (exteriorChild G ell X.centre X.sample X.group))
local notation "Started" => (boot.make w)
local notation "FirstSite" => (boot.make w).result.site

local instance exteriorActivePeakEdges : Fintype (RootCall).host.Edge := (RootCall).host.finiteEdge

variable (head : OwnsHeader X.header.result initial)
variable (D : KeptDrivers X M rank)
variable (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)

private abbrev payloadType {A : Type*} (_ : Meter A) := A

/-- Borrow the layout actually emitted outside the native sweep. The
certificate here is erased; the callback does not run its producer. -/
def firstCallbackFromActualPackedResult
    (packed : payloadType (exteriorPackedAtFirstScope X M boot E on))
    (exactPacked : packed=(exteriorPackedAtFirstScope X M boot E on).result)
    (bad : Meter (Block (T.frame (Path.step RootPath w).reached) ell)) :=
  let issued := boot.make w
  let labels := useAlreadyEmittedLabels X RootPath w issued.result.site issued.result.owners
    (E.setup on) packed exactPacked issued.result.injective (E.order on w) (E.exactLabels on)
  enterPaidFirst X initial retire w issued
    (fun entry=>runRetained X M D retire
      ⟨RootCall,RootPath,w,issued.result.site,congrArg Meter.result (boot.exact w),entry⟩)
    labels bad

theorem the_borrowed_first_callback_is_the_observed_native_stage
    (packed : payloadType (exteriorPackedAtFirstScope X M boot E on))
    (exactPacked : packed=(exteriorPackedAtFirstScope X M boot E on).result)
    (bad : Meter (Block (T.frame (Path.step RootPath w).reached) ell)) :
    firstCallbackFromActualPackedResult X M initial boot E on w D retire packed exactPacked bad =
      actualExteriorFirstCallback X M initial boot E on w D retire bad := by
  subst packed
  rfl

/-- The actual exterior active branch. Its one emitted packed result
feeds both the real preparation and all first callbacks; their local
setup is the same first scope certified above. -/
theorem original_exterior_runs_the_first_scopes_with_one_shared_packed_output :
    let sp := printedParams (f:=f) (ell:=ell) s
    let d := readyAtPath T RootPath on
    let packed := exteriorPackedAtFirstScope X M boot E on
    let taper := actual_path_taper T RootPath on
    let A := prepare (bank:=T.bank) M.modeWidth (D.fit RootPath on) taper.1 taper.2 X.hf
      D.masks.table (D.masks.covers RootPath on) (readExterior X initial head) ⟨packed.result.receipt,packed.steps⟩
    let out := A.result.eval M.modeWidth (reachable_positive T (RootPath).reached) T.vPositive X.hf
      (fun t z β g=>
        let u := addressed (sel:=sel) d t z β g
        project (firstCallbackFromActualPackedResult X M initial boot E on u D retire packed.result rfl
          (zeroM (T.bank (registerPrecision sp RootCall t) (register_positive d t)).hp)))
    runRetainedExterior X M initial head boot D E retire=⟨(out.result,initial),A.steps+out.steps⟩ := by
  simp only [runRetainedExterior,dif_neg (Nat.not_le_of_gt on),exteriorPackedAtFirstScope,
    firstCallbackFromActualPackedResult]

/-- The selected exterior pause after one real layout emission. The
incoming bank is already mounted and the small site words are
retained once in the ambient of that exact execution. -/
def exteriorBeforeFirstBits (ambient : ℕ) : ℕ :=
  chartAndAmbient X M D (ambient+descriptorBits X) + mountedSelectedBits initial +
    packedKeptBits (exteriorPackedAtFirstScope X M boot E on).result

theorem first_scope_adds_one_install_and_reuses_the_extent_packed_words (ambient : ℕ) :
    let x := firstInvocation X M initial boot E on w
    invocationEntryBits X M x (chartAndAmbient X M D (ambient+descriptorBits X))=
      exteriorBeforeFirstBits X M initial boot E on D ambient+
      mountedInsertionBits (FirstSite).birth.job+(residentAddonPayload x.entry.resident).length+
      (indexedOwnerTape x.entry.owners.raw).length+x.entry.labelled.axis.length := by
  let x := firstInvocation X M initial boot E on w
  let shared := chartAndAmbient X M D (ambient+descriptorBits X)
  have bank : mountedSelectedBits x.entry.bank=mountedSelectedBits initial+mountedInsertionBits (FirstSite).birth.job :=
    publication_adds_exact_selected_record initial (FirstSite).birth.job
  have layout := (first_live_contains_the_original_words_and_published_stack X M initial boot E on w).2.2.2
  change shared+mountedSelectedBits x.entry.bank+(residentAddonPayload x.entry.resident).length+
      (indexedOwnerTape x.entry.owners.raw).length+packedKeptBits x.entry.labelled.raw+x.entry.labelled.axis.length=_
  rw [bank,layout]
  unfold exteriorBeforeFirstBits
  dsimp only [x,shared]
  ac_rfl

#print axioms firstCallbackFromActualPackedResult
#print axioms the_borrowed_first_callback_is_the_observed_native_stage
#print axioms original_exterior_runs_the_first_scopes_with_one_shared_packed_output
#print axioms first_scope_adds_one_install_and_reuses_the_extent_packed_words
end
end J6R116RetainedExteriorPeak

