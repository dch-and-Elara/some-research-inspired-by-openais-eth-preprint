import J6R102FinalPhaseProfile

/-! Expose the exact three R68 clock fields before recursion. Only the
actual stopped interpreter, actual selected setup, actual raw sweep,
and actual scoped source providers are used. This exposes the same
phase capsule that the frozen R68 top theorem constructs internally. -/
namespace J6R108FinalDriver
open J6R102FinalPhase
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R9Recursive J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R62Leaf J6R54TerminalBoot J6R52Terminal J6R22Active
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R55CachedLedger J6R56PrintedExponent J6R49Cost J6R16ModeCost J6R10Reachable
open J6R64Active J6R66Active J6R65LeafRate J6R30ProducedGateRegistry
open J6R67UnifiedRate J6R68AbsolutePrescribed J6R68ActiveInputs J6R68ActiveInputs.Sweep
open J6R63Active J6R62ActivePrep J6R57ActiveFee J6R57ScopeFee J6R51Peak J6R50Peak
open J6R79Numeric

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4450
set_option maxSynthPendingDepth 12

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {plant : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) plant
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate rank : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "Pg" => (pageKeyWidth m+pad)
local notation "Bank" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))
local notation "Job" => (PageJob f ell key prec tw bw (pageKeyWidth m+pad))
local instance exteriorProfileDecision :
    DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
      (exteriorChild G ell X.centre X.sample X.group)) :=
  J6R24MeteredRecursion.sourceDecision sel Ext
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (basePos : 0<base)
variable (ord : Fin (exteriorChild G ell X.centre X.sample X.group).edges ≃
  (exteriorChild G ell X.centre X.sample X.group).host.Edge)
variable (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
local notation "R" => (withPaidOwnerLeaves X M basePos ord ownerInputs)


variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (own : OwnsHeader X.header.result B)
variable {K producerPower leafPower : ℕ} {coefficients : ProducerCoefficients}
variable (H : MeasuredProfile (T:=T) (rank:=rank) X M basePos ord ownerInputs B own K producerPower leafPower coefficients)
variable (exterior : (actual : PageBank f ell key prec tw bw (pageKeyWidth m+pad)) →
    OwnsHeader X.header.result actual →
    (a : (printedParams (f:=f) (ell:=ell) s).cutoff<(exteriorChild G ell X.centre X.sample X.group).edges) →
    ChosenSetup sel (readyAtPath T (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
      (exteriorChild G ell X.centre X.sample X.group)) a) rank)

variable (rootGeometry :
  ∀ a : (printedParams (f:=f) (ell:=ell) s).cutoff<(exteriorChild G ell X.centre X.sample X.group).edges,
    letI := (exteriorChild G ell X.centre X.sample X.group).host.finiteEdge
    letI := (exteriorChild G ell X.centre X.sample X.group).host.finiteRow
    letI := (exteriorChild G ell X.centre X.sample X.group).host.finiteCol
    LayoutScales (exterior B own a).input rank K)
variable (rootDebit :
  ∀ a : (printedParams (f:=f) (ell:=ell) s).cutoff<(exteriorChild G ell X.centre X.sample X.group).edges,
    letI := (exteriorChild G ell X.centre X.sample X.group).host.finiteEdge
    (exterior B own a).bytes.paid.steps ≤ H.ingress)

/-- Install an actual measured exterior layout callback at the
selected runner. Only the root ingress/shape proofs are replaced;
every descendant continues to use exactly the existing chosen source. -/
def withMeasuredExteriorOnly :
    MeasuredProfile (T:=T) (rank:=rank) X M basePos ord ownerInputs B own K producerPower leafPower coefficients := by
  let selected := { H.current with exterior := exterior }
  refine {H with current := selected, layoutShape := ?_, rawDebit := ?_}
  · intro z a
    rcases z with ⟨c,p⟩
    cases p with
    | root => exact rootGeometry a
    | step p w => exact H.layoutShape ⟨_,Path.step p w⟩ a
  · intro z a
    rcases z with ⟨c,p⟩
    cases p with
    | root => exact rootDebit a
    | step p w => exact H.rawDebit ⟨_,Path.step p w⟩ a

theorem measured_exterior_is_the_exact_supplied_producer
    (a : (SP).cutoff<(Ext).edges) :
    ((withMeasuredExteriorOnly X M basePos ord ownerInputs B own H exterior rootGeometry rootDebit).current.exterior B own a) =
      exterior B own a := rfl

theorem descendants_keep_the_original_measured_layout_callback
    {c : Call (PhysicalHost f ell)} (p : Path sel (Ext) c) (w : (Plan sel).Slot c)
    (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))
    (a : (SP).cutoff<((Plan sel).child c w).edges) :
    (withMeasuredExteriorOnly X M basePos ord ownerInputs B own H exterior rootGeometry rootDebit).current.after p w Y a =
      H.current.after p w Y a := rfl

#print axioms withMeasuredExteriorOnly
#print axioms measured_exterior_is_the_exact_supplied_producer
#print axioms descendants_keep_the_original_measured_layout_callback
end
end J6R108FinalDriver

