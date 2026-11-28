import J6R94HeldOwnerProviderLiteral

/-! Thin adapter from the actual held-word reader to the existing OwnerInputProvider. -/
namespace J6R110ScopeWordRates
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R58LeafScale J6R62Leaf J6R27OriginalGate J6R36ChildFramedRoute J6R54TerminalBoot
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R52Terminal J6R53TerminalGate J6R53OldOwner J6R49SourceLayout J6R66LeafTariff J6R65LeafRate
set_option autoImplicit false

set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9500000
set_option maxRecDepth 5500
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)

open J6R52CacheWhole J6R51ParentFrames J6R82LayoutDebit J6R82LeafTime
open J6R9Recursive J6R58LeafScale J6R16ModeCost J6R14LayoutCost J6R68ActiveInputs
open V8NativeMessage.N2DLabels J6R10Repack J6R94HeldOwnerProvider
local instance heldStopEdge : Fintype c.host.Edge := c.host.finiteEdge

/-- These are the actual paid tapes from a single scope, not a decoded
result surrogate. Matching is to this `Y`, including the owner roster,
chosen label order, full earlier Gate codes, and resident table. -/
structure LiveKeptStopTapes (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad)) : Type where
  resident : ResidentBank Y
  owners : CompleteRoster Y.site.oldKey (parentData Y (gateHistory T (bootGates X) p))
  names : Function.Injective Y.site.oldKey
  input : CallFormat (printedParams (f:=f) (ell:=ell) s) c
  ingress : Ingress input
  units : ℕ
  dim : ℕ
  copies : ℕ
  rank : ℕ
  extent : ℕ
  raw : KeptLayoutWords dim copies rank extent
  axisBytes : List Bool
  sameChart : ExistingRosterLabels Y (gateHistory T (bootGates X) p) owners input ingress units raw.rawView axisBytes

/-- The literal R94 operation, generalized only over the passed state.
It copies the actual roster keys and current grouped label fields and
mounts the actual already installed resident rows once. -/
def readKeptStopTapes (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))
    (L : LiveKeptStopTapes X p w Y) : Meter (OwnerTerminalInput X p w Y) :=
  let H := groupHeadersFromOwnedRaw Y (gateHistory T (bootGates X) p) L.owners L.input L.ingress L.units
    L.raw.rawView L.axisBytes L.sameChart
  let saved := mountResident Y L.resident
  ⟨⟨saved.result,H.result,L.owners,L.names⟩,saved.steps+H.steps+5⟩

theorem at_the_real_source_the_whole_meter_is_the_R94_reader
    (L : LiveKeptStopTapes X p w (sourceState M p w)) :
    readKeptStopTapes X p w (sourceState M p w) L=
      actualStoppedInputFromKeptTapes X M p w L.resident L.owners L.names L.input L.ingress L.units L.raw L.axisBytes L.sameChart := rfl

/-- The incoming handoff is explicit and billed. This interface cannot
produce tapes which the caller did not retain or independently acquire. -/
abbrev PaidKeptHandoff :=
  ∀ {x : Call (PhysicalHost f ell)} (path : Path sel (exteriorChild G ell X.centre X.sample X.group) x)
    (slot : (Plan sel).Slot x) (Y : StoredSite T (path.ticket slot) key prec tw bw (pageKeyWidth m+pad))
    (_ : ((Plan sel).child x slot).edges≤(printedParams (f:=f) (ell:=ell) s).cutoff),
    Meter (Option (LiveKeptStopTapes X path slot Y))

variable (handoff : PaidKeptHandoff (T:=T) (pad:=pad) X)

def keptTapeOwnerProvider : OwnerInputProvider (T:=T) (pad:=pad) X :=
  fun path slot Y stop=>
    let receive := handoff path slot Y stop
    match receive.result with
    | none=>⟨none,receive.steps+2⟩
    | some owned=>
      let result := readKeptStopTapes X path slot Y owned
      ⟨some result.result,receive.steps+result.steps+3⟩

variable (stop : ((Plan sel).child c w).edges≤(printedParams (f:=f) (ell:=ell) s).cutoff)
variable (L : LiveKeptStopTapes X p w (sourceState M p w)) (charged : ℕ)
variable (arrived : handoff p w (sourceState M p w) stop=Meter.mk (some L) charged)

include arrived in
theorem provider_at_the_exact_arrived_scope_pays_its_real_reader :
    let source := actualStoppedInputFromKeptTapes X M p w L.resident L.owners L.names L.input L.ingress L.units L.raw L.axisBytes L.sameChart
    keptTapeOwnerProvider X handoff p w (sourceState M p w) stop=Meter.mk (some source.result) (charged+source.steps+3) := by
  unfold keptTapeOwnerProvider
  dsimp only
  rw [arrived]
  rfl

/-- A proof about the whole incoming meter at each reached positive slot,
not a claim that the old `StoredSite` already carries these operands. -/
def ActualPositiveArrival : Prop :=
  ∀ {x : Call (PhysicalHost f ell)} (path : Path sel (exteriorChild G ell X.centre X.sample X.group) x)
    (slot : (Plan sel).Slot x) (finite : ((Plan sel).child x slot).edges≤(printedParams (f:=f) (ell:=ell) s).cutoff),
    0<((Plan sel).child x slot).edges→
      ∃ L : LiveKeptStopTapes X path slot (sourceState M path slot), ∃ spent : ℕ,
        handoff path slot (sourceState M path slot) finite=Meter.mk (some L) spent

theorem actual_paid_kept_arrivals_imply_the_existing_success_field (all : ActualPositiveArrival X M handoff) :
    HasMeasuredOwnerInputs X M (keptTapeOwnerProvider X handoff) := by
  intro x path slot finite positive
  obtain ⟨owned,spent,h⟩ := all path slot finite positive
  change (keptTapeOwnerProvider X handoff path slot (sourceState M path slot) finite).result.isSome
  rw [provider_at_the_exact_arrived_scope_pays_its_real_reader X M path slot handoff finite owned spent h]
  rfl

open J6R10Reachable
variable [DecidableEq (Envelope (N sel) (Childs sel) (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

include arrived in
theorem stopped_actual_machine_uses_the_literal_kept_reader_and_handoff_charge
    (basePos : 0<base)
    (ord : Fin (exteriorChild G ell X.centre X.sample X.group).edges≃(exteriorChild G ell X.centre X.sample X.group).host.Edge)
    (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad)) (positive : 0<((Plan sel).child c w).edges) :
    let source := actualStoppedInputFromKeptTapes X M p w L.resident L.owners L.names L.input L.ingress L.units L.raw L.axisBytes L.sameChart
    let debited := Meter.mk source.result (charged+source.steps+3)
    readLeaf (withPaidOwnerLeaves X M basePos ord (keptTapeOwnerProvider X handoff)) initial (.step p w) stop=
      readProvidedOnR65Bank X M p w debited initial := by
  let source := actualStoppedInputFromKeptTapes X M p w L.resident L.owners L.names L.input L.ingress L.units L.raw L.axisBytes L.sameChart
  exact r65_positive_is_the_selected_actual_provider X M p w basePos ord (keptTapeOwnerProvider X handoff)
    initial ⟨source.result,charged+source.steps+3⟩ stop positive
    (provider_at_the_exact_arrived_scope_pays_its_real_reader X M p w handoff stop L charged arrived)

#print axioms at_the_real_source_the_whole_meter_is_the_R94_reader
#print axioms provider_at_the_exact_arrived_scope_pays_its_real_reader
#print axioms actual_paid_kept_arrivals_imply_the_existing_success_field
#print axioms stopped_actual_machine_uses_the_literal_kept_reader_and_handoff_charge
end
end J6R110ScopeWordRates