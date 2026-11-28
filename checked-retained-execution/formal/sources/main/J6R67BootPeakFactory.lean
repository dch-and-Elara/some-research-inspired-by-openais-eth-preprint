import J6R67BootPeakCanonical

/-! The footprint is a proof-side projection of the real operation's
source values, not a second executed allocation trace. -/
namespace J6R67.BootPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R27OriginalGate J6R33StatefulArithmeticPage
open J6R37StructuredRoot J6R30GeneratedRootLayout J6R25PreparedSupply
open J6R48RawRoute J6R11Blueprint J1PPrinted J6R24MeteredRecursion J6R50SourceProducer
open J6R55BootBodies J6R54ExteriorOwner J6R53OldOwnerRoot J6R55TerminalOrigin
open J6R64.BootSeats J6R55SelectedPeak J6R52CacheWhole J6R54PeakInput
open J6R30ProducedGateRegistry J6R48DFS J6R49SourceLayout J6R66.BootPeak
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12500000
set_option maxRecDepth 5000
set_option Elab.async false


structure FirstPlan {f : ℤ[X]} {ell key prec tw bw page : ℕ}
    (seed : PageJob f ell key prec tw bw page) (Out : Type) where
  call : (B : PageBank f ell key prec tw bw page)→IsLive seed B→
    BootOp f ell key prec tw bw page Out
  observe : ∀ (B : PageBank f ell key prec tw bw page) (live : IsLive seed B),
    FirstFootprint (call B live)

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {P₀ : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P₀
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw own next : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
variable {b : ℕ}
variable (template : Meter (OccurrenceInput T ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
  (exteriorChild G ell X.centre X.sample X.group)).ticket w) key prec tw bw (pageKeyWidth m+pad)))
variable (L : BootLaneTape X gate pad)
variable (S : TerminalSeats X sel (ticketReady T ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
  (exteriorChild G ell X.centre X.sample X.group)).ticket w))
  ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
    (exteriorChild G ell X.centre X.sample X.group)).ticket w).centerAt b)
variable (agree : template.result.geometry.edges=orderedExteriorEdges X)
variable {rootName : SourceVertex P₀→Word own}
variable (root : RootRoster (P:=P₀) gate pad rootName)
variable {name : ((exteriorChild G ell X.centre X.sample X.group).host.Row⊕
    (exteriorChild G ell X.centre X.sample X.group).host.Col)→Word next}
variable (K : KeyInputs X gate pad root name) (nameInj : Function.Injective name)
variable (ownerTape : Meter (OwnerTape (bootOccurrence X gate pad w template L S).result name))
variable (backup : Addon next (dim ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
  (exteriorChild G ell X.centre X.sample X.group)).ticket w)) key prec (pageKeyWidth m+pad))
variable (rootInj : Function.Injective rootName)
variable {Out : Type}
variable (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)
variable (go : (state : StoredSite T ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
    (exteriorChild G ell X.centre X.sample X.group)).ticket w) key prec tw bw (pageKeyWidth m+pad))
    →ResidentBank state→SM (PageBank f ell key prec tw bw (pageKeyWidth m+pad)) Out)
variable (bad : Meter Out)

def canonicalFirstPlan : FirstPlan (X.seed pad) Out :=
  ⟨fun B live=>canonicalProgram X gate pad w template L S agree root K nameInj ownerTape backup B live rootInj retire go bad,
   fun B live=>canonicalWindows X gate pad w template L S agree root K nameInj ownerTape backup B live rootInj retire go bad⟩

#print axioms canonicalFirstPlan
end
end J6R67.BootPeak
