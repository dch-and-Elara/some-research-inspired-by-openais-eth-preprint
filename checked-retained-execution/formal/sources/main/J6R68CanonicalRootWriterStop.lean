import J6R68CanonicalRootWriterWhole

/-! Attach the actual raw exterior writer to the original reached
stopping call. Cutoff and frame are those of the true Prepared plan;
the result is exactly the original Blueprint branch. -/
namespace J6R68CanonicalRootWriter
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R27OriginalGate J6R33StatefulArithmeticPage
open J6R37StructuredRoot J6R30GeneratedRootLayout J6R25PreparedSupply
open J6R55BootBodies J6R48RawRoute J6R50SourceProducer J6R54ExteriorOwner
open J6R53OldOwner J6R62Leaf J6R50Leaf J6R52Terminal J6R53TerminalGate
open J6R67CanonicalStop J6R11Blueprint J6R49Leaf J6R51Leaf J6R34ChildPath J6R21Leaf
open J6R54TerminalBoot J6R24MeteredRecursion J6R48Leaf J6R53OldOwnerRoot
open J1PPrinted J6R10Reachable J6R9Recursive

set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8500000
set_option maxRecDepth 4600
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw own s C : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "U" => (Vertex (exteriorChild G ell X.centre X.sample X.group))
local notation "N0" => (exteriorChild G ell X.centre X.sample X.group).edges
local notation "Pg" => (pageKeyWidth m+pad)
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable (T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf)
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]

theorem original_exterior_stop_from_paid_raw_writer {rootOwn : ℕ}
    {rootName : SourceVertex P→Word rootOwn}
    (basePos : 0<base) (name : U→Word own)
    (inj : Function.Injective name) (srcInj : Function.Injective rootName)
    (gateWidth : gate.created.val=base)
    (b : ℕ) (hb : 0<b) (fit : N0≤2^b)
    (incident : PaidIncidentNames X name) (lanes : BootLaneTape X gate pad)
    (source : RootRoster (P:=P) gate pad rootName) (names : KeyInputs X gate pad source name)
    (B : PageBank f ell key prec tw bw Pg) (live : IsLive (X.seed pad) B)
    (stop : N0≤(printedParams (f:=f) (ell:=ell) s).cutoff) :
    let path : Path sel Ext Ext := .root
    let F := T.frame path.reached
    let owners := mountFirstOwners X gate pad source B live names srcInj
    let setup := prepareRootBook X gate pad name incident lanes
    let out := runRootWriter b X.hf F X.positive B setup (paidOwnerRosterRaw X gate pad name owners)
    ∃ word,out.result=some word ∧ F.decode word=(sourceBlueprint sel Ext X.hf).program.run Ext := by
  let path : Path sel Ext Ext := .root
  have edgeCount : (Ext).host.edgeCount=N0 := planEdges (T:=T) path
  obtain ⟨word,ok,law⟩ := real_mounted_owner_roster_drives_the_root_stop X gate pad basePos name inj
    srcInj gateWidth edgeCount b hb fit incident lanes source names (T.frame path.reached) B live
  exact ⟨word,ok,law.trans (true_source_stops_on_same_host T path stop)⟩

#print axioms original_exterior_stop_from_paid_raw_writer
end
end J6R68CanonicalRootWriter

