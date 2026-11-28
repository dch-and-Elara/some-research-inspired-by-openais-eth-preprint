import J6R67BootPeakCore
import J6R66BootPeakExterior

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

structure Window (Cut : Type) where
  view : Cut→ℕ
  roof : ℕ
  within : ∀ pt,view pt≤roof

structure InitPoint where
  origin : ℕ
  query : ℕ
  seat : ℕ
  raw : ℕ
  indexed : ℕ

structure FirstFootprint {f : ℤ[X]} {ell key prec tw bw page : ℕ} {Out : Type}
    (_A : BootOp f ell key prec tw bw page Out) where
  sharedStart : ℕ
  mount : Window (ℕ×ℕ)
  boot : Window InitPoint

def ownerHeaderBits {n : ℕ} (R : OwnerGroup n) : List Bool :=
  R.key.bits++R.group.bits

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
variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (live : IsLive (X.seed pad) B) (rootInj : Function.Injective rootName)
variable {Out : Type}
variable (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)
variable (go : (state : StoredSite T ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
    (exteriorChild G ell X.centre X.sample X.group)).ticket w) key prec tw bw (pageKeyWidth m+pad))
    →ResidentBank state→SM (PageBank f ell key prec tw bw (pageKeyWidth m+pad)) Out)
variable (bad : Meter Out)

def canonicalProgram : BootOp f ell key prec tw bw (pageKeyWidth m+pad) Out :=
  ⟨s,C,cfg,sel,exteriorChild G ell X.centre X.sample X.group,X.hf,T,w,
    canonicalBootAtLiveExterior X gate pad w template L S agree root K nameInj ownerTape backup B live rootInj,
    retire,go,bad⟩

def canonicalWindows :
    FirstFootprint (canonicalProgram X gate pad w template L S agree root K nameInj ownerTape backup B live rootInj retire go bad) :=
  let I := bootOccurrence X gate pad w template L S
  let E := mountFirstOwners X gate pad root B live K rootInj
  let A := canonicalProgram X gate pad w template L S agree root K nameInj ownerTape backup B live rootInj retire go bad
  let picked := (selectOwnerKeys X.address.group K.headers.result).result
  let old := exteriorOldPayloads X gate pad root
  let pages := exteriorReadPages X pad
  let stamp := (X.seed pad).immutable.payload.stamp
  ⟨(indexedOwnerTape root.raw).length+bitSize ownerHeaderBits K.headers.result+
      (selectedWordTape K.dest.result).length+(L.run.result.flatMap rootLanePairBits).length+
      (S.made.result.flatMap physicalSeatBits).length,
    ⟨fun pt=>ownerMountPrefixBits picked old stamp pages K.dest.result E.result.raw pt.1 pt.2,
      ownerMountLocalReserve picked old pages K.dest.result,
      fun pt=>(real_exterior_owner_mount_yields_named_snapshots_and_output X gate pad root B live K rootInj).2 pt.1 pt.2⟩,
    ⟨fun pt=>canonicalInitCut I E ownerTape A.initial.result pt.origin pt.query pt.seat pt.raw pt.indexed,
      canonicalInitReserve I E A.initial.result.birth.port,
      fun pt=>(actual_first_exterior_has_counted_canonical_buffers X gate pad w template L S agree root
        K nameInj ownerTape backup B live rootInj pt.origin pt.query pt.seat pt.raw pt.indexed).2.2⟩⟩

theorem canonical_program_runs_the_r55_real_initializer_once
    (ready : JobsReady B [(canonicalProgram X gate pad w template L S agree root K nameInj ownerTape backup
      B live rootInj retire go bad).job]) :
    let source := canonicalBootAtLiveExterior X gate pad w template L S agree root K nameInj ownerTape backup B live rootInj
    let A := canonicalProgram X gate pad w template L S agree root K nameInj ownerTape backup B live rootInj retire go bad
    A.initial.result.input=(bootOccurrence X gate pad w template L S).result ∧
    A.initial.result.origins=initialOrigin X gate pad ∧
    A.run B=bootBankDemand source retire go bad B ∧
    (A.run B).result.2=B :=
  ⟨rfl,rfl,rfl,congrArg (fun z=>z.result.2)
    (first_boot_uses_its_actual_child_bank_once _ B ready).1⟩

#print axioms canonicalProgram
#print axioms canonicalWindows
#print axioms canonical_program_runs_the_r55_real_initializer_once
end
end J6R67.BootPeak
