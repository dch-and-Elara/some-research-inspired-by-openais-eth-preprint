import J6R68CanonicalRootWriterWhole

/-! The leaf provider receives the actual bank dynamically. It
runs the raw R54 owner read on that bank without having to take a
proof argument at runtime. A live bank certifies the raw byte and
fee equality to the checked mounted roster. -/
namespace J6R68CanonicalRootWriter
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
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

set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4400
set_option Elab.async false

section Raw
variable {f : ℤ[X]} {ell p w own g key prec tw bw page : ℕ}

def runRootWithOwnerOption (b : ℕ) (hf : f.Monic) (F : Frame f p) (pos : 0<ell)
    (B : PageBank f ell key prec tw bw page)
    (setup : Meter (Option (List (FramedEdge w own key prec page) × List (Word w))))
    (owners : Meter (Option (RawRoster own g key prec page))) : Meter (Option (Block F ell)) :=
  match owners.result with
  | none => ⟨none,owners.steps+3⟩
  | some raw =>
    let out := runRootWriter b hf F pos B setup ⟨raw,owners.steps⟩
    ⟨out.result,out.steps+2⟩

theorem run_root_with_owner_hit_exact
    (b : ℕ) (hf : f.Monic) (F : Frame f p) (pos : 0<ell)
    (B : PageBank f ell key prec tw bw page)
    (setup : Meter (Option (List (FramedEdge w own key prec page) × List (Word w))))
    (owners : Meter (Option (RawRoster own g key prec page))) (r : RawRoster own g key prec page)
    (hit : owners.result=some r) :
    let M := runRootWriter b hf F pos B setup ⟨r,owners.steps⟩
    runRootWithOwnerOption b hf F pos B setup owners=⟨M.result,M.steps+2⟩ := by
  unfold runRootWithOwnerOption
  rw [hit]
end Raw

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw own rootOwn : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "U" => (Vertex (exteriorChild G ell X.centre X.sample X.group))
local notation "Pg" => (pageKeyWidth m+pad)
local notation "Bank" => (PageBank f ell key prec tw bw Pg)
local notation "Raw" => (RawRoster own (SuffixWordWidth m) key prec Pg)
variable {rootName : SourceVertex P→Word rootOwn}

def readActualOuterOwnerBytes (name : U→Word own)
    (source : RootRoster (P:=P) gate pad rootName)
    (names : KeyInputs X gate pad source name) (B : Bank) : Meter (Option Raw) :=
  let D := chosenFirstRaw X gate pad source B name names
  ⟨D.result,names.headers.steps+D.steps⟩

theorem live_owner_read_is_the_measured_mounted_roster (name : U→Word own)
    (source : RootRoster (P:=P) gate pad rootName) (names : KeyInputs X gate pad source name)
    (B : Bank) (live : IsLive (X.seed pad) B) (injective : Function.Injective rootName) :
    let M := mountFirstOwners X gate pad source B live names injective
    readActualOuterOwnerBytes X gate pad name source names B=⟨some M.result.raw,M.steps⟩ := by
  let M := mountFirstOwners X gate pad source B live names injective
  have eq : M.result.raw=outputRosterRows X gate pad source name := M.result.exactRows
  unfold readActualOuterOwnerBytes
  dsimp only
  rw [local_exterior_raw_rows X gate pad source B live name names injective]
  change (⟨some (outputRosterRows X gate pad source name),_⟩ : Meter (Option Raw))=
    ⟨some M.result.raw,M.steps⟩
  rw [eq]
  rfl

#print axioms run_root_with_owner_hit_exact
#print axioms readActualOuterOwnerBytes
#print axioms live_owner_read_is_the_measured_mounted_roster
end
end J6R68CanonicalRootWriter

