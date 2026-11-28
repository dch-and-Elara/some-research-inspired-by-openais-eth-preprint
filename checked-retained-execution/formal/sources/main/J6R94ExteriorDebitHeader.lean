import J6R94ExteriorDebitHeaderShape
/-! The original paid R75 publication serializes the marked selected
wire file. Re-read that actual file from its installed head. This is
not re-installation, reissuing the external entry, or replaying the
initial physical selector over the whole graph. -/
namespace J6R94ExteriorDebit
open scoped Classical Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R19Retained
open J6R25PreparedSupply J6R32RootGeneratedRegistryInputs J6R34RootAtlas
open J6R31RootResidentTables J6R27OriginalGate J6Mesh J6R49SourceLayout
open J6R54ExteriorOwner J6R55BootBodies J6R41StructuredAllPaths
open J6R30GeneratedRootLayout J6R28GeneratedRootFrame J6R26StablePreparedRoot
open J6R37StructuredRoot J6R35RootOrigins J6R34ChildPath J6R36ChildFramedRoute
open J6R10Repack J6OrientedHost J6R24LegalLayout J6R26DescriptorTree
open J6R64Active J6R33StatefulArithmeticPage J6R30ProducedGateRegistry
open J6R14ZeroMode J6R12Blueprint J6ActiveRun J6R11Blueprint J6R32StatefulArithmetic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4300
set_option Elab.async false
noncomputable section

variable {V : Type} [Fintype V] {m n base native : ℕ} {P : Plant V m n}
variable {f : ℤ[X]}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co dep edgew tc tj key prec tw bw page : ℕ}
variable (X : StableExterior G ell q ro co dep edgew tc tj key prec tw bw)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Edge" => ((Ext).host.Edge)
local notation "Bank" => (PageBank f ell key prec tw bw page)

def readPublishedHalfRows (_source : StableExterior G ell q ro co dep edgew tc tj key prec tw bw)
    (B : Bank) : Meter (List (PortRow (rootHalfWidth m))) :=
  let head := borrowHeader B
  let cut := cutWord (liveReadPrefixWidth tc tj prec edgew) head.result
  let rows := decodeWireRows (rootHalfWidth m) (pageKeyWidth m+a m) cut.result.2
  ⟨rows.result,head.steps+cut.steps+rows.steps+4⟩

def publishedPortDebit (m tc tj prec edgew wires : ℕ) : ℕ :=
  cutWordFee (liveReadPrefixWidth tc tj prec edgew)+
    (decodeWireFee (rootHalfWidth m) (pageKeyWidth m+a m)+3)*wires+9

theorem real_paid_geometry_comes_from_this_published_header
    (B : Bank) (own : OwnsHeader X.header.result B) :
    readPublishedHalfRows X B=
      ⟨exteriorWireRecords X,publishedPortDebit m tc tj prec edgew (orderedExteriorEdges X).length⟩ := by
  obtain ⟨preWord,whole⟩ := geometry_of_installed_exterior_header X
  let suf := (exteriorWireRecords X).flatMap rowBytes
  have cut := cutWord_exact preWord suf
  have shape (row : PortRow (rootHalfWidth m)) (mem : row∈exteriorWireRecords X) :
      row.body.length=pageKeyWidth m+a m := by
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp mem
    let field := realHalfField X e
    change (field.page.bits++field.slot.bits).length=_
    rw [List.length_append,field.page.size,field.slot.size]
  have decode := actual_fixed_header_rows_roundtrip (exteriorWireRecords X) shape
  unfold readPublishedHalfRows
  dsimp only
  rw [borrow_exact_live_header _ _ own]
  dsimp only
  rw [whole,cut.1,cut.2]
  dsimp only
  change (⟨(decodeWireRows _ _ suf).result,3+cutWordFee (liveReadPrefixWidth tc tj prec edgew)+
    (decodeWireRows _ _ suf).steps+4⟩ : Meter (List (PortRow (rootHalfWidth m))))=_
  rw [show decodeWireRows (rootHalfWidth m) (pageKeyWidth m+a m) suf=_ from decode]
  simp only [exteriorWireRecords,List.length_map,publishedPortDebit]
  congr 1
  omega

#print axioms geometry_of_installed_exterior_header
#print axioms real_paid_geometry_comes_from_this_published_header
end
end J6R94ExteriorDebit
