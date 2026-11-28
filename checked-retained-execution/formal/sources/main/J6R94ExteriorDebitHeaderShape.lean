import J6R94ExteriorDebitGeometry
import J6R94ExteriorDebitHeaderBits
import J6R64ActiveExterior

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
set_option maxHeartbeats 2800000
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

def exteriorWireRecords : List (PortRow (rootHalfWidth m)) :=
  (orderedExteriorEdges X).map (fun e=>halfPortSpec m (side e.val) (realHalfField X e))

def liveReadPrefixWidth (tc tj prec edgew : ℕ) : ℕ :=
  externalAddrWidth tc tj 0+prec+1+edgew

/-- The actual bit writer. Only the widths of the preceding words are
needed for this reader; no second source computation of depth or edge
count, and no occurrence proof-binder search. -/
theorem make_occurrence_has_wire_tail
    {tc tj key w b dep prec : ℕ} (A : OccurrenceAddress tc tj)
    (receive : Word prec) (old : Word dep) (raw : List (PortRow w)) (issue : Meter (Word key)) :
    ∃ pre : A1R10.Word (externalAddrWidth tc tj 0+prec+dep+b),
      (makeOccurrence (b:=b) A receive old raw issue).result.bytes=
        pre.val++((selectPorts A.group raw).result.flatMap rowBytes) := by
  let J : J6R26DescriptorTree.Job w b dep prec := externalHeaderJob A.marked receive old raw
  let d := (increment old).result
  let N := (childPortsWithCount (b:=b) A.group raw).result.2
  let pre := A.marked.bytes++receive.bits++d.bits++N.bits
  have hp : pre.length=externalAddrWidth tc tj 0+prec+dep+b := by
    simp only [pre,List.length_append,external_address_width,receive.size,d.size,N.size]
  refine ⟨⟨pre,hp⟩,?_⟩
  change (J.make issue).result.bytes=pre++_
  have h := (child_stage_exact (b:=b) issue A.group receive old raw).2.1
  calc
    (J.make issue).result.bytes = A.marked.bytes++
        (childStage (b:=b) issue A.group receive old raw).result.bytes :=
      J.make_bytes issue
    _ = A.marked.bytes++childHeaderBytes receive d N
        ((selectPorts A.group raw).result.flatMap rowBytes) :=
      congrArg (A.marked.bytes++·) h
    _ = _ := by simp only [childHeaderBytes,pre,List.append_assoc]

theorem geometry_of_installed_exterior_header :
    ∃ pre : A1R10.Word (liveReadPrefixWidth tc tj prec edgew),
      X.header.result.bytes=pre.val++(exteriorWireRecords X).flatMap rowBytes := by
  let raw := (makeHalfTape m [] X.source.raw).result
  obtain ⟨pre,hp⟩ := make_occurrence_has_wire_tail
    (b:=edgew) X.address X.birth (word (q:=1) 0) raw X.issue
  have hr : (selectPorts X.address.group raw).result=exteriorWireRecords X :=
    measured_selection_uses_the_original_exterior_order X
  refine ⟨pre,?_⟩
  change (makeOccurrence (b:=edgew) X.address X.birth (word (q:=1) 0) raw X.issue).result.bytes=_
  exact hp.trans (congrArg (fun xs : List (PortRow (rootHalfWidth m))=>pre.val++xs.flatMap rowBytes) hr)

#print axioms make_occurrence_has_wire_tail
#print axioms geometry_of_installed_exterior_header
end
end J6R94ExteriorDebit
