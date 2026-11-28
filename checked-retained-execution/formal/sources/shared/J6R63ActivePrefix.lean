import J6R30ProducedGateRegistryHeader
import J6R50SourceProducerOnline

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 11500000
set_option maxRecDepth 2500
set_option Elab.async false

/-! Read the *current* child's inherited precision and edge-count
words from the physically emitted predecessor job.  The metered
reader sees only the resident byte list, not a closure that reruns
job creation or any future outgoing address. -/
namespace J6R63Active
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R30ProducedGateRegistry J6R26DescriptorTree J6R24MeteredRecursion
open J6R33StatefulArithmeticPage J6R50SourceProducer J6R32StatefulArithmetic
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted

def readCallWords (prec edges dep offset : ℕ) (bytes : List Bool) :
    Meter (Option (Word prec×Word edges)) :=
  let P := loadAt prec offset bytes
  let M := loadAt edges (offset+prec+dep) bytes
  ⟨P.result.bind (fun p=>M.result.map (p,·)),P.steps+M.steps+4⟩

def callReadFee (prec edges dep offset : ℕ) : ℕ :=
  headerReadFee prec offset+headerReadFee edges (offset+prec+dep)+4

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {port edge dep tc tz tm : ℕ}

theorem child_edge_word_at_true_offset
    (J : NativeJob T v port edge dep prec tc tz tm)
    (issued : Meter (Word key)) :
    let addr := tc+(tz+(tm+6))
    loadAt edge (addr+prec+dep) (J.job.make issued).result.bytes =
      ⟨some (word v.child.edges),headerReadFee edge (addr+prec+dep)⟩ := by
  let addr := tc+(tz+(tm+6))
  let p : Word prec := word v.child.prec
  let d : Word dep := word v.child.depth
  let e : Word edge := word v.child.edges
  let tail := ((J.physical.physicalSelected v.groupAt).map J.physical.record).flatMap rowBytes
  let front := J.coordinates++p.bits++d.bits
  have hLen : front.length=addr+prec+dep := by
    simp only [front,List.length_append,p.size,d.size,addr,J.address_field_width]
  have bytes : (J.job.make issued).result.bytes=front++e.bits++tail := by
    rw [(J.literal_bytes issued).2]
    simp only [front,childHeaderBytes,List.append_assoc]
    rfl
  change loadAt edge (addr+prec+dep) (J.job.make issued).result.bytes=_
  rw [bytes,←hLen]
  exact load_at_boundary front e tail

theorem read_current_native_header
    (J : NativeJob T v port edge dep prec tc tz tm)
    (issued : Meter (Word key)) (raw : List Bool)
    (auth : raw=(J.job.make issued).result.bytes) :
    let addr := tc+(tz+(tm+6))
    readCallWords prec edge dep addr raw =
      ⟨some (word v.child.prec,word v.child.edges),callReadFee prec edge dep addr⟩ := by
  dsimp only
  rw [auth]
  unfold readCallWords callReadFee
  rw [(source_child_precision_word J issued).1,child_edge_word_at_true_offset J issued]
  rfl

/-- Offsets are those of the actual installed job, not of an untyped
external directory record.  The equation about resident bytes is only
a proof of provenance, not an instruction to reconstruct the bytes. -/
def fromResidentBirth (B : Birth T v key prec tw bw page) (raw : List Bool) :
    Meter (Option (Word prec×Word B.edge)) :=
  readCallWords prec B.edge B.dep B.job.offset raw

theorem actual_birth_header_words (B : Birth T v key prec tw bw page) (raw : List Bool)
    (same : raw=B.job.entry.result.bytes) :
    fromResidentBirth B raw =
      ⟨some (word v.child.prec,word v.child.edges),
        callReadFee prec B.edge B.dep B.job.offset⟩ ∧
      (word (q:=prec) v.child.prec).val=v.child.prec ∧
      (word (q:=B.edge) v.child.edges).val=v.child.edges := by
  have rawNative : raw=(B.native.job.make B.issuance).result.bytes := same
  refine ⟨read_current_native_header B.native B.issuance raw rawNative,
    (source_child_precision_word B.native B.issuance).2,word_val B.native.edgeFit⟩

theorem actual_stored_call_words (X : StoredSite T v key prec tw bw page)
    (raw : List Bool) (same : raw=X.birth.job.entry.result.bytes) :
    fromResidentBirth X.birth raw =
      ⟨some (word v.child.prec,word v.child.edges),
        callReadFee prec X.birth.edge X.birth.dep X.birth.job.offset⟩ ∧
      (word (q:=prec) v.child.prec).val=v.child.prec ∧
      (word (q:=X.birth.edge) v.child.edges).val=v.child.edges :=
  actual_birth_header_words X.birth raw same

#print axioms child_edge_word_at_true_offset
#print axioms read_current_native_header
#print axioms actual_birth_header_words
#print axioms actual_stored_call_words
end
end J6R63Active

