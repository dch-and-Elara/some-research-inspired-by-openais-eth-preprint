
import J6R30ProducedGateRegistryJobs

/-! Literal non-page directory fields in the scoped publication ABI.
Page keys and page payloads are counted separately in R50. Addresses,
copies and signed contexts below are selected encodings; an allocator
can alias equal fields and might retain additional unmodelled data. -/
namespace J6R51Peak
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R30ProducedGateRegistry

set_option autoImplicit false
set_option maxHeartbeats 2600000

variable {key prec tw bw : ℕ} {D : Type*}
local notation "L" => Ledger key prec tw bw D
local notation "J" => Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D

def headerFields (row : DirRow key) : List Bool :=
  row.id.bits ++ row.bytes

def storedFields (row : RefRow key (Stored key prec tw bw D)) : List Bool :=
  row.address.bits ++ row.payload.stamp.creator.bits ++ row.payload.stamp.created.bits ++
    [row.payload.context.negative] ++ row.payload.context.magnitude.bits ++
    row.payload.context.codeWidth.bits ++ row.payload.checkedHeader

def directoryBits (B : L) : ℕ :=
  (B.headers.map (fun row=>(headerFields row).length)).sum+
    (B.records.map (fun row=>(storedFields row).length)).sum

def insertionBits (j : J) : ℕ :=
  3*key+prec+1+tw+bw+2*j.entry.result.bytes.length

theorem exact_header_encoding (row : DirRow key) :
    (headerFields row).length=key+row.bytes.length := by
  rw [headerFields,List.length_append,row.id.size]

theorem exact_stored_encoding (row : RefRow key (Stored key prec tw bw D)) :
    (storedFields row).length=key+key+prec+1+tw+bw+row.payload.checkedHeader.length := by
  simp only [storedFields,List.length_append,row.address.size,row.payload.stamp.creator.size,
    row.payload.stamp.created.size,row.payload.context.magnitude.size,row.payload.context.codeWidth.size]
  rfl

theorem one_publication_adds_exact_directory_bits (B : L) (j : J) :
    directoryBits (afterOne B j)=directoryBits B+insertionBits j := by
  unfold directoryBits afterOne
  simp only [List.map_cons,List.sum_cons,exact_header_encoding,exact_stored_encoding]
  change (key+j.entry.result.bytes.length)+_+
      (key+key+prec+1+tw+bw+j.entry.result.bytes.length+_)=_
  unfold insertionBits
  omega

theorem paid_job_mounts_the_same_selected_directory (B : L) (j : J)
    (sync : B.synced) (fresh : ∀ row∈B.headers,row.id≠j.identifier) :
    j.install B=⟨(afterOne B j,true),publishFee B j.entry j.offset j.built⟩ ∧
      directoryBits (j.install B).result.1=directoryBits B+insertionBits j := by
  have legal : JobsReady B [j] := by
    refine ⟨sync,by simp,?_⟩
    intro k hk row hr
    have e := List.mem_singleton.mp hk
    exact e.symm ▸ fresh row hr
  have step := (next_job_exact B j [] legal).1
  exact ⟨step, by rw [step]; exact one_publication_adds_exact_directory_bits B j⟩

#print axioms exact_header_encoding
#print axioms exact_stored_encoding
#print axioms one_publication_adds_exact_directory_bits
#print axioms paid_job_mounts_the_same_selected_directory
end J6R51Peak
