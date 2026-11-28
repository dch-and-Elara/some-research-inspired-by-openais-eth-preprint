
import J6R33StatefulArithmeticPagePath
import J6R26DescriptorTreeNative

/-! The actual emitted R26 occurrence descriptor contains its four
coordinates and its precision/depth/edge words followed by one
encoded port record per true child edge. No layout is reselected. -/
namespace J6R51Peak
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R33StatefulArithmeticPage J6R10Repack

set_option autoImplicit false
set_option maxHeartbeats 5500000
set_option maxRecDepth 3000

theorem encoded_rows_exact {w : ℕ} (rows : List (PortRow w)) :
    (rows.flatMap rowBytes).length=(rows.map (fun row=>w+6+row.body.length)).sum := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.flatMap_cons,List.length_append,rowBytes,row.address.size,row.group.size,
      List.map_cons,List.sum_cons,ih]

theorem uniform_sum_bound {A : Type*} (rows : List A) (width : A→ℕ) (bound : ℕ)
    (good : ∀ row∈rows,width row≤bound) :
    (rows.map width).sum≤rows.length*bound := by
  induction rows with
  | nil => simp
  | cons row rest ih =>
    rw [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    exact (Nat.add_le_add (good row List.mem_cons_self)
      (ih (fun x hx=>good x (List.mem_cons_of_mem _ hx)))).trans_eq (Nat.add_comm _ _)

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}

noncomputable abbrev selectedSourceRows (B : Birth T v key prec tw bw page) : List (PortRow B.port) :=
  (B.native.physical.physicalSelected v.groupAt).map B.native.physical.record

def fixedWords (B : Birth T v key prec tw bw page) : ℕ :=
  B.tc+(B.tz+(B.tm+6))+prec+B.dep+B.edge

theorem native_literal_header_length (B : Birth T v key prec tw bw page) :
    B.job.entry.result.bytes.length=fixedWords B+
      ((selectedSourceRows B).map (fun row=>B.port+6+row.body.length)).sum := by
  change (B.native.job.make B.issuance).result.bytes.length=_
  rw [(B.native.literal_bytes B.issuance).2]
  unfold fixedWords childHeaderBytes selectedSourceRows
  simp only [List.length_append,B.native.address_field_width,Word.size,encoded_rows_exact]
  omega

theorem native_header_count_is_actual_child (B : Birth T v key prec tw bw page) :
    (selectedSourceRows B).length=v.child.edges := by
  rw [show (selectedSourceRows B).length=(B.native.physical.physicalSelected v.groupAt).length from List.length_map ..]
  exact B.native.physical.physical_count_is_child v.groupAt v.probeAt v.modeAt

theorem actual_child_header_width (B : Birth T v key prec tw bw page) (H K W : ℕ)
    (fixed : fixedWords B≤H) (tag : B.port+6≤K)
    (body : ∀ row∈selectedSourceRows B,row.body.length≤W) :
    B.job.entry.result.bytes.length≤H+v.child.edges*(K+W) := by
  rw [native_literal_header_length]
  apply Nat.add_le_add fixed
  rw [←native_header_count_is_actual_child B]
  exact uniform_sum_bound _ _ _ (fun row mem=>Nat.add_le_add tag (body row mem))

#print axioms encoded_rows_exact
#print axioms native_literal_header_length
#print axioms native_header_count_is_actual_child
#print axioms actual_child_header_width
end J6R51Peak
