
import J6R26DescriptorTreeNative
import J6R26DescriptorTreeRegistry
import J6R27OriginalGateTrace

/-! Read the creation precision out of the strict R26 header bytes.
The four literal occurrence-coordinate fields precede the precision;
neither the ordinal of the centre nor the receiving depth is a
signed centre value or a substitute for a creation time. -/
namespace J6R30ProducedGateRegistry
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R27OriginalGate

def loadWord : (width : ℕ) → List Bool → Meter (Option (Word width))
  | 0,_ => ⟨some ⟨[],rfl⟩,2⟩
  | _+1,[] => ⟨none,2⟩
  | n+1,x::xs =>
    let z := loadWord n xs
    ⟨z.result.map (withSide x),z.steps+4⟩

theorem load_word_exact {b : ℕ} (x : Word b) (rest : List Bool) :
    loadWord b (x.bits++rest)=⟨some x,4*b+2⟩ := by
  rcases x with ⟨bits,h⟩
  subst b
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    simp only [List.length_cons,List.cons_append,loadWord,ih,Option.map_some]
    congr 1

def loadAt (b : ℕ) : ℕ→List Bool→Meter (Option (Word b))
  | 0,bs => loadWord b bs
  | _+1,[] => ⟨none,2⟩
  | j+1,_::bs =>
    let z := loadAt b j bs
    ⟨z.result,z.steps+3⟩

def headerReadFee (b offset : ℕ) := 3*offset+4*b+2

theorem load_at_boundary {b : ℕ} (front : List Bool) (x : Word b) (rest : List Bool) :
    loadAt b front.length (front++x.bits++rest)=⟨some x,headerReadFee b front.length⟩ := by
  induction front with
  | nil =>
    simp only [List.length_nil,List.nil_append,loadAt,headerReadFee,Nat.mul_zero,Nat.zero_add]
    exact load_word_exact x rest
  | cons q qs ih =>
    simp only [List.length_cons,List.cons_append,loadAt,ih,headerReadFee]
    congr 1
    omega

open scoped Polynomial
open Polynomial J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {ticket : Ticket sel r}
variable {port edge dep prec tc tz tm key : ℕ}
variable (D : NativeJob T ticket port edge dep prec tc tz tm)

set_option maxHeartbeats 2500000 in
theorem source_child_precision_word (issue : Meter (Word key)) :
    let row := D.job.make issue
    let offset := tc+(tz+(tm+6))
    loadAt prec offset row.result.bytes=
      ⟨some (word ticket.child.prec),headerReadFee prec offset⟩ ∧
      (word (q:=prec) ticket.child.prec).val=ticket.child.prec := by
  have bytes := (D.literal_bytes issue).2
  have hh := D.address_field_width
  have fit : ticket.child.prec<2^prec := D.receiveExact ▸ val_lt D.receiving
  constructor
  · rw [bytes,←hh,childHeaderBytes]
    let tail := (word (q:=dep) ticket.child.depth).bits++
      (word (q:=edge) ticket.child.edges).bits++
      ((D.physical.physicalSelected ticket.groupAt).map D.physical.record).flatMap rowBytes
    simpa only [List.append_assoc,tail] using
      (load_at_boundary D.coordinates (word (q:=prec) ticket.child.prec) tail)
  · exact word_val fit

#print axioms load_word_exact
#print axioms load_at_boundary
#print axioms source_child_precision_word
end J6R30ProducedGateRegistry


