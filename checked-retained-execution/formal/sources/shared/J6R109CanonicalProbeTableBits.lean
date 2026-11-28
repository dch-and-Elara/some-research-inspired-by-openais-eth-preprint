import J6R50RootIngressRankCore
import J6R58ActivePrepMaskTable
import J6R33OriginalJ6ZeroMenu

/-! The printed algorithm may choose a standard binary prefix. This
is the actual paid ordinal counter/word writer of R50 followed by
a paid copy from its typed words into a literal raw table. It never
enumerates the whole residue field unless the requested count is
the whole field. This is not the old chosenRep order certificate. -/
namespace J6R109CanonicalProbeTable
open A1R10 AOracleMachineTime AOracleMachineTimeTape
open J6R50RootIngress J6R49RootIngress J6R30GeneratedRootLayout J6R27PrescribedProbe
open J6R58ActivePrep J6R33OriginalJ6 J6R27OriginalGate

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 7500000

/-- Serialize the coefficient rows through the existing bit copier. -/
def writeCoefficientRows {e : ℕ} : List (Word e) → Meter (List (List Bool))
  | [] => ⟨[],2⟩
  | w::ws =>
    let x := copyBits w.val
    let xs := writeCoefficientRows ws
    ⟨x.result::xs.result,x.steps+xs.steps+4⟩

def canonicalTable (e n : ℕ) : Meter (List (List Bool)) :=
  let w := indexTape e n
  let A := writeCoefficientRows w.result
  ⟨A.result,w.steps+A.steps+3⟩

def canonicalTableFee (e n : ℕ) : ℕ :=
  19+6*e+(n-1)*(20*e+6)+n*(3*e+5)

theorem actual_coefficient_row_writer_exact {e : ℕ} (ws : List (Word e)) :
    writeCoefficientRows ws=⟨ws.map Subtype.val,2+ws.length*(3*e+5)⟩ := by
  induction ws with
  | nil=>simp [writeCoefficientRows]
  | cons w ws ih=>
    simp only [writeCoefficientRows,copy_bits_exact,w.property,ih,List.map_cons,List.length_cons]
    exact congrArg (Meter.mk (w.val::ws.map Subtype.val)) (by
      rw [Nat.add_mul,Nat.one_mul]
      omega)

theorem actual_index_tape_nonempty_exact (e d : ℕ) (he : 0<e)
    (fit : d+1≤2^e) :
    let W := indexTape e (d+1)
    W.result=List.ofFn (fun i : Fin (d+1)=>wordAt e i.val) ∧
    W.steps=14+6*e+d*(20*e+6) := by
  have exp := index_tape_exact e (d+1) he fit
  refine ⟨exp.1,?_⟩
  have M := (positive_tape_exact e d he (by omega)).2
  change (positiveTape e d).steps+3*e+4=_
  rw [M]
  unfold positiveTapeFee
  omega

theorem actual_canonical_table_is_paid_binary_prefix (e d : ℕ) (he : 0<e)
    (fit : d+1≤2^e) :
    let out := canonicalTable e (d+1)
    out.result=List.ofFn (fun i : Fin (d+1)=>List.ofFn (zeroPrefix e d i)) ∧
    out.steps=canonicalTableFee e (d+1) := by
  obtain ⟨rows,bill⟩ := actual_index_tape_nonempty_exact e d he fit
  let I := indexTape e (d+1)
  have len : I.result.length=d+1 := by
    change (indexTape e (d+1)).result.length=d+1
    rw [rows,List.length_ofFn]
  unfold canonicalTable
  dsimp only
  rw [actual_coefficient_row_writer_exact,show (indexTape e (d+1)).result.length=d+1 from len]
  constructor
  · rw [rows,List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    change encodeBits e i.val=List.ofFn (J6R27PrescribedProbe.bitAt e i.val)
    exact (J6R27PrescribedProbe.bit_word_exact e i.val).symm
  · dsimp only
    rw [bill]
    unfold canonicalTableFee
    rw [Nat.add_sub_cancel]
    omega

def rawPayload (rows : List (List Bool)) : ℕ := (rows.map List.length).sum

theorem raw_of_fixed_width {e : ℕ} (rows : List (List Bool))
    (all : ∀ row∈rows,row.length=e) :
    rawPayload rows=e*rows.length := by
  induction rows with
  | nil=>simp [rawPayload]
  | cons x xs ih=>
    have first := all x List.mem_cons_self
    have tail := ih (fun w mem=>all w (List.mem_cons_of_mem _ mem))
    change x.length+rawPayload xs=e*(xs.length+1)
    rw [first,tail,Nat.mul_add,Nat.mul_one,Nat.add_comm]

theorem word_payload_exact {e : ℕ} (xs : List (Word e)) :
    rawPayload (xs.map Subtype.val)=e*xs.length := by
  rw [raw_of_fixed_width _ (fun row h=>by
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp h
    exact w.property),List.length_map]

theorem actual_canonical_table_payload_exact (e d : ℕ) (he : 0<e) (fit : d+1≤2^e) :
    let out := canonicalTable e (d+1)
    out.result.length=d+1 ∧
    (∀ row∈out.result,row.length=e) ∧ rawPayload out.result=e*(d+1) := by
  have rows := (actual_canonical_table_is_paid_binary_prefix e d he fit).1
  dsimp only
  rw [rows]
  have len : (List.ofFn (fun i : Fin (d+1)=>List.ofFn (zeroPrefix e d i))).length=d+1 :=
    List.length_ofFn
  have bits : ∀ row∈List.ofFn (fun i : Fin (d+1)=>List.ofFn (zeroPrefix e d i)),
      row.length=e := by
    intro row mem
    obtain ⟨i,h⟩ := List.mem_ofFn.mp mem
    rw [←h,List.length_ofFn]
  exact ⟨len,bits,(raw_of_fixed_width _ bits).trans (congrArg (e*·) len)⟩

#print axioms actual_coefficient_row_writer_exact
#print axioms actual_index_tape_nonempty_exact
#print axioms actual_canonical_table_is_paid_binary_prefix
#print axioms actual_canonical_table_payload_exact
end J6R109CanonicalProbeTable
