import J6R94ExteriorDebitBits
import J6R25PreparedSupplyChildStage

/-! The marked exterior suffix uses fixed actual physical row widths;
decode sequentially until the suffix is exhausted. A proof of the
header layout does not make reading these bytes free. -/
namespace J6R94ExteriorDebit
open AOracleMachineTime J6R15ModeCost J6R19Retained J6R25PreparedSupply

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3500000
set_option maxRecDepth 3500
set_option Elab.async false

private def bitsWord {w : ℕ} (W : A1R10.Word w) : Word w := ⟨W.val,W.property⟩

def decodeOneWire (w body : ℕ) (xs : List Bool) :
    Meter (PortRow w×List Bool) :=
  let addr := cutWord w xs
  let group := cutWord 6 addr.result.2
  let payload := cutWord body group.result.2
  ⟨(⟨bitsWord addr.result.1,bitsWord group.result.1,payload.result.1.val⟩,payload.result.2),
    addr.steps+group.steps+payload.steps+4⟩

def decodeWireFee (w body : ℕ) :=
  cutWordFee w+cutWordFee 6+cutWordFee body+4

theorem one_fixed_wire_header_roundtrips {w body : ℕ}
    (r : PortRow w) (h : r.body.length=body) (suffix : List Bool) :
    decodeOneWire w body (rowBytes r++suffix)=⟨(r,suffix),decodeWireFee w body⟩ := by
  let a : A1R10.Word w := ⟨r.address.bits,r.address.size⟩
  let g : A1R10.Word 6 := ⟨r.group.bits,r.group.size⟩
  let b : A1R10.Word body := ⟨r.body,h⟩
  have eq : rowBytes r++suffix=a.val++(g.val++(b.val++suffix)) := by
    simp only [rowBytes,List.append_assoc,a,g,b]
  have ra := cutWord_exact a (g.val++(b.val++suffix))
  have rg := cutWord_exact g (b.val++suffix)
  have rb := cutWord_exact b suffix
  rw [eq]
  unfold decodeOneWire decodeWireFee
  dsimp only
  rw [ra.1,ra.2]
  dsimp only
  rw [rg.1,rg.2]
  dsimp only
  rw [rb.1,rb.2]
  cases r
  rfl

def decodeWireRows (w body : ℕ) (xs : List Bool) :
    Meter (List (PortRow w)) :=
  if h : xs=[] then ⟨[],2⟩ else
    let one := decodeOneWire w body xs
    let rest := decodeWireRows w body one.result.2
    ⟨one.result.1::rest.result,one.steps+rest.steps+3⟩
termination_by xs.length
decreasing_by
  simp only [decodeOneWire,cutWord,List.length_drop]
  have hx : 0<xs.length := by
    exact List.length_pos_iff.mpr h
  omega

theorem actual_fixed_header_rows_roundtrip {w body : ℕ} (rs : List (PortRow w))
    (shape : ∀ r∈rs,r.body.length=body) :
    decodeWireRows w body (rs.flatMap rowBytes)=
      ⟨rs,2+(decodeWireFee w body+3)*rs.length⟩ := by
  induction rs with
  | nil => simp [decodeWireRows]
  | cons r tail ih =>
    have tailShape := fun row incl=>shape row (List.mem_cons_of_mem r incl)
    have rh := shape r List.mem_cons_self
    have notNil : rowBytes r++tail.flatMap rowBytes≠[] := by
      intro bad
      have len := congrArg List.length bad
      simp only [List.length_nil,List.length_append,rowBytes,r.address.size,r.group.size] at len
      omega
    have one := one_fixed_wire_header_roundtrips r rh (tail.flatMap rowBytes)
    rw [List.flatMap_cons,decodeWireRows,dif_neg notNil,one]
    dsimp only
    rw [ih tailShape]
    simp only [List.length_cons,Nat.mul_succ]
    congr 1
    omega

#print axioms one_fixed_wire_header_roundtrips
#print axioms actual_fixed_header_rows_roundtrip
end J6R94ExteriorDebit
