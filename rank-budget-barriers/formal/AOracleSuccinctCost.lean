import AOracleSuccinctPacket
import AOracleSuccinctKernel
import AOracleMachineScan
import Mathlib.Data.Int.Interval

/-!
# Charged local data reads for A1

The witness reads one local Boolean truth-table entry from an actual
finite tape per original vertex; each port address can itself be
retrieved by a separate finite scan.  Source grid enumeration has
exactly its physical size, without enumerating Boolean assignments.
This is a serial access certificate, not a Lean verification of a
particular full Turing machine or of a succinct packing finder.
-/

namespace AOracleSuccinctCost
open AOracleSuccinct AOracleMachineScan P1DyadicGrid

/-- A literal tape of the original vertex's local table. -/
def tensorTape {n delta : ℕ} (T : BoolTensor n delta) : List Bool :=
  List.ofFn T.table

def incidenceTape {n delta : ℕ} (T : BoolTensor n delta) : List (Fin n) :=
  List.ofFn T.port

theorem tape_lookup {n delta : ℕ} (T : BoolTensor n delta) (a : Fin n → Bool) :
    (scan (tensorTape T) (rankBits (fun j => a (T.port j)))).1 = some (T.read a) ∧
    (scan (tensorTape T) (rankBits (fun j => a (T.port j)))).2 ≤ 2^delta := by
  constructor
  · rw [scan_exact]
    simp [tensorTape, BoolTensor.read, rankBits_lt]
  · calc
      _ ≤ (tensorTape T).length := scan_payload_bound _ _
      _ = 2^T.arity := List.length_ofFn
      _ ≤ 2^delta := Nat.pow_le_pow_right (by decide) T.small

theorem incidence_lookup {n delta : ℕ} (T : BoolTensor n delta) (j : Fin T.arity) :
    (scan (incidenceTape T) j.val).1 = some (T.port j) ∧
    (scan (incidenceTape T) j.val).2 ≤ delta := by
  constructor
  · rw [scan_exact]
    simp [incidenceTape, j.isLt]
  · calc
      _ ≤ (incidenceTape T).length := scan_payload_bound _ _
      _ = T.arity := List.length_ofFn
      _ ≤ delta := T.small

theorem tape_size {n delta : ℕ} (T : BoolTensor n delta) (addrBits : ℕ) :
    (tensorTape T).length+(incidenceTape T).length*addrBits = T.payload addrBits := by
  simp [tensorTape, incidenceTape, BoolTensor.payload]

/-- The real signed source grid has size twice the packet length. -/
theorem source_grid_count (a : ℕ) : (grid a).card = 2^(a+1) := by
  rw [grid, Int.card_Ico, sub_neg_eq_add, ← two_mul, pow₂]
  rw [show (2:ℤ)*2^a = ((2^(a+1):ℕ):ℤ) by push_cast; rw [pow_succ, mul_comm]]
  exact Int.toNat_natCast _

theorem grid_product_limit (a : ℕ) (t : ℤ) :
    ((grid a).erase t).card ≤ 2^(a+1) :=
  (Finset.card_erase_le).trans_eq (source_grid_count a)

/-- Pay for every port coordinate, each mode descriptor and requested
multiplicity, plus literal tables, an input terminal-node word and
probe/base-ring coordinates. Header/arity storage can be added to
the supplied original tape lengths. No assignment-indexed table
appears in the input bound. -/
def physicalPayload (r c m a i bp bg b h e p rowBits colBits : ℕ) : ℕ :=
  rowBits+colBits+(r+c)*(a+bp+bg)+m*(bp+i+1+2*bg+b+h)+(a+2)+(e+1)*p+e*p

theorem physicalPayload_bound (r c m a i bp bg b h e p rowBits colBits : ℕ) :
    physicalPayload r c m a i bp bg b h e p rowBits colBits ≤
      12*(r+c+m+a+i+bp+bg+b+h+e+p+rowBits+colBits+1)^2 := by
  let z := r+c+m+a+i+bp+bg+b+h+e+p+rowBits+colBits+1
  have h1 : rowBits+colBits+a+2 ≤ 2*z := by dsimp [z]; omega
  have h2 : r+c ≤ z := by dsimp [z]; omega
  have h3 : a+bp+bg ≤ z := by dsimp [z]; omega
  have h4 : m ≤ z := by dsimp [z]; omega
  have h5 : bp+i+1+2*bg+b+h ≤ 2*z := by dsimp [z]; omega
  have h6 : e+1 ≤ z := by dsimp [z]; omega
  have h7 : e ≤ z := by dsimp [z]; omega
  have hp : p ≤ z := by dsimp [z]; omega
  have hz : z ≤ z^2 := by have : 1 ≤ z := by dsimp [z]; omega
                          nlinarith
  have ha := Nat.mul_le_mul h2 h3
  have hb := Nat.mul_le_mul h4 h5
  have hc := Nat.mul_le_mul h6 hp
  have hd := Nat.mul_le_mul h7 hp
  change _ ≤ 12*z^2
  unfold physicalPayload
  nlinarith

#print axioms tape_lookup
#print axioms incidence_lookup
#print axioms tape_size
#print axioms source_grid_count
#print axioms physicalPayload_bound

end AOracleSuccinctCost

