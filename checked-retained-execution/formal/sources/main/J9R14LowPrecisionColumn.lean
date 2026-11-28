import J9R14LowPrecisionLinear
import LiteralPortCompiler

/-!
# Reading one common bit per equality owner

Linear combinations of actual original ports remain linear after
substituting the common owner bit. A given owner may have multiple
ports but has only one Boolean coordinate, of any arity.
-/

namespace J9R14LowPrecisionColumn
open scoped Classical BigOperators Polynomial
open Polynomial J9R14LowPrecisionLinear

noncomputable section

variable {Q U R : Type*} [Fintype Q] [Fintype U] [CommRing R]

def columnBits (owner : Q→Option U) (other : Q→Bool) (s : Finset U) (q : Q) : Bool :=
  (owner q).elim (other q) (fun u => decide (u∈s))

def bitC (b : Bool) : R[X] := if b then 1 else 0

def lin (owner : Q→Option U) (other : Q→Bool) (v : Q→R[X]) : Linear U R :=
  ⟨∑ q, if owner q=none then v q*bitC (other q) else 0,
    fun u => ∑ q, if owner q=some u then v q else 0⟩

omit [Fintype U] in
theorem lin_exact (owner : Q→Option U) (other : Q→Bool) (v : Q→R[X]) (s : Finset U) :
    (lin owner other v).value s = ∑ q, v q*bitC (columnBits owner other s q) := by
  unfold Linear.value lin
  rw [Finset.sum_comm,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  cases h : owner q with
  | none => simp [h,columnBits]
  | some u =>
    by_cases hu : u∈s <;> simp [h,columnBits,hu,bitC]

omit [Fintype U] in
theorem lin_constant_zero (owner : Q→Option U) (other : Q→Bool) (v : Q→R[X])
    (hz : ∀ q u, owner q=some u → (v q).coeff 0=0) (u : U) :
    ((lin owner other v).byBit u).coeff 0=0 := by
  change (∑ q : Q, if owner q=some u then v q else 0).coeff 0=0
  rw [Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro q _
  by_cases he : owner q=some u <;> simp [he,hz]

omit [Fintype Q] in
def affine (bit : Bool) (f : Linear U R) : Linear U R :=
  if bit then f else ⟨1-f.constant,fun u => -f.byBit u⟩

omit [Fintype Q] [Fintype U] in
theorem affine_exact (bit : Bool) (f : Linear U R) (s : Finset U) :
    (affine bit f).value s = LiteralPortCompiler.affine bit (f.value s) := by
  cases bit
  · simp only [affine,Bool.false_eq_true,if_false,Linear.value,LiteralPortCompiler.affine,Finset.sum_neg_distrib]
    ring
  · rfl

omit [Fintype Q] [Fintype U] in
theorem affine_constant_zero (bit : Bool) (f : Linear U R)
    (h : ∀ u, (f.byBit u).coeff 0=0) (u : U) :
    ((affine bit f).byBit u).coeff 0=0 := by
  cases bit <;> simp [affine,h]

omit [Fintype Q] in
def scale (p : R[X]) (f : Linear U R) : Linear U R :=
  ⟨p*f.constant,fun u => p*f.byBit u⟩

omit [Fintype Q] [Fintype U] in
theorem scale_exact (p : R[X]) (f : Linear U R) (s : Finset U) :
    (scale p f).value s = p*f.value s := by
  simp only [scale,Linear.value,mul_add,Finset.mul_sum]

#print axioms lin_exact
#print axioms lin_constant_zero
#print axioms affine_exact
#print axioms scale_exact

end
end J9R14LowPrecisionColumn
