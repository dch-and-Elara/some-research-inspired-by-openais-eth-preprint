import AOracleCoordinates
import V9BitCost

/-!
# Truncated double-basis multiplication in the A1 verifier

Only the low V^k terms are accumulated. Each retained pair uses the
already-certified schoolbook U multiplier and one inner-coordinate
addition.  Bounds are for the dense scalar-word schedule; no bound
on computing the native source-table values is inferred.
-/

open scoped BigOperators Polynomial

namespace AOracleMachineArithmetic

open Polynomial AOracleCoordinates

section Outer
variable {R : Type*} [CommRing R]

abbrev Trunc (R : Type*) [CommRing R] (ell : ℕ) :=
  AdjoinRoot ((X : R[X])^ell)

noncomputable def rootV (R : Type*) [CommRing R] (ell : ℕ) : Trunc R ell :=
  AdjoinRoot.root ((X : R[X])^ell)

noncomputable def constV (R : Type*) [CommRing R] (ell : ℕ) : R →+* Trunc R ell :=
  AdjoinRoot.of ((X : R[X])^ell)

theorem rootV_pow_zero (ell : ℕ) : rootV R ell ^ ell = 0 := by
  rw [rootV, AdjoinRoot.root, ← map_pow, AdjoinRoot.mk_self]

theorem rootV_hi_zero (ell k : ℕ) (h : ell ≤ k) : rootV R ell ^ k = 0 := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, rootV_pow_zero, zero_mul]

noncomputable def encodeV {ell : ℕ} (a : Fin ell → R) : Trunc R ell :=
  ∑ i, constV R ell (a i) * rootV R ell ^ i.val

/-- The compact schoolbook product as a finite sum; high pairs
contribute literal zero and can be discarded before multiplication. -/
noncomputable def outerSchoolbook {ell : ℕ} (a b : Fin ell → R) : Trunc R ell :=
  ∑ i, ∑ j, if i.val+j.val < ell then
    constV R ell (a i*b j) * rootV R ell ^ (i.val+j.val) else 0

theorem outerSchoolbook_correct {ell : ℕ} (a b : Fin ell → R) :
    outerSchoolbook a b = encodeV a * encodeV b := by
  simp only [outerSchoolbook, encodeV, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_mul_mul_comm, ← map_mul, ← pow_add]
  split
  · rfl
  · rw [rootV_hi_zero _ _ (by omega), mul_zero]

def retainedPairs (ell : ℕ) : Finset (Fin ell × Fin ell) :=
  Finset.univ.filter (fun ij => ij.1.val+ij.2.val < ell)

theorem retainedPairs_le (ell : ℕ) : (retainedPairs ell).card ≤ ell^2 := by
  simpa [pow_two] using Finset.card_filter_le (s := (Finset.univ : Finset (Fin ell × Fin ell)))
    (p := fun ij => ij.1.val+ij.2.val < ell)

end Outer

section Concrete
variable {p : ℕ}

/-- A register consists of ell blocks of e coefficient words.  This
encoding uses the source ring, not a characteristic-two substitute. -/
noncomputable def encodeUV {f : (Base p)[X]} {ell : ℕ}
    (a : Fin ell → Fin f.natDegree → Base p) : Truncated f ell :=
  encodeV (fun i => AdjoinRoot.mk f (V9BitCost.dense (a i)))

/-- One correctly reduced U product per retained V pair. -/
noncomputable def evaluateUV {f : (Base p)[X]} {ell : ℕ}
    (a b : Fin ell → Fin f.natDegree → Base p) : Truncated f ell :=
  ∑ i, ∑ j, if i.val+j.val < ell then
    constV (AdjoinRoot f) ell (AdjoinRoot.mk f (V9BitCost.multiplyDense f (a i) (b j))) *
      rootV (AdjoinRoot f) ell ^ (i.val+j.val) else 0

theorem evaluateUV_correct {f : (Base p)[X]} (hf : f.Monic) {ell : ℕ}
    (a b : Fin ell → Fin f.natDegree → Base p) :
    evaluateUV a b = encodeUV a * encodeUV b := by
  unfold encodeUV
  rw [← outerSchoolbook_correct]
  unfold evaluateUV outerSchoolbook
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [(V9BitCost.multiplyDense_correct hf (a i) (b j)).1]

/-- Schoolbook dense upper budget, including inner reduction, scalar
accumulation and clearing the finite output registers. -/
def doubleMulEnvelope (e ell p : ℕ) : ℕ :=
  ell^2*(V9BitCost.ringMulEnvelope e p + 4*e*(p+1)) + ell*e*(p+1)

theorem doubleMulEnvelope_le (e ell p : ℕ) :
    doubleMulEnvelope e ell p ≤ 25*(ell+1)^2*(e+1)^2*(p+1)^2 := by
  let w := (e+1)^2*(p+1)^2
  have he : e ≤ (e+1)^2 := by nlinarith
  have hp : p+1 ≤ (p+1)^2 := by nlinarith
  have hw : e*(p+1) ≤ w := Nat.mul_le_mul he hp
  have hq : V9BitCost.ringMulEnvelope e p + 4*e*(p+1) ≤ 24*w := by
    have h1 := V9BitCost.ringMulEnvelope_le e p
    have h2 := Nat.mul_le_mul_left 4 hw
    dsimp [w]
    nlinarith
  have hsum := Nat.mul_le_mul_left (ell^2) hq
  have hlin := Nat.mul_le_mul_left ell hw
  have ha : ell^2 ≤ (ell+1)^2 := by nlinarith
  have hb : ell ≤ (ell+1)^2 := by nlinarith
  have hsa := Nat.mul_le_mul_right (24*w) ha
  have hla := Nat.mul_le_mul_right w hb
  unfold doubleMulEnvelope
  calc
    _ ≤ ell^2*(24*w) + ell*w := by simpa [mul_assoc] using Nat.add_le_add hsum hlin
    _ ≤ (ell+1)^2*(24*w)+(ell+1)^2*w := Nat.add_le_add hsa hla
    _ = _ := by dsimp [w]; ring

end Concrete

#print axioms rootV_pow_zero
#print axioms outerSchoolbook_correct
#print axioms retainedPairs_le
#print axioms evaluateUV_correct
#print axioms doubleMulEnvelope_le

end AOracleMachineArithmetic

