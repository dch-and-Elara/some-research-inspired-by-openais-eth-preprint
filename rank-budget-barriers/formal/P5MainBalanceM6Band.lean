import P5MainBalanceM6Distance
import P5MainBalanceM6Mix

/-! Homogeneous matrix support. A k-fold product of one-coordinate
swap steps moves no more than k ordered cells. This proves the exact
printed correction degree instead of supposing the native rows are low-degree. -/
namespace P5MainBalance.M6
open P5MainIterator Polynomial
open scoped BigOperators Classical

section Abstract
variable {S T : Type*} [Fintype S] [DecidableEq S]

def Band (d : S→S→ℕ) (k : ℕ) (A : Matrix S S ℚ) : Prop :=
  ∀ u v,k<d u v → A u v=0

omit [Fintype S] [DecidableEq S] in
theorem band_mono (d : S→S→ℕ) {k l : ℕ} (hk : k≤l) (A : Matrix S S ℚ) (hA : Band d k A) :
    Band d l A := fun _ _ h=>hA _ _ (hk.trans_lt h)

omit [Fintype S] [DecidableEq S] in
theorem band_add (d : S→S→ℕ) (k : ℕ) (A B : Matrix S S ℚ)
    (ha : Band d k A) (hb : Band d k B) : Band d k (A+B) := by
  intro u v h
  simp [ha u v h,hb u v h]

omit [Fintype S] [DecidableEq S] in
theorem band_sub (d : S→S→ℕ) (k : ℕ) (A B : Matrix S S ℚ)
    (ha : Band d k A) (hb : Band d k B) : Band d k (A-B) := by
  intro u v h
  simp [ha u v h,hb u v h]

omit [Fintype S] [DecidableEq S] in
theorem band_smul (d : S→S→ℕ) (k : ℕ) (A : Matrix S S ℚ) (a : ℚ)
    (ha : Band d k A) : Band d k (a•A) := by
  intro u v h
  simp [ha u v h]

omit [Fintype S] [DecidableEq S] in
theorem band_fin_sum (d : S→S→ℕ) (k : ℕ) (s : Finset T) (A : T→Matrix S S ℚ)
    (hA : ∀ t∈s,Band d k (A t)) : Band d k (∑ t∈s,A t) := by
  intro u v h
  rw [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  exact fun t ht=>hA t ht u v h

omit [Fintype S] in
theorem band_one (d : S→S→ℕ) (same : ∀ u,d u u=0) : Band d 0 (1:Matrix S S ℚ) := by
  intro u v h
  by_cases hu : u=v
  · subst v
    simp [same] at h
  · simp [hu]

omit [DecidableEq S] in
theorem band_mul (d : S→S→ℕ) (tri : ∀ u v w,d u w≤d u v+d v w)
    (k l : ℕ) (A B : Matrix S S ℚ) (ha : Band d k A) (hb : Band d l B) :
    Band d (k+l) (A*B) := by
  intro u v hv
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro w _
  by_cases hw : k<d u w
  · rw [ha u w hw,zero_mul]
  · have hw' : l<d w v := by have h := tri u w v; omega
    rw [hb w v hw',mul_zero]


theorem band_fold_of_steps (d : S→S→ℕ) (same : ∀ u,d u u=0)
    (tri : ∀ u v w,d u w≤d u v+d v w)
    (s : List (Matrix S S ℚ)) (hA : ∀ A∈s,Band d 1 A) : Band d s.length s.prod := by
  induction s with
  | nil => simpa using band_one d same
  | cons a s ih =>
    rw [List.prod_cons,List.length_cons,Nat.add_comm]
    exact band_mul d tri 1 s.length _ _ (hA a List.mem_cons_self)
      (ih fun b hb=>hA b (List.mem_cons_of_mem _ hb))

end Abstract

variable {Copy I B : Type*} [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B]

omit [Fintype Copy] [Fintype B] in
theorem native_swap_band (i : I) : Band hcDist 1 (swapMatrix i : Operator Copy I B) := by
  intro u v h
  have hv : v≠flipAt i u := fun hEq=> (not_lt_of_ge (one_flip_distance i u)) (hEq ▸ h)
  simp [swapMatrix,permMat,hv]

omit [Fintype Copy] [Fintype B] in
theorem native_weight_band : Band hcDist 1 (weightMatrix : Operator Copy I B) := by
  unfold weightMatrix
  apply band_smul
  apply band_fin_sum
  intro i _
  exact band_sub hcDist 1 _ _ (band_mono _ (by decide) _ (band_one _ hcDist_same))
    (native_swap_band i)

theorem scalar_matrix_band (c : ℚ) :
    Band hcDist 0 (algebraMap ℚ (Operator Copy I B) c) := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact band_smul _ _ _ _ (band_one _ hcDist_same)

set_option maxHeartbeats 5000000 in

theorem falling_weight_band (a j : ℕ) :
    Band hcDist j (Polynomial.aeval (weightMatrix : Operator Copy I B) (falling a j)) := by
  let W : Operator Copy I B := weightMatrix
  have hone (u : ℕ) : Band hcDist 1 (Polynomial.aeval W (X-C ((a+u:ℕ):ℚ))) := by
    rw [map_sub,Polynomial.aeval_X,Polynomial.aeval_C]
    exact band_sub _ _ _ _ native_weight_band (band_mono _ (by decide) _ (scalar_matrix_band _))
  have hProd (s : Finset ℕ) : Band hcDist s.card
      (Polynomial.aeval W (∏ u∈s, (X-C ((a+u:ℕ):ℚ)))) := by
    induction s using Finset.induction_on with
    | empty => simpa using band_one hcDist hcDist_same
    | insert b s hb ih =>
      rw [Finset.prod_insert hb,map_mul,Finset.card_insert_of_notMem hb,Nat.add_comm]
      exact band_mul _ hcDist_triangle _ _ _ _ (hone b) ih
  unfold falling
  rw [map_mul,Polynomial.aeval_C,←Nat.zero_add j]
  apply band_mul _ hcDist_triangle _ _ _ _ (scalar_matrix_band _)
  simpa only [Finset.card_range,Nat.zero_add] using hProd (Finset.range j)

set_option maxHeartbeats 5000000 in
theorem full_weight_band (a R : ℕ) :
    Band hcDist (R-1) (Polynomial.aeval (weightMatrix : Operator Copy I B) (printedInterval a R)) := by
  unfold printedInterval
  rw [map_mul,Polynomial.aeval_C,map_sum,←Nat.zero_add (R-1)]
  apply band_mul _ hcDist_triangle _ _ _ _ (scalar_matrix_band _)
  apply band_fin_sum
  intro j hj
  rw [map_mul,Polynomial.aeval_C]
  apply band_mono _ (show 0+j≤R-1 from by have := Finset.mem_range.mp hj; omega) _
  exact band_mul _ hcDist_triangle _ _ _ _ (scalar_matrix_band _) (falling_weight_band a j)

theorem fullMatrix_mul_entry (M : Operator Copy I B) (u v : SwapSlot Copy I B) :
    ((fullMatrix : Operator Copy I B)*M) u v=M (flipAll u) v := by
  rw [Matrix.mul_apply]
  simp only [fullMatrix,permMat,Matrix.of_apply,ite_mul,one_mul,zero_mul]
  rw [Finset.sum_eq_single (flipAll u)]
  · simp
  · intro x _ h
    simp [h]
  · simp

theorem printed_mix_mismatch (a R : ℕ) (u v : SwapSlot Copy I B) (h : (mismatch u v).card>R-1) :
    (printedMix a R : Operator Copy I B) u v=0 := by
  rw [printedMix,fullMatrix_mul_entry]
  exact full_weight_band a R _ _ (h.trans_le (mismatch_at_most_swapped_dist u v))

#print axioms band_mul
#print axioms band_fold_of_steps
#print axioms native_weight_band
#print axioms falling_weight_band
#print axioms full_weight_band
#print axioms printed_mix_mismatch
end P5MainBalance.M6
