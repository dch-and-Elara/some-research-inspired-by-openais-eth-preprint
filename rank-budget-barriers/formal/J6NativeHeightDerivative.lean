import J6NativeHeightMesh
import P1DyadicGridBridge
import Mathlib.Tactic

/-! Identify the literally printed dyadic Cauchy derivative coefficient
with the signed rational slot scalar of J6. Compare consecutive grid
nodes by translating the product by one, then removing boundary factors. -/
namespace J6NativeHeightDerivative
open scoped BigOperators Polynomial
open P1DyadicGrid P1DyadicGridBridge
private def middle (L t : ℤ) : Finset ℤ := (Finset.Ico (-L) (L-1)).erase t

private theorem unshifted (a : ℕ) (t : ℤ) (ht : t+1<pow₂ a) :
    (grid a).erase t = insert (pow₂ a-1) (middle (pow₂ a) t) := by
  have hL := pow₂_pos a
  ext q
  simp only [grid,middle,Finset.mem_insert,Finset.mem_erase,Finset.mem_Ico]
  omega

private theorem shifted_product (a : ℕ) (t : ℤ) (hlo : -pow₂ a ≤ t) :
    (∏ q ∈ (grid a).erase (t+1), (t+1-q)) =
      ∏ r ∈ insert (-pow₂ a-1) (middle (pow₂ a) t), (t-r) := by
  have hL := pow₂_pos a
  refine Finset.prod_bij (fun q _ => q-1) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [grid,middle,Finset.mem_insert,Finset.mem_erase,Finset.mem_Ico] at hq ⊢
    omega
  · intro q _ r _ he
    change q-1=r-1 at he
    omega
  · intro r hr
    refine ⟨r+1,?_,?_⟩
    · simp only [grid,middle,Finset.mem_insert,Finset.mem_erase,Finset.mem_Ico] at hr ⊢
      omega
    · change r+1-1=r
      omega
  · intro q _
    change t+1-q=t-(q-1)
    omega

theorem ratio_step (a t : ℕ) (ht : t+1 < 2^a) :
    (derivRatio a ((t+1:ℕ):ℤ) : ℚ) =
      -(derivRatio a (t:ℤ) : ℚ) *
        (((2:ℚ)^a+(t+1))/((2:ℚ)^a-(t+1))) := by
  have hlt : (t:ℤ)+1 < pow₂ a := by unfold pow₂; exact_mod_cast ht
  have hL := pow₂_pos a
  have hi : (t:ℤ) ∈ grid a := mem_grid.mpr ⟨by omega,by omega⟩
  have hj : (t:ℤ)+1 ∈ grid a := mem_grid.mpr ⟨by omega,hlt⟩
  have hRight : pow₂ a-1 ∉ middle (pow₂ a) (t:ℤ) := by simp [middle]
  have hLeft : -pow₂ a-1 ∉ middle (pow₂ a) (t:ℤ) := by simp [middle]
  have h0 : (((cauchyPolynomial a).derivative.eval 0 : ℤ):ℚ) ≠ 0 := by
    exact_mod_cast cauchy_derivative_nonzero (zero_mem_grid a)
  have hDen : (2:ℚ)^a-((t:ℚ)+1) ≠ 0 := by
    exact (sub_pos.mpr (by exact_mod_cast ht)).ne'
  simp only [Nat.cast_add,Nat.cast_one,derivRatio]
  rw [cauchy_derivative_eval hi,cauchy_derivative_eval hj,shifted_product a (t:ℤ) (by omega),
    unshifted a (t:ℤ) hlt,Finset.prod_insert hRight,Finset.prod_insert hLeft]
  push_cast
  simp only [cast_pow₂]
  field_simp
  ring

theorem ratio_eq_grid (a t : ℕ) (ht : t < 2^a) :
    (derivRatio a (t:ℤ) : ℚ) = (-1:ℚ)^t * LayerRecovery.gridRatio (2^a) t := by
  induction t with
  | zero =>
    have h0 : (((cauchyPolynomial a).derivative.eval 0 : ℤ):ℚ) ≠ 0 := by
      exact_mod_cast cauchy_derivative_nonzero (zero_mem_grid a)
    simp only [Nat.cast_zero,derivRatio,pow_zero,one_mul,LayerRecovery.gridRatio,
      Finset.range_zero,Finset.prod_empty]
    exact div_self h0
  | succ t ih =>
    have hr : LayerRecovery.gridRatio (2^a) (t+1) =
      LayerRecovery.gridRatio (2^a) t *
      (((2:ℚ)^a+(t+1))/((2:ℚ)^a-(t+1))) := by
      unfold LayerRecovery.gridRatio
      rw [Finset.prod_range_succ]
      push_cast
      rfl
    rw [ratio_step a t ht,ih (by omega),hr,pow_succ]
    ring

theorem source_scalar_eq_actual_mesh (m : ℕ) (i : Fin (m+1)) :
    (derivRatio (J6Mesh.a m) (J6Mesh.index m i : ℤ) : ℚ) = J6Mesh.point m i := by
  have ht := (J6Mesh.address_index m i).2.2.2
  rw [ratio_eq_grid _ _ ht,J6Mesh.point]
  have h : (-1:ℚ)^J6Mesh.index m i = -1 := (J6Mesh.address_index m i).2.1.neg_one_pow
  rw [h,J6Mesh.L,neg_one_mul]

#print axioms ratio_step
#print axioms ratio_eq_grid
#print axioms source_scalar_eq_actual_mesh
end J6NativeHeightDerivative
