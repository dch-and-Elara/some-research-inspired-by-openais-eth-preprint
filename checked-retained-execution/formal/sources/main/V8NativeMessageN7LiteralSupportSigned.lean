import V8NativeMessageN7Shift
import J6DeformationPoly

/-! Exact sign of the printed symmetric grid. Reflection is about
-1/2, not about zero: the grid includes -L and excludes +L. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped BigOperators Polynomial
open Polynomial P1DyadicGrid P1DyadicGridBridge DenominatorBudget J6R9PacketCoeff
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

theorem reflected_grid {a : ℕ} {t : ℤ} (h : t∈grid a) : -1-t∈grid a := by
  rw [mem_grid] at h ⊢
  omega

theorem grid_derivative_reflected {a : ℕ} {t : ℤ} (h : t∈grid a) :
    (cauchyPolynomial a).derivative.eval (-1-t)=-(cauchyPolynomial a).derivative.eval t := by
  rw [cauchy_derivative_eval (reflected_grid h),cauchy_derivative_eval h]
  have rep :
      (∏ x ∈ (grid a).erase (-1-t), (-1-t-x))=∏ y ∈ (grid a).erase t, -(t-y) := by
    refine Finset.prod_bij (fun x _=>-1-x) ?_ ?_ ?_ ?_
    · intro x hx
      change -1-x ∈ (grid a).erase t
      obtain ⟨hn,hm⟩ := Finset.mem_erase.mp hx
      refine Finset.mem_erase.mpr ⟨?_,reflected_grid hm⟩
      intro E
      apply hn
      omega
    · intro x _ y _ hxy
      change -1-x=-1-y at hxy
      omega
    · intro y hy
      obtain ⟨hn,hm⟩ := Finset.mem_erase.mp hy
      refine ⟨-1-y,Finset.mem_erase.mpr ⟨?_,reflected_grid hm⟩,?_⟩
      · intro E; apply hn; omega
      · change -1-(-1-y)=y; omega
    · intro x _
      ring
  rw [rep]
  have hfactor (x : ℤ) : -(t-x)=(-1:ℤ)*(t-x) := (neg_one_mul _).symm
  simp only [hfactor,Finset.prod_mul_distrib,Finset.prod_const]
  have odd : Odd ((grid a).erase t).card := by
    have hp : 0 < (2:ℕ)^a := pow_pos (by decide) _
    rw [Finset.card_erase_of_mem h,J6DeformationPoly.grid_card]
    exact ⟨2^a-1,by omega⟩
  rw [odd.neg_one_pow,neg_one_mul]

theorem derivative_ratio_reflected {a : ℕ} {t : ℤ} (h : t∈grid a) :
    (derivRatio a (-1-t):ℚ)=-(derivRatio a t:ℚ) := by
  simp only [derivRatio,grid_derivative_reflected h,Int.cast_neg,neg_div]

theorem neg_one_in_signed_grid (a : ℕ) : (-1:ℤ)∈grid a := by
  simpa only [sub_zero] using reflected_grid (zero_mem_grid a)

theorem rho_at_actual_unit_shift (a : ℕ) : rho a (-1) = -1 := by
  apply twoLocalRat_injective
  rw [rho_rat (neg_one_in_signed_grid a)]
  have h := derivative_ratio_reflected (zero_mem_grid a)
  simp only [sub_zero] at h
  rw [h,map_neg,map_one]
  have hn : (((cauchyPolynomial a).derivative.eval 0 : ℤ):ℚ)≠0 := by
    exact_mod_cast (cauchy_derivative_nonzero (zero_mem_grid a))
  unfold derivRatio
  rw [div_self hn]

theorem normalized_unit_shift (a : ℕ) (k : ℤ) :
    (V8PooledMenu.normalizedW a (-1) k).eval 0 =
      if k=(-1) then (-1:TwoLocal) else 0 := by
  have h := V8NativeMessage.N7.normalized_at_zero (RingHom.id TwoLocal) a (-1) k
  simpa only [Polynomial.eval₂_id,RingHom.id_apply,rho_at_actual_unit_shift] using h

end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.reflected_grid
#print axioms V8NativeMessage.N7LiteralSupport.grid_derivative_reflected
#print axioms V8NativeMessage.N7LiteralSupport.derivative_ratio_reflected
#print axioms V8NativeMessage.N7LiteralSupport.neg_one_in_signed_grid
#print axioms V8NativeMessage.N7LiteralSupport.rho_at_actual_unit_shift
#print axioms V8NativeMessage.N7LiteralSupport.normalized_unit_shift
