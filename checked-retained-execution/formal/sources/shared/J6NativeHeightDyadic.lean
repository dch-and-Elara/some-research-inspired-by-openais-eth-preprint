import J6NativeHeightMesh
import J6NativeHeightResidue
import Mathlib.Tactic

/-! The odd mesh scalar is intrinsically two-local. Divide both
L+j and L-j by two while j is even, then the remaining denominator
is odd. This avoids taking the inverse of the raw denominator. -/
namespace J6NativeHeightDyadic
open DenominatorBudget J6Mesh J6NativeHeightMesh J6NativeHeightResidue

theorem plus_minus_mem (a j : ℕ) (hj : 0<j) (hlt : j < 2^a) :
    ((2:ℚ)^a+j)/((2:ℚ)^a-j) ∈ twoLocalSubalgebra := by
  induction a generalizing j with
  | zero => norm_num at hlt; omega
  | succ a ih =>
    by_cases he : j%2=0
    · let k := j/2
      have hJ : j = 2*k := by dsimp [k]; omega
      have hk : 0 < k := by omega
      have hK : k < 2^a := by rw [pow_succ] at hlt; omega
      have hrat : (j:ℚ) = (k:ℚ)*2 := by
        exact_mod_cast (show j=k*2 by omega)
      have hnon : (2:ℚ)^a-(k:ℚ) ≠ 0 :=
        (sub_pos.mpr (by exact_mod_cast hK)).ne'
      rw [pow_succ,hrat,← add_mul,← sub_mul]
      have hEq :
          (((2:ℚ)^a+k)*2)/(((2:ℚ)^a-k)*2) = ((2:ℚ)^a+k)/((2:ℚ)^a-k) := by
        field_simp
      rw [hEq]
      exact ih k hk hK
    · apply (mem_twoLocal_iff _).mpr
      refine ⟨(2:ℤ)^(a+1)+(j:ℤ),(2:ℤ)^(a+1)-(j:ℤ),?_,by push_cast; rfl⟩
      rintro ⟨d,hd⟩
      have ho : (j:ℤ)%2=1 := by exact_mod_cast (show j%2=1 by omega)
      rw [pow_succ] at hd
      omega

theorem actual_point_mem (m : ℕ) (i : Fin (m+1)) :
    point m i ∈ twoLocalSubalgebra := by
  unfold point LayerRecovery.gridRatio
  apply twoLocalSubalgebra.neg_mem
  apply Subalgebra.prod_mem
  intro j hj
  have ht := (address_index m i).2.2.2
  have hj₀ := Finset.mem_range.mp hj
  have hLt : j+1 < 2^a m := by change index m i < 2^a m at ht; omega
  unfold L
  push_cast
  simpa only [Nat.cast_add,Nat.cast_one] using plus_minus_mem (a m) (j+1) (by omega) hLt

noncomputable def scalar (m : ℕ) (i : Fin (m+1)) : TwoLocal :=
  ⟨point m i,actual_point_mem m i⟩

theorem actual_scalar_clearing {R : Type*} [CommRing R] (f : TwoLocal →+* R)
    (m : ℕ) (i : Fin (m+1)) :
    (sampleDen m i:R)*f (scalar m i) = (sampleNum m i:R) := by
  have hd : sampleDen m i ≠ 0 := (mesh_bounds m i).1.ne'
  exact scalarClearing f _ _ _ hd (mesh_fraction m i)

#print axioms plus_minus_mem
#print axioms actual_point_mem
#print axioms actual_scalar_clearing
end J6NativeHeightDyadic
