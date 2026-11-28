import J8EndToEndConstants
import J9FactorBoundsMesh

/-!
The two independently formalized meshes are the same finite grid. This
connects the integer amplitude used by the J9 magnitude certificate to
the actual J8 physical center and removes a separate amplitude premise.
-/

namespace J8EndToEnd

open scoped BigOperators Polynomial Classical
open Polynomial J8Physical J9FactorBounds

def meshIndex (L : ℕ) : ℕ ↪ ℤ :=
  ⟨fun i => (i:ℤ) - L, by
    intro i j h
    change (i:ℤ) - L = (j:ℤ) - L at h
    omega⟩

theorem grid_reindex (L : ℕ) :
    printedGrid L = (Finset.range (2*L)).map (meshIndex L) := by
  ext j
  simp only [printedGrid, Finset.mem_Ico, Finset.mem_map, Finset.mem_range]
  constructor
  · intro h
    let i := (j+(L:ℤ)).toNat
    have hi : (i:ℤ) = j+(L:ℤ) := by
      exact Int.toNat_of_nonneg (by omega)
    refine ⟨i, by omega, ?_⟩
    change (i:ℤ) - L = j
    omega
  · rintro ⟨i, hi, rfl⟩
    change -(L:ℤ) ≤ (i:ℤ)-L ∧ (i:ℤ)-L < L
    omega

theorem derivativeProduct_reindex (L r : ℕ) :
    derivativeProduct L ((r:ℤ)-L) = (meshSlope (2*L) r : ℚ) := by
  unfold derivativeProduct meshSlope
  have h : ((r : ℤ)-L) = meshIndex L r := rfl
  rw [grid_reindex, h, ← Finset.map_erase, Finset.prod_map, Int.cast_prod]
  apply Finset.prod_congr rfl
  intro i hi
  change (((r:ℤ)-L-((i:ℤ)-L) : ℤ) : ℚ) = (((r:ℤ)-i:ℤ):ℚ)
  congr 1
  omega

/-- This is exactly the mesh ratio on physical addresses, not an upper
bound imposed on an otherwise free certificate coefficient. -/
theorem printed_amplitude_integral (L : ℕ) (hL : 1 ≤ L) (even : Even L) :
    (J9FactorBounds.kernel L : ℚ) = outerAmplitude L := by
  have heven : L % 2 = 0 := by obtain ⟨i,hi⟩ := even; omega
  have h₀ : L < 2*L := by omega
  have h₁ : 2*L-1 < 2*L := by omega
  have hz : ((L:ℕ):ℤ)-L = 0 := by omega
  have ht : ((2*L-1:ℕ):ℤ)-L = ((L:ℤ)-1) := by omega
  have hzero := nativeMesh_derivative_at_index L L h₀
  have htop := nativeMesh_derivative_at_index L (2*L-1) h₁
  rw [hz] at hzero
  rw [ht] at htop
  have rz := derivativeProduct_reindex L L
  have rt := derivativeProduct_reindex L (2*L-1)
  rw [hz] at rz
  rw [ht] at rt
  rw [kernel_is_literal_grid_ratio L hL heven, htop, hzero, outerAmplitude, rt, rz]

#print axioms grid_reindex
#print axioms derivativeProduct_reindex
#print axioms printed_amplitude_integral

end J8EndToEnd
