import HermiteLossCount
import HermiteLossArithmetic

/-! The actual retained node multiplicities beat the source degree
bound. All L odd signed nodes are included; no cardinal assumption. -/

namespace HermiteLoss
open P1DyadicGrid
open scoped BigOperators

def retained (a u h : ℕ) : Finset ℤ :=
  ((grid a).erase 0).filter fun t => 0 < taper u h (level t)

theorem retained_mem {a u h : ℕ} {t : ℤ} :
    t∈retained a u h ↔ t∈grid a ∧ t≠0 ∧ 0<taper u h (level t) := by
  simp only [retained,Finset.mem_filter,Finset.mem_erase]
  tauto

theorem actual_hermite_degree {a u M : ℕ} (hu : 0<u) (hM : u≤M) :
    M*(2*(2:ℕ)^a-1) < ∑ t∈retained a u (sourceH M u),
      taper u (sourceH M u) (level t) := by
  let h := sourceH M u
  let L : ℕ := 2^a
  have hMu : 0<M := hu.trans_le hM
  have hHC := h_cover M u hu
  change 3*M≤h*u at hHC
  have hp : 0<h := by
    by_contra! hn
    have hz : h=0 := by omega
    rw [hz, zero_mul] at hHC
    omega
  have hsubset : levelCell a 0 ⊆ retained a u h := by
    intro t ht
    obtain ⟨hg,hz,hi⟩ := mem_levelCell.mp ht
    refine retained_mem.mpr ⟨hg,hz,?_⟩
    rw [hi]
    exact (nonzero_node_active u h 0 hp).mpr hu
  have hOdd :
      (∑ t∈levelCell a 0, taper u h (level t)) = L*(h*u) := by
    calc
      _ = ∑ _t∈levelCell a 0, h*u := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [(mem_levelCell.mp ht).2.2,taper,Nat.sub_zero]
      _ = _ := by
        rw [Finset.sum_const,nsmul_eq_mul,level_card (Nat.zero_le _),Nat.sub_zero]
        rfl
  have hL : 0<L := by dsimp [L]; positivity
  calc
    _ < M*(3*L) := Nat.mul_lt_mul_of_pos_left (by omega) hMu
    _ = L*(3*M) := by ring
    _ ≤ L*(h*u) := Nat.mul_le_mul_left _ hHC
    _ = ∑ t∈levelCell a 0, taper u h (level t) := hOdd.symm
    _ ≤ _ := Finset.sum_le_sum_of_subset hsubset

#print axioms actual_hermite_degree
end HermiteLoss

