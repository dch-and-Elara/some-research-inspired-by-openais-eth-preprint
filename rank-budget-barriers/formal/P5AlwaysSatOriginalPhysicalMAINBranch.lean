import P5AlwaysSatOriginalPhysicalSparsePorts
import P5AlwaysSatOriginalPhysicalMAINNumbers

/-! The actual printed degree threshold fixes no copy in the sparse
(M.7) branch. This uses its real G-scope count, not a caller-selected
value of the threshold. -/
namespace Paper5.AlwaysSatOriginal.Physical
open scoped BigOperators Classical
open P5MainBalance

variable {V : Type*} [Fintype V]
variable (E : Finset (V×V)) (T : Finset V)

theorem sparse_exact_relative_count :
    Fintype.card (SparsePort E T)=4*Fintype.card (Port E T)-2 := by
  rw [Fintype.card_sum,port_card,cycle_slots_card]
  have hp := original_port_card E T
  omega

noncomputable def sparseHeavyThreshold : ℕ :=
  ⌈(Fintype.card (SparsePort E T):ℝ)/Fintype.card (Port E T)⌉₊ *
    ⌈Real.sqrt (mainLambda (Fintype.card (Port E T)):ℝ)⌉₊

theorem sparse_printed_average_ceil (hn : 3≤Fintype.card (Port E T)) :
    ⌈(Fintype.card (SparsePort E T):ℝ)/Fintype.card (Port E T)⌉₊=4 := by
  let M : ℕ := Fintype.card (SparsePort E T)
  let n : ℕ := Fintype.card (Port E T)
  have h := sparse_exact_relative_count E T
  change M=4*n-2 at h
  have hn' : 3≤n := hn
  have hnR : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hhi : M≤4*n := by omega
  have hlo : 3*n<M := by omega
  have h₁ : ⌈(M:ℝ)/n⌉₊≤4 := by
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hnR).mpr
    exact_mod_cast hhi
  have h₂ : 3<⌈(M:ℝ)/n⌉₊ := by
    apply Nat.lt_ceil.mpr
    apply (lt_div_iff₀ hnR).mpr
    exact_mod_cast hlo
  exact Nat.le_antisymm h₁ (Nat.succ_le_of_lt h₂)

noncomputable def sparseHeavy : Finset (Port E T) :=
  Finset.univ.filter (fun p=>sparseHeavyThreshold E T <
    Nat.card {e : SparsePort E T // sparseOwner E T e=p})

theorem sparse_printed_heavy_empty (hn : 3≤Fintype.card (Port E T)) :
    sparseHeavy E T=∅ := by
  let n := Fintype.card (Port E T)
  have hLambda : 1≤mainLambda n := by
    rw [mainLambda_as_clog]
    apply Nat.succ_le_of_lt
    apply (Nat.lt_clog_iff_pow_lt (by decide : 1<(2:ℕ))).mpr
    change 1<n
    omega
  have hReal : (1:ℝ)≤mainLambda n := by exact_mod_cast hLambda
  have hR := Real.sqrt_le_sqrt hReal
  rw [Real.sqrt_one] at hR
  have hceil : 1≤⌈Real.sqrt (mainLambda n:ℝ)⌉₊ := by
    exact_mod_cast hR.trans (Nat.le_ceil _)
  have hb : 4≤sparseHeavyThreshold E T := by
    rw [sparseHeavyThreshold,sparse_printed_average_ceil E T hn]
    exact by simpa only [mul_one] using Nat.mul_le_mul_left 4 hceil
  ext v
  simp only [sparseHeavy,Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false]
  exact not_lt.mpr ((sparse_copy_degree_le E T v).trans hb)

#print axioms sparse_exact_relative_count
#print axioms sparse_printed_average_ceil
#print axioms sparse_printed_heavy_empty
end Paper5.AlwaysSatOriginal.Physical