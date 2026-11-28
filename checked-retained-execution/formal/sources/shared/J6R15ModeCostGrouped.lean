import J6R15ModeCostPotential
import J6R15ModeCostRoster
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Pool the exact generating product by the printed multiplicity,
then instantiate the abstract bound for one actual P11 packing. The
finite product itself is explicit; no asymptotic simplification is
asserted in this file. -/
namespace J6R15ModeCost
open scoped BigOperators
open J6R10Repack

def weightFactor (r : ℚ) (j : ℕ) : ℚ := (1-r^j)⁻¹

theorem weightFactor_one_le (r : ℚ) (hr : 0≤r) (hR : r<1) (j : ℕ) (hj : 0<j) :
    1≤weightFactor r j := by
  unfold weightFactor
  rw [← one_div]
  apply (le_div_iff₀ (sub_pos.mpr (pow_lt_one₀ hr hR hj.ne'))).mpr
  have h := pow_nonneg hr j
  linarith

theorem potential_grouped (r : ℚ) (hr : 0≤r) (hR : r<1)
    (ws : List ℕ) (p B : ℕ) (hw : ∀ w∈ws,0<w ∧ w<p)
    (hB : ∀ j,ws.count j≤B) :
    potential r ws≤(∏ i ∈ Finset.Ico 1 p,weightFactor r i)^B := by
  have hin : ws.toFinset⊆Finset.Ico 1 p := by
    intro w hw'
    obtain ⟨h1,h2⟩ := hw w (List.mem_toFinset.mp hw')
    exact Finset.mem_Ico.mpr ⟨h1,h2⟩
  change (ws.map (weightFactor r)).prod≤_
  rw [Finset.prod_list_map_count]
  have h := Finset.prod_subset hin (f:=fun i=>weightFactor r i ^ ws.count i)
    (fun i _ notMem => by
      change weightFactor r i ^ ws.count i=1
      rw [List.count_eq_zero_of_not_mem (fun h=>notMem (List.mem_toFinset.mpr h)),pow_zero])
  rw [h,← Finset.prod_pow]
  apply Finset.prod_le_prod
  · intro i hi
    have H := weightFactor_one_le r hr hR i (Finset.mem_Ico.mp hi).1
    exact pow_nonneg (zero_le_one.trans H) _
  · intro i hi
    exact pow_le_pow_right₀ (weightFactor_one_le r hr hR i (Finset.mem_Ico.mp hi).1) (hB i)

theorem native_finite_potential {E R C G : Type*} [Fintype E] [LinearOrder G] [Fintype G]
    {a p : ℕ} {N : Network E R C} (P : PhysicalPacking N a G) (i : Fin a)
    (ms : List (Mode (Crossing (G:=G) (pages:=P.copies) i) (2^(i.val+1)) p))
    (hm : ms.Nodup) (hall : ∀ m,m∈ms) (hp : 0<p) (r : ℚ) (hr : 0<r) (hR : r<1) :
    let B := (6*Nat.card E)/2^(a-i.val)
    ((strictTuples (ms.map modeWeight) p).length:ℚ) ≤
      (∏ j ∈ Finset.Ico 1 p,weightFactor r j)^B / r^(p-1) := by
  classical
  let ws := ms.map modeWeight
  have hw (w : ℕ) (h : w∈ws) : 0<w ∧ w<p := by
    obtain ⟨m,_,rfl⟩ := List.mem_map.mp h
    exact modeWeight_bounds m
  let B := (6*Nat.card E)/2^(a-i.val)
  have hB (j : ℕ) : ws.count j≤B := by
    have H := native_weight_multiplicity P i p j
    have hpos : 0<2^(a-i.val) := by positivity
    change (ms.map modeWeight).count j≤B
    rw [roster_weight_count ms hm hall]
    exact (Nat.le_div_iff_mul_le hpos).mpr H
  refine (strict_tuple_potential r hr hR ws (fun w h=> (hw w h).1) p hp).trans ?_
  exact div_le_div_of_nonneg_right (potential_grouped r hr.le hR ws p B hw hB) (pow_nonneg hr.le _)

#print axioms potential_grouped
#print axioms native_finite_potential
end J6R15ModeCost


