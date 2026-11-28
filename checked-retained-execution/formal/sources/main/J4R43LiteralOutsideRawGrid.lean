import J4R43LiteralOutsideUnitStrip

/-! Executable signed-grid order: the actual raw factors are generated
by an integer range, not by choosing an arbitrary finite-set traversal.
The intermediate width holds for every partial derivative product. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P1DyadicGrid DenominatorBudget P1DyadicGridBridge
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5800000

def orderedGrid (a : ℕ) : List ℤ :=
  (List.range (2*2^a)).map (fun j : ℕ=>(j:ℤ)-(2:ℤ)^a)

theorem explicit_grid_count (a : ℕ) : (orderedGrid a).length=2*2^a := by
  simp [orderedGrid]

theorem explicit_grid_mem {a : ℕ} {t : ℤ} : t∈orderedGrid a ↔ t∈grid a := by
  rw [orderedGrid,List.mem_map,mem_grid]
  simp only [pow₂,List.mem_range]
  constructor
  · rintro ⟨j,lt,rfl⟩
    have lb : (0:ℤ)≤j := by positivity
    have hb : (j:ℤ)<2*(2:ℤ)^a := by exact_mod_cast lt
    omega
  · rintro ⟨lo,hi⟩
    let k := t+(2:ℤ)^a
    have nn : 0≤k := by dsimp [k]; omega
    have kk : (k.toNat:ℤ)=k := Int.toNat_of_nonneg nn
    refine ⟨k.toNat,?_,?_⟩
    · have hr : (k.toNat:ℤ)<2*(2:ℤ)^a := by rw [kk]; dsimp [k]; omega
      exact_mod_cast hr
    · rw [kk]; dsimp [k]; omega

theorem explicit_grid_nodup (a : ℕ) : (orderedGrid a).Nodup := by
  unfold orderedGrid
  apply List.Nodup.map
  · intro x y e
    change (x:ℤ)-(2:ℤ)^a=(y:ℤ)-(2:ℤ)^a at e
    have h : (x:ℤ)=(y:ℤ) := by omega
    exact_mod_cast h
  · exact List.nodup_range

def orderedFactors (a : ℕ) (t : ℤ) : List ℤ :=
  (orderedGrid a).filter (fun q=>decide (q≠t))

def orderedDerivative (a : ℕ) (t : ℤ) : List ℤ :=
  (orderedFactors a t).map (t-·)

theorem ordered_factors_membership {a : ℕ} {t q : ℤ} :
    q∈orderedFactors a t ↔ q∈(grid a).erase t := by
  simp [orderedFactors,explicit_grid_mem,and_comm]

theorem ordered_factors_exact (a : ℕ) (t : ℤ) :
    (orderedDerivative a t).prod = ∏ q∈(grid a).erase t,(t-q) := by
  have nd : (orderedFactors a t).Nodup := (explicit_grid_nodup a).filter _
  have e : (orderedFactors a t).toFinset=(grid a).erase t := by
    ext q
    simp only [List.mem_toFinset,ordered_factors_membership]
  unfold orderedDerivative
  rw [←List.prod_toFinset (fun q : ℤ=>t-q) nd,e]

theorem ordered_derivative_actual (a : ℕ) {t : ℤ} :
    (orderedDerivative a t).prod=(derivativeTape a t).prod :=
  (ordered_factors_exact a t).trans
    (Finset.prod_map_toList ((grid a).erase t) (fun q : ℤ=>t-q)).symm

theorem ordered_derivative_len (a : ℕ) {t : ℤ} (mem : t∈grid a) :
    (orderedDerivative a t).length=2*2^a-1 := by
  have q : (orderedFactors a t).toFinset=(grid a).erase t := by
    ext x
    simp [ordered_factors_membership]
  have card := List.toFinset_card_of_nodup ((explicit_grid_nodup a).filter (fun q=>decide (q≠t)))
  change (orderedFactors a t).toFinset.card=(orderedFactors a t).length at card
  rw [orderedDerivative,List.length_map,←card,q]
  have e := derivativeTape_count a mem
  simpa only [derivativeTape,List.length_map,Finset.length_toList] using e

theorem any_partial_product_fits (d : ℕ) (l : List ℤ)
    (fits : ∀ x∈l,|x|≤(2:ℤ)^d) :
    |l.prod|≤(2:ℤ)^(d*l.length) := by
  induction l with
  | nil => simp
  | cons x xs thenP =>
    have A := fits x List.mem_cons_self
    have B := thenP (fun y h=>fits y (List.mem_cons_of_mem _ h))
    rw [List.prod_cons,abs_mul,List.length_cons,Nat.mul_add,mul_one,pow_add]
    calc
      _≤(2:ℤ)^d*(2:ℤ)^(d*xs.length) := mul_le_mul A B (abs_nonneg _) (by positivity)
      _=_ := mul_comm _ _

theorem every_native_derivative_prefix_fits (a : ℕ) {t : ℤ} (mem : t∈grid a) (n : ℕ) :
    |((orderedDerivative a t).take n).prod|≤(2:ℤ)^derivativeWidth a := by
  have wb (x : ℤ) (hx : x∈(orderedDerivative a t).take n) : |x|≤(2:ℤ)^(a+1) := by
    obtain ⟨q,oq,rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hx)
    have h := grid_difference_bounds mem (Finset.mem_erase.mp (ordered_factors_membership.mp oq)).2
    exact (abs_lt.mpr (by simpa [pow₂] using h)).le
  apply (any_partial_product_fits (a+1) _ wb).trans
  apply pow_le_pow_right₀ (by decide)
  unfold derivativeWidth
  rw [←ordered_derivative_len a mem]
  apply Nat.mul_le_mul_left
  simp only [List.length_take]
  exact min_le_right ..

def explicitNormalizeUnit (a : ℕ) (t : ℤ) : StripRun :=
  stripBoth (orderedDerivative a t).prod (orderedDerivative a 0).prod (derivativeWidth a)

theorem explicit_normalize_is_native (a : ℕ) {t : ℤ} (_mem : t∈grid a) :
    explicitNormalizeUnit a t=paidNormalizeUnit a t := by
  unfold explicitNormalizeUnit paidNormalizeUnit
  rw [ordered_derivative_actual a,ordered_derivative_actual a]

#print axioms explicit_grid_count
#print axioms explicit_grid_mem
#print axioms explicit_grid_nodup
#print axioms ordered_factors_exact
#print axioms ordered_derivative_len
#print axioms every_native_derivative_prefix_fits
#print axioms explicit_normalize_is_native
end
end J4R43LiteralOutside

