import P5HybridClosureMatching
import Mathlib.Data.Nat.Sqrt

/-! Rational weights that realize the two route-specific scales. No
irrational weights, approximations, or input-dependent choices are needed. -/
namespace Paper5.HybridClosure
open scoped BigOperators Classical
open CommonMatchingSelection

def weightDen (k : ℕ) : ℕ := k.sqrt+1
def routeWeight (k : ℕ) : ℚ := 1/(weightDen k:ℚ)
def matchingCoeff (γ : ℚ) : ℚ := rate 36*γ^2/6144
def routeDepth (γ : ℚ) (N k : ℕ) : ℕ := ⌊matchingCoeff γ*(N:ℚ)*routeWeight k⌋₊

theorem weightDen_pos (k : ℕ) : 0<(weightDen k:ℚ) := by
  unfold weightDen
  positivity

theorem weightDen_squared (k : ℕ) (hk : 0<k) :
    k < weightDen k^2 ∧ weightDen k^2≤4*k := by
  refine ⟨Nat.lt_succ_sqrt' k,?_⟩
  have h := Nat.sqrt_le' k
  have hk' := Nat.sqrt_pos.mpr hk
  have hh : k.sqrt+1≤2*k.sqrt := by omega
  calc
    _ ≤ (2*k.sqrt)^2 := Nat.pow_le_pow_left hh 2
    _ = 4*k.sqrt^2 := by ring
    _ ≤ _ := Nat.mul_le_mul_left 4 h

theorem routeWeight_pos (k : ℕ) : 0<routeWeight k :=
  one_div_pos.mpr (weightDen_pos k)

theorem routeWeight_le_one (k : ℕ) : routeWeight k≤1 := by
  apply (div_le_iff₀ (weightDen_pos k)).2
  simp [weightDen]

theorem routeWeight_square_scale (k : ℕ) :
    routeWeight k^2*(k:ℚ)≤1 := by
  have hW : (k:ℚ)≤(weightDen k:ℚ)^2 := by exact_mod_cast (Nat.lt_succ_sqrt' k).le
  unfold routeWeight
  rw [div_pow,one_pow,div_mul_eq_mul_div,one_mul]
  exact (div_le_iff₀ (pow_pos (weightDen_pos k) 2)).mpr (by simpa using hW)

theorem matchingCoeff_pos (γ : ℚ) (hγ : 0<γ) : 0<matchingCoeff γ := by
  unfold matchingCoeff
  have h := rate_pos 36
  positivity

theorem normalized_matching_margin {V : Type*} [Fintype V] (F : Finset (V×V))
    (hF : 2*F.card=3*Fintype.card V) (γ : ℚ) (k : ℕ) :
    rate 36*(3*(γ/6)^2*(F.card:ℚ)*routeWeight k/(64*(12:ℚ))) =
      matchingCoeff γ*(Fintype.card V:ℚ)*routeWeight k := by
  have h : (F.card:ℚ)=3*(Fintype.card V:ℚ)/2 := by
    have h' : 2*(F.card:ℚ)=3*(Fintype.card V:ℚ) := by exact_mod_cast hF
    linarith only [h']
  rw [h]
  unfold matchingCoeff
  ring

theorem routeDepth_margin (γ : ℚ) (hγ : 0<γ) (N k : ℕ) :
    (routeDepth γ N k:ℚ) ≤ matchingCoeff γ*(N:ℚ)*routeWeight k ∧
      matchingCoeff γ*(N:ℚ)*routeWeight k < (routeDepth γ N k:ℚ)+1 := by
  have h := matchingCoeff_pos γ hγ
  have hw := routeWeight_pos k
  exact ⟨Nat.floor_le (by positivity),Nat.lt_floor_add_one _⟩

theorem one_route_union_test (c : ℚ) (hc : 0<c) (N k : ℕ) (hN : 0<N) (hk : 0<k) :
    (k:ℚ)*(7776*(N:ℚ))/(c*(N:ℚ)*routeWeight k)^2 ≤
      31104*(k:ℚ)^2/(c^2*(N:ℚ)) := by
  let n : ℚ := N
  let d : ℚ := weightDen k
  have hn : 0<n := by dsimp [n]; exact_mod_cast hN
  have hd : 0<d := weightDen_pos k
  have hu : d^2≤4*(k:ℚ) := by dsimp [d]; exact_mod_cast (weightDen_squared k hk).2
  change (k:ℚ)*(7776*n)/(c*n*(1/d))^2 ≤ _
  have hId : (k:ℚ)*(7776*n)/(c*n*(1/d))^2 =
      (7776*(k:ℚ)*d^2)/(c^2*n) := by field_simp [hc.ne',hn.ne',hd.ne']
  rw [hId]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hh := mul_le_mul_of_nonneg_left hu (show 0≤7776*(k:ℚ) by positivity)
  nlinarith only [hh]

theorem two_route_union_test (c : ℚ) (hc : 0<c) (N Q u : ℕ) (hN : 0<N) (hQ : 0<Q) (hu : 0<u)
    (h : 31104*((Q:ℚ)^2+(u:ℚ)^2)<c^2*(N:ℚ)) :
    (Q:ℚ)*(7776*(N:ℚ))/(c*(N:ℚ)*routeWeight Q)^2+
      (u:ℚ)*(7776*(N:ℚ))/(c*(N:ℚ)*routeWeight u)^2<1 := by
  apply (add_le_add (one_route_union_test c hc N Q hN hQ) (one_route_union_test c hc N u hN hu)).trans_lt
  rw [←add_div]
  apply (div_lt_iff₀ (by positivity : (0:ℚ)<c^2*(N:ℚ))).2
  nlinarith only [h]

#print axioms weightDen_squared
#print axioms routeWeight_square_scale
#print axioms normalized_matching_margin
#print axioms routeDepth_margin
#print axioms one_route_union_test
#print axioms two_route_union_test
end Paper5.HybridClosure