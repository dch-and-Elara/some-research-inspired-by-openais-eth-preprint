import V8CapacitySpecialFrobenius
import V8CapacitySpecialResidueCapacity

/-! Substitute pi=0 in the actual centered feature, not in a surrogate.
The precision-1 active test becomes nonzero ordinary residue polynomial. -/
namespace V8CapacitySpecialJ6Source
open scoped Polynomial Classical BigOperators
open Polynomial V8CapacityFeatures V8CapacitySymbolic V8CapacityNativeMatrix

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {O K H : Type*} [CommRing O] [CommRing K] [Fintype H]

theorem map_symbolic_input (ρ : O →+* K) (k : ℕ) (i : H) (r : ℕ) :
    MvPolynomial.map ρ (symInput (R:=O) k i r)=symInput (R:=K) k i r := by
  unfold symInput
  split_ifs
  · exact MvPolynomial.map_X _ _
  · exact map_zero _

theorem map_shifted_symbolic (ρ : O →+* K) (π : O) (k : ℕ) (i : H) :
    (shiftedPolynomial (MvPolynomial.C π) k (symInput (R:=O) k i)).map (MvPolynomial.map ρ) =
      shiftedPolynomial (MvPolynomial.C (ρ π)) k (symInput (R:=K) k i) := by
  simp only [shiftedPolynomial,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,
    Polynomial.map_X,Polynomial.map_sum,Polynomial.map_pow,map_mul,MvPolynomial.map_C,
    map_symbolic_input]

theorem map_symbolic_feature (ρ : O →+* K) (π : O) (k : ℕ) (a : H → ℕ) (j : ℕ) :
    MvPolynomial.map ρ (feature π k a j)=feature (ρ π) k a j := by
  unfold feature rawFeature
  rw [← Polynomial.coeff_map]
  simp only [Polynomial.map_prod,Polynomial.map_pow,map_shifted_symbolic]

variable [IsDomain O] [IsLocalRing O]

local notation "κ" => IsLocalRing.ResidueField O
local notation "res" => IsLocalRing.residue O

theorem active_iff_residue_nonzero (π : O) (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
    (k : ℕ) (i : Box H 1 k) :
    active π 1 k i ↔ MvPolynomial.map res (symCol π 1 k i)≠0 := by
  constructor
  · rintro ⟨d,hd⟩ hz
    have he := congrArg (MvPolynomial.coeff d) hz
    rw [MvPolynomial.coeff_map,MvPolynomial.coeff_zero] at he
    have hm := (IsLocalRing.residue_eq_zero_iff _).mp he
    rw [hMax,Ideal.mem_span_singleton] at hm
    exact hd (by simpa only [pow_one] using hm)
  · intro hn
    unfold active
    by_contra! hd
    apply hn
    ext d
    rw [MvPolynomial.coeff_map,MvPolynomial.coeff_zero,IsLocalRing.residue_eq_zero_iff,
      hMax,Ideal.mem_span_singleton]
    exact by simpa only [pow_one] using hd d

theorem active_iff_zero_constant (π : O) (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
    (k : ℕ) (i : Box H 1 k) :
    active π 1 k i ↔ feature (0:κ) k (α 1 k i) i.2.val≠0 := by
  rw [active_iff_residue_nonzero π hMax]
  have hz : res π=0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr (by rw [hMax,Ideal.mem_span_singleton])
  unfold symCol
  split_ifs with hi
  · rw [map_symbolic_feature,hz]
  · rw [map_zero]
    have j := i.2.isLt
    have hh : i.2.val<∑ i' : H, α 1 k i i' := by unfold DegreeCap at hi; omega
    rw [V8CapacitySpecialFrobenius.feature_below_order_zero (α 1 k i) i.2 hh]

#print axioms map_symbolic_feature
#print axioms active_iff_residue_nonzero
#print axioms active_iff_zero_constant
end
end V8CapacitySpecialJ6Source

