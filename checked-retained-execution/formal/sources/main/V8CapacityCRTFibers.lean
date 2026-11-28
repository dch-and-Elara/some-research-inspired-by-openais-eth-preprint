import V8CapacityCRT
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Exact simultaneous realization of all residue fiber polynomial
columns, including projected outputs. This closes the independent-fiber
part of v8 A3/A4 without assuming that separate Taylor coefficients are
linearly independent. -/
namespace V8CapacityCRT
open scoped Polynomial Classical BigOperators

noncomputable section
variable {O S I H : Type*} [CommRing O] [CommRing S]
variable [Fintype I] [DecidableEq I] [Fintype H]
variable (φ : O →+* S) (d : I → O) (sep : ∀ a b, a≠b → IsUnit (d a-d b))
variable (n : ℕ)

def fiberSelector (a : H → I) : MvPolynomial H O :=
  ∏ e : H, (selector d sep n (a e)).eval₂ MvPolynomial.C (MvPolynomial.X e)

theorem fiber_selector_exact (a want : H → I) (x : H → S)
    (hx : ∀ e, (x e-φ (d (a e)))^n=0) :
    MvPolynomial.eval₂Hom φ x (fiberSelector d sep n want) = if a=want then 1 else 0 := by
  let E := MvPolynomial.eval₂Hom φ x
  change E (fiberSelector d sep n want) = _
  rw [fiberSelector,map_prod]
  have h (e : H) :
      E ((selector d sep n (want e)).eval₂ MvPolynomial.C (MvPolynomial.X e)) =
        if a e=want e then 1 else 0 := by
    rw [Polynomial.hom_eval₂]
    have hc : E.comp MvPolynomial.C = φ := RingHom.ext (fun j => MvPolynomial.eval₂Hom_C _ _ _)
    rw [hc]
    change (selector d sep n (want e)).eval₂ φ (MvPolynomial.eval₂Hom φ x (MvPolynomial.X e)) = _
    have hx₀ : (MvPolynomial.eval₂Hom φ x) (MvPolynomial.X e)=x e := by simp
    rw [hx₀]
    exact selector_at_nilpotent φ d sep n (want e) (a e) (x e) (hx e)
  simp only [h]
  by_cases hh : a=want
  · rw [if_pos hh]
    exact Finset.prod_eq_one (fun e _ => if_pos (congrFun hh e))
  · rw [if_neg hh]
    obtain ⟨e,he⟩ := not_forall.mp (fun np => hh (funext np))
    exact Finset.prod_eq_zero (Finset.mem_univ e) (if_neg he)

def glue (C : (H → I) → MvPolynomial H O) : MvPolynomial H O :=
  ∑ a : H → I, fiberSelector d sep n a*C a

theorem glue_exact (C : (H → I) → MvPolynomial H O) (a : H → I) (x : H → S)
    (hx : ∀ e, (x e-φ (d (a e)))^n=0) :
    MvPolynomial.eval₂Hom φ x (glue d sep n C) = MvPolynomial.eval₂Hom φ x (C a) := by
  simp only [glue,map_sum,map_mul, fiber_selector_exact φ d sep n a _ x hx]
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
  · simp
  · intro b _ hb
    simp only [if_neg (Ne.symm hb),zero_mul]

include sep in
/-- Every fiber can be specified separately, and one integral source C
realizes all of them at once after any fixed output function. No assumption
on the value distribution or linearity of that function is needed. -/
theorem raw_fiber_product {U : (H → I) → Type*} {D : Type*}
    (jet : ∀ a, U a → H → S) (calcOutput : S → D) (goal : ∀ a, U a → D)
    (hJet : ∀ a (u : U a) e, (jet a u e-φ (d (a e)))^n=0) :
    (∃ C : MvPolynomial H O, ∀ a u, calcOutput (MvPolynomial.eval₂Hom φ (jet a u) C)=goal a u) ↔
      (∀ a, ∃ C : MvPolynomial H O, ∀ u, calcOutput (MvPolynomial.eval₂Hom φ (jet a u) C)=goal a u) := by
  constructor
  · rintro ⟨C,hC⟩ a
    exact ⟨C,hC a⟩
  · intro hC
    choose C h using hC
    refine ⟨glue d sep n C,fun a u => ?_⟩
    rw [glue_exact φ d sep n C a (jet a u) (hJet a u)]
    exact h a u

include sep in
/-- Actual double-truncated jet charts use `π times constant-digit` plus
`z times the higher coefficients`; no CRT membership oracle is assumed. -/
theorem raw_double_truncated_product {U : (H → I) → Type*} {D : Type*}
    (P k : ℕ) (π z : S) (hπ : π^P=0) (hz : z^k=0)
    (constantDigit higher : ∀ a, U a → H → S)
    (calcOutput : S → D) (goal : ∀ a, U a → D) :
    let jet := fun a u e => φ (d (a e)) + (π*constantDigit a u e+z*higher a u e)
    (∃ C : MvPolynomial H O, ∀ a u, calcOutput (MvPolynomial.eval₂Hom φ (jet a u) C)=goal a u) ↔
      (∀ a, ∃ C : MvPolynomial H O, ∀ u, calcOutput (MvPolynomial.eval₂Hom φ (jet a u) C)=goal a u) := by
  dsimp only
  refine raw_fiber_product φ d sep (P+k-1) _ calcOutput goal (fun a u e => ?_)
  rw [add_sub_cancel_left]
  exact two_ideal_power π z _ _ P k hπ hz

#print axioms fiber_selector_exact
#print axioms glue_exact
#print axioms raw_fiber_product
#print axioms raw_double_truncated_product
end
end V8CapacityCRT
