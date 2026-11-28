import J9R14LowPrecisionGeometry
import J8Physical
import Mathlib.Data.ZMod.Basic

/-!
# Touching, signs, and the necessity of literal linear tails

At the outer centre the actual endpoint layout forbids a shift into
a pin. A whole tile can also contain ordinary columns; their touched
status must still be checked. A pinned bit is never counted as one of
the free independent equality bits. Conversely an arbitrary nonlinear
higher tail is not the source input, and need not obey the bound.
-/

namespace J9R14LowPrecisionScope
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget J9R14LowPrecisionGeometry

noncomputable section

section Geometry
open J8Physical
variable {P R S V G : Type*} {A : V→Type*} {L : ℕ}

theorem pin_constant_zero (d : Layout P R S V G A L) (e : EndpointSeating d)
    (a : ℕ) (take : Wire R→Wire R→Prop) (r : Wire R) (s : S) :
    (coeffEntry (⟨d.seat,d.seat⟩ : Seats P (Wire R) (Wire R) L)
      a ((L:ℤ)-1) take r (pinWire d s)).coeff 0=0 := by
  rw [coeff_entry_constant]
  apply if_neg
  intro h
  apply shift_reads_no_pins d e s r
  refine ⟨h.1.1.symm,?_⟩
  have he := h.2
  dsimp only at he ⊢
  omega

end Geometry

def forbiddenTail (s : Finset (Fin 2)) : ℤ[X] := if s=Finset.univ then X else 0

theorem all_zero_constants (s : Finset (Fin 2)) : (forbiddenTail s).coeff 0=0 := by
  by_cases h : s=Finset.univ <;> simp [forbiddenTail,h]

theorem forbidden_tail_sum : (∑ s : Finset (Fin 2), forbiddenTail s) = X := by
  rw [Finset.sum_eq_single (Finset.univ : Finset (Fin 2))]
  · simp [forbiddenTail]
  · intro s _ hs
    simp [forbiddenTail,hs]
  · simp

theorem forbidden_hCoeff :
    ¬ (2:ℤ)^(2-0-1:ℕ) ∣ (∑ s : Finset (Fin 2), forbiddenTail s).coeff 1 := by
  rw [forbidden_tail_sum]
  norm_num

theorem forbidden_menu_survives :
    (∑ s : Finset (Fin 2), forbiddenTail s).eval₂ (Int.castRingHom (ZMod 4)) (2:ZMod 4) ≠ 0 := by
  rw [forbidden_tail_sum,Polynomial.eval₂_X]
  decide

#print axioms pin_constant_zero
#print axioms all_zero_constants
#print axioms forbidden_hCoeff
#print axioms forbidden_menu_survives

end
end J9R14LowPrecisionScope
