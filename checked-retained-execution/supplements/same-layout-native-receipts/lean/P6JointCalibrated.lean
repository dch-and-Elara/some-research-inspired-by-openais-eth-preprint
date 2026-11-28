import P6JointGeometryModel

namespace Paper6JointSeating
open scoped Classical Polynomial
open P11FullPacking J7SourceLabels J7PrintedParams J7PrintedParamsGraph
open J7ToJ8Incidence J9R20SameFile J8Physical
noncomputable section
set_option linter.unusedSectionVars false

variable {Pair H : Type} [Fintype Pair] [Fintype H]
variable (ends : H×Bool ≃ Pin Pair×Fin 3)
variable {a b : ℕ} (geom : JointSourceGeometry ends a b)
local notation "N" => Fintype.card (Pin Pair)
local notation "L" => ((2:ℕ)^a)
local notation "M" => Fintype.card (J8Physical.Wire (Subdivision Pair (OrdinaryRow Pair H)))

theorem calibrated_cap :
    let B := (2*(M:ℝ)/6+9*(M:ℝ))/(L:ℕ)
    (M:ℝ)/(6*(L:ℕ)) ≤
      ((min (geom.keep false).card (geom.keep true).card : ℕ) : ℝ) +
        Real.sqrt B + Real.sqrt (((L:ℕ):ℝ)^12*B) := by
  have hM : M=24*N :=
    (Fintype.card_congr (geom.layout.column.trans (colWire (column ends cycle)))).trans (actual_incidence ends).1
  have hE : Fintype.card (Clones Pair) = 4*N := by
    simp [Clones,Index,Fintype.card_prod,Nat.mul_comm]
  have hE' : (Fintype.card (Clones Pair):ℝ) = (M:ℝ)/6 := by
    rw [hE,hM]
    push_cast
    ring
  have hD : Fintype.card (Cell (Fin a) (Fin 64)) = L^12 := by
    have hh := total_cells (K:=Fin 64) (a:=a)
    rw [Nat.card_eq_fintype_card] at hh
    simp only [Fintype.card_fin] at hh
    rw [hh,← pow_mul]
    rw [show 64=(2:ℕ)^6 by decide, ← pow_mul]
    congr 1
    omega
  dsimp only
  rcases le_total (geom.keep false).card (geom.keep true).card with h | h
  · have hh := geom.guard_size false
    simp only [hE',hD,Nat.cast_pow] at hh
    rw [min_eq_left h]
    rw [mul_div_assoc (2:ℝ) (M:ℝ) 6]
    simpa only [Nat.cast_pow, div_div] using hh
  · have hh := geom.guard_size true
    simp only [hE',hD,Nat.cast_pow] at hh
    rw [min_eq_right h]
    rw [mul_div_assoc (2:ℝ) (M:ℝ) 6]
    simpa only [Nat.cast_pow, div_div] using hh

#print axioms calibrated_cap
end
end Paper6JointSeating



