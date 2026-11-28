import J9EndCoefficient

/-! Concrete physical outer layout fed into the actual printed
J9 schedule, without externally supplied parity or hit bounds. -/

namespace J9End
open scoped BigOperators Polynomial Classical
open Polynomial

noncomputable section

variable {Packet R S V G : Type*} {P : V → Type*}
variable [Fintype R] [DecidableEq R] [Fintype Packet] [DecidableEq Packet] [DecidableEq G]

theorem printed_physical_center
    (s M p b : ℕ)
    (d : J8Physical.Layout Packet R S V G P (J9PrintedSchedule.rootL (Nat.clog 2 s)))
    (e : J8Physical.EndpointSeating d) (anchor : S)
    (idx : J8Physical.Wire R ≃ Fin M)
    (tables : LiteralPortCompiler.CNF (Fin M))
    (hLambda : 262144 ≤ Nat.clog 2 s)
    (hActive : J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) < M)
    (hP : 0 < p) (hb : b < J9PrintedSchedule.rootL (Nat.clog 2 s))
    (capacity : J9PrintedSchedule.rootL (Nat.clog 2 s) * Fintype.card Packet ≤ 3*M)
    (rows : (Fin M → Bool) → R → Bool → ℚ[X])
    (cross : Fin (J9PrintedSchedule.rootL (Nat.clog 2 s)) → ℚ[X])
    (source : (Fin M → Bool) → ℚ[X]) :
    let lambda := Nat.clog 2 s
    let L := J9PrintedSchedule.rootL lambda
    let u := J9PrintedSchedule.rootU lambda
    let a := J9PrintedSchedule.rootA lambda
    let pt := J9PrintedSchedule.precision p ((3*M+u-1)/u) L M a
    let g := chart d anchor idx (LiteralPortCompiler.satisfied tables)
    let modulus := (2:ℤ)^(10*M)
    10*M < pt ∧ 10*M+1 ≤ J9PrintedSchedule.probeCount M L ∧
      Odd (J9FactorBounds.publicDenominator g b) ∧
      (J9FactorBounds.exactCleared g b)*2 ∈ Set.Ioc (-modulus) modulus ∧
      ∀ z : ℤ, modulus ∣ z - J9FactorBounds.exactCleared g b →
        J9FactorBounds.centerResidue modulus z = J9FactorBounds.exactCleared g b ∧
        (J9FactorBounds.centerResidue modulus z : ℚ) /
            J9FactorBounds.publicDenominator g b = (literalCompleted g b rows cross source).coeff 1 := by
  dsimp only
  let truth := LiteralPortCompiler.satisfied tables
  let g := chart d anchor idx truth
  have hpar : ∀ i ∈ g.targets, i.val%2 = g.tau.val%2 := by
    intro i hi
    rw [Nat.mod_eq_of_lt g.tau.isLt]
    exact chart_parity d anchor idx truth i hi
  rw [literal_first_exact]
  exact J9FactorBounds.printed_center_recover s M p b g hLambda hActive hP hb
    hpar (chart_tile_injective d anchor idx truth)
    (chart_one_hit d anchor idx truth e) (chart_active_rows_budget d anchor idx truth capacity)

#print axioms printed_physical_center

end
end J9End

