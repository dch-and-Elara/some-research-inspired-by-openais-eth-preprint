import P6JointPartition
import P6SeparatorCost

open scoped BigOperators Classical Polynomial
open Polynomial NativeProbeRing J8Physical J8EndToEnd J8J9Grouped DyadicProbeCompiler

namespace P6Joint
open BoundaryPlan
noncomputable section
set_option linter.unusedSectionVars false
variable {D Ω R K : Type*} [Fintype D] [Fintype Ω] [Fintype R] [DecidableEq R] [CommRing K]

/-- The explicit table-plan witness for a local partition consists of an
assignment correspondence and pointwise factor equality, rather than a
premise that the two partition sums already agree. -/
structure PartitionPlan (widthCap : ℕ) (weight : Ω → K) (args : Ω → R → Bool → K)
    (mark : Option (R × Bool)) (feat : Ω → K) where
  plan : BoundaryPlan D K 0
  width_ok : width plan ≤ widthCap
  assignments : Ω ↪ Config plan
  factors_eq : ∀ x, raw plan Fin.elim0 (assignments x) =
      (weight x * feat x) * ∏ r : R,
        J8SourceMoment.rowFactor (J8SourceMoment.marker mark r) (args x r false) (args x r true)

  zeroOutside : ∀ c, c ∉ Set.range assignments → raw plan Fin.elim0 c = 0

theorem PartitionPlan.exact_value_and_cost
    {w : ℕ} {weight : Ω → K} {args : Ω → R → Bool → K}
    {mark : Option (R × Bool)} {feat : Ω → K}
    (plan : PartitionPlan (D := D) w weight args mark feat)
    (hD : 0 < Fintype.card D) (hD8 : Fintype.card D ≤ 8) :
    denotation plan.plan Fin.elim0 = partition weight args mark feat ∧
      tableOps plan.plan ≤ nodes plan.plan * 8^w := by
  constructor
  · exact from_padded_assignment plan.plan Fin.elim0 plan.assignments _ plan.factors_eq plan.zeroOutside
  · exact (tableOps_le plan.plan plan.width_ok hD).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hD8 _))

#print axioms PartitionPlan.exact_value_and_cost
end
noncomputable section
section Physical
variable {K : Type*} [CommRing K]
variable {Packet R S V G : Type*} {P : V → Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

abbrev PhysicalGroupPlan (F : OldTables d) (base : IntegralArguments d)
    (sign : S → Bool) (g : G) (φ : Source[X] →+* K) (w : ℕ)
    (mark : Option (LocalRow d g × Bool)) (feature : ((LocalPin d g → Bool) × LocalBits d g) → Source) :=
  PartitionPlan (D := Fin 8) w (fun x => φ (C (physicalTableWeight d F g x)))
    (fun x r b => φ (base g ((fun i => sign i.1),x) r b))
    mark (fun x => φ (C (feature ((fun i => sign i.1),x))))

omit [Fintype S] [DecidableEq S] [Fintype G] [Fintype Packet] [DecidableEq Packet] in
theorem PhysicalGroupPlan.correct (F : OldTables d) (base : IntegralArguments d)
    (sign : S → Bool) (g : G) (φ : Source[X] →+* K) (w : ℕ)
    (mark : Option (LocalRow d g × Bool)) (feature : ((LocalPin d g → Bool) × LocalBits d g) → Source)
    (p : PhysicalGroupPlan d F base sign g φ w mark feature) :
    denotation p.plan Fin.elim0 = groupPartition d F base sign g φ mark feature ∧
      tableOps p.plan ≤ nodes p.plan * 8^w :=
  p.exact_value_and_cost (by simp) (by simp)

#print axioms PhysicalGroupPlan.correct
end Physical

end
end P6Joint
