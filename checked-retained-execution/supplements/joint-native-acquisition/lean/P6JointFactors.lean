import P6Joint

open scoped BigOperators Classical Polynomial
open Polynomial NativeProbeRing J8EndToEnd DyadicProbeCompiler

namespace P6Joint
noncomputable section
set_option linter.unusedSectionVars false
variable {K R Ω S : Type*} [CommRing K] [Fintype R] [DecidableEq R] [Fintype Ω]
  [Fintype S] [DecidableEq S]

theorem pinWeightSource_delta (sign x : S → Bool) :
    pinWeightSource sign x = if x = sign then 1 else 0 := by
  apply rationalMap_injective
  rw [pinWeightSource_rational, J8SourceMoment.pinWeight_iff]
  split <;> simp

def partition (weight : Ω → K) (args : Ω → R → Bool → K)
    (mark : Option (R × Bool)) (feat : Ω → K) : K :=
  ∑ x : Ω, (weight x * feat x) *
    ∏ r : R, J8SourceMoment.rowFactor (J8SourceMoment.marker mark r)
      (args x r false) (args x r true)

theorem integralChild_eval_partition (φ : Source[X] →+* K)
    (weight : Ω → Source) (sign : S → Bool)
    (base : ((S → Bool) × Ω) → R → Bool → Source[X]) (mark : Option (R × Bool))
    (feature : ((S → Bool) × Ω) → Source) :
    φ (integralChild weight sign base mark feature) =
    partition (fun x => φ (C (weight x))) (fun x r b => φ (base (sign,x) r b))
      mark (fun x => φ (C (feature (sign,x)))) := by
  simp only [integralChild, partition, pinWeightSource_delta, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single sign]
  · simp [map_prod, J8SourceMoment.map_rowFactor]
  · intro bits _ hn
    simp [hn]
  · simp

theorem partition_plain (weight : Ω → K) (args : Ω → R → Bool → K)
    (feat : Ω → K) :
    partition weight args none feat =
    ∑ x : Ω, (weight x * feat x) *
      ∏ r : R, TargetDerivative.equality (args x r false) (args x r true) := by
  simp [partition, J8SourceMoment.marker, J8SourceMoment.rowFactor, J8SourceMoment.oldEquality_eq]

theorem partition_marked (weight : Ω → K) (args : Ω → R → Bool → K)
    (r₀ : R) (right : Bool) :
    partition weight args (some (r₀,right)) (fun _ => 1) =
    ∑ x : Ω, weight x *
      ((-1 + 2 * args x r₀ (!right)) *
      ∏ r ∈ (Finset.univ : Finset R).erase r₀,
        TargetDerivative.equality (args x r false) (args x r true)) := by
  unfold partition
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ r₀)]
  simp only [mul_one]
  congr 1
  congr 1
  · cases right <;> simp [J8SourceMoment.marker, J8SourceMoment.rowFactor,
      J8SourceMoment.selectedEquality_eq]
  · apply Finset.prod_congr rfl
    intro r hr
    have hn : r₀ ≠ r := Ne.symm (Finset.ne_of_mem_erase hr)
    simp [J8SourceMoment.marker, hn, J8SourceMoment.rowFactor, J8SourceMoment.oldEquality_eq]

#print axioms integralChild_eval_partition
#print axioms partition_plain
#print axioms partition_marked
end
end P6Joint
