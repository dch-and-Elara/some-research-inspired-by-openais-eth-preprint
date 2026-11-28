import P6SeparatorCost

open scoped BigOperators Classical
namespace P6Joint
open BoundaryPlan
noncomputable section

variable {I J P S T D K : Type*} [Fintype I] [Fintype J] [Fintype D]
  [CommRing K]

/-- One mode reuses the same per-probe child table pool by address.
Kernels and source weight powers are created by the source's coefficient
routines outside this finite-ring assembler. -/
structure SlotRequests (I P S T K : Type*) where
  siblings : Finset P
  sourcePorts : Finset S
  targetPorts : Finset T
  siblingAddress : P → I
  sourceAddress : S → I
  targetAddress : T → I
  sourceWeight : S → K
  targetWeight : T → K

def SlotRequests.assemble (r : SlotRequests I P S T K) (read : I → K) : K :=
  ((∏ p ∈ r.siblings, read (r.siblingAddress p)) *
  (∑ s ∈ r.sourcePorts, r.sourceWeight s * read (r.sourceAddress s))) *
  (∑ t ∈ r.targetPorts, r.targetWeight t * read (r.targetAddress t))

def SlotRequests.assemblyOps (r : SlotRequests I P S T K) : ℕ :=
  r.siblings.card + 2*r.sourcePorts.card + 2*r.targetPorts.card + 2

omit [Fintype I] in theorem SlotRequests.assemble_pool_correct
    (r : SlotRequests I P S T K) {ar : I → ℕ}
    (p : ∀ i, BoundaryPlan D K (ar i)) (x : ∀ i, Fin (ar i) → D)
    (v : I → K) (h : ∀ i, denotation (p i) (x i) = v i) :
    r.assemble (fun i => denotation (p i) (x i)) = r.assemble v := by
  simp only [h]

omit [Fintype I] [Fintype J] [Fintype D] [CommRing K] in
theorem SlotRequests.assemblyOps_le
    (r : SlotRequests I P S T K) (M : ℕ)
    (hp : r.siblings.card ≤ 64) (hs : r.sourcePorts.card ≤ M)
    (ht : r.targetPorts.card ≤ M) :
    r.assemblyOps ≤ 66 + 4*M := by
  unfold SlotRequests.assemblyOps
  omega

omit [CommRing K] in theorem capped_pool_and_assembly_cost
    {ar : I → ℕ} (p : ∀ i, BoundaryPlan D K (ar i))
    (r : J → SlotRequests I P S T K) (w tariff M : ℕ)
    (hw : ∀ i, width (p i) ≤ w)
    (hD : 0 < Fintype.card D) (hD8 : Fintype.card D ≤ 8)
    (hp : ∀ j, (r j).siblings.card ≤ 64)
    (hs : ∀ j, (r j).sourcePorts.card ≤ M)
    (ht : ∀ j, (r j).targetPorts.card ≤ M) :
    (∑ i, tableOps (p i) * tariff) + (∑ j, (r j).assemblyOps * tariff) ≤
      ((∑ i, nodes (p i)) * 8^w + Fintype.card J * (66 + 4*M)) * tariff := by
  classical
  rw [Nat.add_mul]
  apply Nat.add_le_add
  · apply (pooled_table_arithmetic_cost ar p w tariff hw hD).trans
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hD8 _))
  · calc
      _ ≤ ∑ _ : J, (66 + 4*M) * tariff := Finset.sum_le_sum fun j _ =>
        Nat.mul_le_mul_right _ ((r j).assemblyOps_le M (hp j) (hs j) (ht j))
      _ = _ := by simp [Nat.mul_assoc]

#print axioms SlotRequests.assemble_pool_correct
#print axioms SlotRequests.assemblyOps_le
#print axioms capped_pool_and_assembly_cost
end
end P6Joint
