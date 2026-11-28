import J7R43LiteralNoDivision

/-! The table-visit part of the actual division-free evaluator. The trace
names the original retained column and its actual assignment. Arithmetic
width and original-column visit counts are separate bounds; this module
does not charge graph layout discovery or recursing on nonzero probes. -/
namespace J7R43Literal
open scoped Classical BigOperators
open J8Physical J8J9Grouped 
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
variable {Packet R S V G : Type} {P : V→Type} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]

abbrev OldVisit (g : G) := Σ v : LocalColumn d g, LocalPort d v → Bool

def actualColumnVisits (g : G) (v : LocalColumn d g) : List (OldVisit d g) :=
  (Finset.univ : Finset (LocalPort d v→Bool)).toList.map (fun x => ⟨v,x⟩)

def actualSubsetVisits (g : G) (pick : Finset (LocalColumn d g)) : List (OldVisit d g) :=
  pick.toList.flatMap (actualColumnVisits d g)

def actualBaselineVisits (g : G) : List (OldVisit d g) := actualSubsetVisits d g Finset.univ

/-- Recompute every old-column contribution without caching: for each
real old tile port pay its marginal scan and the product's other scans,
then compute the baseline for the pin part. -/
def actualSourceVisits (s : S) : List (OldVisit d (d.pinLabel s)) :=
  (Finset.univ : Finset (OldTile d s)).toList.flatMap (fun y =>
    actualColumnVisits d (d.pinLabel s) (tileOldInSource d y).1 ++
    actualSubsetVisits d (d.pinLabel s) (Finset.univ.erase (tileOldInSource d y).1)) ++
  actualBaselineVisits d (d.pinLabel s)

theorem columnVisit_length (g : G) (v : LocalColumn d g) :
    (actualColumnVisits d g v).length = 2^Fintype.card (P v.val) := by
  simp [actualColumnVisits]

theorem subsetVisits_length (g : G) (pick : Finset (LocalColumn d g)) :
    (actualSubsetVisits d g pick).length = ∑ v ∈ pick, 2^Fintype.card (P v.val) := by
  unfold actualSubsetVisits
  rw [List.length_flatMap, Finset.sum_map_toList]
  refine Finset.sum_congr rfl (fun v _ => columnVisit_length d g v)

theorem sourceVisits_length (s : S) :
    (actualSourceVisits d s).length =
      (Fintype.card (OldTile d s)+1) * (actualBaselineVisits d (d.pinLabel s)).length := by
  unfold actualSourceVisits
  rw [List.length_append, List.length_flatMap, Finset.sum_map_toList]
  have h (y : OldTile d s) :
      (actualColumnVisits d (d.pinLabel s) (tileOldInSource d y).1 ++
        actualSubsetVisits d (d.pinLabel s) (Finset.univ.erase (tileOldInSource d y).1)).length =
        (actualBaselineVisits d (d.pinLabel s)).length := by
    rw [List.length_append,columnVisit_length,subsetVisits_length,actualBaselineVisits,subsetVisits_length]
    exact Finset.add_sum_erase _ (fun v : LocalColumn d (d.pinLabel s) => 2^Fintype.card (P v.val))
      (Finset.mem_univ (tileOldInSource d y).1)
  simp [h,Nat.add_mul]

theorem baselineVisits_bounded_degree (g : G) (Δ : ℕ)
    (hΔ : ∀ v : V, Fintype.card (P v) ≤ Δ) :
    (actualBaselineVisits d g).length ≤ Fintype.card (LocalColumn d g)*2^Δ := by
  rw [actualBaselineVisits,subsetVisits_length]
  calc
    _ ≤ ∑ _ : LocalColumn d g, (2:ℕ)^Δ := Finset.sum_le_sum
      (fun v _ => Nat.pow_le_pow_right (by decide) (hΔ v.val))
    _ = _ := by simp

theorem sourceVisits_bounded_degree (s : S) (Δ : ℕ)
    (hΔ : ∀ v : V, Fintype.card (P v) ≤ Δ) :
    (actualSourceVisits d s).length ≤
      (Fintype.card (OldTile d s)+1) * (Fintype.card (LocalColumn d (d.pinLabel s))*2^Δ) := by
  rw [sourceVisits_length]
  exact Nat.mul_le_mul_left _ (baselineVisits_bounded_degree d (d.pinLabel s) Δ hΔ)

#print axioms columnVisit_length
#print axioms subsetVisits_length
#print axioms sourceVisits_length
#print axioms baselineVisits_bounded_degree
#print axioms sourceVisits_bounded_degree
end
end J7R43Literal