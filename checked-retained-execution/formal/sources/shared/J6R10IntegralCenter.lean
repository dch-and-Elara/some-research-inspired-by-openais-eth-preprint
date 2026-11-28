import J6R10IntegralRun

namespace J6R10Integral
open J6ActiveRun J6ActiveSchedule

/-- The exact retained centre, not an arbitrary mesh point, has a
valuation strictly below the depth's width. Thus the physical mode
bit lies within the slot's a binary coordinates when u ≤ a. -/
theorem active_level_lt {a M u : ℕ} {t : ℤ} (ht : t ∈ active a M u) :
    padicValInt 2 t < u := by
  have hn : 0 < order M u t := (Finset.mem_filter.mp ht).2
  by_contra! h
  change 0 < height M u * (u-padicValInt 2 t) at hn
  rw [Nat.sub_eq_zero_of_le h,mul_zero] at hn
  exact (lt_irrefl 0) hn

variable {Host Mode : Type*} 

def bitOfCenter (S : Shape Host Mode) (c : Call Host) (t : Center S c)
    (hwidth : S.levelWidth c.depth ≤ S.levelBits c.depth) : Fin (S.levelBits c.depth) :=
  ⟨padicValInt 2 t.val, (active_level_lt t.property).trans_le hwidth⟩

theorem register_positive (S : Shape Host Mode) (c : Call Host) (t : Center S c)
    (ha : S.cutoff < c.edges) : 0 < registerPrecision S c t :=
  (Nat.zero_le c.prec).trans_lt (child_monotone _ _ _ _ _ (Nat.zero_lt_of_lt ha))

#print axioms active_level_lt
#print axioms bitOfCenter
#print axioms register_positive
end J6R10Integral
