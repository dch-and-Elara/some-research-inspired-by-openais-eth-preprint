import BooleanMeasurement
import P5MainIteratorMeasure
import P5MainIteratorSourceLayout
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! F.A1 with the actual occupied source cell, not a freely chosen matrix:
the measured rows are the retained copy-orbit Walsh eigenvectors, source
variables have their fixed first words, and tuples use the coordinate grouping. -/
namespace P5MainIterator
open scoped BigOperators Classical

variable {E V F Copy I B : Type*} [Fintype E] [Fintype V]
  [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B]

noncomputable def exceptionalMatrix (keep : ℕ → Prop) (L : SourceLayout E V F Copy I B) :
    Matrix (Exceptional (CoordFamily (Copy:=Copy) (I:=I) (B:=B)) keep) V ℚ :=
  rawMeasurement CoordFamily keep L.orbitPlacement

noncomputable def sourceTuple (keep : ℕ → Prop) (L : SourceLayout E V F Copy I B)
    (t : I) (x : V → Bool) (g : B) :
    Exceptional (CoordFamily (Copy:=Copy) (I:=I) (B:=B)) keep → ℚ :=
  (exceptionalMatrix keep L).mulVec
    (fun v => if L.a v t=g then BooleanMeasurement.bit ℚ (x v) else 0)

theorem cube_attained (keep : ℕ → Prop) (L : SourceLayout E V F Copy I B) (t : I) :
    2 ^ (exceptionalMatrix keep L).rank ≤ (Set.range (sourceTuple keep L t)).ncard :=
  BooleanMeasurement.two_pow_rank_le_grouped_range_ncard (exceptionalMatrix keep L)
    (fun v => L.a v t)

noncomputable def activeCount (u : WordCell I B) : ℕ :=
  Fintype.card {i : I // (u i).1≠(u i).2}

omit [Fintype B] [Fintype Copy] in
theorem copied_count (s : Copy × WordCell I B) :
    Fintype.card (CoordFamily (copyEncode s).1) = activeCount s.2 := by
  exact Fintype.card_congr (Equiv.subtypeEquivRight (unequal_at_key_iff _))

omit [Fintype V] [Fintype B] [Fintype Copy] in
theorem source_energy_sum (keep : ℕ → Prop) (L : SourceLayout E V F Copy I B) (v : V) :
    ((∑ s ∈ filled L.orbitPlacement v, binomialMass (Fintype.card (CoordFamily s.1)) keep) /
        (filled L.orbitPlacement v).card) =
      (∑ e ∈ incidences L.placement v, binomialMass (activeCount (L.placement.slot e).2) keep) /
        (incidences L.placement v).card := by
  rw [filled_card]
  congr 1
  unfold filled
  rw [Finset.sum_image (fun x _ y _ h => L.orbitPlacement.slot.injective h)]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  exact copied_count (L.placement.slot e)

theorem source_projection_rank (keep : ℕ → Prop) (L : SourceLayout E V F Copy I B) :
    (∑ v, (∑ e∈incidences L.placement v, binomialMass (activeCount (L.placement.slot e).2) keep) /
      (incidences L.placement v).card) ≤ ((exceptionalMatrix keep L).rank : ℝ) := by
  have h := orbit_attainable_rank CoordFamily keep L.orbitPlacement (fun v s hs t ht => L.orbit_unique v s t hs ht)
  simp_rw [source_energy_sum keep L] at h
  exact h

theorem source_rank_le_log_attained (keep : ℕ → Prop) (L : SourceLayout E V F Copy I B)
    (t : I) :
    ((exceptionalMatrix keep L).rank : ℝ) ≤
      Real.log ((Set.range (sourceTuple keep L t)).ncard : ℝ) / Real.log 2 := by
  apply (le_div_iff₀ (Real.log_pos (by norm_num))).mpr
  have hc : (2:ℝ) ^ (exceptionalMatrix keep L).rank ≤ ((Set.range (sourceTuple keep L t)).ncard : ℝ) := by
    exact_mod_cast cube_attained keep L t
  have h := Real.log_le_log (show 0 < (2:ℝ) ^ (exceptionalMatrix keep L).rank from by positivity) hc
  rwa [Real.log_pow] at h

/-- The complete finite F.A1 pair of inequalities, at every actual node. -/
theorem finite_FA1 (keep : ℕ → Prop) (L : SourceLayout E V F Copy I B) (t : I) :
    (∑ v, (∑ e∈incidences L.placement v, binomialMass (activeCount (L.placement.slot e).2) keep) /
      (incidences L.placement v).card) ≤ ((exceptionalMatrix keep L).rank : ℝ) ∧
    ((exceptionalMatrix keep L).rank : ℝ) ≤
      Real.log ((Set.range (sourceTuple keep L t)).ncard : ℝ) / Real.log 2 :=
  ⟨source_projection_rank keep L,source_rank_le_log_attained keep L t⟩

omit [Fintype E] [Fintype V] [Fintype Copy] [Fintype I] [Fintype B] in
/-- Every Boolean group assignment is visited by a global-assignment trace
or a trace that visits all compatible fibers. No surjectivity heuristic. -/
theorem local_assignment_extends (L : SourceLayout E V F Copy I B) (t : I) (g : B)
    (y : {v // L.a v t=g} → Bool) : ∃ x : V → Bool, ∀ v, x v.val=y v := by
  refine ⟨fun v => if h:L.a v t=g then y ⟨v,h⟩ else false,?_⟩
  intro v
  exact dif_pos v.property

#print axioms cube_attained
#print axioms copied_count
#print axioms source_energy_sum
#print axioms source_projection_rank
#print axioms source_rank_le_log_attained
#print axioms finite_FA1
#print axioms local_assignment_extends
end P5MainIterator
