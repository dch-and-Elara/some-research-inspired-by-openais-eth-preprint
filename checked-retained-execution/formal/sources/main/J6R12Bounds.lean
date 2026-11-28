import J6R12BlueprintReach
import J6R11SourceReady

namespace J6R12Bounds
open scoped Classical Polynomial
open J6R12Blueprint J6R11Threshold J6R11ProbeSetup J1PPrinted

/-- The manuscript's single asymptotic size guard implies every
scalar conjunct used to construct the valid physical source program. -/
theorem rootBounds_of_printed_guard (s C : ℕ) (f : ℤ[X])
    (hC : 0<C) (hDegree : f.natDegree = 4*Nat.clog 2 s)
    (hsize : J6R11Small.threshold C ≤ Nat.clog 2 s) :
    RootBounds s C f := by
  obtain ⟨_,hCs,hU⟩ := printed_size_implies_numeric_guards s C hC hsize
  exact ⟨hDegree,hC,hCs,hU,hsize⟩

/-- Existence of one exact source field and finite word order before the
program constructs any graph or recursive request. Not a search-time claim. -/
theorem sourceField_of_printed_guard (s C : ℕ) (hC : 0<C)
    (hsize : J6R11Small.threshold C ≤ Nat.clog 2 s) :
    ∃ f : ℤ[X], RootBounds s C f ∧ f.Monic ∧ Irreducible (NativeProbeRing.residuePoly f) ∧
      ∃ words : Fin (2^(4*Nat.clog 2 s)) → Fin f.natDegree → Bool,
        words ⟨0,pow_pos (by decide) _⟩ = (fun _ => false) ∧
        ∀ p, 0 < p →
          NativeProbeRing.probe p f (words ⟨0,pow_pos (by decide) _⟩)=0 ∧
          ∀ i j, i≠j →
            IsUnit (NativeProbeRing.probe p f (words j)-NativeProbeRing.probe p f (words i)) := by
  obtain ⟨hs,_,_⟩ := printed_size_implies_numeric_guards s C hC hsize
  obtain ⟨f,hm,hd,hi,w⟩ := shared_field_and_words s hs
  exact ⟨f,rootBounds_of_printed_guard s C f hC hd hsize,hm,hi,w⟩

theorem positive_degree {s C : ℕ} {f : ℤ[X]} (cfg : RootBounds s C f) :
    0 < f.natDegree := by
  rw [cfg.coefficient]
  have hv := (J9PrintedSchedule.rootU_range (Nat.clog 2 s)).1
  have hw := cfg.widthPos
  omega

#print axioms positive_degree
#print axioms rootBounds_of_printed_guard
#print axioms sourceField_of_printed_guard
end J6R12Bounds
