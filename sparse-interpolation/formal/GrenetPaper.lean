import Main
import Scale
import RationalSign

open Round4Prefix Round4Transfer

namespace GrenetPaper

/-- Exact uniform worst-case prefix length for each fixed admissible ring and step. -/
theorem four_t_worst_case {R : Type*} [CommRing R] [Nontrivial R] [IsAddTorsionFree R]
    (t : ℕ) (ht : 1 ≤ t) (b : R) (hb : b ∈ nonZeroDivisors R) :
    (∀ a : R, DeterminesUnboundedSparse (progression (prefixOffsets t) a b) t) ∧
    (∃ a : R, ∀ m : ℕ, m < 4*t →
      ¬ DeterminesUnboundedSparse (progression (fun i : Fin m => i.val) a b) t) :=
  ⟨fun a => four_t_samples t a b hb,
   ⟨worstStart t b, fun m hm => regular_step_prefix_not_determining t m ht hm b hb⟩⟩

end GrenetPaper
