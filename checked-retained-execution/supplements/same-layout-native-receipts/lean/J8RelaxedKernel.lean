import J8RelaxedWiring
import J8PhysicalKernel
set_option warningAsError true
namespace J8Physical.Relaxed
open scoped Classical BigOperators
noncomputable section
variable {Packet R S V G : Type*} {P : V → Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq Packet]
theorem physicalArgument_pin_invariant (e : RowEndpointSeating d)
    (X Y : Wire R → Bool) (x : Wire R)
    (agree : ∀ y (p : Sigma P), d.column y = Sum.inr p → X y = Y y) :
    physicalArgument d X x = physicalArgument d Y x := by
  by_cases h : ∃ y, Shift d x y
  · obtain ⟨y,hy⟩ := h
    obtain ⟨p,hp⟩ := hit_is_nonpin d e hy
    rw [physicalArgument_hit d X hy, physicalArgument_hit d Y hy, agree y p hp]
  · rw [physicalArgument_no_hit d X x (not_exists.mp h),
      physicalArgument_no_hit d Y x (not_exists.mp h)]

section KernelTransfer

variable [DecidableEq R] [Fintype V] [DecidableEq V] [DecidableEq G]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

def localBitsFromWire (g : G) (X : Wire R → Bool)
    (v : LocalColumn d g) (p : LocalPort d v) : Bool :=
  X (recoverWire d ⟨v,p⟩)

omit [DecidableEq R] [DecidableEq V] [(v : V) → Fintype (P v)] [(v : V) → DecidableEq (P v)] in
/-- Pass the actual original Cauchy center argument to the existing J8
source/target compiler. No equality of abstract hit functions is an
assumption. Even the old-column assignment is a concrete restriction
of the same original physical port assignment. -/
theorem center_to_compiled_argument (e : RowEndpointSeating d) (even : Even L) {g : G}
    (F : (v : LocalColumn d g) → LiteralPortCompiler.CNF (LocalPort d v))
    (X : Wire R → Bool) (r : LocalRow d g) (b : Bool) :
    physicalArgument d X (r.1,b) =
      J8SourceMoment.input0
        (J8SourceMoment.literalChild (groupWiring d e even g) (outerAmplitude L) F)
        (localBitsFromWire d g X) r b := by
  cases hh : localHit d e even r with
  | none =>
    have nh : ∀ y, ¬ Shift d (r.1,b) y := by
      intro y hy
      have h := localHit_complete d e even r hy
      rw [hh] at h
      cases h
    rw [physicalArgument_no_hit d X _ nh]
    simp only [J8SourceMoment.input0, J8SourceMoment.literalChild, groupWiring,
      wiringOfOption_read_none _ _ hh]
  | some addr =>
    have good := localHit_sound d e even r hh
    simp only [J8SourceMoment.input0, J8SourceMoment.literalChild, groupWiring,
      wiringOfOption_read_some _ _ _ _ hh]
    by_cases hb : addr.1 = b
    · have hb' : Shift d (r.1,b) (recoverWire d addr.2) := by simpa only [hb] using good
      rw [physicalArgument_hit d X hb', if_pos hb]
      rfl
    · have nh : ∀ y, ¬ Shift d (r.1,b) y := by
        intro y hy
        exact hb (congrArg Prod.snd (row_hit_unique d e good hy rfl))
      rw [physicalArgument_no_hit d X _ nh, if_neg hb]

end KernelTransfer


#print axioms physicalArgument_pin_invariant
#print axioms center_to_compiled_argument
end
end J8Physical.Relaxed