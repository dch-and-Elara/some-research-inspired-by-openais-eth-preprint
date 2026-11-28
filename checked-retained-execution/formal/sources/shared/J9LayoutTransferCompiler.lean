import J9LayoutTransferRows

/-! The signed singleton of the native literal compiler, over the actual
row ports (not an axiomatized marked-row derivative). -/
namespace J9LayoutTransfer
open scoped BigOperators Classical
open LiteralPortCompiler
noncomputable section
variable {R K : Type*} [Fintype R] [DecidableEq R] [CommRing K]

abbrev β : Unit →₀ ℕ := Finsupp.single () 1

def rowCompiler (base kernel : Port R → K) : MvPolynomial Unit K :=
  completed (allRows (R:=R)) (fun _ p => base p) (fun _ p _ => kernel p)

/-- Lower-level singleton allocation, summed on the original binary
rows. The outer displayed sum chooses exactly one original port. -/
theorem singleton_native_rows (base kernel : Port R → K) :
    MvPolynomial.coeff β (rowCompiler base kernel) =
      ∑ p : Port R, kernel p * (-1 + 2 * base (p.1,!p.2)) *
        ∏ r ∈ (Finset.univ : Finset R).erase p.1,
          TargetDerivative.equality (base (r,false)) (base (r,true)) := by
  rw [rowCompiler, β, singleton_coeff, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [← contracted_mark base p (kernel p)]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply Finset.prod_congr rfl
  intro q _
  by_cases h : q = p
  · subst q
    simp [portTerm, atPort, selectEntry]
  · simp [portTerm, atPort, selectEntry, h]

omit [DecidableEq R] in
theorem targetWire_at_actual_slot
    {Packet S V G : Type*} {P : V → Type*} {L : ℕ}
    [Fintype Packet] [DecidableEq Packet] [DecidableEq G]
    (d : J8Physical.Layout Packet R S V G P L) (anchor : S)
    (p : Port R) (hp : p ∈ J8Physical.targets d (J8Physical.pinWire d anchor)) :
    J9End.targetWire d anchor (J9End.slot d p) = p := by
  have hm : J9End.slot d p ∈ J9End.targetSlots d anchor :=
    Finset.mem_image.mpr ⟨p,hp,rfl⟩
  obtain ⟨hw,he⟩ := J9End.targetWire_spec d anchor hm
  exact J9End.targetSlot_injective d anchor hw hp he

omit [DecidableEq R] in
/-- Reindex the original physical target ports to the numerical target
slots. This uses physical injectivity in one packet, not a renaming
that could identify two occupied ports. -/
theorem sum_actual_target_slots
    {Packet S V G : Type*} {P : V → Type*} {L : ℕ}
    [Fintype Packet] [DecidableEq Packet] [DecidableEq G]
    (d : J8Physical.Layout Packet R S V G P L) (anchor : S) (f : Port R → K) :
    (∑ i ∈ J9End.targetSlots d anchor, f (J9End.targetWire d anchor i)) =
      ∑ p ∈ J8Physical.targets d (J8Physical.pinWire d anchor), f p := by
  rw [J9End.targetSlots, Finset.sum_image]
  · exact Finset.sum_congr rfl fun p hp => by rw [targetWire_at_actual_slot d anchor p hp]
  · exact J9End.targetSlot_injective d anchor

#print axioms singleton_native_rows
#print axioms sum_actual_target_slots
end
end J9LayoutTransfer

