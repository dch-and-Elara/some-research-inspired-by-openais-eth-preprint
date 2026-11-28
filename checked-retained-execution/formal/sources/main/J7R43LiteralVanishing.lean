import J7R43LiteralSlots

/-! The completed product cannot be used to acquire the separate source
moment. This is an exact zero at the actual zero probe, irrespective
of the positive precision or the chosen allowed modal order. -/
namespace J7R43Literal
open scoped BigOperators Classical Polynomial
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R10Integral J6R11Integral
open J6R9PacketScopes J6R9PacketChild J6R10PacketAssembly J6R10RowAffine J6R10RowIdentity
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

section Cross
variable {G K : Type*} [LinearOrder G] [CommRing K] {a b : ℕ}

theorem crossing_zero_probe (mask : MaskFamily a b G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ) (hnil : (2:K)^p=0)
    (w : Physical a b G) (m : Mode i p mask) :
    scaledRow mask i ht hv p hnil (0:K) w m = 0 := by
  unfold scaledRow crossNorm
  split
  · simp [J6R9PacketScaled.normalized]
  · rw [mul_zero]
end Cross

variable {E A B G : Type*} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}
variable (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
variable (p : ℕ) (file : EntryFile f ell N) (hf : f.Monic)
local notation "D" => Box f ell p
local notation "h2" => box_two_nil p f ell
local notation "σ" => (fun e : E => P.seat e)

set_option maxHeartbeats 3000000 in
theorem literal_nonzero_product_vanishes (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (β : Mode i p P.mask →₀ ℕ) (hβ : β≠0) :
    (∏ g : G, reduce p f ell (actualChildTruth P i ht hv p (0:D) file hf β g)) = 0 := by
  let old := fun g v => oldState P i g p file hf v
  let bit := fun g v => groupBit σ σ P.mask i g v
  let base := fun g v => groupBase σ σ P.mask i t p h2 (0:D) g v
  let feat := fun g v => stateMoment (R:=D) P i g p v
  have heq (g : G) :
      reduce p f ell (actualChildTruth P i ht hv p (0:D) file hf β g) =
        J6RecursiveModes.child (childTarget P i) (childSource P i)
          (actualRows (childBlock P i)) old bit base (fun _ _ _ _ => 0) feat β g := by
    rw [actualChildTruth,actual_physical_child]
    unfold J6RecursiveModes.child actualPacket
    simp only [crossing_zero_probe]
    rfl
  simp only [heq]
  exact J6RecursiveModes.offZero_childProduct (childTarget P i) (childSource P i)
    (actualRows (childBlock P i)) old bit base feat β hβ

#print axioms crossing_zero_probe
#print axioms literal_nonzero_product_vanishes
end
end J7R43Literal