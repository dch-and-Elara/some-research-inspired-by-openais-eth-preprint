import J6R14ZeroModePolynomial
import J6R11IntegralStep
import J6R10IntegralFinite

/-! At the omitted probe itself, the actual scaled crossing coefficients
vanish. This proves the zero-mode product equals the ordinary parent
localized contraction at this probe, not at other probe values. -/
namespace J6R15PlantedIdentity
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking P1DyadicGrid J6R9Recursive
open J6R10Repack J6R10Integral J6R11Integral J6R9PacketScopes J6R9PacketChild
open J6R10RowIdentity J6R10RowAffine J6R10PacketAssembly
noncomputable section

variable {R G : Type*} [CommRing R] [LinearOrder G] {a b : ℕ}

theorem scaled_at_zero (mask : MaskFamily a b G) (i : Fin a) {t : ℤ}
    (ht : t ≠ 0) (hv : padicValInt 2 t=i.val) (p : ℕ) (hnil : (2:R)^p=0)
    (w : Physical a b G) (m : Mode i p mask) :
    scaledRow mask i ht hv p hnil 0 w m = 0 := by
  unfold scaledRow crossNorm
  split <;> simp [J6R9PacketScaled.normalized]

variable {E A B : Type*} [Fintype E] [Fintype A] [Fintype B] [Fintype G]
variable {N : Network E A B} {f : ℤ[X]} {ell : ℕ}

set_option maxHeartbeats 2200000 in
theorem zero_child_formula (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t ≠ 0) (hv : padicValInt 2 t=i.val) (p : ℕ)
    (file : EntryFile f ell N) (hf : f.Monic) (β : Mode i p P.mask →₀ ℕ) (g : G) :
    reduce p f ell (actualChildTruth P i ht hv p 0 file hf β g) =
      J6RecursiveModes.child (childTarget P i) (childSource P i)
        (actualRows (childBlock P i)) (fun g v => oldState P i g p file hf v)
        (fun g v => groupBit (fun e => P.seat e) (fun e => P.seat e) P.mask i g v)
        (fun g v => groupBase (fun e => P.seat e) (fun e => P.seat e)
          P.mask i t p (box_two_nil p f ell) 0 g v)
        (fun _ _ _ _ => 0) (fun g v => stateMoment P i g p v) β g := by
  rw [actualChildTruth,actual_physical_child,J6RecursiveModes.child]
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  exact Finset.prod_congr rfl fun k _ => by
    simp only [actualPacket,scaled_at_zero]

set_option maxHeartbeats 2200000 in
theorem positive_mode_zero (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t ≠ 0) (hv : padicValInt 2 t=i.val) (p : ℕ)
    (file : EntryFile f ell N) (hf : f.Monic) (β : Mode i p P.mask →₀ ℕ) (hb : β ≠ 0) :
    (∏ g : G, reduce p f ell (actualChildTruth P i ht hv p 0 file hf β g)) = 0 := by
  simp only [zero_child_formula P i ht hv p file hf]
  exact J6RecursiveModes.offZero_childProduct _ _ _ _ _ _ _ β hb

omit [Fintype E] [Fintype A] [Fintype B] in
theorem zero_menu (P : PhysicalPacking N a G) (i : Fin a) (p : ℕ) (hp : 0<p) :
    0 ∈ J6RecursiveMenu.menu p (weight i p P.mask) := by
  rw [J6RecursiveMenu.exact_printed_menu _ _ (fun m => m.order.val.succ_pos)]
  simpa [J6RecursiveMenu.weighted] using hp

set_option maxHeartbeats 2800000 in
theorem zero_eq_parentJet (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (htM : t ∈ grid a) (ht : t ≠ 0) (hv : padicValInt 2 t=i.val) (p : ℕ) (hp : 0<p)
    (file : EntryFile f ell N) (hf : f.Monic) :
    (J6R14ZeroMode.polynomial P i t p file hf).eval 0 =
      ((parentJet P file hf t).map (reduce p f ell)).eval 0 := by
  rw [J6R14ZeroMode.polynomial_eval P i ht hv p file hf 0,
    native_finite_step P i htM ht hv p hp 0 file hf,
    Finset.sum_eq_single_of_mem 0 (zero_menu P i p hp)]
  exact fun β _ hβ => positive_mode_zero P i ht hv p file hf β hβ

#print axioms scaled_at_zero
#print axioms zero_child_formula
#print axioms positive_mode_zero
#print axioms zero_menu
#print axioms zero_eq_parentJet
end
end J6R15PlantedIdentity
