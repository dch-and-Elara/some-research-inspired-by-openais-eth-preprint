import V8PooledMenuSlots
import J6R14ZeroModeFallback

/-! Actual prescribed, residue-distinct zero-mode replies at the fixed
chosen root recover the value at the omitted probe. This is a claim
about the chosen completed-slot interface, not acquiring the samples
or materializing nonzero internal modes. -/
namespace A4R45ZeroFallback
open scoped Polynomial BigOperators Classical
open Polynomial P1DyadicGrid P11FullPacking J6R9Recursive J6R10Repack J6R12Repack
open J6R10Integral J6R12Integral J6R14ZeroMode
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3900000

noncomputable section
variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}

theorem actual_zero_mode_eval (P : PhysicalPacking N a G) (i : Fin a)
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p : ℕ) (file : EntryFile f ell N) (hf : f.Monic)
    (z : Box f ell p) :
    (J6R14ZeroMode.polynomial P i t p file hf).eval z =
      V8PooledMenu.slot P i ht hv p (box_two_nil p f ell) z file hf 0 := by
  rw [J6R14ZeroMode.polynomial_eval P i ht hv p file hf z, V8PooledMenu.slot]
  refine Finset.prod_congr (Finset.ext fun _ => by simp only [Finset.mem_univ]) fun g _ => ?_
  rw [actualPacketHost_truth P i ht hv p z file hf 0 g]

theorem same_completed_zero_mode_from_original_words (P : PhysicalPacking N a G)
    (i : Fin a) {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (hgrid : t∈grid a) (p : ℕ) (hp : 0<p) (file : EntryFile f ell N)
    (hf : f.Monic) (hd : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (W : Prescribed f (J9PrintedSchedule.degreeBound (Fintype.card E) (2^a))) :
    (J6ActiveInterpolation.decoded (prescribedNode W p ell)
      (fun j => V8PooledMenu.slot P i ht hv p (box_two_nil p f ell)
        (prescribedNode W p ell j) file hf 0)).eval 0 =
      V8PooledMenu.slot P i ht hv p (box_two_nil p f ell) 0 file hf 0 := by
  let Q := J6R14ZeroMode.polynomial P i t p file hf
  have table : (fun j => V8PooledMenu.slot P i ht hv p (box_two_nil p f ell)
      (prescribedNode W p ell j) file hf 0) = (fun j => Q.eval (prescribedNode W p ell j)) :=
    funext fun j => (actual_zero_mode_eval P i ht hv p file hf (prescribedNode W p ell j)).symm
  rw [table,J6ActiveInterpolation.decoded_exact _ _ (degree P i t p hgrid file hf)
    (prescribed_units W p ell hp hf hd)]
  exact actual_zero_mode_eval P i ht hv p file hf 0

#print axioms actual_zero_mode_eval
#print axioms same_completed_zero_mode_from_original_words
end
end A4R45ZeroFallback
