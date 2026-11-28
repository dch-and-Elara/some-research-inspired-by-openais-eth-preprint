import A4R45ZeroFallback
import J6R15PlantedIdentityCenter

/-! No high-precision cross-mode assumption is required at the true zero
probe: the complete product of a positive mode vanishes. At nonzero
probes the fallback deliberately reads the same beta=0 mode only. -/
namespace A4R45ZeroModeTotal
open scoped Classical Polynomial BigOperators
open Polynomial P1DyadicGrid P11FullPacking J6R9Recursive J6R10Repack J6R12Repack
open J6R10Integral J6R11Integral J6R12Integral A4R45ZeroFallback
open J6R9PacketScopes J6R9PacketChild
set_option autoImplicit false
set_option warningAsError true

noncomputable section
variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}

theorem whole_at_zero_is_same_zero_slot (P : PhysicalPacking N a G) (i : Fin a)
    {t : ℤ} (hgrid : t∈grid a) (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p : ℕ) (hp : 0<p) (file : EntryFile f ell N) (hf : f.Monic) :
    ((J6R11Integral.parentJet P file hf t).map (reduce p f ell)).eval 0 =
      V8PooledMenu.slot P i ht hv p (box_two_nil p f ell) 0 file hf 0 := by
  exact (J6R15PlantedIdentity.zero_eq_parentJet P i hgrid ht hv p hp file hf).symm.trans
    (actual_zero_mode_eval P i ht hv p file hf 0)

theorem positive_completed_mode_wipes_at_zero (P : PhysicalPacking N a G) (i : Fin a)
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p : ℕ) (file : EntryFile f ell N) (hf : f.Monic)
    (β : Mode i p P.mask →₀ ℕ) (hb : β≠0) :
    V8PooledMenu.slot P i ht hv p (box_two_nil p f ell) 0 file hf β = 0 := by
  rw [V8PooledMenu.slot]
  have same := J6R15PlantedIdentity.positive_mode_zero P i ht hv p file hf β hb
  refine Eq.trans ?_ same
  refine Finset.prod_congr (Finset.ext fun _ => by simp only [Finset.mem_univ]) fun g _ => ?_
  rw [actualPacketHost_truth P i ht hv p 0 file hf β g]

#print axioms whole_at_zero_is_same_zero_slot
#print axioms positive_completed_mode_wipes_at_zero
end
end A4R45ZeroModeTotal
