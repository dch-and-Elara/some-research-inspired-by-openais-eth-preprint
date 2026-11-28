import J6R12RepackSchedule
import J6SourcePrecision
import J6RecursiveCrossing

/-! The odd centres used by the J6 reduction are genuine active signed
source centres; their receiving precision is the exact printed p_t.
No claim that an arbitrary binary enumeration contains zero is made. -/
namespace J6R12Repack
open scoped Polynomial Classical
open J6Mesh J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R11Repack
open J1PPrinted P1DyadicGrid J6OrientedHost
variable {S V : Type} [LinearOrder S] [Fintype S] [Fintype V]

abbrev rootParams (f : ℤ[X]) (ell m native : ℕ) : Shape (PhysicalHost f ell) Unit :=
  printedShape (physicalSize m native) (fun _ _ _ => 0)

theorem odd_root_active (m native : ℕ) (hn : native≤m) (j : Fin (m+1)) :
    (index m j : ℤ) ∈ active (stepA (Nat.clog 2 (physicalSize m native)) 0)
      (M m) (stepU (Nat.clog 2 (physicalSize m native)) 0) := by
  rw [mesh_root_bits m native hn,mesh_root_width m native hn]
  have hn0 : (index m j : ℤ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (address_index m j).1
  have hpos : (0:ℤ) < (index m j : ℤ) := by exact_mod_cast (address_index m j).1
  have huv : 0<u m := by unfold u; have := b_pos m; omega
  have hM : 0<M m := by unfold M; positivity
  have ht : (index m j : ℤ) ∈ grid (a m) := by
    rw [mem_grid]
    constructor
    · exact (neg_nonpos.mpr (pow₂_pos (a m)).le).trans hpos.le
    · change (index m j : ℤ) < (2:ℤ)^a m
      exact_mod_cast (address_index m j).2.2.2
  refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hn0,ht⟩,?_⟩
  rw [order,(J6RecursiveCrossing.odd_center_valuation m j).2.1,Nat.sub_zero]
  exact J9PrintedSchedule.odd_node_multiplicity_pos (M m) (u m) hM huv

def oddRootCenter (f : ℤ[X]) (ell p m l q native : ℕ)
    (T : Plant V m q) (w : Fin (a m) → S) (hn : native≤m) (j : Fin (m+1)) :
    Center (rootParams f ell m native) (physicalRootCall f ell p m l q T w) :=
  ⟨(index m j : ℤ),odd_root_active m native hn j⟩

theorem oddRootCenter_value (f : ℤ[X]) (ell p m l q native : ℕ)
    (T : Plant V m q) (w : Fin (a m) → S) (hn : native≤m) (j : Fin (m+1)) :
    (oddRootCenter f ell p m l q native T w hn j).val = (index m j : ℤ) := rfl

theorem oddRootCenter_precision (f : ℤ[X]) (ell p m l q native : ℕ)
    (T : Plant V m q) (w : Fin (a m) → S) (hn : native≤m) (j : Fin (m+1)) :
    registerPrecision (rootParams f ell m native) (physicalRootCall f ell p m l q T w)
      (oddRootCenter f ell p m l q native T w hn j) = J6SourcePrecision.printed m p := by
  change childPrecision p (stepA (Nat.clog 2 (physicalSize m native)) 0)
    (M m) (stepU (Nat.clog 2 (physicalSize m native)) 0) (index m j : ℤ) = _
  rw [mesh_root_bits m native hn,mesh_root_width m native hn]
  unfold childPrecision
  rw [(J6RecursiveCrossing.odd_center_valuation m j).2.1,pow_zero,Nat.div_one]
  rfl

#print axioms odd_root_active
#print axioms oddRootCenter_value
#print axioms oddRootCenter_precision
end J6R12Repack
