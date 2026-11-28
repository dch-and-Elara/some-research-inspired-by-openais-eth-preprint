import J6R12IntegralDirectPrinted
import J6R15SpecializedBoxOrientedSeat

/-! Pin the exact checked seating at the original host, and use the
printed selector on descendants. The positive extreme is an admitted
odd centre at every positive legal layer, and its observable probes
are literally the printed initial binary representatives. -/
namespace J6R14SpecializedBox
open scoped Polynomial Classical BigOperators
open Polynomial J6ActiveRun J6ActiveSchedule J6R9Recursive J6R12Blueprint
open J6R11Blueprint J6R10Repack J6R11Repack P1DyadicGrid P11FullPacking
noncomputable section
set_option linter.unusedSectionVars false

theorem positiveExtreme_odd (a : ℕ) (ha : 0<a) :
    Odd (((2^a:ℕ):ℤ)-1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  refine ⟨((2^k:ℕ):ℤ)-1,?_⟩
  rw [pow_succ,Nat.cast_mul,Nat.cast_ofNat]
  ring

theorem positiveExtreme_active (a M u : ℕ) (ha : 0<a) (hu : 0<u) (huM : u ≤ M) :
    (((2^a:ℕ):ℤ)-1) ∈ active a M u := by
  apply oddGrid_subset_active a M u hu huM
  refine Finset.mem_filter.mpr ⟨mem_grid.mpr ?_,positiveExtreme_odd a ha⟩
  have hx : 0 < pow₂ a := pow₂_pos a
  have hx' : (((2^a:ℕ):ℤ)) = pow₂ a := by simp [pow₂]
  rw [hx']
  omega

variable {f : ℤ[X]} {ell : ℕ}
variable (S : Params (f:=f) (ell:=ell)) (Δ : ℕ)
variable (r : Call (PhysicalHost f ell))
variable (Q : PhysicalPacking r.host.network (S.levelBits r.depth) (Fin 64))

noncomputable def exactSeatSelector : Selector S Δ :=
  fun c d => if h : c=r then h.symm ▸ Q else defaultSelector S Δ c d

theorem exactSeatSelector_at_root (d : Ready S Δ r) :
    packing (exactSeatSelector S Δ r Q) d = Q := by
  simp [packing,exactSeatSelector]

theorem exactSeatSelector_at_descendant (c : Call (PhysicalHost f ell))
    (d : Ready S Δ c) (h : c≠r) :
    packing (exactSeatSelector S Δ r Q) d = packing (defaultSelector S Δ) d := by
  simp only [packing,exactSeatSelector,dif_neg h]

def extremeCenter (ha : 0 < S.levelBits r.depth)
    (hu : 0 < S.levelWidth r.depth) (huM : S.levelWidth r.depth ≤ r.edges) :
    Center S r :=
  ⟨_,positiveExtreme_active _ _ _ ha hu huM⟩

theorem extremeCenter_index (d : Ready S Δ r) (ha : 0 < S.levelBits r.depth)
    (hu : 0 < S.levelWidth r.depth) (huM : S.levelWidth r.depth ≤ r.edges) :
    (centerIndex d (extremeCenter S r ha hu huM)).val = 0 :=
  odd_valuation_zero (positiveExtreme_odd _ ha)

theorem literal_address_at_sample (d : Ready S Δ r) (t : Center S r) (z : Probe S r) :
    sampleNode S f ell r d.fit t z =
      J6ActiveInterpolation.scalarIn (registerPrecision S r t) f ell
        (NativeProbeRing.probe (registerPrecision S r t) f
          (NativeProbeRing.chosenRep f.natDegree _ d.fit z)) := rfl

#print axioms positiveExtreme_odd
#print axioms positiveExtreme_active
#print axioms exactSeatSelector_at_root
#print axioms exactSeatSelector_at_descendant
#print axioms extremeCenter_index
#print axioms literal_address_at_sample
end
end J6R14SpecializedBox