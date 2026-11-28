import P5OuterCenterChild
import P5HybridDUnclonedCount

set_option warningAsError true
set_option maxHeartbeats 4000000

namespace Paper5.OuterCenters
open scoped BigOperators Polynomial Classical
open Polynomial P11FullPacking J6R9PacketChild J6R9PacketScopes J6R10Repack
  J6R9Recursive HybridDUncloned

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W × W)) (cubic : ∀ v, GraphCutMoments.degree F v = 3)
variable {G : Type} [LinearOrder G] [Fintype G] {a : ℕ}
local notation "NW" => network F cubic

def pinOwner (P : PhysicalPacking NW a G) (i : Fin a) (v : W) : G :=
  atGroup P i (.inl (.inr (.inl v)))

omit [Fintype W] in
theorem pin_owner_exact (P : PhysicalPacking NW a G) (i : Fin a) (v : W) :
    rowGroup P.mask i (P.seat (pinWire F v)) = pinOwner F cubic P i v :=
  row_symbol P i (pinWire F v)

theorem canonicalLift_zero_exact (p : ℕ) (f : ℤ[X]) (hf : f.Monic) (ell : ℕ) :
    canonicalLift p f hf ell (0 : Residue f ell p) = 0 := by
  simp [canonicalLift, polynomialSection]

theorem pinOldState_zero (P : PhysicalPacking NW a G) (i : Fin a) (g : G)
    (f : ℤ[X]) (hf : f.Monic) (p p₀ : ℕ) (σ : W → Bool) (z : W)
    (hg : pinOwner F cubic P i z = g) (hz : σ z = true)
    (v : PhysicalState P i g)
    (hbit : v.1 ⟨pinWire F z,(pin_owner_exact F cubic P i z).trans hg⟩ = false) :
    oldState P i g p (file F cubic f p₀ σ) hf v = 0 := by
  classical
  let owner : J6R10Repack.Old (atGroup P i) g := ⟨.inl (.inr (.inl z)), hg⟩
  have hread : restrictOriginal NW (atGroup P i) g owner ((stateEquiv P i g).symm v)
      ⟨.inl (pinWire F z), rfl⟩ = false := by
    have he := state_reads_row P i g ((stateEquiv P i g).symm v)
      (pinWire F z) ((pin_owner_exact F cubic P i z).trans hg)
    rw [Equiv.apply_symm_apply, hbit] at he
    exact he.symm
  unfold oldState
  refine Finset.prod_eq_zero (Finset.mem_univ owner) ?_
  change (file F cubic f p₀ σ (.inl (.inr (.inl z)))).read hf p
    (restrictOriginal NW (atGroup P i) g owner ((stateEquiv P i g).symm v)) = 0
  simp [CreatedEntry.read, CreatedEntry.frozen, file, truth, hread, hz, canonicalLift_zero_exact]

theorem pinOldState_eq_of_group (P : PhysicalPacking NW a G) (i : Fin a) (g : G)
    (f : ℤ[X]) (hf : f.Monic) (p p₀ : ℕ) (σ τ : W → Bool)
    (hgrp : ∀ z, pinOwner F cubic P i z = g → σ z = τ z)
    (v : PhysicalState P i g) :
    oldState P i g p (file F cubic f p₀ σ) hf v =
      oldState P i g p (file F cubic f p₀ τ) hf v := by
  classical
  unfold oldState
  apply Finset.prod_congr rfl
  intro u _
  have he : file F cubic f p₀ σ u.val = file F cubic f p₀ τ u.val := by
    by_cases hp : ∃ z : W, u.val = .inl (.inr (.inl z))
    · obtain ⟨z,hz⟩ := hp
      have hg : pinOwner F cubic P i z = g := by
        have h := u.property
        rw [hz] at h
        exact h
      rw [hz]
      exact pin_file_local F cubic f p₀ σ τ z (hgrp z hg)
    · exact nonpin_file_unchanged F cubic f p₀ σ τ u.val
        (fun z hz => hp ⟨z, hz⟩)
  rw [he]

#print axioms pin_owner_exact
#print axioms canonicalLift_zero_exact
#print axioms pinOldState_zero
#print axioms pinOldState_eq_of_group

end Paper5.OuterCenters

