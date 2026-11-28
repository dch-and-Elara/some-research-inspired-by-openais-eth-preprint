import P5OuterCenterClonePins
import P5OuterCenterFiber

set_option warningAsError true
set_option maxHeartbeats 4000000

namespace Paper5.OuterCenters.Cloned
open scoped BigOperators Classical Polynomial
open P11FullPacking J6R9PacketScopes J6R10Repack J6R9Recursive
  HybridClosure D1Literal J6R11Blueprint

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W × W)) (cubic : ∀ v, GraphCutMoments.degree F v = 3)
variable {G : Type} [LinearOrder G] [Fintype G] {a : ℕ}
local notation "NW" => dNetwork F cubic

def robustPin (P : PhysicalPacking NW a G) (K : ℕ) (v : W) : Prop :=
  K ≤ (P.seat (clonePinWire F v)).2.val ∧ (P.seat (clonePinWire F v)).2.val + K < 2^a

noncomputable def nativeRead (P : PhysicalPacking NW a G) (i : Fin a)
    {t : ℤ} (ht : t ≠ 0) (hv : padicValInt 2 t = i.val) (p₀ p : ℕ)
    (f : ℤ[X]) (hf : f.Monic) (hnil : (2 : Residue f 1 p)^p = 0)
    (σ : W → Bool) (β : Mode i p P.mask →₀ ℕ) (g : G) : Residue f 1 p :=
  reduce p f 1 ((actualPacketHost P i ht hv p hnil 0 (oldRowFile F cubic f p₀ σ) β g).contract hf)

theorem nativeRead_eq_of_group (P : PhysicalPacking NW a G) (i : Fin a)
    {t : ℤ} (ht : t ≠ 0) (hv : padicValInt 2 t = i.val) (p₀ p : ℕ)
    (f : ℤ[X]) (hf : f.Monic) (hnil : (2 : Residue f 1 p)^p = 0)
    (σ τ : W → Bool) (β : Mode i p P.mask →₀ ℕ) (g : G)
    (hgrp : ∀ z, pinOwner F cubic P i z = g → σ z = τ z) :
    nativeRead F cubic P i ht hv p₀ p f hf hnil σ β g =
      nativeRead F cubic P i ht hv p₀ p f hf hnil τ β g := by
  unfold nativeRead actualPacketHost physicalChildHost physicalHost
  change reduce p f 1 (trueContraction _ _ hf) = reduce p f 1 (trueContraction _ _ hf)
  rw [actual_physical_child, actual_physical_child]
  apply Finset.sum_congr rfl
  intro v _
  rw [pinOldState_eq_of_group F cubic P i g f hf p p₀ σ τ hgrp v]

theorem nativeRead_zero_of_robust (P : PhysicalPacking NW a G) (i : Fin a)
    {t : ℤ} (ht : t ≠ 0) (hv : padicValInt 2 t = i.val) (p₀ p : ℕ)
    (f : ℤ[X]) (hf : f.Monic) (hnil : (2 : Residue f 1 p)^p = 0)
    (σ : W → Bool) (β : Mode i p P.mask →₀ ℕ) (g : G) (K : ℕ)
    (outer : ((2^a : ℕ) : ℤ) - K ≤ t ∨ t ≤ -(((2^a : ℕ) : ℤ) - K))
    (z : W) (hg : pinOwner F cubic P i z = g) (hσ : σ z = true)
    (hr : robustPin F cubic P K z) :
    nativeRead F cubic P i ht hv p₀ p f hf hnil σ β g = 0 := by
  unfold nativeRead actualPacketHost physicalChildHost physicalHost
  change reduce p f 1 (trueContraction _ _ hf) = 0
  apply actualChild_zero_of_sentry P i ht hv p hnil _ hf β g (clonePinWire F z)
    ((pin_owner_exact F cubic P i z).trans hg)
  · exact pinOldState_zero F cubic P i g f hf p p₀ σ z hg hσ
  · intro q _
    exact outer_slot_unmatched (2^a) K _ _ t hr.1 hr.2 (P.seat q).2.isLt outer

theorem genuine_outer_child_fiber (P : PhysicalPacking NW a G) (K : ℕ)
    (m : W ≃ W) (edge : ∀ x, (x,m x) ∈ F ∨ (m x,x) ∈ F)
    (budget : 2 * ((bad (robustPin F cubic P K) (pinOwner F cubic P)).card) < Fintype.card W) :
    ∃ x : W,
      let σ : W → Bool := fun _ => true
      let τ := signsWithTwoZero x (m x)
      PinnedCNF.modelCount (PinnedCNF.formula F σ) = 1 ∧
      PinnedCNF.modelCount (PinnedCNF.formula F τ) = 0 ∧
      ∀ (i : Fin a) (t : ℤ) (ht : t ≠ 0) (hv : padicValInt 2 t = i.val) (p₀ p : ℕ)
        (f : ℤ[X]) (hf : f.Monic) (hnil : (2 : Residue f 1 p)^p = 0)
        (β : Mode i p P.mask →₀ ℕ) (g : G),
        (((2^a : ℕ) : ℤ) - K ≤ t ∨ t ≤ -(((2^a : ℕ) : ℤ) - K)) →
        nativeRead F cubic P i ht hv p₀ p f hf hnil σ β g =
        nativeRead F cubic P i ht hv p₀ p f hf hnil τ β g := by
  classical
  obtain ⟨x,hx,hy⟩ := exterior_avoids_bad _ m budget
  refine ⟨x, ?_, ?_, ?_⟩
  · rw [PinnedCNF.count_eq_indicator]
    have h : PinnedCNF.AllEdges F (fun _ => true) := by
      intro e he
      exact Or.inl rfl
    exact if_pos h
  · rw [PinnedCNF.count_eq_indicator]
    apply if_neg
    intro h
    rcases edge x with he|he
    · simpa [signsWithTwoZero] using h (x,m x) he
    · simpa [signsWithTwoZero] using h (m x,x) he
  · intro i t ht hv p₀ p f hf hnil β g houter
    by_cases hxg : pinOwner F cubic P i x = g
    · obtain ⟨z,hz,hzg,hzx,hzy⟩ := good_has_sentry
        (robustPin F cubic P K) (pinOwner F cubic P) i x (m x) hx
      rw [nativeRead_zero_of_robust F cubic P i ht hv p₀ p f hf hnil _ β g K houter z
          (hzg.trans hxg) rfl hz,
        nativeRead_zero_of_robust F cubic P i ht hv p₀ p f hf hnil _ β g K houter z
          (hzg.trans hxg) (by simp [signsWithTwoZero,hzx,hzy]) hz]
    · by_cases hyg : pinOwner F cubic P i (m x) = g
      · obtain ⟨z,hz,hzg,hzy,hzx⟩ := good_has_sentry
          (robustPin F cubic P K) (pinOwner F cubic P) i (m x) x hy
        rw [nativeRead_zero_of_robust F cubic P i ht hv p₀ p f hf hnil _ β g K houter z
            (hzg.trans hyg) rfl hz,
          nativeRead_zero_of_robust F cubic P i ht hv p₀ p f hf hnil _ β g K houter z
            (hzg.trans hyg) (by simp [signsWithTwoZero,hzx,hzy]) hz]
      · apply nativeRead_eq_of_group
        intro z hz
        have hne₁ : z ≠ x := fun h => hxg (h ▸ hz)
        have hne₂ : z ≠ m x := fun h => hyg (h ▸ hz)
        simp [signsWithTwoZero,hne₁,hne₂]

#print axioms nativeRead_eq_of_group
#print axioms nativeRead_zero_of_robust
#print axioms genuine_outer_child_fiber
end Paper5.OuterCenters.Cloned


