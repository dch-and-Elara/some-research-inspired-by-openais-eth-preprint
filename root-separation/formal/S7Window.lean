import Mathlib.Tactic
import Mathlib.Data.Finset.Lattice.Fold

/-! The integer window criterion and its exact positive maximum (P.2). -/
namespace S7
open Finset

def WindowCriterion {I : Type*} (gap : I → ℕ) (budget : I → ℤ)
    (q : I → ℕ) (b : ℕ) : Prop :=
  ∀ t, ((b : ℤ)+q t-2) * gap t ≤ budget t

theorem windowCriterion_iff {I : Type*} (gap : I → ℕ) (budget : I → ℤ)
    (q : I → ℕ) (hgap : ∀ t, 0 < gap t) (b : ℕ) :
    WindowCriterion gap budget q b ↔
      ∀ t, (b : ℤ) ≤ 2-q t+(budget t)/(gap t) := by
  unfold WindowCriterion
  apply forall_congr'
  intro t
  have hg : (0 : ℤ) < gap t := by exact_mod_cast hgap t
  rw [← Int.le_ediv_iff_mul_le hg]
  omega

def windowLimit {I : Type*} [Fintype I] [Nonempty I]
    (S d : ℕ) (gap : I → ℕ) (budget : I → ℤ) (q : I → ℕ) : ℤ :=
  min ((S : ℤ)-d)
    (univ.inf' univ_nonempty fun t => 2-q t+(budget t)/(gap t))

theorem certifiedWindow_iff {I : Type*} [Fintype I] [Nonempty I]
    (S d : ℕ) (gap : I → ℕ) (budget : I → ℤ) (q : I → ℕ)
    (hgap : ∀ t, 0 < gap t) (b : ℕ) :
    (0 < b ∧ d+b ≤ S ∧ WindowCriterion gap budget q b) ↔
      0 < b ∧ (b : ℤ) ≤ windowLimit S d gap budget q := by
  rw [windowCriterion_iff gap budget q hgap, windowLimit, le_min_iff, le_inf'_iff]
  simp only [mem_univ, true_implies, and_congr_right_iff]
  intro _
  constructor
  · rintro ⟨hdeg,hcrit⟩
    exact ⟨by omega, hcrit⟩
  · rintro ⟨hdeg,hcrit⟩
    exact ⟨by omega, hcrit⟩

theorem largestPositiveWindow {I : Type*} [Fintype I] [Nonempty I]
    (S d : ℕ) (gap : I → ℕ) (budget : I → ℤ) (q : I → ℕ)
    (hgap : ∀ t, 0 < gap t) :
    let bound := windowLimit S d gap budget q
    (bound ≤ 0 ↔ ¬ ∃ b, 0 < b ∧ d+b ≤ S ∧ WindowCriterion gap budget q b) ∧
    (0 < bound → (0 < bound.toNat ∧ d+bound.toNat ≤ S ∧
      WindowCriterion gap budget q bound.toNat) ∧
      ∀ b, (0 < b ∧ d+b ≤ S ∧ WindowCriterion gap budget q b) → b ≤ bound.toNat) := by
  dsimp
  let B := windowLimit S d gap budget q
  simp_rw [certifiedWindow_iff S d gap budget q hgap]
  change (B ≤ 0 ↔ ¬ ∃ b : ℕ, 0 < b ∧ (b : ℤ) ≤ B) ∧
    (0 < B → (0 < B.toNat ∧ (B.toNat : ℤ) ≤ B) ∧
      ∀ b : ℕ, (0 < b ∧ (b : ℤ) ≤ B) → b ≤ B.toNat)
  constructor
  · constructor
    · rintro h ⟨b,hb,hB⟩
      omega
    · intro h
      by_contra! hp
      apply h
      exact ⟨B.toNat, by omega, by omega⟩
  · intro h
    exact ⟨⟨by omega, by omega⟩, fun b hb => by omega⟩

end S7
