import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! Exact complete-block counts in the DVR digit ordering. For every
residue modulo D>0, the first n naturals use n/D full occurrences plus
one leftover exactly below n mod D. Later files apply this with D=q^u. -/
namespace V8CapacityResidues
open scoped Classical

theorem affine_lt_iff (n D r j : ℕ) (hD : 0<D) (hr : r<D) :
    r+D*j<n ↔ j<n/D ∨ (j=n/D ∧ r<n%D) := by
  have split := Nat.mod_add_div n D
  have remSmall := Nat.mod_lt n hD
  have blocks (u : ℕ) : D*(u+1)=D*u+D := by rw [Nat.mul_succ]
  rcases lt_trichotomy j (n/D) with hj | hj | hj
  · have h₁ : r+D*j<D*(j+1) := by rw [blocks]; omega
    have h₂ := Nat.mul_le_mul_left D (Nat.succ_le_of_lt hj)
    constructor
    · intro _
      exact Or.inl hj
    · intro _
      exact h₁.trans_le (h₂.trans (by omega))
  · subst j
    omega
  · have h₁ : n<D*(n/D+1) := by rw [blocks]; omega
    have h₂ := Nat.mul_le_mul_left D (Nat.succ_le_of_lt hj)
    constructor
    · intro h
      exact ((h₁.trans_le h₂).not_ge (by omega)).elim
    · intro h
      omega

theorem affine_lt_residue_count (n D r j : ℕ) (hD : 0<D) (hr : r<D) :
    r+D*j<n ↔ j<n/D+(if r<n%D then 1 else 0) := by
  rw [affine_lt_iff n D r j hD hr]
  by_cases h : r<n%D
  · rw [if_pos h]
    constructor
    · rintro (hk|⟨hk,_⟩) <;> omega
    · intro hj
      by_cases hk : j<n/D
      · exact Or.inl hk
      · exact Or.inr ⟨by omega,h⟩
  · rw [if_neg h,add_zero]
    exact ⟨fun h' => h'.elim id (fun hk => (h hk.2).elim),Or.inl⟩

def exactFiber (n D r : ℕ) := {j : Fin n // j.val%D=r}

def fiberEquiv (n D r : ℕ) (hD : 0<D) (hr : r<D) :
    exactFiber n D r ≃ Fin (n/D+(if r<n%D then 1 else 0)) where
  toFun x := ⟨x.val.val/D, (affine_lt_residue_count n D r _ hD hr).mp (by
    have e := Nat.mod_add_div x.val.val D
    rw [x.property] at e
    exact e.trans_lt x.val.isLt)⟩
  invFun j := ⟨⟨r+D*j.val,(affine_lt_residue_count n D r _ hD hr).mpr j.isLt⟩,by
    change (r+D*j.val)%D=r
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hr]⟩
  left_inv x := by
    apply Subtype.ext
    apply Fin.ext
    have e := Nat.mod_add_div x.val.val D
    rw [x.property] at e
    exact e
  right_inv j := by
    apply Fin.ext
    change (r+D*j.val)/D=j.val
    rw [Nat.add_mul_div_left _ _ hD,Nat.div_eq_of_lt hr,zero_add]

theorem residue_count (n D r : ℕ) (hD : 0<D) (hr : r<D) :
    Fintype.card {j : Fin n // j.val%D=r}=n/D+(if r<n%D then 1 else 0) := by
  letI : Fintype (exactFiber n D r) := inferInstanceAs (Fintype {j : Fin n // j.val%D=r})
  change Fintype.card (exactFiber n D r)=_
  simp only [Fintype.card_congr (fiberEquiv n D r hD hr), Fintype.card_fin]

theorem residue_count_at_least (n D r : ℕ) (hD : 0<D) (hr : r<D) :
    n/D ≤ Fintype.card {j : Fin n // j.val%D=r} := by
  rw [residue_count n D r hD hr]
  omega

theorem residue_count_diagonal (n D : ℕ) (hD : 0<D) :
    Fintype.card {j : Fin n // j.val%D=n%D}=n/D := by
  rw [residue_count n D _ hD (Nat.mod_lt n hD)]
  simp

#print axioms affine_lt_iff
#print axioms fiberEquiv
#print axioms residue_count
#print axioms residue_count_at_least
#print axioms residue_count_diagonal
end V8CapacityResidues
