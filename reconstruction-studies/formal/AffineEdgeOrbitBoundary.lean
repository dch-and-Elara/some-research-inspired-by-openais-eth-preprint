import AffineEdgeOrbitBoundaryLower
import AffineEdgeAffine
import AffineEdgeEncoderData

open scoped BigOperators Polynomial

namespace AffineEdge.Orbit

noncomputable section

variable {q : ℕ} {F : Type*} [Field F]

/-- On one-inactive orbits measure the sum. On the all-active orbit measure
the two parity sums. -/
def boundaryEncoder (q : ℕ) : Matrix (BoundaryRow q) (Word q) F
  | .inl p, v => if key v = nearKey p then 1 else 0
  | .inr b, v => if key v = fullKey q ∧ parity v.1 = b then 1 else 0

theorem boundaryEncoder_orbitwise (q : ℕ) : Orbitwise (boundaryEncoder (F := F) q) := by
  apply orbitwise_of_supported_rows
  rintro (p | b)
  · exact ⟨nearKey p, fun v h => by simp [boundaryEncoder,h]⟩
  · exact ⟨fullKey q, fun v h => by simp [boundaryEncoder,h]⟩

private theorem key_near_known {v : Word q} {s : Fin q} {b : Bool}
    (h : key v = nearKey (s,b)) : v.1 s = b := by
  have he := congrFun h s
  cases h₁ : v.1 s <;> cases h₂ : v.2 s <;> cases b <;>
    simp [key, nearKey, h₁,h₂] at he ⊢

private theorem boundaryEncoder_affine (sites : Fin q → F) (hi : Function.Injective sites) :
    AffineCondition sites (boundaryEncoder q) := by
  classical
  intro u f g hf _ hl
  let a := complement u.2
  have ha : complement a = u.2 := by funext t; simp [a,complement]
  have hzero (v : Word q) (s t : Fin q) (hst : s ≠ t)
      (hs : v.1 s = u.2 s) (ht : v.1 t = u.2 t) : f v = 0 :=
    (affine_zero_two_sites (fun h => hst (hi h)) (hl s v hs) (hl t v ht)).1
  rcases word_cases a u.1 with he | ⟨s,hs⟩ | ⟨s,t,hst,hs,ht⟩
  · have hu : u = hardWord a none := Prod.ext he ha.symm
    have hk : key u = fullKey q := by rw [hu, key_hardWord_full]
    have hz (v : Word q) (hv : key v = fullKey q ∧ parity v.1 = parity u.1)
        (hvu : v ≠ u) : f v = 0 := by
      rcases word_cases a v.1 with he' | ⟨t,ht⟩ | ⟨s,t,hst,hs,ht⟩
      · exact (hvu (first_eq_of_key_eq (hv.1.trans hk.symm) (he'.trans he.symm))).elim
      · exact (parity_flip a t (by simpa [ht,he] using hv.2)).elim
      · exact hzero v s t hst (ha ▸ hs) (ha ▸ ht)
    have h := hf (.inr (parity u.1))
    simp only [boundaryEncoder, ite_mul, one_mul, zero_mul] at h
    rw [Finset.sum_eq_single u] at h
    · simpa [hk] using h
    · intro v _ hv
      split
      next he => exact hz v he hv
      next => rfl
    · simp
  · have hu : u = hardWord (flip s a) (some s) := by
      apply Prod.ext hs
      simpa [hardWord, step] using ha.symm
    have hk : key u = nearKey (s,u.1 s) := by
      rw [hu]
      exact key_hardWord_near _ _
    have hmatch : u.1 s = u.2 s := by
      rw [hs, flip_same]
      exact congrFun ha s
    have hz (v : Word q) (hv : key v = nearKey (s,u.1 s)) (hvu : v ≠ u) : f v = 0 := by
      have hvs := key_near_known hv
      obtain ⟨t,ht⟩ : ∃ t, v.1 t ≠ u.1 t := by
        by_contra! h
        exact hvu (first_eq_of_key_eq (hv.trans hk.symm) (funext h))
      have hts : t ≠ s := fun h => ht (h.symm ▸ hvs)
      have hvt : v.1 t = u.2 t := by
        have hf : u.1 t = a t := (congrFun hs t).trans (flip_other hts a)
        rw [hf] at ht
        rw [← ha]
        unfold complement
        cases ha' : a t <;> cases hv' : v.1 t <;> simp [ha',hv'] at ht ⊢
      exact hzero v s t hts.symm (hvs.trans hmatch) hvt
    have h := hf (.inl (s,u.1 s))
    simp only [boundaryEncoder, ite_mul, one_mul, zero_mul] at h
    rw [Finset.sum_eq_single u] at h
    · simpa [hk] using h
    · intro v _ hv
      split
      next he => exact hz v he hv
      next => rfl
    · simp
  · exact hzero u s t hst (ha ▸ hs) (ha ▸ ht)

theorem boundaryEncoder_attains (sites : Fin q → F) (hq : 2 ≤ q)
    (hi : Function.Injective sites) (hn : ∀ t, sites t ≠ 0) :
    (∃ P, PairedCondition sites (boundaryEncoder q) (q-2) P) ∧
      (boundaryEncoder (F := F) q).rank = 2*q+2 := by
  obtain ⟨P,hP⟩ := paired_of_affine hq hn (boundaryEncoder_affine sites hi)
  refine ⟨⟨P,hP⟩, le_antisymm ?_
    (orbitwise_boundary_rank_lower hq hi (boundaryEncoder_orbitwise q) hP)⟩
  simpa [BoundaryRow, Nat.mul_comm] using (boundaryEncoder (F := F) q).rank_le_card_height

end
end AffineEdge.Orbit
