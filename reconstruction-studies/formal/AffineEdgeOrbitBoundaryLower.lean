import AffineEdgeOrbit
import AffineEdgeCenter

open Polynomial
open scoped BigOperators Polynomial

namespace AffineEdge.Orbit

noncomputable section

variable {q : ℕ} {F I : Type*} [Field F]

def fullKey (q : ℕ) : Key q Bool := fun _ => (false,true)
def nearKey (p : Fin q × Bool) : Key q Bool := fun t =>
  if t = p.1 then (p.2,p.2) else (false,true)

private theorem nearKey_ne_full (p : Fin q × Bool) : nearKey p ≠ fullKey q := by
  intro h
  have he := congrFun h p.1
  cases p.2 <;> simp [nearKey, fullKey, *] at he

private theorem nearKey_injective (q : ℕ) : Function.Injective (nearKey (q := q)) := by
  rintro ⟨s,a⟩ ⟨t,b⟩ h
  have he := congrFun h s
  by_cases hst : s = t
  · subst t
    simpa [nearKey] using he
  · cases a <;> simp [nearKey, *] at he

@[simp] theorem key_hardWord_full (a : Bits q) : key (hardWord a none) = fullKey q := by
  funext t
  cases h : a t <;> simp [key, hardWord, step, complement, fullKey, h]

@[simp] theorem key_hardWord_near (a : Bits q) (t : Fin q) :
    key (hardWord a (some t)) = nearKey (t,a t) := by
  funext s
  by_cases h : s = t
  · subst s
    simp [key, hardWord, step, complement, nearKey]
  · cases he : a s <;> simp [key, hardWord, step, complement, nearKey, h, he]

theorem first_eq_of_key_eq {u v : Word q} (hk : key u = key v) (hf : u.1 = v.1) :
    u = v := by
  apply Prod.ext hf
  funext t
  have h := congrFun hk t
  simp only [key] at h
  rw [hf] at h
  cases h₁ : v.1 t <;> cases h₂ : u.2 t <;> cases h₃ : v.2 t <;>
    simp [h₁,h₂,h₃] at h ⊢

private theorem eval_kernel_at_zero_of_many_sites {A : Type*} [LinearOrder A] [Fintype A]
    {sites : Fin q → F} {C : Matrix I (PairWord q A) F}
    {P : PairWord q A → PairWord q A → F[X]} {d : ℕ}
    (hp : PairedCondition sites C d P) (hi : Function.Injective sites)
    (u : PairWord q A) (z : PairWord q A → F) (S : Finset (Fin q)) (hd : d < S.card)
    (hk : ∀ j, ∑ v, C j v * z v = 0)
    (hl : ∀ t ∈ S, ∀ v, v.1 t = u.2 t → z v = 0) : z u = 0 := by
  classical
  let R : F[X] := ∑ v, P u v * Polynomial.C (z v)
  have hdeg : R.natDegree ≤ d := by
    apply natDegree_sum_le_of_forall_le
    intro v _
    exact (natDegree_mul_le.trans (by simpa using hp.1 u v))
  have hroot (t : ↥S) : R.eval (sites t.val) = 0 := by
    simpa only [R, eval_finset_sum, eval_mul, eval_C] using hp.2.2 u t.val z hk (hl _ t.prop)
  have hzero := eq_zero_of_natDegree_lt_card_of_eval_eq_zero R
    (hi.comp Subtype.val_injective) hroot (by simpa using hdeg.trans_lt hd)
  simpa [R, eval_finset_sum, hp.2.1, ite_mul] using congrArg (Polynomial.eval (0:F)) hzero

abbrev BoundaryRow (q : ℕ) := (Fin q × Bool) ⊕ Bool

def boundaryWord (t₀ : Fin q) : BoundaryRow q → Word q
  | .inl (t,b) => hardWord (fun _ => b) (some t)
  | .inr b => hardWord (fun t => if t = t₀ then b else false) none

theorem boundaryWord_injective (t₀ : Fin q) : Function.Injective (boundaryWord t₀) := by
  rintro (p | b) (p' | b') h
  · have hk : nearKey p = nearKey p' := by
      cases p; cases p'
      simpa [boundaryWord] using congrArg key h
    exact congrArg Sum.inl (nearKey_injective q hk)
  · exfalso
    apply nearKey_ne_full p
    cases p
    simpa [boundaryWord] using congrArg key h
  · exfalso
    apply nearKey_ne_full p'
    cases p'
    simpa [boundaryWord] using congrArg key h.symm
  · apply congrArg Sum.inr
    have he := congrFun (congrArg Prod.fst h) t₀
    simpa [boundaryWord, hardWord] using he

def excluded (t₀ : Fin q) : BoundaryRow q → Fin q
  | .inl p => p.1
  | .inr _ => t₀

private theorem boundary_unknown (t₀ : Fin q) (i j : BoundaryRow q)
    (h : key (boundaryWord t₀ j) = key (boundaryWord t₀ i)) (t : Fin q)
    (ht : t ≠ excluded t₀ i) : (boundaryWord t₀ j).1 t ≠ (boundaryWord t₀ i).2 t := by
  rcases i with ⟨s,b⟩ | b <;> rcases j with ⟨r,c⟩ | c
  · have he := nearKey_injective q (by simpa [boundaryWord] using h)
    have hb : c = b := congrArg Prod.snd he
    subst c
    change t ≠ s at ht
    cases b <;> simp [boundaryWord, hardWord, step, complement, ht]
  · exact (nearKey_ne_full (s,b) (by simpa [boundaryWord] using h.symm)).elim
  · exact (nearKey_ne_full (r,c) (by simpa [boundaryWord] using h)).elim
  · change t ≠ t₀ at ht
    simp [boundaryWord, hardWord, step, complement, ht]

theorem orbitwise_boundary_rank_lower [Fintype I] {sites : Fin q → F}
    {C : Matrix I (Word q) F} {P : Word q → Word q → F[X]}
    (hq : 2 ≤ q) (hi : Function.Injective sites) (ho : Orbitwise C)
    (hp : PairedCondition sites C (q-2) P) : 2*q+2 ≤ C.rank := by
  let t₀ : Fin q := ⟨0,by omega⟩
  have h := rank_le_of_independent_columns C (boundaryWord t₀) (by
    apply independent_physical_columns C _ (boundaryWord_injective t₀)
    intro z hker hs i
    let u := boundaryWord t₀ i
    let z' := project (key u) z
    have hl (t : Fin q) (ht : t ∈ Finset.univ.erase (excluded t₀ i)) (v : Word q)
        (hv : v.1 t = u.2 t) : z' v = 0 := by
      by_cases hk : key v = key u
      · by_cases hr : v ∈ Set.range (boundaryWord t₀)
        · obtain ⟨j,rfl⟩ := hr
          exact (boundary_unknown t₀ i j hk t (Finset.ne_of_mem_erase ht) hv).elim
        · simp [z', project, hs v hr]
      · simp [z', project, hk]
    have hcard : (Finset.univ.erase (excluded t₀ i)).card = q-1 := by
      simp [Finset.card_erase_of_mem (Finset.mem_univ _)]
    have he := eval_kernel_at_zero_of_many_sites hp hi u z'
      (Finset.univ.erase (excluded t₀ i)) (by rw [hcard]; omega) (kernel_project ho z hker _) hl
    simpa [z', project, u] using he)
  simpa [BoundaryRow, Nat.mul_comm] using h

end
end AffineEdge.Orbit
