import AffineEdgeOrbitBoundaryLower
import ReleaseColorWalsh

open scoped BigOperators Polynomial

namespace Paper3.WalshAssembly

open AffineEdge AffineEdge.Orbit
open Reconstruction.ReleaseColor.Walsh

noncomputable section

abbrev Active {q : ℕ} (u : Word q) := {t : Fin q // u.1 t ≠ u.2 t}
abbrev Fibre {q : ℕ} (u : Word q) := {v : Word q // key v = key u}

def activeSet {q : ℕ} (u : Word q) : Finset (Fin q) :=
  Finset.univ.filter (fun t => u.1 t ≠ u.2 t)

def orientation {q : ℕ} (u v : Word q) (t : Active u) : Bool := v.1 t.val

def inflate {q : ℕ} (u : Word q) (x : Active u → Bool) : Word q :=
  (fun t => if h : u.1 t ≠ u.2 t then x ⟨t,h⟩ else u.1 t,
   fun t => if h : u.1 t ≠ u.2 t then !(x ⟨t,h⟩) else u.2 t)

theorem key_at_active {q : ℕ} {u : Word q} {t : Fin q} (h : u.1 t ≠ u.2 t) :
    key u t = (false,true) := by
  cases h₁ : u.1 t <;> cases h₂ : u.2 t <;> simp [key,h₁,h₂] at h ⊢

theorem key_at_inactive {q : ℕ} {u : Word q} {t : Fin q} (h : u.1 t = u.2 t) :
    key u t = (u.1 t,u.1 t) := by
  simp [key,← h]

theorem inactive_same {q : ℕ} {u v : Word q} (hk : key v = key u)
    {t : Fin q} (h : u.1 t = u.2 t) : v.1 t = u.1 t ∧ v.2 t = u.2 t := by
  have e : key v t = (u.1 t,u.1 t) := (congrFun hk t).trans (key_at_inactive h)
  rw [← h]
  cases h₁ : v.1 t <;> cases h₂ : v.2 t <;> cases h₃ : u.1 t <;>
    simp [key,h₁,h₂,h₃] at e ⊢

@[simp] theorem inflate_key {q : ℕ} (u : Word q) (x : Active u → Bool) :
    key (inflate u x) = key u := by
  funext t
  by_cases h : u.1 t ≠ u.2 t
  · rw [key_at_active h]
    cases hx : x ⟨t,h⟩ <;> simp [key,inflate,h,hx]
  · have he := not_not.mp h
    simp [key,inflate,he]

@[simp] theorem orientation_inflate {q : ℕ} (u : Word q) (x : Active u → Bool) :
    orientation u (inflate u x) = x := by
  funext t
  simp [orientation,inflate,t.property]

theorem inflate_orientation {q : ℕ} {u v : Word q} (hk : key v = key u) :
    inflate u (orientation u v) = v := by
  apply first_eq_of_key_eq ((inflate_key _ _).trans hk.symm)
  funext t
  by_cases h : u.1 t ≠ u.2 t
  · simp [inflate,orientation,h]
  · have he := not_not.mp h
    simpa [inflate,he] using (inactive_same hk he).1.symm

/-- An orientation is indexed by the genuine active slots and selects an actual
physical word, not an auxiliary cube whose points may be unattainable. -/
def orbitCube {q : ℕ} (u : Word q) : (Active u → Bool) ≃ Fibre u where
  toFun x := ⟨inflate u x, inflate_key u x⟩
  invFun v := orientation u v.val
  left_inv := orientation_inflate u
  right_inv v := Subtype.ext (inflate_orientation v.property)

theorem sum_fibre {q : ℕ} (u : Word q) (f : Word q → ℚ) :
    (∑ x : Active u → Bool, f (inflate u x)) =
      ∑ v : Word q, if key v = key u then f v else 0 := by
  classical
  calc
    _ = ∑ v : Fibre u, f v.val := (orbitCube u).sum_comp (fun v => f v.val)
    _ = _ := by
      rw [← Finset.sum_subtype (Finset.univ.filter (fun v : Word q => key v = key u))
        (by simp) f, Finset.sum_filter]

theorem active_card {q : ℕ} (u : Word q) :
    Fintype.card (Active u) = (activeSet u).card := by
  rw [Fintype.card_subtype]
  rfl

theorem active_card_le {q : ℕ} (u : Word q) :
    Fintype.card (Active u) ≤ q := by
  have h := Fintype.card_le_of_injective (f := (fun i : Active u => i.val))
    Subtype.val_injective
  rw [Fintype.card_fin] at h
  exact h

theorem all_active_of_card {q : ℕ} {u : Word q}
    (hc : Fintype.card (Active u) = q) (t : Fin q) : u.1 t ≠ u.2 t := by
  have h : activeSet u = Finset.univ :=
    Finset.eq_univ_of_card (activeSet u) (by simpa only [← active_card, Fintype.card_fin] using hc)
  have ht : t ∈ activeSet u := h.symm ▸ Finset.mem_univ t
  exact (Finset.mem_filter.mp ht).2

theorem full_key_of_card {q : ℕ} {u : Word q}
    (hc : Fintype.card (Active u) = q) : key u = fullKey q := by
  funext t
  exact key_at_active (all_active_of_card hc t)

theorem near_key_of_card {q : ℕ} {u : Word q} (hq : 2 ≤ q)
    (hc : Fintype.card (Active u) = q-1) :
    ∃ p : Fin q × Bool, key u = nearKey p := by
  classical
  have h : ((activeSet u)ᶜ).card = 1 := by
    rw [Finset.card_compl, Fintype.card_fin, ← active_card, hc]
    omega
  obtain ⟨t,ht⟩ := Finset.card_eq_one.mp h
  have ht' : ¬(u.1 t ≠ u.2 t) := by
    have hm : t ∈ (activeSet u)ᶜ := ht.symm ▸ Finset.mem_singleton_self t
    simpa [activeSet] using hm
  refine ⟨(t,u.1 t), ?_⟩
  funext s
  by_cases e : s = t
  · subst s
    simpa [nearKey] using key_at_inactive (not_not.mp ht')
  · have hs : u.1 s ≠ u.2 s := by
      intro he
      have hm : s ∈ (activeSet u)ᶜ := by simp [activeSet,he]
      exact e (Finset.mem_singleton.mp (ht ▸ hm))
    simpa [nearKey,e] using key_at_active hs

/-- At a genuinely active location the known orientation is the other one. -/
theorem active_known {q : ℕ} (u v : Word q) (t : Active u) :
    v.1 t.val = u.2 t.val ↔ orientation u v t ≠ orientation u u t := by
  have ht := t.property
  cases h₁ : u.1 t.val <;> cases h₂ : u.2 t.val <;> cases h₃ : v.1 t.val <;>
    simp [orientation,h₁,h₂,h₃] at ht ⊢

/-- Literal highest Walsh character on the all-active orbit. -/
theorem full_character {q : ℕ} (u v : Word q)
    (hc : Fintype.card (Active u) = q) :
    character (Finset.univ : Finset (Active u)) (orientation u v) =
      character (Finset.univ : Finset (Fin q)) v.1 := by
  classical
  have ha : ∀ t, u.1 t ≠ u.2 t := all_active_of_card hc
  let f (t : Fin q) := character ({t} : Finset (Fin q)) v.1
  have hs : ∀ t : Fin q, t ∈ (Finset.univ : Finset (Fin q)) ↔ u.1 t ≠ u.2 t := by
    intro t
    simp [ha t]
  have hp : (∏ t : Active u, f t.val) = ∏ t : Fin q, f t :=
    (Finset.prod_subtype Finset.univ hs f).symm
  simpa only [f,character,Finset.prod_singleton,orientation] using hp

end

end Paper3.WalshAssembly

#print axioms Paper3.WalshAssembly.orbitCube
#print axioms Paper3.WalshAssembly.sum_fibre
#print axioms Paper3.WalshAssembly.near_key_of_card
#print axioms Paper3.WalshAssembly.active_known
#print axioms Paper3.WalshAssembly.full_character

