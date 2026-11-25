import AffineCostRows

open scoped BigOperators Polynomial

namespace AffineCost
open AffineEdge

variable {q : ℕ} {F : Type*} [Field F]

private theorem zero_slot (sites : Fin q → F) (u v : Word q) (h : scan u v = .zero) :
    coeffPair sites u v = (selector u v, 0) := by
  have hvfirst := first_of_zero h
  have hs (he : u = v) : scan u u = .zero := he.symm ▸ h
  cases hu : scan u u with
  | zero =>
    cases hv : scan v v with
    | zero =>
      have he : u = v := (hard_zero hu).symm.trans
        ((congrArg (fun a => hardWord a none)
          ((first_of_zero hu).trans hvfirst.symm)).trans (hard_zero hv))
      simp [coeffPair, selector, hv, he, hvfirst]
    | one s =>
      have hn : u ≠ v := fun he => by simp [← he, hu] at hv
      simp [coeffPair, selector, hu, hv, hn]
    | two s t =>
      have hn : u ≠ v := fun he => by simp [← he, hu] at hv
      simp [coeffPair, selector, hu, hv, hn]
  | one t =>
    have hn : u ≠ v := fun he => by simpa [hu] using hs he
    cases hv : scan v v <;>
      simp [coeffPair, selector, hu, hv, hn, hvfirst, bitDiff]
  | two s t =>
    have hn : u ≠ v := fun he => by simpa [hu] using hs he
    cases hv : scan v v <;> simp [coeffPair, selector, hu, hv, hn]

private theorem one_slot (sites : Fin q → F) (hi : Function.Injective sites)
    (u v : Word q) (t : Fin q) (h : scan u v = .one t) :
    (coeffPair sites u v).2 + sites t * (selector u v - (coeffPair sites u v).1) = 0 := by
  have hvfirst := first_of_one h
  have he₀ (he : u = v) : scan u u = .one t := he.symm ▸ h
  have he₁ (he : u = v) : scan v v = .one t := he ▸ he₀ he
  cases hu : scan u u with
  | zero =>
    have hne : u ≠ v := fun he => by simpa [hu] using he₀ he
    have hp : parity v.1 ≠ parity (complement u.2) := by
      rw [hvfirst]
      exact parity_flip (complement u.2) t
    cases hv : scan v v <;>
      simp [coeffPair, selector, hu, hv, hne, hp]
  | two s r =>
    have hne : u ≠ v := fun he => by simpa [hu] using he₀ he
    cases hv : scan v v <;> simp [coeffPair, selector, hu, hv, hne]
  | one s =>
    cases hv : scan v v with
    | zero =>
      have hne : u ≠ v := fun he => by simpa [hv] using he₁ he
      simp [coeffPair, selector, hu, hv, hne]
    | two r r' =>
      have hne : u ≠ v := fun he => by simpa [hv] using he₁ he
      simp [coeffPair, selector, hu, hv, hne]
    | one k =>
      by_cases hkt : k = t
      · subst k
        by_cases hts : t = s
        · subst s
          have he : u = v := (hard_one hu).symm.trans
            ((congrArg (fun a => hardWord a (some t))
              ((first_of_one hu).trans hvfirst.symm)).trans (hard_one hv))
          simp only [coeffPair, selector, hu, hv, if_true, if_pos he, hvfirst, flip_same]
          linear_combination scale_selected sites hi (complement u.2) t
        · have hne : u ≠ v := fun he => hts (by simpa [hu, eq_comm] using he₀ he)
          by_cases hb : bucket t = bucket s
          · simp only [coeffPair, selector, hu, hv, if_pos hb, if_neg hne, hvfirst, flip_same]
            rw [scale_partner sites (complement u.2) hb hts]
            ring
          · simp [coeffPair, selector, hu, hv, hne, hb]
      · have hne : u ≠ v := fun he => hkt (by simpa [hv] using he₁ he)
        simp [coeffPair, selector, hu, hv, hne, hvfirst, flip_other hkt, bitDiff]

def localWeight (sites : Fin q → F) (u v : Word q) (i : Fin q) : F :=
  let ab := coeffPair sites u v
  let r := selector u v - ab.1
  match scan u v with
  | .zero => 0
  | .one t => if i = t then r else 0
  | .two s t =>
    let l := (-ab.2 - sites t * r)/(sites s - sites t)
    if i = s then l else if i = t then r-l else 0

private theorem two_ite {i s t : Fin q} (hst : s ≠ t) (x y : F) :
    (if i = s then x else if i = t then y else 0) =
      (if i = s then x else 0) + (if i = t then y else 0) := by
  by_cases hs : i = s
  · subst i
    simp [hst]
  · simp [hs]

theorem explicit_rowSystem (sites : Fin q → F) (hi : Function.Injective sites) (u : Word q) :
    RowSystem sites (binaryEncoder q) u (fun j => (weights sites u j).1)
      (fun j => (weights sites u j).2) (fun t v => localWeight sites u v t) := by
  classical
  have hs₀ (v : Word q) := (weights_sum sites u v).1
  have hs₁ (v : Word q) := (weights_sum sites u v).2
  constructor
  · intro i v h
    have hs := scan_spec u v
    cases hv : scan u v with
    | zero => simp [localWeight, hv]
    | one t =>
      rw [hv] at hs
      have hn : i ≠ t := fun he => h ((hs i).2 he)
      simp [localWeight, hv, hn]
    | two s t =>
      rw [hv] at hs
      have hn₁ : i ≠ s := fun he => h (he.symm ▸ hs.2.1)
      have hn₂ : i ≠ t := fun he => h (he.symm ▸ hs.2.2)
      simp [localWeight, hv, hn₁, hn₂]
  · constructor
    · intro v
      change _ = selector u v
      rw [hs₀]
      cases hv : scan u v with
      | zero =>
        simp [localWeight, hv, zero_slot sites u v hv]
      | one t =>
        simp [localWeight, hv]
      | two s t =>
        have hs := scan_spec u v
        rw [hv] at hs
        simp only [localWeight, hv, two_ite hs.1, Finset.sum_add_distrib,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        ring
    · intro v
      rw [hs₁]
      cases hv : scan u v with
      | zero =>
        simp [localWeight, hv, zero_slot sites u v hv]
      | one t =>
        simpa [localWeight, hv, mul_ite] using one_slot sites hi u v t hv
      | two s t =>
        have hs := scan_spec u v
        rw [hv] at hs
        have hne : sites s - sites t ≠ 0 := sub_ne_zero.mpr (fun h => hs.1 (hi h))
        simp only [localWeight, hv, two_ite hs.1, mul_add, mul_ite, mul_zero,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        field_simp
        ring

end AffineCost
