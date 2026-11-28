import AffineEdgeDual
import AffineEdgeDimension

open scoped BigOperators

namespace AffineEdge

noncomputable section

variable {q : ℕ} {F ι : Type*} [Field F]

theorem word_cases (a b : Bits q) :
    b = a ∨ (∃ t, b = flip t a) ∨ ∃ s t, s ≠ t ∧ b s = complement a s ∧ b t = complement a t := by
  classical
  by_cases h : b = a
  · exact Or.inl h
  · right
    by_cases hn : ∃ t, b = flip t a
    · exact Or.inl hn
    · right
      obtain ⟨t, ht⟩ : ∃ t, b t ≠ a t := by
        by_contra! h'
        exact h (funext h')
      have hc (i : Fin q) (hi : b i ≠ a i) : b i = complement a i := by
        cases ha : a i <;> cases hb : b i <;> simp_all [complement]
      obtain ⟨s, hst, hs⟩ : ∃ s, s ≠ t ∧ b s ≠ a s := by
        by_contra! he
        apply hn
        refine ⟨t, funext fun i => ?_⟩
        by_cases h : i = t
        · subst i
          exact (hc t ht).trans (flip_same t a).symm
        · rw [flip_other h]
          exact he i h
      exact ⟨s, t, hst, hc s hs, hc t ht⟩

theorem affine_zero_two_sites {x y f g : F} (hxy : x ≠ y)
    (hx : f + x*g = 0) (hy : f + y*g = 0) : f = 0 ∧ g = 0 := by
  have hv : (x-y)*g = 0 := by
    calc
      _ = (f+x*g) - (f+y*g) := by ring
      _ = 0 := by rw [hx, hy, sub_zero]
  have hg := (mul_eq_zero.mp hv).resolve_left (sub_ne_zero.mpr hxy)
  exact ⟨by simpa [hg] using hx, hg⟩

theorem affine_slope {s f g : F} (hs : s ≠ 0) (h : f + s*g = 0) :
    g = (-s⁻¹)*f := by
  have h' := eq_neg_of_add_eq_zero_right h
  calc
    g = s⁻¹ * (s*g) := by rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
    _ = (-s⁻¹)*f := by rw [h', mul_neg, neg_mul]

private theorem collect_at {a : Bits q} (x : Slot q → F) (p : Kind q × Kind q) :
    collect a x (wordAt a p) = ∑ i, if placement i = p then x i else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  simp only [(wordAt_injective a).eq_iff]

private theorem collect_near {a : Bits q} (x : Slot q → F) (t : Fin q) (k : Kind q) :
    collect a x (wordAt a (some t,k)) = x (.inr (t,k)) := by
  classical
  rw [collect_at, Finset.sum_eq_single (Sum.inr (t,k))]
  · simp [placement]
  · intro i _ hi
    apply if_neg
    rcases i with p | ⟨s,j⟩
    · simp [placement]
    · intro h
      have h' : s = t ∧ j = k := by simpa [placement] using h
      exact hi (by rw [h'.1,h'.2])
  · simp

set_option maxHeartbeats 900000 in
theorem affine_of_centerCondition {sites : Fin q → F} {C : ι → Word q → F}
    (hi : Function.Injective sites) (hn : ∀ t, sites t ≠ 0)
    (hzero : ∀ v, (¬∃ k, hardWord v.1 k = v) → ∀ j, C j v = 0)
    (hc : CenterCondition (fun t => -(sites t)⁻¹)
      (fun a k j => C j (hardWord a k))) : AffineCondition sites C := by
  classical
  intro u f g hf hg hlocal
  let a := complement u.2
  have ha : complement a = u.2 := by
    funext t
    simp [a, complement]
  let x : Slot q → F :=
    Sum.elim (fun p => if p.2 then g (wordAt a (none,p.1)) else f (wordAt a (none,p.1)))
      (fun p => f (wordAt a (some p.1,p.2)))
  let f' := collect a (fun i => x i * intercept i)
  let g' := collect a (fun i => x i * gradient (fun t => -(sites t)⁻¹) i)
  have hAt₀ (p : Kind q × Kind q) : f' (wordAt a p) = f (wordAt a p) := by
    rcases p with ⟨_ | t, k⟩
    · simp [f', collect_at, Fintype.sum_sum_type, Fintype.sum_prod_type,
        placement, intercept, x, Prod.mk.injEq]
    · simp [f', collect_near, x, intercept]
  have hAt₁ (p : Kind q × Kind q) : g' (wordAt a p) = g (wordAt a p) := by
    rcases p with ⟨_ | t, k⟩
    · simp [g', collect_at, Fintype.sum_sum_type, Fintype.sum_prod_type,
        placement, gradient, x, Prod.mk.injEq]
    · have hv : (wordAt a (some t,k)).1 t = u.2 t := by
        rw [← ha]
        exact flip_same t a
      have hs := affine_slope (hn t) (hlocal t _ hv)
      simpa [g', collect_near, x, gradient, mul_comm] using hs.symm
  have hz (v : Word q) (s t : Fin q) (hst : s ≠ t)
      (hs : v.1 s = complement a s) (ht : v.1 t = complement a t) :
      f v = 0 ∧ g v = 0 :=
    affine_zero_two_sites (fun h => hst (hi h))
      (hlocal s v (by simpa only [ha] using hs)) (hlocal t v (by simpa only [ha] using ht))
  have hsimilar (v : Word q) (k : Kind q) (hv : hardWord v.1 k = v) :
      f' v = f v ∧ g' v = g v := by
    rcases word_cases a v.1 with he | ⟨t, ht⟩ | ⟨s,t,hst,hs,ht⟩
    · have hw : wordAt a (none,k) = v := by simpa [wordAt, step, ← he] using hv
      rw [← hw]
      exact ⟨hAt₀ _, hAt₁ _⟩
    · have hw : wordAt a (some t,k) = v := by simpa [wordAt, step, ← ht] using hv
      rw [← hw]
      exact ⟨hAt₀ _, hAt₁ _⟩
    · have hne (i : Slot q) : wordAt a (placement i) ≠ v := by
        intro h
        have hb := congrArg Prod.fst h
        rcases i with ⟨k,b⟩ | ⟨j,k⟩
        · have h' := congrFun hb s
          have : a s = !(a s) := h'.trans hs
          cases a s <;> simp_all
        · change flip j a = v.1 at hb
          by_cases hj : s = j
          · subst j
            have h' : a t = !(a t) := (flip_other hst.symm a).symm.trans ((congrFun hb t).trans ht)
            cases a t <;> simp_all
          · have h' : a s = !(a s) := (flip_other hj a).symm.trans ((congrFun hb s).trans hs)
            cases a s <;> simp_all
      have hz' := hz v s t hst hs ht
      simp [f', g', collect, hne, hz'.1, hz'.2]
  have hk (j : ι) :
      (∑ v, C j v * f' v) = 0 ∧ (∑ v, C j v * g' v) = 0 := by
    have he (v : Word q) : C j v * f' v = C j v * f v ∧ C j v * g' v = C j v * g v := by
      by_cases h : ∃ k, hardWord v.1 k = v
      · obtain ⟨k,h⟩ := h
        obtain ⟨h1,h2⟩ := hsimilar v k h
        rw [h1, h2]
        exact ⟨rfl,rfl⟩
      · simp only [hzero v h j, zero_mul, and_self]
    exact ⟨(Finset.sum_congr rfl fun v _ => (he v).1).trans (hf j),
      (Finset.sum_congr rfl fun v _ => (he v).2).trans (hg j)⟩
  have hsum : (∑ i, x i • slotColumn (fun t => -(sites t)⁻¹)
      (fun a k j => C j (hardWord a k)) a i) = 0 := by
    apply Prod.ext <;> funext j
    · have h := (hk j).1
      change (∑ v, C j v * collect a _ v) = 0 at h
      rw [sum_collect] at h
      simpa only [slotColumn, Prod.fst_sum, Prod.smul_fst, Prod.fst_zero, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply, wordAt, mul_assoc, mul_comm, mul_left_comm] using h
    · have h := (hk j).2
      change (∑ v, C j v * collect a _ v) = 0 at h
      rw [sum_collect] at h
      simpa only [slotColumn, Prod.snd_sum, Prod.smul_snd, Prod.snd_zero, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply, wordAt, mul_assoc, mul_comm, mul_left_comm] using h
  rcases word_cases a u.1 with he | ⟨t, ht⟩ | ⟨s,t,hst,hs,ht⟩
  · have hu : wordAt a (none,none) = u := Prod.ext he.symm ha
    simpa [x, targetSlot, hu] using hc a x hsum none
  · have hu : wordAt a (some t,some t) = u := by
      apply Prod.ext ht.symm
      simpa [wordAt, hardWord, step] using ha
    simpa [x, targetSlot, hu] using hc a x hsum (some t)
  · exact (hz u s t hst hs ht).1

end
end AffineEdge
