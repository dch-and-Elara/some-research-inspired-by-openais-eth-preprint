import P1DyadicGrid

/-! Reflection on the actual signed complete dyadic grid. This exchanges
the numerator and denominator valuations of the source Hermite stencil. -/
namespace HermiteLoss
open P1DyadicGrid
open scoped BigOperators

def level (x : ℤ) : ℕ := padicValInt 2 x

def rep (a : ℕ) (x : ℤ) : ℤ := (x+pow₂ a) % pow₂ (a+1) - pow₂ a

theorem rep_mem (a : ℕ) (x : ℤ) : rep a x ∈ grid a := by
  have hp := pow₂_pos (a+1)
  have hm := pow₂_succ a
  have hlo := Int.emod_nonneg (x+pow₂ a) hp.ne'
  have hhi := Int.emod_lt_of_pos (x+pow₂ a) hp
  rw [mem_grid]
  unfold rep
  omega

theorem rep_mod (a : ℕ) (x : ℤ) : rep a x ≡ x [ZMOD pow₂ (a+1)] := by
  have he := (Int.mod_modEq (x+pow₂ a) (pow₂ (a+1))).sub_right (pow₂ a)
  rwa [show x+pow₂ a-pow₂ a=x by ring] at he

theorem rep_of_mem {a : ℕ} {x : ℤ} (hx : x ∈ grid a) : rep a x = x :=
  grid_modEq_injective (rep_mem a x) hx (rep_mod a x)

theorem level_difference_le {a : ℕ} {x y : ℤ}
    (hx : x∈grid a) (hy : y∈grid a) (hne : x≠y) : level (x-y) ≤ a :=
  grid_difference_valuation_le hx hy hne

theorem level_grid_le {a : ℕ} {x : ℤ} (hx : x∈grid a) (hne : x≠0) : level x ≤ a := by
  simpa using level_difference_le hx (zero_mem_grid a) hne

theorem level_rep_difference {a : ℕ} {x y : ℤ}
    (hx : x∈grid a) (hy : y∈grid a) (hne : x≠y) :
    level (rep a (x-y)) = level (x-y) := by
  have hr : rep a (x-y) ≠ 0 := by
    intro hr
    have hh := (rep_mod a (x-y)).dvd
    rw [hr,sub_zero] at hh
    have hb := grid_difference_bounds hx hy
    exact hne (sub_eq_zero.mp (small_dvd_zero hb.1 hb.2 hh))
  exact valuation_eq_of_modEq_pow₂ (rep_mod a (x-y)) hr (sub_ne_zero.mpr hne)
    ((level_grid_le (rep_mem a (x-y)) hr).trans (Nat.le_succ _))
    ((level_difference_le hx hy hne).trans (Nat.le_succ _))

def others (a : ℕ) (t : ℤ) : Finset ℤ := ((grid a).erase 0).erase t

theorem mem_others {a : ℕ} {t q : ℤ} : q∈others a t ↔ q∈grid a ∧ q≠0 ∧ q≠t := by
  simp only [others,Finset.mem_erase]
  tauto

def reflect (a : ℕ) (t q : ℤ) : ℤ := rep a (t-q)

theorem reflect_map {a : ℕ} {t q : ℤ} (ht : t∈grid a) (hq : q∈others a t) :
    reflect a t q∈others a t := by
  obtain ⟨hg,h0,hn⟩ := mem_others.mp hq
  have hm := rep_mod a (t-q)
  have hb := grid_difference_bounds ht hg
  apply mem_others.mpr
  refine ⟨rep_mem a _,?_,?_⟩
  · intro hz
    change rep a (t-q)=0 at hz
    have hdiv := hm.dvd
    rw [hz,sub_zero] at hdiv
    exact hn (sub_eq_zero.mp (small_dvd_zero hb.1 hb.2 hdiv)).symm
  · intro he
    change rep a (t-q)=t at he
    have hdiv := hm.dvd
    rw [he,show t-q-t = -q by ring,Int.dvd_neg] at hdiv
    have hwin := grid_difference_bounds hg (zero_mem_grid a)
    simp only [sub_zero] at hwin
    exact h0 (small_dvd_zero hwin.1 hwin.2 hdiv)

theorem reflect_involutive {a : ℕ} {t q : ℤ} (hq : q∈grid a) :
    reflect a t (reflect a t q)=q := by
  have h := (rep_mod a (t-q)).sub_left t
  rw [show t-(t-q)=q by ring] at h
  exact grid_modEq_injective (rep_mem a _) hq ((rep_mod a _).trans h)

theorem reflect_exchanges {a : ℕ} {t q : ℤ} (ht : t∈grid a) (hq : q∈others a t) :
    level (reflect a t q)=level (t-q) ∧ level (t-reflect a t q)=level q := by
  have hm := mem_others.mp hq
  have hr := mem_others.mp (reflect_map ht hq)
  refine ⟨level_rep_difference ht hm.1 hm.2.2.symm,?_⟩
  have h := level_rep_difference ht hr.1 hr.2.2.symm
  change level (reflect a t (reflect a t q))=level (t-reflect a t q) at h
  rw [reflect_involutive hm.1] at h
  exact h.symm

theorem sum_reflect {a : ℕ} {t : ℤ} {R : Type*} [AddCommMonoid R]
    (ht : t∈grid a) (f : ℤ → R) :
    (∑ q ∈ others a t, f (reflect a t q)) = ∑ q ∈ others a t, f q := by
  refine Finset.sum_bij (fun q _ => reflect a t q) (fun _ hq => reflect_map ht hq) ?_ ?_ (fun _ _ => rfl)
  · intro x hx y hy h
    have hh := congrArg (reflect a t) h
    rw [reflect_involutive (mem_others.mp hx).1, reflect_involutive (mem_others.mp hy).1] at hh
    exact hh
  · intro q hq
    exact ⟨reflect a t q, reflect_map ht hq, reflect_involutive (mem_others.mp hq).1⟩

theorem level_of_add_unequal {x y : ℤ} (hx : x≠0)
    (hxy : level x < level y) : level (x+y)=level x := by
  have hn : x+y ≠ 0 := by
    intro hh
    have he : y = -x := by omega
    rw [he] at hxy
    simp [level,padicValInt] at hxy
  have hdX : pow₂ (level x) ∣ x := padicValInt_dvd (p:=2) x
  have hdY : pow₂ (level x) ∣ y :=
    (padicValInt_dvd_iff (p:=2) (level x) y).mpr (Or.inr hxy.le)
  have hlow : level x ≤ level (x+y) :=
    ((padicValInt_dvd_iff (p:=2) (level x) (x+y)).mp (dvd_add hdX hdY)).resolve_left hn
  refine le_antisymm ?_ hlow
  by_contra! hh
  have hs : pow₂ (level x+1) ∣ (x+y) :=
    (padicValInt_dvd_iff (p:=2) _ _).mpr (Or.inr hh)
  have hy' : pow₂ (level x+1) ∣ y :=
    (padicValInt_dvd_iff (p:=2) _ _).mpr (Or.inr hxy)
  have hx' : pow₂ (level x+1) ∣ x := by simpa using dvd_sub hs hy'
  have hm := ((padicValInt_dvd_iff (p:=2) _ _).mp hx').resolve_left hx
  change level x+1 ≤ level x at hm
  omega

theorem reflect_positive_level {a : ℕ} {t q : ℤ} (hq : q∈others a t)
    (hv : level q < level (t-q)) : level q = level t := by
  have he := level_of_add_unequal (mem_others.mp hq).2.1 hv
  rw [show q+(t-q)=t by ring] at he
  exact he.symm

#print axioms reflect_exchanges
#print axioms sum_reflect
#print axioms level_of_add_unequal

end HermiteLoss

