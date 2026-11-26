import P5PrecisionOptProfiles

/-! The arbitrary-profile pointwise carrier identity (P.7). Orders may
vary independently inside any shell and may be zero. The signs are
derived from the signed grid valuations, not from a uniform-profile
restriction. -/
namespace Paper5.PrecisionOpt
open P1DyadicGrid HermiteLoss
open scoped BigOperators

theorem level_neg (z : ℤ) : level (-z)=level z := by simp [level,padicValInt]

theorem level_sub_low_left {x y : ℤ} (hx : x≠0) (hl : level x<level y) :
    level (x-y)=level x := by
  rw [sub_eq_add_neg]
  exact level_of_add_unequal hx (by rwa [level_neg])

theorem level_sub_low_right {x y : ℤ} (hy : y≠0) (hl : level y<level x) :
    level (x-y)=level y := by
  rw [←level_neg (x-y),neg_sub]
  exact level_sub_low_left hy hl

theorem level_sub_ge_min {x y : ℤ} (hne : x≠y) (i : ℕ)
    (hx : i≤level x) (hy : i≤level y) : i≤level (x-y) := by
  have hdx := (padicValInt_dvd_iff (p:=2) i x).mpr (Or.inr hx)
  have hdy := (padicValInt_dvd_iff (p:=2) i y).mpr (Or.inr hy)
  exact ((padicValInt_dvd_iff (p:=2) i (x-y)).mp (dvd_sub hdx hdy)).resolve_left
    (sub_ne_zero.mpr hne)

def shell (u i : ℕ) : Finset (Paper5.P3.rootNodes u) :=
  Finset.univ.filter fun t => level t.val=i

def shellOrderMass (u : ℕ) (q : Profile u) (i : ℕ) : ℕ :=
  ∑ t∈shell u i,q t

def sameShellCost (u : ℕ) (q : Profile u) (t : Paper5.P3.rootNodes u) : ℤ :=
  ∑ s∈(shell u (level t.val)).erase t,
    (q s:ℤ)*((level (t.val-s.val):ℤ)-level t.val)

def higherShellGain (u : ℕ) (q : Profile u) (i : ℕ) : ℤ :=
  ∑ s,(q s:ℤ)*((level s.val-i:ℕ):ℤ)

theorem shellOrderMass_grouped (u : ℕ) (q : Profile u) (i : ℕ) :
    higherShellGain u q i =
      ∑ j∈Finset.range u,(shellOrderMass u q j:ℤ)*((j-i:ℕ):ℤ) := by
  unfold higherShellGain
  have hm (t : Paper5.P3.rootNodes u) (_ : t∈Finset.univ) : level t.val∈Finset.range u :=
    Finset.mem_range.mpr (Finset.mem_filter.mp t.property).2.2
  rw [←Finset.sum_fiberwise_of_maps_to hm]
  apply Finset.sum_congr rfl
  intro j _
  unfold shellOrderMass shell
  rw [Nat.cast_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [(Finset.mem_filter.mp ht).2]

theorem arbitrary_profile_carrier (u : ℕ) (q : Profile u) (t : Paper5.P3.rootNodes u) :
    Paper5.P3.nativeCarrierVal Subtype.val q t =
      higherShellGain u q (level t.val)-sameShellCost u q t := by
  let F : Finset (Paper5.P3.rootNodes u) := Finset.univ.erase t
  have hF : (shell u (level t.val)).erase t = F.filter (fun s => level s.val=level t.val) := by
    ext s
    simp only [F,shell,Finset.mem_filter,Finset.mem_univ,Finset.mem_erase,true_and, and_true]
  let g (s : Paper5.P3.rootNodes u) : ℤ := (q s:ℤ)*((level s.val-level t.val:ℕ):ℤ)
  have hg : (∑ s∈F,g s) = higherShellGain u q (level t.val) := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Paper5.P3.rootNodes u)) g (Finset.mem_univ t)
    have hz : g t=0 := by simp [g]
    rwa [hz,add_zero] at h
  unfold Paper5.P3.nativeCarrierVal sameShellCost
  rw [←hg,hF,Finset.sum_filter,←Finset.sum_sub_distrib]
  change (∑ s∈F,(q s:ℤ)*((level s.val:ℤ)-level (t.val-s.val))) =
    ∑ s∈F,(g s-(if level s.val=level t.val then (q s:ℤ)*((level (t.val-s.val):ℤ)-level t.val) else 0))
  apply Finset.sum_congr rfl
  intro s _
  rcases lt_trichotomy (level s.val) (level t.val) with he|he|he
  · have hw := level_sub_low_right (Finset.mem_filter.mp s.property).2.1 he
    simp [hw,he.ne,g,Nat.sub_eq_zero_of_le he.le]
  · rw [if_pos he]
    have hz : g s=0 := by simp [g,he]
    rw [hz,he]
    ring
  · have hw := level_sub_low_left (Finset.mem_filter.mp t.property).2.1 he
    simp [hw,he.ne',g,Nat.cast_sub he.le]

theorem sameShellCost_nonnegative (u : ℕ) (q : Profile u) (t : Paper5.P3.rootNodes u) :
    0≤sameShellCost u q t := by
  apply Finset.sum_nonneg
  intro s hs
  have he : level s.val=level t.val := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hs)).2
  have hne : t.val≠s.val := fun e => Finset.ne_of_mem_erase hs (Subtype.ext e.symm)
  have h := level_sub_ge_min hne (level t.val) le_rfl he.ge
  have hz : 0≤(level (t.val-s.val):ℤ)-level t.val := by omega
  exact Int.mul_nonneg (Int.natCast_nonneg _) hz

theorem deepest_carrier_nonpositive (u : ℕ) (q : Profile u) (t : Paper5.P3.rootNodes u)
    (deep : ∀ s,0<q s → level s.val≤level t.val) :
    Paper5.P3.nativeCarrierVal Subtype.val q t≤0 := by
  rw [arbitrary_profile_carrier]
  have hg : higherShellGain u q (level t.val)=0 := by
    apply Finset.sum_eq_zero
    intro s _
    by_cases hz : q s=0
    · simp [hz]
    · have hw := deep s (Nat.pos_of_ne_zero hz)
      simp [Nat.sub_eq_zero_of_le hw]
  rw [hg]
  exact sub_nonpos.mpr (sameShellCost_nonnegative u q t)

#print axioms level_sub_low_left
#print axioms level_sub_ge_min
#print axioms shellOrderMass_grouped
#print axioms arbitrary_profile_carrier
#print axioms deepest_carrier_nonpositive
end Paper5.PrecisionOpt
