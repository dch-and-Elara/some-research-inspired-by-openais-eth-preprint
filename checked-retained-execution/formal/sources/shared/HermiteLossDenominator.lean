import HermiteLossArithmetic
import HermiteLossCount

/-! Actual weighted Hermite stencil denominator losses on the signed
complete grid, not a uniform-multiplicity or crude product estimate. -/
namespace HermiteLoss
open P1DyadicGrid
open scoped BigOperators

def numerator (a u h : ℕ) (t : ℤ) : ℤ :=
  ∏ q ∈ others a t, (-q)^taper u h (level q)

def denominator (a u h : ℕ) (t : ℤ) : ℤ :=
  ∏ q ∈ others a t, (t-q)^taper u h (level q)

theorem numerator_ne (a u h : ℕ) (t : ℤ) : numerator a u h t ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun _ hq => pow_ne_zero _ (neg_ne_zero.mpr (mem_others.mp hq).2.1))

theorem denominator_ne (a u h : ℕ) (t : ℤ) : denominator a u h t ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun _ hq => pow_ne_zero _ (sub_ne_zero.mpr (mem_others.mp hq).2.2.symm))

theorem level_power {x : ℤ} (hx : x≠0) (n : ℕ) : level (x^n) = n*level x := by
  induction n with
  | zero => simp [level,padicValInt]
  | succ n ih =>
    rw [pow_succ,show level (x^n*x)=level (x^n)+level x from
      padicValInt.mul (pow_ne_zero n hx) hx,ih,Nat.succ_mul]

theorem numerator_level (a u h : ℕ) (t : ℤ) :
    level (numerator a u h t) = ∑ q ∈ others a t, taper u h (level q)*level q := by
  unfold numerator level
  rw [valuation_prod_of_ne_zero _ _ (fun _ hq => pow_ne_zero _ (neg_ne_zero.mpr (mem_others.mp hq).2.1))]
  apply Finset.sum_congr rfl
  intro q hq
  change level ((-q)^taper u h (level q)) = _
  rw [level_power (neg_ne_zero.mpr (mem_others.mp hq).2.1)]
  simp [level,padicValInt]

theorem denominator_level (a u h : ℕ) (t : ℤ) :
    level (denominator a u h t) = ∑ q ∈ others a t, taper u h (level q)*level (t-q) := by
  unfold denominator level
  rw [valuation_prod_of_ne_zero _ _ (fun _ hq => pow_ne_zero _ (sub_ne_zero.mpr (mem_others.mp hq).2.2.symm))]
  apply Finset.sum_congr rfl
  intro q hq
  exact level_power (sub_ne_zero.mpr (mem_others.mp hq).2.2.symm) _

def weightedLoss (u h : ℕ) (t q : ℤ) : ℤ :=
  (taper u h (level q):ℤ)*((level (t-q):ℤ)-(level q:ℤ))

def drop (u h i j : ℕ) : ℕ :=
  (taper u h i-taper u h j)*(j-i)

theorem abs_pair_lower {a u h : ℕ} {t q : ℤ}
    (ht : t∈grid a) (hq : q∈others a t) (hV : level q < level (t-q)) :
    weightedLoss u h t q + weightedLoss u h t (reflect a t q) =
      (drop u h (level t) (level q):ℤ)+drop u h (level t) (level (reflect a t q)) := by
  have he := reflect_exchanges ht hq
  have hi := reflect_positive_level hq hV
  have hmon := taper_decreases u h (level q) (level (t-q)) hV.le
  unfold weightedLoss drop
  rw [he.1,he.2,←hi]
  simp only [Nat.sub_self,zero_mul]
  rw [Nat.cast_mul,Nat.cast_sub hmon,Nat.cast_sub hV.le]
  ring

theorem abs_pair {a u h : ℕ} {t q : ℤ}
    (ht : t∈grid a) (h0 : t≠0) (hq : q∈others a t) :
    weightedLoss u h t q + weightedLoss u h t (reflect a t q) =
      (drop u h (level t) (level q):ℤ)+drop u h (level t) (level (reflect a t q)) := by
  rcases lt_trichotomy (level q) (level (t-q)) with hV | hV | hV
  · exact abs_pair_lower ht hq hV
  · have hd := padicValInt_dvd (p:=2) q
    have hD : pow₂ (level q) ∣ t-q := by rw [hV]; exact padicValInt_dvd (p:=2) (t-q)
    have hdiv : pow₂ (level q) ∣ t := by
      simpa using dvd_add hD hd
    have hi : level q ≤ level t :=
      ((padicValInt_dvd_iff (p:=2) _ _).mp hdiv).resolve_left h0
    have e := reflect_exchanges ht hq
    unfold weightedLoss drop
    rw [e.1,e.2,←hV,Nat.sub_eq_zero_of_le hi]
    simp
  · have hr := reflect_map ht hq
    have hh := reflect_exchanges ht hq
    have hv : level (reflect a t q)<level (t-reflect a t q) := by rw [hh.1,hh.2]; exact hV
    have z := abs_pair_lower (u:=u) (h:=h) ht hr hv
    rw [reflect_involutive (mem_others.mp hq).1] at z
    simpa only [add_comm] using z

theorem weighted_to_drop {a u h : ℕ} {t : ℤ} (ht : t∈grid a) (h0 : t≠0) :
    ∑ q∈others a t, weightedLoss u h t q =
      (∑ q∈others a t, drop u h (level t) (level q):ℕ) := by
  have hEq :
      (∑ q∈others a t, (weightedLoss u h t q + weightedLoss u h t (reflect a t q))) =
      ∑ q∈others a t, ((drop u h (level t) (level q):ℤ)+
          drop u h (level t) (level (reflect a t q))) :=
    Finset.sum_congr rfl (fun _ hq => abs_pair ht h0 hq)
  simp only [Finset.sum_add_distrib] at hEq
  rw [sum_reflect ht (weightedLoss u h t),sum_reflect ht (fun q => (drop u h (level t) (level q):ℤ))] at hEq
  push_cast
  omega

theorem drop_insert_center (a u h : ℕ) (t : ℤ) :
    (∑ q∈others a t, drop u h (level t) (level q)) =
      ∑ q∈(grid a).erase 0, drop u h (level t) (level q) := by
  apply Finset.sum_subset (Finset.erase_subset _ _)
  intro q hq hq'
  have e : q=t := by
    by_contra hn
    exact hq' (Finset.mem_erase.mpr ⟨hn,hq⟩)
  subst q
  simp [drop]

theorem histogram_sum (a : ℕ) (f : ℕ → ℕ) :
    (∑ q∈(grid a).erase 0, f (level q)) =
      ∑ i∈Finset.range (a+1), 2^(a-i)*f i := by
  have h q (hq : q∈(grid a).erase 0) : level q∈Finset.range (a+1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (level_grid_le (Finset.mem_of_mem_erase hq) (Finset.ne_of_mem_erase hq)))
  rw [← Finset.sum_fiberwise_of_maps_to' h f]
  apply Finset.sum_congr rfl
  intro i hi
  have hc : ((grid a).erase 0).filter (fun q => level q=i) = levelCell a i := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_erase, mem_levelCell]
    tauto
  rw [hc,Finset.sum_const,nsmul_eq_mul,level_card (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
  rfl

/-- Exact valuation identity for the actual product E_t(0). The
other nodes of valuation below i cancel, not merely get upper-bounded. -/
theorem exact_denominator_loss (a u h : ℕ) {t : ℤ} (ht : t∈grid a) (h0 : t≠0) :
    ((level (denominator a u h t):ℤ)-(level (numerator a u h t):ℤ)) =
      ((∑ j∈Finset.range (a-level t),
        2^(a-level t-1-j)*(j+1)*
          (taper u h (level t)-taper u h (level t+j+1)) : ℕ):ℤ) := by
  let i := level t
  have hi : i≤a := level_grid_le ht h0
  rw [denominator_level,numerator_level,Nat.cast_sum,Nat.cast_sum,← Finset.sum_sub_distrib]
  simp only [Nat.cast_mul,← mul_sub]
  change (∑ q∈others a t, weightedLoss u h t q) = _
  rw [weighted_to_drop ht h0,drop_insert_center,histogram_sum]
  change ((∑ j∈Finset.range (a+1),2^(a-j)*drop u h i j : ℕ):ℤ) = _
  have ha : a+1=(i+1)+(a-i) := by omega
  conv_lhs => rw [ha,Finset.sum_range_add]
  have hz : (∑ j∈Finset.range (i+1),2^(a-j)*drop u h i j : ℕ)=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [drop,Nat.sub_eq_zero_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  rw [hz,zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hA : a-(i+1+j)=a-i-1-j := by omega
  have hB : i+1+j-i=j+1 := by omega
  have hC : i+1+j=i+j+1 := by omega
  unfold drop
  change 2^(a-(i+1+j))*((taper u h i-taper u h (i+1+j))*(i+1+j-i)) = _
  rw [hA,hB,hC]
  ring

theorem denominator_loss_le (a u h : ℕ) {t : ℤ} (ht : t∈grid a) (h0 : t≠0) :
    level (denominator a u h t) ≤ 6*h*2^(a-level t)+level (numerator a u h t) := by
  have he := exact_denominator_loss a u h ht h0
  let i := level t
  have hs : (∑ j∈Finset.range (a-i),
        2^(a-i-1-j)*(j+1)*(taper u h i-taper u h (i+j+1))) ≤ 6*h*2^(a-i) := by
    calc
      _ ≤ ∑ j∈Finset.range (a-i), 2^(a-i-1-j)*(j+1)*(h*(j+1)) := by
        apply Finset.sum_le_sum
        intro j _
        apply Nat.mul_le_mul_left
        exact (taper_lipschitz u h i (i+j+1) (by omega)).trans_eq
          (by rw [show i+j+1-i=j+1 by omega])
      _ = h*squareMass (a-i) := by
        rw [squareMass,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ h*(6*2^(a-i)) := Nat.mul_le_mul_left _ (squareMass_cap _)
      _ = _ := by ring
  have hc : ((∑ j∈Finset.range (a-i),
        2^(a-i-1-j)*(j+1)*(taper u h i-taper u h (i+j+1)) : ℕ):ℤ) ≤ 6*h*(2:ℤ)^(a-i) := by
    exact_mod_cast hs
  change ((level (denominator a u h t):ℤ)-(level (numerator a u h t):ℤ)) = _ at he
  rw [← he] at hc
  have h := sub_le_iff_le_add.mp hc
  exact_mod_cast h

#print axioms exact_denominator_loss
#print axioms denominator_loss_le
end HermiteLoss

