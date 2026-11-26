import P5PrecisionOptP9
import P5PrecisionOptRecurrence

/-! Finite uniform upper constraints for the full nodewise optimum:
a real deepest retained node exists and sees the short precision
window; the total profile mass pays the proven reverse shell bound. -/
namespace Paper5.PrecisionOpt
open P1DyadicGrid HermiteLoss
open scoped BigOperators

def meanAllowance (M u : ℕ) : ℚ :=
  4*(sourceH M u:ℚ)+(M:ℚ)*(12*(2*u:ℕ)+16)/(2:ℚ)^(u+2)

theorem orderMass_grouped (u : ℕ) (q : Profile u) :
    orderMass u q = ∑ j∈Finset.range u,shellOrderMass u q j := by
  unfold orderMass shellOrderMass shell
  have h (t : Paper5.P3.rootNodes u) (_ : t∈Finset.univ) : level t.val∈Finset.range u :=
    Finset.mem_range.mpr (Finset.mem_filter.mp t.property).2.2
  exact (Finset.sum_fiberwise_of_maps_to h q).symm

theorem orderMass_mean_reindex (u v : ℕ) (q : Profile u) (hv : v≤u)
    (hcut : ∀ j,v ≤ j → shellMean u q j=0) :
    (orderMass u q:ℚ)/(2:ℚ)^(2*u) =
      ∑ j∈Finset.range v,shellMean u q j/(2:ℚ)^j := by
  rw [orderMass_grouped,Nat.cast_sum,Finset.sum_div]
  have H : (∑ j∈Finset.range u,(shellOrderMass u q j:ℚ)/(2:ℚ)^(2*u)) =
          ∑ j∈Finset.range u,shellMean u q j/(2:ℚ)^j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hlt := Finset.mem_range.mp hj
    have he : (2:ℚ)^(2*u)=(2:ℚ)^(2*u-j)*(2:ℚ)^j := by
      rw [←pow_add,Nat.sub_add_cancel (by omega)]
    rw [he]
    unfold shellMean
    ring
  rw [H]
  symm
  apply Finset.sum_subset (Finset.range_mono hv)
  intro j _ hj
  rw [hcut j (Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))),zero_div]

theorem zero_mean_after_deepest (u : ℕ) (q : Profile u) (t : Paper5.P3.rootNodes u)
    (hdeep : ∀ s,0<q s → level s.val≤level t.val) :
    ∀ j, level t.val+1≤j → shellMean u q j=0 := by
  intro j hj
  have hz : shellOrderMass u q j=0 := by
    apply Finset.sum_eq_zero
    intro s hs
    by_contra h
    have hL := hdeep s (Nat.pos_of_ne_zero h)
    have hE := (Finset.mem_filter.mp hs).2
    omega
  simp [shellMean,hz]

theorem exists_deepest_retained (u : ℕ) (q : Profile u) (Snonzero : 0<orderMass u q) :
    ∃ t : Paper5.P3.rootNodes u,0<q t ∧ ∀ s,0<q s → level s.val≤level t.val := by
  let A : Finset (Paper5.P3.rootNodes u) := Paper5.P3.activeNodes q
  have hA : A.Nonempty := by
    by_contra hn
    have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hz (t : Paper5.P3.rootNodes u) : q t=0 := by
      by_contra h
      have ht : t∈A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,Nat.pos_of_ne_zero h⟩
      simp [he] at ht
    simp [orderMass,hz] at Snonzero
  let I := A.image (fun t => level t.val)
  have hI : I.Nonempty := hA.image _
  obtain ⟨t,ht,he⟩ := Finset.mem_image.mp (Finset.max'_mem I hI)
  have hpos : 0<q t := (Finset.mem_filter.mp ht).2
  refine ⟨t,hpos,?_⟩
  intro s hs
  have hIn : level s.val∈I :=
    Finset.mem_image.mpr ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩,rfl⟩
  rw [he]
  exact Finset.le_max' I _ hIn

theorem paper_mean_recurrence (M u p b : ℕ) (hM : u≤M) (q : Profile u)
    (hq : admissibleOrders M u q) (hb : 0<b) (hcert : RootInequalities M u p q b)
    (v : ℕ) (hv : v≤u) (hcut : ∀ j,v ≤ j → shellMean u q j=0) :
    (orderMass u q:ℚ)/(2:ℚ)^(2*u) ≤ meanAllowance M u/3*(2*(v:ℚ)+2) := by
  have hB : 0≤meanAllowance M u := by unfold meanAllowance; positivity
  have hrec (i : ℕ) (hi : i<v) :=
    arbitrary_native_p9 M u p b hM q hq hb hcert i (hi.trans_le hv)
  have hScale : 8*(sourceH M u:ℚ)+(M:ℚ)*(12*(2*u:ℕ)+16)/(2:ℚ)^(u+1)
      = 2*meanAllowance M u := by
    unfold meanAllowance
    rw [pow_succ (2:ℚ) (u+1)]
    field_simp
    ring
  simp_rw [hScale] at hrec
  have h := finite_backward_means (shellMean u q) hv _ hB (shellMean_nonnegative u q) hcut hrec
  rw [orderMass_mean_reindex u v q hv hcut]
  exact reverse_mean_totals _ v _ hB h

theorem deepest_exact_integer_window (M u p b : ℕ) (q : Profile u) (hb : 0<b)
    (hcert : RootInequalities M u p q b) (t : Paper5.P3.rootNodes u) (ht : 0<q t)
    (deep : ∀ s,0<q s → level s.val≤level t.val) :
    b≤1+rootSlack M u (level t.val)/(2*u+1-level t.val) := by
  let i := level t.val
  let ell := 2*u+1-i
  have hi : i<u := (Finset.mem_filter.mp t.property).2.2
  have he : 0<ell := by dsimp [ell]; omega
  have hL : Paper5.P3.nativeLoss (2*u) t.val=(ell:ℤ) := by
    unfold Paper5.P3.nativeLoss
    change ((2*u+1:ℕ):ℤ)-(i:ℤ)=(ell:ℤ)
    rw [show ell=2*u+1-i by rfl,Nat.cast_sub (by omega)]
  have hn := deepest_carrier_nonpositive u q t deep
  have h := hcert t ht
  rw [rootSlack_eq,hL] at h
  change ((b:ℤ)+(q t:ℤ)-2)*(ell:ℤ) ≤
    (rootSlack M u i:ℤ)+Paper5.P3.nativeCarrierVal Subtype.val q t at h
  have h' : ((b-1:ℕ):ℤ)*(ell:ℤ) ≤ (rootSlack M u i:ℤ) := by
    have h0 : ((b-1:ℕ):ℤ)≤(b:ℤ)+q t-2 := by omega
    have hw := mul_le_mul_of_nonneg_right h0 (by positivity : 0≤(ell:ℤ))
    exact hw.trans (h.trans (by omega))
  have hN : (b-1)*ell≤rootSlack M u i := by exact_mod_cast h'
  have hQ := (Nat.le_div_iff_mul_le he).mpr hN
  change b≤1+rootSlack M u i/ell
  calc
    b = (b-1)+1 := (Nat.sub_add_cancel (show 1≤b from hb)).symm
    _ ≤ rootSlack M u i/ell+1 := Nat.add_le_add_right hQ _
    _ = _ := Nat.add_comm ..

theorem actual_profile_finite_upper {K : Type*} [Field K] [CharZero K] (O : Subring K)
    [IsLocalRing O] (hn2 : ¬IsUnit (2:O)) (M u p : ℕ) (hM : u≤M)
    (q : Profile u) (hq : admissibleOrders M u q) (b : ℕ)
    (hc : RootCertified O hn2 M u p q b) :
    ∃ t : Paper5.P3.rootNodes u,0<q t ∧
      (∀ s,0<q s → level s.val≤level t.val) ∧
      (Paper5.P3.printedDegree u M:ℚ)/(2:ℚ)^(2*u) <
        meanAllowance M u/3*(2*((level t.val+1:ℕ):ℚ)+2) ∧
      b≤1+rootSlack M u (level t.val)/(2*u+1-level t.val) := by
  let s := orderMass u q
  have hs : Paper5.P3.printedDegree u M < s := by
    have hfit := hc.1.2
    have hpos := hc.1.1
    change b≤s-Paper5.P3.printedDegree u M at hfit
    omega
  obtain ⟨t,ht,deep⟩ := exists_deepest_retained u q (Nat.zero_lt_of_lt hs)
  let v := level t.val+1
  have hv : v≤u := (Nat.succ_le_of_lt (Finset.mem_filter.mp t.property).2.2)
  have hp := actual_certificate_inequalities O hn2 M u p q b hc
  have hx := paper_mean_recurrence M u p b hM q hq hc.1.1 hp v hv
    (zero_mean_after_deepest u q t deep)
  have hlt : (Paper5.P3.printedDegree u M:ℚ)/(2:ℚ)^(2*u) < (s:ℚ)/(2:ℚ)^(2*u) :=
    div_lt_div_of_pos_right (by exact_mod_cast hs) (by positivity)
  exact ⟨t,ht,deep,hlt.trans_le hx,deepest_exact_integer_window M u p b q hc.1.1 hp t ht deep⟩

#print axioms orderMass_mean_reindex
#print axioms exists_deepest_retained
#print axioms paper_mean_recurrence
#print axioms deepest_exact_integer_window
#print axioms actual_profile_finite_upper
end Paper5.PrecisionOpt
