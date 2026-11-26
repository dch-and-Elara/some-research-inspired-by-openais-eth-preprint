import P5PrecisionOptProfiles

/-! §7 (P.5) for the actual signed dyadic carrier of the saturated
taper, and the resulting finite precision slack. All equalities are
finite; the factor at nodes of order zero is genuinely absent. -/
namespace Paper5.PrecisionOpt
open P1DyadicGrid HermiteLoss
open scoped BigOperators

def cappedMass (n r : ℕ) : ℕ :=
  ∑ j∈Finset.range n,2^(n-1-j)*(j+1)*min (j+1) r

theorem cappedMass_succ (n r : ℕ) :
    cappedMass (n+1) r = 2*cappedMass n r+(n+1)*min (n+1) r := by
  unfold cappedMass
  rw [Finset.sum_range_succ,Finset.mul_sum]
  have hl : n+1-1-n=0 := by omega
  rw [hl,pow_zero,one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hle := Finset.mem_range.mp hj
  rw [show n+1-1-j=n-1-j+1 by omega,pow_succ]
  ring

theorem cappedMass_at_square (r : ℕ) : cappedMass r r = squareMass r := by
  unfold cappedMass squareMass
  apply Finset.sum_congr rfl
  intro j hj
  have h := Finset.mem_range.mp hj
  rw [min_eq_left (by omega),pow_two]
  ring

/-- Natural-number form of the rational finite sum in (P.5). Dividing
by 2^n gives the manuscript's two tail terms without infinite sums. -/
theorem cappedMass_closed (n r : ℕ) (hr : r≤n) :
    cappedMass n r+(2*r+6)*2^(n-r)+r*(n+2)=6*2^n := by
  induction n, hr using Nat.le_induction with
  | base =>
    have h := squareMass_closed r
    rw [cappedMass_at_square,Nat.sub_self,pow_zero,mul_one]
    nlinarith
  | succ n hr ih =>
    have he : n+1-r=n-r+1 := by omega
    rw [cappedMass_succ,min_eq_right (by omega),he,pow_succ,pow_succ (2:ℕ) n]
    nlinarith

theorem taper_order_difference (H v i j : ℕ) :
    taper v H i - taper v H (i+j) = H*min j (v-i) := by
  unfold taper
  rw [← Nat.mul_sub_left_distrib]
  congr 1
  omega

theorem root_erase_sum (u : ℕ) (t : Paper5.P3.rootNodes u) (f : ℤ→ℤ) :
    (∑ s∈(Finset.univ : Finset (Paper5.P3.rootNodes u)).erase t,f s.val) =
      ∑ s∈(Paper5.P3.rootNodes u).erase t.val,f s := by
  have ht := Finset.sum_erase_add (Finset.univ : Finset (Paper5.P3.rootNodes u))
    (fun s => f s.val) (Finset.mem_univ t)
  have hv := Finset.sum_erase_add (Paper5.P3.rootNodes u) f t.property
  rw [Finset.sum_subtype (Paper5.P3.rootNodes u) (fun _ => Iff.rfl) f] at hv
  exact add_right_cancel (ht.trans hv.symm)

theorem native_taper_stencil (u v H : ℕ) (hv : v≤u) (t : Paper5.P3.rootNodes u) :
    -Paper5.P3.nativeCarrierVal Subtype.val (taperProfile u v H) t =
      (level (denominator (2*u) v H t.val):ℤ)-level (numerator (2*u) v H t.val) := by
  unfold Paper5.P3.nativeCarrierVal
  rw [←Finset.sum_neg_distrib,denominator_level,numerator_level,Nat.cast_sum,Nat.cast_sum,
    ←Finset.sum_sub_distrib]
  let f (s : ℤ) : ℤ := (taper v H (level s):ℤ)*((level (t.val-s):ℤ)-level s)
  have hs : (∑ s∈(Finset.univ : Finset (Paper5.P3.rootNodes u)).erase t,
      -((taperProfile u v H) s:ℤ)*((level s.val:ℤ)-level (t.val-s.val))) =
        ∑ s∈(Finset.univ : Finset (Paper5.P3.rootNodes u)).erase t,f s.val := by
    apply Finset.sum_congr rfl
    intro s _
    unfold f taperProfile
    ring
  simp only [neg_mul] at hs
  rw [hs,root_erase_sum]
  have hsubset : (Paper5.P3.rootNodes u).erase t.val ⊆ others (2*u) t.val := by
    intro s hs
    have hh := Finset.mem_filter.mp (Finset.mem_of_mem_erase hs)
    exact mem_others.mpr ⟨hh.1,hh.2.1,Finset.ne_of_mem_erase hs⟩
  rw [Finset.sum_subset hsubset]
  · apply Finset.sum_congr rfl
    intro s _
    simp only [f,Nat.cast_mul]
    ring
  · intro s hs hroot
    obtain ⟨hg,hn,he⟩ := mem_others.mp hs
    have h : u≤level s := by
      by_contra hh
      exact hroot (Finset.mem_erase.mpr ⟨he,
        Finset.mem_filter.mpr ⟨hg,hn,Nat.lt_of_not_ge hh⟩⟩)
    simp [f,taper,Nat.sub_eq_zero_of_le (hv.trans h)]

theorem saturation_exact_loss (u v H : ℕ) (hv : v≤u) (t : Paper5.P3.rootNodes u) :
    -Paper5.P3.nativeCarrierVal Subtype.val (taperProfile u v H) t =
      (H*cappedMass (2*u-level t.val) (v-level t.val):ℕ) := by
  have ht := Finset.mem_filter.mp t.property
  rw [native_taper_stencil u v H hv t,exact_denominator_loss (2*u) v H ht.1 ht.2.1]
  have he : (∑ j∈Finset.range (2*u-level t.val),2^(2*u-level t.val-1-j)*(j+1)*
        (taper v H (level t.val)-taper v H (level t.val+j+1))) =
      H*cappedMass (2*u-level t.val) (v-level t.val) := by
    rw [cappedMass,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show level t.val+j+1=level t.val+(j+1) by omega,taper_order_difference]
    ring
  exact congrArg (fun n : ℕ => (n:ℤ)) he

theorem saturation_tail_slack (u v H h : ℕ) (hv : v≤u) (hH : 6*H≤8*h)
    (t : Paper5.P3.rootNodes u) (ht : 0<taperProfile u v H t) :
    (8*H*2^(2*u-v):ℕ) ≤
      (8*h*2^(2*u-level t.val):ℕ)+Paper5.P3.nativeCarrierVal Subtype.val (taperProfile u v H) t := by
  let i := level t.val
  let n := 2*u-i
  let r := v-i
  have hpos : 0<r := by
    change 0<H*r at ht
    by_contra hn
    have hz : r=0 := by omega
    rw [hz,mul_zero] at ht
    omega
  have hr : r≤n := by dsimp [r,n]; omega
  have hp : n-r=2*u-v := by dsimp [n,r]; omega
  have he := cappedMass_closed n r hr
  rw [hp] at he
  have h2 := Nat.mul_le_mul_right (H*2^(2*u-v)) (show 8≤2*r+6 by omega)
  have h3 := Nat.mul_le_mul_right (2^n) hH
  have hb : 8*H*2^(2*u-v) ≤ H*((2*r+6)*2^(2*u-v)) := by
    simpa only [Nat.mul_assoc,Nat.mul_left_comm] using h2
  have hf : (8*H*2^(2*u-v))+(H*cappedMass n r)≤8*h*2^n := by
    calc
      _ ≤ H*((2*r+6)*2^(2*u-v))+H*cappedMass n r := Nat.add_le_add_right hb _
      _ = H*(cappedMass n r+(2*r+6)*2^(2*u-v)) := by ring
      _ ≤ H*(cappedMass n r+(2*r+6)*2^(2*u-v)+r*(n+2)) :=
        Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
      _ = 6*H*2^n := by rw [he]; ring
      _ ≤ _ := h3
  have hInt : ((8*H*2^(2*u-v):ℕ):ℤ)+((H*cappedMass n r:ℕ):ℤ)≤
      ((8*h*2^n:ℕ):ℤ) := by exact_mod_cast hf
  have hc := saturation_exact_loss u v H hv t
  change -Paper5.P3.nativeCarrierVal Subtype.val (taperProfile u v H) t = (H*cappedMass n r:ℕ) at hc
  rw [←hc] at hInt
  linarith

#print axioms cappedMass_closed
#print axioms taper_order_difference
#print axioms native_taper_stencil
#print axioms saturation_exact_loss
#print axioms saturation_tail_slack
end Paper5.PrecisionOpt
