import P5PrecisionOptFiniteUpper
import P5PrecisionOptTail

/-! The unoptimized all-native-coefficients profile, for comparison
with (P.4)–(P.9). The exact finite certificate is for the same degree
window and the same fixed decoder, not for all representations. -/
namespace Paper5.PrecisionOpt
open P1DyadicGrid HermiteLoss
open scoped BigOperators

def allNativeProfile (M u : ℕ) : Profile u := taperProfile u u (sourceH M u)

def allNativeWindow (M u : ℕ) : ℕ :=
  min (orderMass u (allNativeProfile M u)-Paper5.P3.printedDegree u M)
    (4*M+(2*sourceH M u*2^(u+1))/(2*u+1))

theorem all_native_slack (M u : ℕ) (hu : 0<u) :
    M*(2^(2*u)+1) ≤ orderMass u (allNativeProfile M u)-Paper5.P3.printedDegree u M := by
  let L : ℕ := 2^(2*u)
  let s := orderMass u (allNativeProfile M u)
  let h := sourceH M u
  have hd : Paper5.P3.printedDegree u M+M=2*M*L := by
    unfold Paper5.P3.printedDegree
    have hL : 0<L := by dsimp [L]; positivity
    change M*(2*L-1)+M=2*M*L
    calc
      M*(2*L-1)+M = M*((2*L-1)+1) := by rw [Nat.mul_add,Nat.mul_one]
      _ = _ := by rw [Nat.sub_add_cancel (by omega)]; ring
  have hs0 : L*u≤shellTaperMass (2*u) u := by
    unfold shellTaperMass
    have he := Finset.single_le_sum (f:=fun j => (2:ℕ)^(2*u-j)*(u-j))
      (fun j _ => Nat.zero_le _) (Finset.mem_range.mpr hu)
    simpa only [Nat.sub_zero] using he
  have hs : 3*M*L≤s := by
    change 3*M*L≤orderMass u (taperProfile u u h)
    rw [taperProfile_mass u u h le_rfl]
    calc
      3*M*L ≤ (h*u)*L := Nat.mul_le_mul_right _ (h_cover M u hu)
      _ = h*(L*u) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hs0
  change M*(L+1)≤s-Paper5.P3.printedDegree u M
  rw [Nat.mul_add,Nat.mul_one]
  have h1 : 3*M*L=2*M*L+M*L := by ring
  rw [h1] at hs
  omega

theorem all_native_window_pos (M u : ℕ) (hu : 0<u) (hM : 0<M) :
    0<allNativeWindow M u := by
  have hs := all_native_slack M u hu
  exact lt_min ((show 0 < M*(2^(2*u)+1) by positivity).trans_le hs)
    ((show 0<4*M by omega).trans_le (Nat.le_add_right _ _))

theorem all_native_carrier_slack (M u : ℕ) (t : Paper5.P3.rootNodes u) :
    ((2*sourceH M u*2^(u+1):ℕ):ℤ) ≤
      ((8*sourceH M u*2^(2*u-level t.val):ℕ):ℤ)+
        Paper5.P3.nativeCarrierVal Subtype.val (allNativeProfile M u) t := by
  let h := sourceH M u
  let i := level t.val
  let c := Paper5.P3.nativeCarrierVal Subtype.val (allNativeProfile M u) t
  let DN := (2:ℕ)^(2*u-i)
  have ht := Finset.mem_filter.mp t.property
  have h1 := native_taper_stencil u u h le_rfl t
  change -c=(level (denominator (2*u) u h t.val):ℤ)-level (numerator (2*u) u h t.val) at h1
  have h2 := denominator_loss_le (2*u) u h ht.1 ht.2.1
  have hi : i<u := ht.2.2
  have hDN : (2:ℕ)^(u+1)≤DN := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega)
  have hI : -(c:ℤ)≤ ((6*h*DN:ℕ):ℤ) := by
    rw [h1,sub_le_iff_le_add]
    exact_mod_cast h2
  have hb : 2*h*2^(u+1)≤2*h*DN := Nat.mul_le_mul_left _ hDN
  have hh : (8*h*DN:ℕ)= (2*h*DN)+(6*h*DN) := by ring
  change ((2*h*2^(u+1):ℕ):ℤ)≤((8*h*DN:ℕ):ℤ)+c
  rw [hh,Nat.cast_add]
  exact (show ((2*h*2^(u+1):ℕ):ℤ) ≤ ((2*h*DN:ℕ):ℤ) from by exact_mod_cast hb).trans (by omega)

theorem window_from_uniform_slack (M u p W b : ℕ) (q : Profile u)
    (hq : ∀ t,q t≤4*M) (hb : b≤4*M+W/(2*u+1))
    (hcar : ∀ t,0<q t → (W:ℤ)≤((8*sourceH M u*2^(2*u-level t.val):ℕ):ℤ)+
      Paper5.P3.nativeCarrierVal Subtype.val q t) :
    RootInequalities M u p q b := by
  intro t ht
  let D := 2*u+1
  have hL : 0<Paper5.P3.nativeLoss (2*u) t.val := Paper5.P3.native_loss_positive
    (Finset.mem_filter.mp t.property).1 (Finset.mem_filter.mp t.property).2.1
  have hLD : Paper5.P3.nativeLoss (2*u) t.val ≤ (D:ℤ) := by simp [Paper5.P3.nativeLoss,D]
  have hQ := hq t
  have hmul : ((b:ℤ)+(q t:ℤ)-2)*Paper5.P3.nativeLoss (2*u) t.val ≤
      (((8*M+W/D)*D:ℕ):ℤ) := by
    have hLHS : ((b:ℤ)+(q t:ℤ)-2)≤((8*M+W/D:ℕ):ℤ) := by change b≤4*M+W/D at hb; omega
    rw [Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_right hLHS hL.le).trans
      (mul_le_mul_of_nonneg_left hLD (by positivity))
  have hD : ((8*M+W/D)*D:ℕ)≤8*M*D+W := by
    rw [Nat.add_mul]
    exact Nat.add_le_add_left (Nat.div_mul_le_self _ _) _
  have hcar' := hcar t ht
  have hsum := rootSlack_eq M u p t
  rw [hsum]
  calc
    _ ≤ (((8*M+W/D)*D:ℕ):ℤ) := hmul
    _ ≤ ((8*M*D+W:ℕ):ℤ) := by exact_mod_cast hD
    _ ≤ (rootSlack M u (level t.val):ℤ)+Paper5.P3.nativeCarrierVal Subtype.val q t := by
      unfold rootSlack
      change (((8*M*D+W:ℕ):ℤ))≤
        ((8*sourceH M u*2^(2*u-level t.val)+8*M*D:ℕ):ℤ)+Paper5.P3.nativeCarrierVal Subtype.val q t
      simp only [Nat.cast_add]
      omega

theorem all_native_window_certified {K : Type*} [Field K] [CharZero K] (O : Subring K)
    [IsLocalRing O] (hn2 : ¬IsUnit (2:O)) {M u : ℕ} (hu : 0<u) (hM : u≤M) (p : ℕ) :
    RootCertified O hn2 M u p (allNativeProfile M u) (allNativeWindow M u) := by
  have hb := all_native_window_pos M u hu (hu.trans_le hM)
  have H : RootInequalities M u p (allNativeProfile M u) (allNativeWindow M u) :=
    window_from_uniform_slack M u p (2*sourceH M u*2^(u+1)) _ _
      (fun t => q_cap M u (level t.val) hM) (min_le_right _ _)
      (fun t _ => all_native_carrier_slack M u t)
  exact ⟨⟨hb,min_le_left _ _⟩,
    (Paper5.P3.printed_root_p1 O hn2 u M (Paper5.P3.printedHeight u M) p
      (allNativeWindow M u) hb (allNativeProfile M u)).mpr H⟩

#print axioms all_native_slack
#print axioms all_native_carrier_slack
#print axioms window_from_uniform_slack
#print axioms all_native_window_certified
end Paper5.PrecisionOpt
