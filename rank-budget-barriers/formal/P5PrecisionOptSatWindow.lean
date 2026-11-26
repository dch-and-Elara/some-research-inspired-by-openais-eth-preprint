import P5PrecisionOptTail

/-! §7 (P.6) as a literal finite recovery certificate, with explicit
finite parameter threshold. No claim about costs at unretained nodes
or a different decoder is made. -/
namespace Paper5.PrecisionOpt
open P1DyadicGrid HermiteLoss
open scoped BigOperators

def adaptedProfile (M u : ℕ) : Profile u :=
  taperProfile u (adaptedDepth M u) (adaptedHeight M u)

def adaptedWindow (M u : ℕ) : ℕ :=
  min (orderMass u (adaptedProfile M u) - Paper5.P3.printedDegree u M)
    (4*M+(8*adaptedHeight M u*2^(2*u-adaptedDepth M u))/(2*u+1))

theorem adapted_window_pos {M u : ℕ} (hu : 8≤u) (hM : u≤M) : 0<adaptedWindow M u := by
  obtain ⟨_,_,hv,hcov,_⟩ := adapted_profile_parameters hu hM
  have hs := taperProfile_degree_slack M u (adaptedDepth M u) (adaptedHeight M u) hv hcov
  have h1 : 0<orderMass u (adaptedProfile M u)-Paper5.P3.printedDegree u M :=
    (show 0<2*adaptedHeight M u*2^(2*u)+M by omega).trans_le hs
  exact lt_min h1 ((show 0<4*M by omega).trans_le (Nat.le_add_right _ _))

theorem adapted_window_admissible {M u : ℕ} (hu : 8≤u) (hM : u≤M) :
    Paper5.P3.degreeAdmissible (adaptedProfile M u) (Paper5.P3.printedDegree u M)
      (adaptedWindow M u) := by
  exact ⟨adapted_window_pos hu hM,min_le_left _ _⟩

theorem adapted_window_inequality {M u : ℕ} (hu : 8≤u) (hM : u≤M) (p : ℕ)
    (t : Paper5.P3.rootNodes u) (ht : 0<adaptedProfile M u t) :
    ((adaptedWindow M u:ℤ)+(adaptedProfile M u t:ℤ)-2)*Paper5.P3.nativeLoss (2*u) t.val ≤
      Paper5.P3.rootPrecision u M (Paper5.P3.printedHeight u M) p t.val-p+
        Paper5.P3.nativeCarrierVal Subtype.val (adaptedProfile M u) t := by
  obtain ⟨_,_,hv,_,_⟩ := adapted_profile_parameters hu hM
  let H := adaptedHeight M u
  let v := adaptedDepth M u
  let h := sourceH M u
  let q := adaptedProfile M u
  let b := adaptedWindow M u
  let c := Paper5.P3.nativeCarrierVal Subtype.val q t
  let W : ℕ := 8*H*2^(2*u-v)
  let D : ℕ := 2*u+1
  have h6 : 6*H≤8*h := (adapted_height_arithmetic M u).2
  have hcN := saturation_tail_slack u v H h hv h6 t ht
  change (W:ℤ) ≤ ((8*h*2^(2*u-level t.val):ℕ):ℤ)+c at hcN
  have hcv : q t≤4*M := (adapted_profile_admissible hu hM t).trans
    (q_cap M u (level t.val) hM)
  have hb : b≤4*M+W/D := min_le_right _ _
  have hL : 0 < Paper5.P3.nativeLoss (2*u) t.val := Paper5.P3.native_loss_positive
    (Finset.mem_filter.mp t.property).1 (Finset.mem_filter.mp t.property).2.1
  have hL' : Paper5.P3.nativeLoss (2*u) t.val ≤ (D:ℤ) := by
    simp [Paper5.P3.nativeLoss,D]
  have hJ : ((b:ℤ)+(q t:ℤ)-2)≤((8*M+W/D:ℕ):ℤ) := by omega
  have hprod := mul_le_mul_of_nonneg_right hJ hL.le
  have hprod2 := mul_le_mul_of_nonneg_left hL' (Int.natCast_nonneg (8*M+W/D))
  have hdiv : W/D*D≤W := Nat.div_mul_le_self _ _
  have hsum : ((8*M+W/D)*D:ℕ)≤(8*M)*D+W := by rw [Nat.add_mul]; omega
  have hi : ((b:ℤ)+(q t:ℤ)-2)*Paper5.P3.nativeLoss (2*u) t.val ≤ ((8*M)*D+W:ℕ) := by
    have h := hprod.trans hprod2
    exact h.trans (by exact_mod_cast hsum)
  have he : Paper5.P3.rootPrecision u M (Paper5.P3.printedHeight u M) p t.val-(p:ℤ) =
      ((8*h*2^(2*u-level t.val):ℕ):ℤ)+(((8*M)*D:ℕ):ℤ) := by
    change (p:ℤ)+8*(h:ℤ)*(2:ℤ)^(2*u-level t.val)+8*(M:ℤ)*(2*(u:ℤ)+1)-(p:ℤ)=_
    push_cast
    dsimp [D]
    ring
  change ((b:ℤ)+(q t:ℤ)-2)*Paper5.P3.nativeLoss _ _ ≤ _+c
  rw [he]
  calc
    _ ≤ (((8*M)*D+W:ℕ):ℤ) := hi
    _ = (((8*M)*D:ℕ):ℤ)+(W:ℤ) := Nat.cast_add _ _
    _ ≤ _ := by omega

theorem adapted_window_actual {K : Type*} [Field K] [CharZero K] (O : Subring K)
    [IsLocalRing O] (hn2 : ¬IsUnit (2:O)) {M u : ℕ} (hu : 8≤u) (hM : u≤M) (p : ℕ) :
    Paper5.P3.ActualCertified O (fun t : Paper5.P3.rootNodes u => Paper5.P3.nativeCenter (2*u) t.val)
      (adaptedProfile M u) (adaptedWindow M u)
      (fun s t => Paper5.P3.nativeDifference_integral_inverses O hn2 (2*u) s.val t.val
        (Finset.mem_filter.mp s.property).1 (Finset.mem_filter.mp t.property).1)
      (fun t => (↑(Paper5.P3.twoUnit K^Paper5.P3.rootPrecision u M (Paper5.P3.printedHeight u M) p t.val):K))
      (↑(Paper5.P3.twoUnit K^(p:ℤ)):K) :=
  (Paper5.P3.printed_root_p1 O hn2 u M (Paper5.P3.printedHeight u M) p
    (adaptedWindow M u) (adapted_window_pos hu hM) (adaptedProfile M u)).2
      (adapted_window_inequality hu hM p)

#print axioms adapted_window_admissible
#print axioms adapted_window_inequality
#print axioms adapted_window_actual
end Paper5.PrecisionOpt
