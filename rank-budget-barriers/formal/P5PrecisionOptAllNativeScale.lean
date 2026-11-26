import P5PrecisionOptAllNative
import P5PrecisionOptTheta

/-! The explicitly different comparison regime: every native
coefficient is used. This fixed profile has Θ(M 2^u/u²) window,
whereas optimizing all legal profiles gives Θ(M 2^(7u/4)/u²). -/
namespace Paper5.PrecisionOpt
open P1DyadicGrid HermiteLoss Filter Asymptotics
open scoped BigOperators

theorem all_native_scaled_witness {M u : ℕ} (hu : 0<u) (hM : u≤M) :
    M*2^u ≤ (u*u)*allNativeWindow M u := by
  let L := (2:ℕ)^(2*u)
  let T := (2:ℕ)^u
  let h := sourceH M u
  let D := 2*u+1
  let W := 2*h*2^(u+1)
  let s := orderMass u (allNativeProfile M u)-Paper5.P3.printedDegree u M
  let b := 4*M+W/D
  have hT : T≤L := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega)
  have hs : M*(L+1) ≤ s := all_native_slack M u hu
  have h1 : M*T≤(u*u)*s := by
    calc
      M*T ≤ M*(L+1) := Nat.mul_le_mul_left _ (hT.trans (Nat.le_add_right _ _))
      _ ≤ s := hs
      _ ≤ (u*u)*s := by
        have hv : 1≤u*u := Nat.mul_le_mul hu hu
        simpa only [one_mul] using Nat.mul_le_mul_right s hv
  have h2 : M*T≤(u*u)*b := by
    have hW : W≤b*D := by
      have hz := Nat.mod_lt W (show 0<D by dsimp [D]; omega)
      have hh := Nat.div_add_mod W D
      have hq : W/D+1≤b := by
        dsimp [b]
        have h4 : 1≤4*M := by omega
        exact (Nat.add_le_add_left h4 _).trans_eq (Nat.add_comm ..)
      have hp : W≤(W/D+1)*D := by
        rw [add_mul,one_mul,mul_comm (W/D) D]
        omega
      exact hp.trans (Nat.mul_le_mul_right D hq)
    have hD : D≤3*u := by dsimp [D]; omega
    have hh : 3*M≤h*u := h_cover M u hu
    have hs : 3*(M*T)≤u*W := by
      calc
        _ = (3*M)*T := by ring
        _ ≤ (h*u)*T := Nat.mul_le_mul_right _ hh
        _ ≤ ((h*u)*T)*4 := by
          have H := Nat.mul_le_mul_left ((h*u)*T) (show 1≤4 by decide)
          simpa only [mul_one] using H
        _ = _ := by dsimp [W,T]; rw [pow_succ]; ring
    have hs2 : u*W≤3*((u*u)*b) := by
      calc
        _ ≤ u*(b*D) := Nat.mul_le_mul_left _ hW
        _ ≤ u*(b*(3*u)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hD)
        _ = _ := by ring
    exact positive_left_cancel (by decide : 0<3) (hs.trans hs2)
  change M*T≤u*u*min s b
  rw [←Nat.mul_min_mul_left]
  exact le_min h1 h2

theorem all_native_scaled_upper {K : Type*} [Field K] [CharZero K] (O : Subring K)
    [IsLocalRing O] (hn2 : ¬IsUnit (2:O)) {M u : ℕ} (hu : 4≤u) (hM : u≤M) (p b : ℕ)
    (hc : RootCertified O hn2 M u p (allNativeProfile M u) b) :
    (u*u)*b ≤ 100*(M*2^u) := by
  let i := u-1
  let q := allNativeProfile M u
  let T := (2:ℕ)^u
  have hu0 : 0<u := by omega
  have hi : i<u := by dsimp [i]; omega
  have hn : Nonempty (NativeShell u i) := by
    apply Fintype.card_pos_iff.mp
    rw [native_shell_card u i hi]
    positivity
  obtain ⟨t⟩ := hn
  have hl : level t.val.val=i := rawShell_level t
  have hpos : 0<sourceH M u := by
    have hh := h_cover M u hu0
    by_contra hz
    rw [show sourceH M u=0 by omega,zero_mul] at hh
    omega
  have hqt : 0<q t.val := by
    change 0<sourceH M u*(u-level t.val.val)
    rw [hl]
    exact Nat.mul_pos hpos (by omega)
  have hdeep : ∀ s,0<q s → level s.val≤level t.val.val := by
    intro s _
    rw [hl]
    have hh := (Finset.mem_filter.mp s.property).2.2
    omega
  have HI := actual_certificate_inequalities O hn2 M u p q b hc
  have H := deepest_exact_integer_window M u p b q hc.1.1 HI t.val hqt hdeep
  rw [hl] at H
  let D := 2*u+1
  let ell := 2*u+1-i
  have hE : u≤ell := by dsimp [ell]; omega
  have hD : D≤3*u := by dsimp [D]; omega
  have hPow : (2:ℕ)^(2*u-i)=2*T := by
    dsimp [i,T]
    rw [show 2*u-(u-1)=u+1 by omega,pow_succ,mul_comm]
  have hBd : (b-1)*ell≤rootSlack M u i := by
    apply (Nat.le_div_iff_mul_le (hu0.trans_le hE)).mp
    change b≤1+rootSlack M u i/ell at H
    have hG := Nat.sub_le_sub_right H 1
    rw [Nat.add_comm (1:ℕ),Nat.add_sub_cancel] at hG
    exact hG
  have hBd' : ((b-1)*u)*u≤rootSlack M u i*u :=
    Nat.mul_le_mul_right _ ((Nat.mul_le_mul_left _ hE).trans hBd)
  have hh := h_upper M u hM
  have hQ : (u*u)*(b-1)≤64*(M*T)+24*(M*(u*u)) := by
    calc
      _ = ((b-1)*u)*u := by ring
      _ ≤ rootSlack M u i*u := hBd'
      _ = 16*(sourceH M u*u)*T+8*M*(D*u) := by
        unfold rootSlack
        rw [hPow]
        dsimp [D]
        ring
      _ ≤ 16*(4*M)*T+8*M*((3*u)*u) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hh))
          (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hD))
      _ = _ := by ring
  have htU : u*u≤T := square_le_dyadic u hu
  have h1 := Nat.mul_le_mul_left 24 (Nat.mul_le_mul_left M htU)
  have hMpos : 1≤M := by omega
  have h2 : u*u≤M*T := htU.trans (by simpa only [one_mul] using Nat.mul_le_mul_right T hMpos)
  have hde : (u*u)*b=(u*u)*(b-1)+(u*u) := by
    calc
      (u*u)*b = (u*u)*((b-1)+1) := congrArg ((u*u)*·)
        (Nat.sub_add_cancel (show 1≤b from hc.1.1)).symm
      _ = _ := by rw [Nat.mul_add,Nat.mul_one]
  change (u*u)*b ≤100*(M*T)
  rw [hde]
  omega

theorem all_native_profile_two_sided {K : Type*} [Field K] [CharZero K] (O : Subring K)
    [IsLocalRing O] (hn2 : ¬IsUnit (2:O)) {M u : ℕ} (hu : 4≤u) (hM : u≤M) (p : ℕ) :
    M*2^u ≤ (u*u)*profileCap M u p (allNativeProfile M u) ∧
      (u*u)*profileCap M u p (allNativeProfile M u) ≤ 100*(M*2^u) := by
  have hu0 : 0<u := by omega
  have hb := all_native_window_pos M u hu0 (hu0.trans_le hM)
  have hc := all_native_window_certified O hn2 hu0 hM p
  have hcap := (fixed_profile_cap_exact O hn2 M u p (allNativeProfile M u) hb).mp hc
  have hv := all_native_scaled_witness hu0 hM
  have hc' := (fixed_profile_cap_exact O hn2 M u p (allNativeProfile M u) (hb.trans_le hcap)).mpr le_rfl
  exact ⟨hv.trans (Nat.mul_le_mul_left _ hcap),all_native_scaled_upper O hn2 hu hM p _ hc'⟩

#print axioms all_native_scaled_witness
#print axioms all_native_scaled_upper
#print axioms all_native_profile_two_sided
end Paper5.PrecisionOpt
