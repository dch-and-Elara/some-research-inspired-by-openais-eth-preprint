import V8NativeMessageN1MainRegister
import Mathlib.Data.Nat.Log

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

/-! A coefficient-height theorem for reduced rationals, not just a bound
on an arbitrarily chosen representation. Includes all intermediate group
summands, accumulator values, and partial products of actual N1. -/
namespace V8NativeMessage.N1
open scoped Classical BigOperators Polynomial
open Polynomial V8NativeMessage.C3.NativeAssembly.MainScan
noncomputable section

def jetCoeff (J j : ℕ) (x : Jet J) : ℚ :=
  (AdjoinRoot.modByMonicHom (monic_X.pow J) x).coeff j

theorem jetify_coeff (J j : ℕ) (hj : j<J) (p : ℤ[X]) :
    jetCoeff J j (jetify J p)=(p.coeff j:ℚ) := by
  simp only [jetCoeff,jetify,RingHom.comp_apply,AdjoinRoot.modByMonicHom_mk]
  change ((p.map (Int.castRingHom ℚ)) %ₘ ((X:ℚ[X])^J)).coeff j=_
  rw [modByMonic_eq_sub_mul_div _ (monic_X.pow J),coeff_sub,coeff_X_pow_mul',if_neg (not_le.mpr hj),
    sub_zero,coeff_map]
  rfl

theorem jetCoeff_scale (J j d : ℕ) (x : Jet J) :
    jetCoeff J j ((d:Jet J)*x)=(d:ℚ)*jetCoeff J j x := by
  have he : (d:Jet J)*x=(d:ℚ) • x := by rw [Algebra.smul_def,map_natCast]
  rw [he,jetCoeff,LinearMap.map_smul,coeff_smul,smul_eq_mul]
  rfl

theorem normalized_rational_bound (q : ℚ) (d : ℕ) (hd : 0<d) (a : ℤ) (h : (d:ℚ)*q=(a:ℚ)) :
    q.den∣d ∧ q.num.natAbs≤a.natAbs := by
  have hn : (d:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hq : q=Rat.divInt a (d:ℤ) := by
    rw [Rat.divInt_eq_div,Int.cast_natCast]
    apply (eq_div_iff hn).mpr
    exact (mul_comm q (d:ℚ)).trans h
  rw [hq]
  constructor
  · obtain ⟨z,hz⟩ := Rat.den_dvd a (d:ℤ)
    refine ⟨z.natAbs,?_⟩
    simpa only [Int.natAbs_natCast,Int.natAbs_mul] using congrArg Int.natAbs hz
  · by_cases ha : a=0
    · subst a
      simp
    · have hd' : (d:ℤ)≠0 := by exact_mod_cast (Nat.ne_of_gt hd)
      obtain ⟨z,hz⟩ := Rat.num_dvd a hd'
      apply Nat.le_of_dvd (Int.natAbs_pos.mpr ha)
      refine ⟨z.natAbs,?_⟩
      simpa only [Int.natAbs_mul] using congrArg Int.natAbs hz

theorem integral_jet_height (J j d : ℕ) (hj : j<J) (hd : 0<d) (x : Jet J) (p : ℤ[X])
    (h : jetify J p=(d:Jet J)*x) :
    (jetCoeff J j x).den∣d ∧ (jetCoeff J j x).num.natAbs≤coeffNorm p := by
  have he : (d:ℚ)*jetCoeff J j x=(p.coeff j:ℚ) := by
    rw [← jetCoeff_scale,← h,jetify_coeff _ _ hj]
  obtain ⟨hD,hA⟩ := normalized_rational_bound _ _ hd _ he
  exact ⟨hD,hA.trans (coeff_le_norm _ _)⟩

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {r Q J : ℕ}
variable (L : CloneTuple F r Q J) (hreg : ∀ v, GraphCutMoments.degree F v=3)
variable {R BP : ℕ} (H : RowBound L hreg R BP)

include H in
theorem row_coefficient_height (o : Occ F) (v : Clone W) (j : ℕ) :
    ((row L hreg o v).coeff j).den∣δ R Q ∧
      ((row L hreg o v).coeff j).num.natAbs≤2^BP := by
  obtain ⟨a,he,ha⟩ := H.scaled o v j
  rw [coeff_C_mul] at he
  obtain ⟨hd,hn⟩ := normalized_rational_bound _ _ (δ_pos R Q) _ he.symm
  exact ⟨hd,hn.trans ha⟩

include H in
theorem unary_height (s : W→Bool) (x : Clone W→Bool) (v : W) (j : Fin J) :
    (jetCoeff J j (signedArg L x s v)).den∣δ R Q ∧
      (jetCoeff J j (signedArg L x s v)).num.natAbs≤B₀ W R Q BP := by
  have hp := jetify_literal L hreg H x (.inl v) (s v)
  have hA := norm_literal L hreg H x (.inl v) (s v)
  obtain ⟨hd,hn⟩ := integral_jet_height J j (δ R Q) j.isLt (δ_pos R Q)
    _ _ hp
  exact ⟨hd,hn.trans hA⟩

include H in
theorem summand_height (s : W→Bool) (g : Fin r) (x : Clone W→Bool) (j : Fin J) :
    (jetCoeff J j (nativeGroup F hreg L s g x)).den∣(δ R Q)^(groupDeg L g) ∧
      (jetCoeff J j (nativeGroup F hreg L s g x)).num.natAbs≤A W R Q BP^(groupDeg L g) := by
  obtain ⟨hd,hn⟩ := integral_jet_height J j ((δ R Q)^(groupDeg L g)) j.isLt
    (Nat.pow_pos (δ_pos _ _)) _ _ (by rw [Nat.cast_pow]; exact int_group_lift L hreg H s g x)
  exact ⟨hd,hn.trans (norm_group L hreg H s g x)⟩

include H in
theorem accumulation_height (s : W→Bool) (h : feasible L.frame) (g : Fin r)
    (xs : Finset (Word L.frame g)) (j : Fin J) :
    (jetCoeff J j (ratAccum L hreg s h g xs)).den∣(δ R Q)^(groupDeg L g) ∧
      (jetCoeff J j (ratAccum L hreg s h g xs)).num.natAbs≤2^room L g*A W R Q BP^(groupDeg L g) := by
  obtain ⟨hd,hn⟩ := integral_jet_height J j ((δ R Q)^(groupDeg L g)) j.isLt
    (Nat.pow_pos (δ_pos _ _)) _ _ (by rw [Nat.cast_pow]; exact int_accum_lift L hreg H s h g xs)
  exact ⟨hd,hn.trans (norm_accum L hreg H s h g xs)⟩

include H in
theorem partial_rational_height (s : W→Bool) (h : feasible L.frame) (G : Finset (Fin r))
    (xs : ∀ g, Finset (Word L.frame g)) (j : Fin J) :
    (jetCoeff J j (ratPartial L hreg s h G xs)).den∣(δ R Q)^(degreeAt L G) ∧
      (jetCoeff J j (ratPartial L hreg s h G xs)).num.natAbs≤
        2^roomAt L G*A W R Q BP^(degreeAt L G) := by
  obtain ⟨hd,hn⟩ := integral_jet_height J j ((δ R Q)^(degreeAt L G)) j.isLt
    (Nat.pow_pos (δ_pos _ _)) _ _ (by rw [Nat.cast_pow]; exact int_partial_lift L hreg H s h G xs)
  exact ⟨hd,hn.trans (norm_partial L hreg H s h G xs)⟩

include H in
theorem completed_rational_height (s : W→Bool) (h : feasible L.frame) (j : Fin J) :
    (jetCoeff J j (nativeScan F hreg L s).2.2).den∣(δ R Q)^(12*Fintype.card W) ∧
      (jetCoeff J j (nativeScan F hreg L s).2.2).num.natAbs≤
        2^(4*Fintype.card W)*A W R Q BP^(12*Fintype.card W) := by
  rw [completed_is_full_partial L hreg s h]
  have hp := partial_rational_height L hreg H s h Finset.univ (fullFibre L) j
  simpa only [degreeAt,roomAt,total_group_degree L,native_degree hreg,total_room L] using hp

def within (bits : ℕ) (q : ℚ) : Prop := q.num.natAbs<2^bits ∧ q.den<2^bits

theorem bits_of_bounds {q : ℚ} {d m b base a : ℕ} (ha : 0<a) (hle : a≤base)
    (hb : base≤2^b) (hd : q.den∣a^d) (hn : q.num.natAbs≤2^m*base^d) :
    within (m+b*d+1) q := by
  have h₁ : base^d≤2^(b*d) := by rw [pow_mul]; exact Nat.pow_le_pow_left hb d
  have hnum : q.num.natAbs≤2^(m+b*d) := by
    rw [pow_add]
    exact hn.trans (Nat.mul_le_mul_left _ h₁)
  have hden : q.den≤2^(m+b*d) := by
    refine (Nat.le_of_dvd (Nat.pow_pos ha) hd).trans ((Nat.pow_le_pow_left hle d).trans (h₁.trans ?_))
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hlt : 2^(m+b*d)<2^(m+b*d+1) := Nat.pow_lt_pow_right (by decide) (by omega)
  exact ⟨hnum.trans_lt hlt,hden.trans_lt hlt⟩

omit [DecidableEq W] in
theorem base_pos : 0<A W R Q BP := by
  unfold A
  exact Nat.mul_pos (by decide) ((δ_pos R Q).trans_le (δ_le_B₀ (W:=W)))

omit [DecidableEq W] in
theorem δ_le_base : δ R Q≤A W R Q BP :=
  (δ_le_B₀ (W:=W) (R:=R) (Q:=Q) (BP:=BP)).trans (by unfold A; omega)

include H in
/-- A sign bit is additional if signed binary encoding is used. Both
magnitudes fit the displayed width (including zero numerator). -/
theorem completed_bit_height (s : W→Bool) (h : feasible L.frame) (j : Fin J) :
    within (4*Fintype.card W+(Nat.log 2 (A W R Q BP)+1)*(12*Fintype.card W)+1)
      (jetCoeff J j (nativeScan F hreg L s).2.2) := by
  obtain ⟨hd,hn⟩ := completed_rational_height L hreg H s h j
  exact bits_of_bounds (δ_pos _ _) (δ_le_base (W:=W))
    (Nat.lt_pow_succ_log_self (by decide) _).le hd hn

#print axioms jetify_coeff
#print axioms jetCoeff_scale
#print axioms normalized_rational_bound
#print axioms integral_jet_height
#print axioms row_coefficient_height
#print axioms unary_height
#print axioms summand_height
#print axioms accumulation_height
#print axioms partial_rational_height
#print axioms completed_rational_height
#print axioms bits_of_bounds
#print axioms completed_bit_height
end
end V8NativeMessage.N1
