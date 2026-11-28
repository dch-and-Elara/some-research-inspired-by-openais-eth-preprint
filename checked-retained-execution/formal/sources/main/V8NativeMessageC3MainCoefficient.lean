import V8NativeMessageC3MainRegisterLoss
import V8NativeMessageC3Canonical

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4500000

/-! An actual extracted MAIN coefficient, not a nominal loss label:
every retained coefficient of the real complete private-list register
has two-adic loss at most d·v₂(δ), for dyadically integral jet weights. -/
namespace V8NativeMessage.C3.RawMain
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P1DyadicGrid J6R9Recursive V8PooledRange
noncomputable section

def jetCoeff (k j : ℕ) (x : C3.Jet ℚ k) : ℚ :=
  (AdjoinRoot.modByMonicHom (monic_X.pow k) x).coeff j

theorem integral_coefficient (k j : ℕ) (x : C3.Jet ℚ k) (h : x∈localJetImage k) :
    jetCoeff k j x ∈ twoLocalSubalgebra := by
  obtain ⟨p,hp⟩ := h
  change localJetHom k p=x at hp
  rw [← hp]
  unfold jetCoeff
  simp only [localJetHom,RingHom.comp_apply,AdjoinRoot.modByMonicHom_mk]
  change (p.map twoLocalRat %ₘ ((X:ℚ[X])^k)).coeff j ∈ twoLocalSubalgebra
  have he : (p %ₘ ((X:TwoLocal[X])^k)).map twoLocalRat =
      p.map twoLocalRat %ₘ ((X:ℚ[X])^k) := by
    simpa only [Polynomial.map_pow,Polynomial.map_X] using
      (Polynomial.map_modByMonic twoLocalRat (monic_X.pow k) :
        (p %ₘ ((X:TwoLocal[X])^k)).map twoLocalRat =
          p.map twoLocalRat %ₘ (((X:TwoLocal[X])^k).map twoLocalRat))
  rw [← he,Polynomial.coeff_map]
  exact ((p %ₘ ((X:TwoLocal[X])^k)).coeff j).property

theorem remove_odd_scale {d₀ : ℕ} (h₀ : 0<d₀) (d : ℕ) (x : ℚ)
    (h : ((d₀:ℚ)^d)*x∈twoLocalSubalgebra) :
    (2:ℚ)^(padicValInt 2 (d₀:ℤ)*d)*x∈twoLocalSubalgebra := by
  have hnon : (d₀:ℤ)≠0 := by exact_mod_cast Nat.ne_of_gt h₀
  obtain ⟨w,hw,he⟩ := integer_odd_factor hnon
  have hwrat : (w:ℚ)≠0 := by exact_mod_cast odd_int_ne_zero hw
  have hodd : ¬(2:ℤ)∣w := fun hd => (Int.not_even_iff_odd.mpr hw) (even_iff_two_dvd.mpr hd)
  have hp : ((w:ℚ)⁻¹)∈twoLocalSubalgebra :=
    (mem_twoLocal_iff _).mpr ⟨1,w,hodd,by simp⟩
  have heq : (d₀:ℚ)=(2:ℚ)^(padicValInt 2 (d₀:ℤ))*(w:ℚ) := by
    unfold pow₂ at he
    exact_mod_cast he
  have hwprod : (w:ℚ)^d * ((w:ℚ)⁻¹)^d=1 := by
    rw [← mul_pow,mul_inv_cancel₀ hwrat,one_pow]
  have hcalc : ((d₀:ℚ)^d*x)*((w:ℚ)⁻¹)^d =
      (2:ℚ)^(padicValInt 2 (d₀:ℤ)*d)*x := by
    rw [heq,mul_pow,pow_mul]
    calc
      _ = (((2:ℚ)^(padicValInt 2 (d₀:ℤ)))^d*x)*((w:ℚ)^d * ((w:ℚ)⁻¹)^d) := by ring
      _ = _ := by rw [hwprod,mul_one]
  rw [← hcalc]
  exact twoLocalSubalgebra.mul_mem h (twoLocalSubalgebra.pow_mem hp d)

variable {V E Γ : Type} [Fintype V] [Fintype E] [Fintype Γ] {G : Graph V E} {p : ThreePorts G}
variable (F : FiveFile (Γ:=Γ) G p) (a : Address F.layout) (k : ℕ)
variable {b : Γ → ℕ} (Q : NativePrivateLists F a k b)

def directDegree (V E : Type) [Fintype V] [Fintype E] : ℕ := 2*Fintype.card (ClauseId V E)

def coefficientLoss : ℕ := padicValInt 2 ((δ F.layout:ℕ):ℤ)*directDegree V E

theorem coefficient_loss (hw : ∀ g q, Q.weight g q∈localJetImage k) (s : V→Bool) (j : ℕ) :
    (2:ℚ)^coefficientLoss F * jetCoeff k j (actualRegister F a k Q s)∈twoLocalSubalgebra := by
  let x := actualRegister F a k Q s
  let d := directDegree V E
  have hs := integral_coefficient k j _ (local_register F a k Q hw s)
  have hsc : ((δ F.layout:C3.Jet ℚ k)^d)*x = ((δ F.layout:ℚ)^d) • x := by
    rw [Algebra.smul_def,map_pow,map_natCast]
  change jetCoeff k j (((δ F.layout:C3.Jet ℚ k)^d)*x) ∈twoLocalSubalgebra at hs
  rw [hsc,jetCoeff,LinearMap.map_smul,Polynomial.coeff_smul,smul_eq_mul] at hs
  have pos : 0<δ F.layout := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  exact remove_odd_scale pos d (jetCoeff k j x) hs

theorem coefficient_multiplier_loss (hw : ∀ g q, Q.weight g q∈localJetImage k)
    (s : V→Bool) (j : ℕ) (f : ℤ[X]) (ℓ : ℕ) :
    Canonical.HasLoss f ℓ (coefficientLoss F)
      (algebraMap ℚ (RatRing f ℓ) (jetCoeff k j (actualRegister F a k Q s))) := by
  let wx : ℚ := jetCoeff k j (actualRegister F a k Q s)
  let u : TwoLocal := ⟨(2:ℚ)^coefficientLoss F*wx,coefficient_loss F a k Q hw s j⟩
  refine ⟨localScalar f ℓ u,?_⟩
  rw [embed_localScalar]
  change (2:RatRing f ℓ)^coefficientLoss F * algebraMap ℚ (RatRing f ℓ) wx =
    algebraMap ℚ (RatRing f ℓ) ((2:ℚ)^coefficientLoss F*wx)
  rw [map_mul,map_pow,map_ofNat]

#print axioms integral_coefficient
#print axioms remove_odd_scale
#print axioms coefficient_loss
#print axioms coefficient_multiplier_loss
end
end V8NativeMessage.C3.RawMain