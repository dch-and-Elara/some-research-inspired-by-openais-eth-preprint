import P5P3NativeGeometry
import P5P3ActualError
import P5P3Largest

/-! Source-node instantiation of the exact coefficientwise criterion.
The valuation of the carrier is computed from the actual entire chosen
profile, not from the full or odd-only profile. -/
namespace Paper5.P3
open P1DyadicGrid HermiteLoss
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]
variable {T : Type*} [Fintype T] [DecidableEq T]

omit [Fintype T] [DecidableEq T] in
theorem signed_ratio_factor (O : Subring K) (x y : K) (A B : ℤ) (w v : Oˣ)
    (hx : x=(↑(twoUnit K^A):K)*(((w:O):K)))
    (hy : y=(↑(twoUnit K^B):K)*(((v:O):K))) :
    (-x)*y⁻¹ = (↑(twoUnit K^(A-B)):K)*(((((-w)*v⁻¹:Oˣ):O):K)) := by
  have hz : (((v:O):K))≠0 := Units.ne_zero (Units.map O.subtype.toMonoidHom v)
  have hInv : ((((v⁻¹:Oˣ):O):K)) = ((((v:O):K)))⁻¹ := by
    apply mul_left_cancel₀ hz
    rw [←Subring.coe_mul,Units.mul_inv,Subring.coe_one,mul_inv_cancel₀ hz]
  rw [hx,hy,mul_inv_rev,zpow_sub]
  simp only [Units.val_mul,Units.val_inv_eq_inv_val,Subring.coe_mul,Units.val_neg,Subring.coe_neg,hInv]
  ring

omit [Fintype T] [DecidableEq T] in
theorem finite_product_unit_factor (O : Subring K) {I : Type*} (S : Finset I)
    (f : I→K) (e : I→ℤ) (h : ∀ s∈S,∃ w : Oˣ, f s=(↑(twoUnit K^e s):K)*(((w:O):K))) :
    ∃ w : Oˣ,(∏ s∈S,f s) = (↑(twoUnit K^(∑ s∈S,e s)):K)*(((w:O):K)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨1,by simp⟩
  | insert s S hs ih =>
    obtain ⟨w,hw⟩ := h s (Finset.mem_insert_self s S)
    obtain ⟨v,hv⟩ := ih (fun t ht => h t (Finset.mem_insert_of_mem ht))
    refine ⟨w*v,?_⟩
    rw [Finset.prod_insert hs,Finset.sum_insert hs,hw,hv,zpow_add]
    simp only [Units.val_mul,Subring.coe_mul]
    ring

def nativeCarrierVal (centers : T→ℤ) (q : T→ℕ) (t : T) : ℤ :=
  ∑ s ∈ Finset.univ.erase t, (q s:ℤ)*((level (centers s):ℤ)-level (centers t-centers s))

theorem native_carrier_unit (O : Subring K) [IsLocalRing O] (hn2 : ¬IsUnit (2:O))
    (a : ℕ) (z : T→ℤ) (q : T→ℕ) (t : T)
    (hinj : Function.Injective z) (hn : ∀ s,z s≠0) :
    ∃ w : Oˣ,carrierZero (nativeCenter a ∘ z) q t =
      (↑(twoUnit K^(nativeCarrierVal z q t)):K)*(((w:O):K)) := by
  unfold carrierZero nativeCarrierVal
  apply finite_product_unit_factor
  intro s hs
  have hdiff : z t-z s≠0 :=
    sub_ne_zero.mpr (fun h => (Finset.ne_of_mem_erase hs) (hinj h).symm)
  obtain ⟨w,hw⟩ := nativeCenter_unit O hn2 a (hn s)
  obtain ⟨v,hv⟩ := nativeCenter_unit O hn2 a hdiff
  let u : T→K := nativeCenter a ∘ z
  have he : (u t-u s) = nativeCenter a (z t-z s) := nativeCenter_sub a (z t) (z s)
  have hh := signed_ratio_factor O (u s) (u t-u s) _ _ w v hw (he.trans hv)
  have hexp : ((level (z s):ℤ)-(a+1:ℕ))-((level (z t-z s):ℤ)-(a+1:ℕ)) =
      (level (z s):ℤ)-level (z t-z s) := by omega
  rw [hexp] at hh
  let b : ℤ := (level (z s):ℤ)-level (z t-z s)
  let E : Oˣ := (-w)*v⁻¹
  refine ⟨E^(q s),?_⟩
  have H := pow_factor (twoUnit K) (1:K) ((-u s)*(u t-u s)⁻¹) 0 b (q s)
    (1:Oˣ) E (by simp) hh
  rw [one_mul] at H
  simpa only [zero_add,one_mul,mul_comm b] using H

def nativeLoss (a : ℕ) (z : ℤ) : ℤ := (a+1:ℕ)-level z

theorem native_loss_positive {a : ℕ} {z : ℤ} (hz : z∈grid a) (hn : z≠0) :
    0<nativeLoss a z := by
  have h := level_grid_le hz hn
  unfold nativeLoss
  omega

theorem native_precise_p1 (O : Subring K) [IsLocalRing O] (hn2 : ¬IsUnit (2:O))
    (a : ℕ) (z : T→ℤ) (q : T→ℕ) (b : ℕ) (hb : 0<b)
    (hinj : Function.Injective z) (hgrid : ∀ t,z t∈grid a) (hn : ∀ t,z t≠0)
    (P : T→ℤ) (p : ℤ) :
    ActualCertified O (nativeCenter a ∘ z) q b
      (fun r s => nativeDifference_integral_inverses O hn2 a (z r) (z s) (hgrid r) (hgrid s))
      (fun t => (↑(twoUnit K^P t):K)) (↑(twoUnit K^p):K) ↔
      ∀ t,0<q t → ((b:ℤ)+↑(q t)-2)*nativeLoss a (z t) ≤ P t-p+nativeCarrierVal z q t := by
  apply actual_certified_p1 O (twoUnit K) (two_power_integral_iff O hn2) _ q b hb P
    (nativeLoss a ∘ z) (nativeCarrierVal z q) p
  · exact fun t => nativeCenter_nonzero a (hn t)
  · exact fun t => nativeCenter_integral_inverses O hn2 a (z t) (hgrid t) (hn t)
  · intro t _
    have H := nativeCenter_unit O hn2 a (hn t)
    unfold nativeLoss
    simpa only [Function.comp_apply,neg_sub] using H
  · exact fun t _ => native_carrier_unit O hn2 a z q t hinj hn

def rootNodes (u : ℕ) : Finset ℤ :=
  (grid (2*u)).filter (fun t => t≠0 ∧ level t<u)

def rootPrecision (u M h p : ℕ) (t : ℤ) : ℤ :=
  p + 8*h*(2:ℤ)^(2*u-level t) + 8*M*(2*u+1)

theorem printed_root_p1 (O : Subring K) [IsLocalRing O] (hn2 : ¬IsUnit (2:O))
    (u M h p b : ℕ) (hb : 0<b) (q : (rootNodes u)→ℕ) :
    ActualCertified O (fun t : rootNodes u => nativeCenter (2*u) t.val) q b
      (fun s t => nativeDifference_integral_inverses O hn2 (2*u) s.val t.val
        (Finset.mem_filter.mp s.property).1 (Finset.mem_filter.mp t.property).1)
      (fun t => (↑(twoUnit K^rootPrecision u M h p t.val):K)) (↑(twoUnit K^(p:ℤ)):K) ↔
      ∀ t,0<q t → ((b:ℤ)+↑(q t)-2)*nativeLoss (2*u) t.val ≤
        rootPrecision u M h p t.val-p+nativeCarrierVal (fun a : rootNodes u => a.val) q t :=
  native_precise_p1 O hn2 (2*u) Subtype.val q b hb Subtype.val_injective
    (fun t => (Finset.mem_filter.mp t.property).1) (fun t => (Finset.mem_filter.mp t.property).2.1)
    (fun t => rootPrecision u M h p t.val) p

#print axioms signed_ratio_factor
#print axioms finite_product_unit_factor
#print axioms native_carrier_unit
#print axioms native_loss_positive
#print axioms native_precise_p1
#print axioms printed_root_p1
end Paper5.P3
