import P5HermiteTransportGenericPrecision
import Mathlib.RingTheory.Valuation.Integers

/-! The printed H.2 additive valuation threshold is equivalent to the
actual integral error lattice, derived from a genuine normalized
field valuation. In particular v(0)=infinity and a zero transfer is
never assigned a fictitious finite minimum. -/
namespace Paper5.HermiteGeneric
open Matrix
open scoped BigOperators Classical

variable {R K Γ : Type*} [CommRing R] [Field K] [Algebra R K]
  [LinearOrderedCommGroupWithZero Γ]

theorem embedded_multiple_iff (v : Valuation K Γ) (hv : v.Integers R) (a : R)
    (ha : algebraMap R K a≠0) (x : K) :
    (∃ u : R,x=algebraMap R K (a*u)) ↔ v x ≤ v (algebraMap R K a) := by
  constructor
  · rintro ⟨u,rfl⟩
    rw [map_mul,v.map_mul]
    exact (mul_le_mul_left' (hv.map_le_one u) _).trans_eq (mul_one _)
  · intro h
    let c := algebraMap R K a
    have hc : 0<v c := by
      apply lt_of_not_ge
      intro hz
      exact (v.ne_zero_iff.mpr ha) (le_zero_iff.mp hz)
    have hd : v (x/c)≤1 := by
      rw [v.map_div]
      exact (div_le_one₀ hc).mpr h
    obtain ⟨u,hu⟩ := hv.exists_of_le_one hd
    refine ⟨u,?_⟩
    rw [map_mul,hu]
    change x=c*(x/c)
    rw [mul_comm, div_mul_cancel₀ _ ha]

omit [LinearOrderedCommGroupWithZero Γ] in
theorem valuation_pi_pow (v : AddValuation K (WithTop ℤ)) (π : R)
    (hπ : v (algebraMap R K π)=1) (p : ℕ) :
    v (algebraMap R K (π^p)) = ((p:ℤ):WithTop ℤ) := by
  induction p with
  | zero => simp
  | succ p h =>
    rw [pow_succ,map_mul,v.map_mul,h,hπ]
    change ((p:ℤ):WithTop ℤ)+((1:ℤ):WithTop ℤ)=((↑(p+1):ℤ):WithTop ℤ)
    rw [←WithTop.coe_add,Int.natCast_succ]

omit [LinearOrderedCommGroupWithZero Γ] in
theorem additive_precision_ideal (v : AddValuation K (WithTop ℤ))
    (hv : v.toValuation.Integers R) (π : R) (hπ : v (algebraMap R K π)=1)
    (p : ℕ) (x : K) :
    (∃ u : R,x=algebraMap R K (π^p*u)) ↔ ((p:ℤ):WithTop ℤ)≤v x := by
  have h1 : algebraMap R K π≠0 := v.ne_top_iff.mp (by rw [hπ]; exact WithTop.coe_ne_top)
  have h2 : algebraMap R K (π^p)≠0 := by rw [map_pow]; exact pow_ne_zero p h1
  rw [embedded_multiple_iff v.toValuation hv _ h2]
  change v (algebraMap R K (π^p))≤v x ↔ _
  rw [valuation_pi_pow v π hπ p]

omit [LinearOrderedCommGroupWithZero Γ] in
theorem scaled_additive_precision_ideal (v : AddValuation K (WithTop ℤ))
    (hv : v.toValuation.Integers R) (π : R) (hπ : v (algebraMap R K π)=1)
    (p P : ℕ) (x : K) :
    (∃ u : R,x*algebraMap R K (π^P)=algebraMap R K (π^p*u)) ↔
      ((p:ℤ):WithTop ℤ)≤((P:ℤ):WithTop ℤ)+v x := by
  rw [additive_precision_ideal v hv π hπ p,v.map_mul,valuation_pi_pow v π hπ P,add_comm]

omit [LinearOrderedCommGroupWithZero Γ] in
theorem finite_shift_threshold (p P : ℕ) (x : WithTop ℤ) :
    ((p:ℤ):WithTop ℤ)≤((P:ℤ):WithTop ℤ)+x ↔ (((p:ℤ)-(P:ℤ):ℤ):WithTop ℤ)≤x := by
  cases x with
  | top => simp
  | coe z =>
    rw [←WithTop.coe_add,WithTop.coe_le_coe,WithTop.coe_le_coe]
    omega

variable {T U V : Type*} [Fintype T] [DecidableEq T] [Nonempty U] [Nonempty V]

noncomputable def minimumTransfer (L : Layout K T) (b : ℕ)
    (v : AddValuation K (WithTop ℤ)) (s : Slot L) : WithTop ℤ :=
  Finset.univ.inf (fun ij : Fin b × Fin b=>v (decoderTable L b ij s))

omit [LinearOrderedCommGroupWithZero Γ] in
theorem all_independent_lifts_H2 (L : Layout K T) (b : ℕ)
    (v : AddValuation K (WithTop ℤ)) (hv : v.toValuation.Integers R)
    (π : R) (hπ : v (algebraMap R K π)=1) (P : Slot L→ℕ) (p : ℕ)
    (A : (t : T)→Fin (L.order t)→Matrix U V K) :
    (∀ B,Permissible L π P A B → EntryPrecision π p (expanded L b A) (expanded L b B)) ↔
      ∀ s : Slot L, ((p:ℤ):WithTop ℤ)≤((P s:ℤ):WithTop ℤ)+minimumTransfer L b v s := by
  rw [independent_error_lattice_iff]
  constructor
  · intro h s
    rw [finite_shift_threshold,minimumTransfer,Finset.le_inf_iff]
    rintro ⟨i,j⟩ _
    apply (finite_shift_threshold p (P s) _).1
    exact (scaled_additive_precision_ideal v hv π hπ p (P s) _).1 (h i j s)
  · intro H i j s
    have h := H s
    rw [finite_shift_threshold,minimumTransfer,Finset.le_inf_iff] at h
    apply (scaled_additive_precision_ideal v hv π hπ p (P s) _).2
    exact (finite_shift_threshold p (P s) _).2 (h (i,j) (Finset.mem_univ _))

#print axioms embedded_multiple_iff
#print axioms valuation_pi_pow
#print axioms additive_precision_ideal
#print axioms finite_shift_threshold
#print axioms all_independent_lifts_H2
end Paper5.HermiteGeneric
