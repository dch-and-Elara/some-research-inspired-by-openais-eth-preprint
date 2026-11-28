import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

/-!
# Boolean-cube precision erasure

Assignments to independently summed Boolean equality bits are encoded by their
true supports. Terms use an idempotent support, not the number of repeated
occurrences. The coefficient argument is purely finite, with the coefficient
ring and probe ring arbitrary; it does not assume convergence of a power series
or encode the published layout or collision certificate.
-/

namespace PrecisionErasure

open scoped BigOperators
open Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every superset of s is uniquely s plus a subset of its complement. -/
theorem card_extensions (s : Finset ι) :
    (Finset.univ.filter (fun a : Finset ι => s ⊆ a)).card =
      2 ^ (Fintype.card ι - s.card) := by
  classical
  let c := sᶜ
  have he : Finset.univ.filter (fun a : Finset ι => s ⊆ a) =
      c.powerset.image (fun b => s ∪ b) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_powerset]
    constructor
    · intro h
      refine ⟨a \ s, ?_, Finset.union_sdiff_of_subset h⟩
      intro i hi
      exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2
    · rintro ⟨b,_,rfl⟩
      exact Finset.subset_union_left
  have hinj : Set.InjOn (fun b : Finset ι => s ∪ b) ↑c.powerset := by
    intro a ha b hb eq
    have sep (T : Finset ι) (hT : T ∈ c.powerset) : (s ∪ T) \ s = T := by
      have hsub := Finset.mem_powerset.mp hT
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_union]
      have hn : i ∈ T → i ∉ s := fun hi => Finset.mem_compl.mp (hsub hi)
      tauto
    have e := congrArg (fun x : Finset ι => x \ s) eq
    change (s ∪ a) \ s = (s ∪ b) \ s at e
    rwa [sep a ha, sep b hb] at e
  rw [he, Finset.card_image_of_injOn hinj, Finset.card_powerset, Finset.card_compl]

/-- Sum exactly one squarefree monomial, with arbitrary coefficient. -/
theorem sum_monomial {R : Type*} [CommSemiring R] (s : Finset ι) (c : R) :
    (∑ a : Finset ι, if s ⊆ a then c else 0) =
      (2 : R) ^ (Fintype.card ι - s.card) * c := by
  rw [← Finset.sum_filter, Finset.sum_const, card_extensions, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- A choice in a finite factor expansion, e.g. a summand of a source moment,
a coefficient of a normalized kernel, or a summand in a local affine row. -/
structure Atom (ι R : Type*) where
  bits : Finset ι
  order : ℕ
  coeff : R

omit [Fintype ι] in
/-- A summand vanishes unless all its protected bits are one. -/
def atomValue {R : Type*} [Zero R] (a : Atom ι R) (mask : Finset ι) : R :=
  if a.bits ⊆ mask then a.coeff else 0

section Products

variable {F R : Type*} [Fintype F] [CommSemiring R]

omit [Fintype ι] [Fintype F] in
private theorem product_monomials (s : Finset F) (f : F → Atom ι R) (mask : Finset ι) :
    (∏ i ∈ s, monomial (f i).order (atomValue (f i) mask)) =
      monomial (∑ i ∈ s, (f i).order) (∏ i ∈ s, atomValue (f i) mask) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Polynomial.monomial_zero_left]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, Polynomial.monomial_mul_monomial,
      Finset.sum_insert ha, Finset.prod_insert ha]

omit [Fintype ι] in
private theorem product_atoms (f : F → Atom ι R) (mask : Finset ι) :
    (∏ i, atomValue (f i) mask) =
      if Finset.univ.biUnion (fun i => (f i).bits) ⊆ mask then (∏ i, (f i).coeff) else 0 := by
  classical
  by_cases h : Finset.univ.biUnion (fun i => (f i).bits) ⊆ mask
  · rw [if_pos h]
    refine Finset.prod_congr rfl fun i _ => if_pos ?_
    intro b hb
    exact h (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hb⟩)
  · rw [if_neg h]
    obtain ⟨b,hb,hn⟩ := Finset.not_subset.mp h
    obtain ⟨i,hi,hb'⟩ := Finset.mem_biUnion.mp hb
    exact Finset.prod_eq_zero hi (if_neg fun hm => hn (hm hb'))

/-- The finite normalization polynomial after the factors 2^v and z^k are
removed, in the formal variable corresponding to 2z. This still sums the
original Boolean cube *after* multiplying the finite local factors. -/
noncomputable def cubeProduct {C : F → Type*} [∀ i, Fintype (C i)]
    (a : ∀ i, C i → Atom ι R) : Polynomial R :=
  ∑ mask : Finset ι, ∏ i, ∑ j, monomial (a i j).order (atomValue (a i j) mask)

/-- Explicit expansion: selected supports union, selected orders add, and
each untouched protected bit contributes an independent factor of two. -/
theorem cubeProduct_expand [DecidableEq F] {C : F → Type*} [∀ i, Fintype (C i)]
    (a : ∀ i, C i → Atom ι R) :
    cubeProduct a = ∑ sel : (∀ i, C i),
      monomial (∑ i, (a i (sel i)).order)
        ((2 : R) ^ (Fintype.card ι - (Finset.univ.biUnion (fun i => (a i (sel i)).bits)).card)
          * ∏ i, (a i (sel i)).coeff) := by
  classical
  unfold cubeProduct
  simp only [Fintype.prod_sum, product_monomials]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sel _
  simp only [product_atoms, ← map_sum, sum_monomial]

/-- P5, for one product before summing unprotected assignments or allocations.
Each source factor may spend one protected bit at no precision cost. A local
row factor spends no such allowance. Any additional distinct bit must be
paid for by order in the formal variable 2z. -/
theorem coeff_support_dvd [DecidableEq F] {C : F → Type*} [∀ i, Fintype (C i)]
    (a : ∀ i, C i → Atom ι R) (allowance : F → ℕ) (k j : ℕ)
    (hallow : (∑ i, allowance i) ≤ k)
    (hbits : ∀ i c, (a i c).bits.card ≤ allowance i + (a i c).order) :
    (2 : R) ^ (Fintype.card ι - k - j) ∣ (cubeProduct a).coeff j := by
  classical
  rw [cubeProduct_expand, Polynomial.finset_sum_coeff]
  apply Finset.dvd_sum
  intro sel _
  rw [Polynomial.coeff_monomial]
  split_ifs with eq
  · have h := Finset.card_biUnion_le (s := (Finset.univ : Finset F))
        (t := fun i => (a i (sel i)).bits)
    have h' := Finset.sum_le_sum (s := (Finset.univ : Finset F)) (fun i _ => hbits i (sel i))
    rw [Finset.sum_add_distrib, eq] at h'
    have he : Fintype.card ι - k - j ≤
        Fintype.card ι - (Finset.univ.biUnion (fun i => (a i (sel i)).bits)).card := by omega
    exact dvd_mul_of_dvd_left (pow_dvd_pow _ he) _
  · exact dvd_zero _

end Products

section Eval

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- P5 survives a finite sum, including the different unprotected assignments
and feasible target allocations. No sign restriction is needed in rings. -/
theorem coeff_budget_sum {I : Type*} (I₀ : Finset I) (p : I → R[X]) (K k : ℕ)
    (hc : ∀ i ∈ I₀, ∀ j, (2 : R) ^ (K-k-j) ∣ (p i).coeff j) (j : ℕ) :
    (2 : R) ^ (K-k-j) ∣ (∑ i ∈ I₀, p i).coeff j := by
  rw [Polynomial.finset_sum_coeff]
  exact Finset.dvd_sum fun i hi => hc i hi j

/-- Evaluating a finite normalized expansion in the variable 2z recompenses
the j units of divisibility potentially lost from its coefficient of order j. -/
theorem scaled_eval_dvd (ψ : R →+* S) (p : R[X]) (z : S) (K k : ℕ)
    (hc : ∀ j, (2 : R) ^ (K-k-j) ∣ p.coeff j) :
    (2 : S) ^ (K-k) ∣ p.eval₂ ψ (2*z) := by
  rw [Polynomial.eval₂_eq_sum_range]
  apply Finset.dvd_sum
  intro j _
  obtain ⟨b,hb⟩ := hc j
  rw [hb, map_mul, map_pow, map_ofNat, mul_pow]
  have he : K-k ≤ (K-k-j)+j := by omega
  refine (pow_dvd_pow (2 : S) he).trans ?_
  refine ⟨ψ b * z^j, ?_⟩
  rw [pow_add]
  ac_rfl

/-- P7: the normalized finite expression gives the exact modulus of erasure
uniformly at every probe, even in a different (extension or quotient) ring. -/
theorem completed_slot_dvd (ψ : R →+* S) (p : R[X]) (z : S) (K k v : ℕ)
    (hc : ∀ j, (2 : R) ^ (K-k-j) ∣ p.coeff j) :
    (2 : S) ^ (v+(K-k)) ∣ (2 : S)^v * z^k * p.eval₂ ψ (2*z) := by
  obtain ⟨b,hb⟩ := scaled_eval_dvd ψ p z K k hc
  refine ⟨z^k * b, ?_⟩
  rw [hb, pow_add]
  ac_rfl

/-- Because the native normalization cost v dominates the number of source
occurrences k, every completed slot is erased through at least K bits. -/
theorem every_slot_erased (ψ : R →+* S) (p : R[X]) (z : S) (K k v : ℕ)
    (hkv : k ≤ v) (hc : ∀ j, (2 : R) ^ (K-k-j) ∣ p.coeff j) :
    (2 : S) ^ K ∣ (2 : S)^v * z^k * p.eval₂ ψ (2*z) :=
  (pow_dvd_pow _ (show K ≤ v+(K-k) by omega)).trans (completed_slot_dvd ψ p z K k v hc)

end Eval

section Normalization

variable {F R S : Type*} [Fintype F] [CommSemiring R] [CommSemiring S]

/-- P3, finite local expansion: one extracts the prescribed factor of two
and the prescribed power of the probe from each selected factor, *before*
summing the underlying assignments. Products of such scalars add exponents;
the remaining finite expression is evaluated at 2z. -/
theorem normalize_product {C : F → Type*} [∀ i, Fintype (C i)]
    (a : ∀ i, C i → Atom ι R) (ψ : R →+* S) (z : S) (v k : F → ℕ) :
    (∑ mask : Finset ι, ∏ i,
      (((2 : S) ^ v i * z ^ k i) *
        ∑ j, ψ (atomValue (a i j) mask) * (2*z) ^ (a i j).order)) =
    (2 : S) ^ (∑ i, v i) * z ^ (∑ i, k i) * (cubeProduct a).eval₂ ψ (2*z) := by
  simp only [cubeProduct, Polynomial.eval₂_finset_sum, Polynomial.eval₂_finset_prod,
    Polynomial.eval₂_monomial]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun mask _ => ?_
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- A concrete structural condition for the source/local menus of P5:
a source-moment summand touches at most one bit; a non-source summand can
touch a protected bit only at strictly positive order. -/
theorem coeff_linearMenus_dvd [DecidableEq F] {C : F → Type*} [∀ i, Fintype (C i)]
    (a : ∀ i, C i → Atom ι R) (source : F → Bool) (k j : ℕ)
    (hsources : (Finset.univ.filter fun i => source i = true).card ≤ k)
    (hlinear : ∀ i c, (a i c).bits.card ≤ 1)
    (hpositive : ∀ i c, source i = false → (a i c).order = 0 → (a i c).bits = ∅) :
    (2 : R) ^ (Fintype.card ι-k-j) ∣ (cubeProduct a).coeff j := by
  classical
  refine coeff_support_dvd a (fun i => if source i = true then 1 else 0) k j ?_ ?_
  · simpa only [Finset.sum_boole, Nat.cast_id] using hsources
  · intro i c
    cases hc : source i with
    | true =>
      simp only [hc, ↓reduceIte]
      exact (hlinear i c).trans (Nat.le_add_right _ _)
    | false =>
      simp only [hc, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      by_cases ho : (a i c).order = 0
      · simp [hpositive i c hc ho]
      · have hl := hlinear i c
        omega

/-- Finite reduction commutes with the actual sum of products. Hence a value
at a requested precision with 2^b=0 is literally zero, not just assigned a
large formal order. The stronger threshold v+(K-k) permits v<k as well. -/
theorem normalize_product_zero [DecidableEq F] {C : F → Type*} [∀ i, Fintype (C i)]
    (a : ∀ i, C i → Atom ι R) (ψ : R →+* S) (z : S) (v k allowance : F → ℕ) (b : ℕ)
    (hallow : (∑ i, allowance i) ≤ ∑ i, k i)
    (hbits : ∀ i c, (a i c).bits.card ≤ allowance i + (a i c).order)
    (hb : b ≤ (∑ i, v i) + (Fintype.card ι - ∑ i, k i))
    (hp : (2 : S)^b = 0) :
    (∑ mask : Finset ι, ∏ i,
      (((2 : S) ^ v i * z ^ k i) *
        ∑ j, ψ (atomValue (a i j) mask) * (2*z) ^ (a i j).order)) = 0 := by
  rw [normalize_product]
  have hv := (pow_dvd_pow (2 : S) hb).trans
    (completed_slot_dvd ψ (cubeProduct a) z (Fintype.card ι) (∑ i, k i) (∑ i, v i)
      (fun j => coeff_support_dvd a allowance _ j hallow hbits))
  simpa only [hp, zero_dvd_iff] using hv

end Normalization

section CoefficientDenominators

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A truncated geometric series is a genuine finite polynomial inverse
for 1+(2z)a at any probe of precision b (2^b=0). Thus positive powers of
this inverse can be represented by finite polynomials in the very coordinate
whose degree pays for new protected bits; no completeness assumption. -/
theorem truncGeom_inverse (ψ : R →+* S) (a : R) (z : S) (b : ℕ)
    (hp : (2 : S)^b = 0) :
    ((∑ j ∈ Finset.range b, monomial j ((-a)^j)).eval₂ ψ (2*z)) *
        (1 + ψ a * (2*z)) = 1 := by
  have hn : (-(ψ a * (2*z))) ^ b = 0 := by
    rw [neg_pow, mul_pow, mul_pow, hp, zero_mul, mul_zero, mul_zero]
  simpa [Polynomial.eval₂_finset_sum, Polynomial.eval₂_monomial, ← mul_pow, hn] using
    (geom_sum_mul_neg (-(ψ a * (2*z))) b)

end CoefficientDenominators

section Digits

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The shared normalized base coefficients suffice simultaneously for
every probe in every coefficient extension with the requested nilpotence.
This is a sufficiency statement, not cost of acquiring those coefficients. -/
theorem base_digits_determine (ψ : R →+* S) (p q : R[X]) (z : S) (b v k : ℕ)
    (hprec : (2 : S)^b = 0)
    (hagree : ∀ j, (2 : R)^(b-v-j) ∣ (p-q).coeff j) :
    (2 : S)^v * z^k * p.eval₂ ψ (2*z) = (2 : S)^v * z^k * q.eval₂ ψ (2*z) := by
  apply sub_eq_zero.mp
  rw [← mul_sub, ← Polynomial.eval₂_sub]
  obtain ⟨x,hx⟩ := scaled_eval_dvd ψ (p-q) z b v hagree
  have hpow := pow_dvd_pow (2 : S) (show b ≤ v+(b-v) by omega)
  have hd : (2 : S)^(v+(b-v)) ∣ 2^v * z^k * (p-q).eval₂ ψ (2*z) := by
    refine ⟨z^k*x, ?_⟩
    rw [hx, pow_add, mul_mul_mul_comm]
  have hz := hpow.trans hd
  simpa only [hprec, zero_dvd_iff] using hz

/-- With P5, it is enough to send the quotient digits after removing the
guaranteed powers of two. A sufficient order for coefficient j is b-v-max(j,K-k), truncated at zero. -/
theorem erased_digits_determine (ψ : R →+* S) (p q : R[X]) (z : S) (b v k K : ℕ)
    (hprec : (2 : S)^b = 0) (x y : ℕ → R)
    (hx : ∀ j, p.coeff j = (2 : R)^(K-k-j) * x j)
    (hy : ∀ j, q.coeff j = (2 : R)^(K-k-j) * y j)
    (hagree : ∀ j, (2 : R)^(b-v-max j (K-k)) ∣ x j - y j) :
    (2 : S)^v * z^k * p.eval₂ ψ (2*z) = (2 : S)^v * z^k * q.eval₂ ψ (2*z) := by
  apply base_digits_determine ψ p q z b v k hprec
  intro j
  rw [Polynomial.coeff_sub, hx, hy, ← mul_sub]
  have hd := mul_dvd_mul (dvd_refl ((2:R)^(K-k-j))) (hagree j)
  rw [← pow_add] at hd
  apply (pow_dvd_pow (2:R) ?_).trans hd
  omega

/-- The triangular bit sum at height n. We use the equivalent sum form in
the proof, avoiding division rounding issues. -/
def triangle (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (n-i)

/-- P6's bit arithmetic: counting per-coefficient digits after the guaranteed
powers are removed gives the positive part of the triangular difference. -/
theorem bit_count (x y : ℕ) :
    (∑ j ∈ Finset.range x, (x-max j y)) = triangle x - triangle y := by
  unfold triangle
  by_cases hy : y ≤ x
  · have hsub : Finset.range y ⊆ Finset.range x := Finset.range_mono hy
    have hsplit (j : ℕ) : (x - max j y) + (y-j) = x-j := by omega
    have hmono : (∑ j ∈ Finset.range x, (y-j)) = ∑ j ∈ Finset.range y, (y-j) := by
      exact Finset.sum_subset hsub (fun j _ hn => Nat.sub_eq_zero_of_le (by
        rw [Finset.mem_range] at hn
        omega)) |>.symm
    have he := Finset.sum_congr (s₁ := Finset.range x) rfl (fun j _ => hsplit j)
    rw [Finset.sum_add_distrib, hmono] at he
    exact Nat.eq_sub_of_add_eq he
  · have hzero : (∑ j ∈ Finset.range x, (x-max j y)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      omega
    have hle : (∑ j ∈ Finset.range x, (x-j)) ≤ ∑ j ∈ Finset.range y, (y-j) :=
      (Finset.sum_le_sum (s := Finset.range x) (fun j _ => show x-j ≤ y-j by omega)).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (by intros; omega))
    omega

/-- Closed form of the triangular digit count. -/
theorem triangle_closed (n : ℕ) : triangle n = n * (n+1) / 2 := by
  have hrec (j : ℕ) : triangle (j+1) = (j+1) + triangle j := by
    unfold triangle
    rw [Finset.sum_range_succ', Nat.sub_zero, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun a _ => by omega
  have h : 2 * triangle n = n * (n+1) := by
    induction n with
    | zero => simp [triangle]
    | succ n ih =>
      rw [hrec, Nat.mul_add, ih]
      ring
  omega

end Digits

/-- The printed order offset for one native kernel, after its scalar powers of
two are separated. This is an arithmetic identity, not a valuation assertion
about a rational denominator or a full packet. -/
theorem kernel_exponent_arithmetic (a i h b : ℕ) (ha : i ≤ a+1) (hh : h ≤ i) :
    a+1 + (i+1)*b - h*(b+1) = (a+1-i) + b + (b+1)*(i-h) := by
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one, Nat.mul_sub, Nat.add_mul,
    Nat.one_mul]
  rw [Nat.add_mul, Nat.one_mul]
  have hb := Nat.mul_le_mul_right b hh
  rw [Nat.mul_comm b i, Nat.mul_comm b h]
  omega

/-- Summing over repetitions in a mode tuple, v dominates k as soon as the
baseline cost delta is positive. This is the hypothesis of every_slot_erased
in the native source tariff. -/
theorem mode_cost_ge_count {F : Type*} [Fintype F] (delta : ℕ)
    (index mult : F → ℕ) (hdelta : 1 ≤ delta) :
    (∑ i, mult i) ≤ ∑ i, (delta + index i) * mult i := by
  apply Finset.sum_le_sum
  intro i _
  simpa only [one_mul] using Nat.mul_le_mul_right (mult i)
    (show 1 ≤ delta + index i by omega)

#print axioms card_extensions
#print axioms sum_monomial
#print axioms cubeProduct_expand
#print axioms coeff_support_dvd
#print axioms coeff_budget_sum
#print axioms scaled_eval_dvd
#print axioms completed_slot_dvd
#print axioms every_slot_erased
#print axioms normalize_product
#print axioms coeff_linearMenus_dvd
#print axioms normalize_product_zero
#print axioms truncGeom_inverse
#print axioms base_digits_determine
#print axioms erased_digits_determine
#print axioms bit_count
#print axioms triangle_closed
#print axioms kernel_exponent_arithmetic
#print axioms mode_cost_ge_count

end PrecisionErasure