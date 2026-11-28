import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Finite.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Localization.Basic

/-! Joint low-precision probe menus (N8). The coefficient ring is the
localization of the integers at the odd denominators. The receiving ring may
be any commutative ring annihilated by the specified power of two. One
finite message works at every evaluation point, including extension-valued
points. The source Cauchy calculation, nonzero-mode vanishing threshold and
the extraction of the matching from the native layout are written arguments. -/

namespace TruncatedProbeMenu

open Polynomial

/-- An integer is an allowed denominator exactly when its absolute value
is coprime to two. -/
def oddDenominators : Submonoid ℤ where
  carrier := {n | n.natAbs.Coprime 2}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change (a * b).natAbs.Coprime 2
    rw [Int.natAbs_mul]
    exact Nat.Coprime.mul_left ha hb

abbrev Base := Localization oddDenominators

theorem odd_denominator_unit (p : ℕ) (d : oddDenominators) :
    IsUnit ((d : ℤ) : ZMod (2 ^ p)) := by
  have hc : (d : ℤ).natAbs.Coprime 2 := d.property
  have hu := (ZMod.isUnit_iff_coprime (d : ℤ).natAbs (2 ^ p)).2 (hc.pow_right p)
  rcases Int.natAbs_eq (d : ℤ) with hd | hd
  · conv => arg 1; rw [hd, Int.cast_natCast]
    exact hu
  · conv => arg 1; rw [hd, Int.cast_neg, Int.cast_natCast]
    exact hu.neg

noncomputable def reduce (p : ℕ) : Base →+* ZMod (2 ^ p) :=
  IsLocalization.lift (g := Int.castRingHom _) (odd_denominator_unit p)

variable {R : Type*} [CommRing R]

/-- Cast a base residue into any receiving ring killed by
the specified modulus. This map may have a kernel at lower characteristic. -/
noncomputable def residueCast {p : ℕ} (h₂ : (2 : R) ^ p = 0) : ZMod (2 ^ p) →+* R :=
  ZMod.castHom (show ringChar R ∣ 2 ^ p from ringChar.dvd (by
    simpa only [Nat.cast_pow, Nat.cast_two] using h₂)) R

/-- Every map from the odd-denominator localization to a ring with
`2^p = 0` agrees with casting the canonical base-ring representative. -/
theorem cast_representative {p : ℕ} (h₂ : (2 : R) ^ p = 0)
    (f : Base →+* R) (c : Base) : ((reduce p c).val : R) = f c := by
  let g := residueCast h₂
  have hf : g.comp (reduce p) = f :=
    IsLocalization.ringHom_ext oddDenominators (Subsingleton.elim _ _)
  calc
    ((reduce p c).val : R) = g ((reduce p c).val : ZMod (2 ^ p)) := (map_natCast g _).symm
    _ = f c := by rw [ZMod.natCast_zmod_val]; exact RingHom.congr_fun hf c

private theorem pow_vanish_of_le {p j : ℕ} (h₂ : (2 : R) ^ p = 0) (hpj : p ≤ j) :
    (2 : R) ^ j = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hpj
  rw [pow_add, h₂, zero_mul]

private theorem zmod_pow_vanish (j : ℕ) : (2 : ZMod (2 ^ j)) ^ j = 0 := by
  simpa only [Nat.cast_pow, Nat.cast_two] using ZMod.natCast_self (2 ^ j)

/-- A coefficient on `(2 z)^j` needs only its residue modulo `2^(p-j)`.
The receiving ring need not have a finite carrier. -/
theorem weighted_coefficient {p j : ℕ} (hj : j ≤ p) (h₂ : (2 : R) ^ p = 0)
    (f : Base →+* R) (c : Base) :
    f c * (2 : R) ^ j = ((reduce (p - j) c).val : R) * 2 ^ j := by
  let n := (reduce p c).val
  have hlow : (n : ZMod (2 ^ (p - j))) = reduce (p - j) c :=
    cast_representative (pow_vanish_of_le (zmod_pow_vanish (p - j)) (Nat.sub_le _ _))
      (reduce (p - j)) c
  have hexpand : (n : R) =
      ((n % 2 ^ (p - j) : ℕ) : R) + (2 : R) ^ (p - j) * ((n / 2 ^ (p - j) : ℕ) : R) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_two] using
      congrArg (fun k : ℕ => (k : R)) (Nat.mod_add_div n (2 ^ (p - j))).symm
  have hzero : (2 : R) ^ (p - j) * 2 ^ j = 0 := by
    rw [← pow_add, Nat.sub_add_cancel hj, h₂]
  rw [← cast_representative h₂ f c, ← hlow, ZMod.val_natCast]
  change (n : R) * 2 ^ j = _
  calc
    (n : R) * 2 ^ j =
        (((n % 2 ^ (p - j) : ℕ) : R) +
          (2 : R) ^ (p - j) * ((n / 2 ^ (p - j) : ℕ) : R)) * 2 ^ j :=
      congrArg (fun a : R => a * 2 ^ j) hexpand
    _ = ((n % 2 ^ (p - j) : ℕ) : R) * 2 ^ j +
        ((n / 2 ^ (p - j) : ℕ) : R) * (2 ^ (p - j) * 2 ^ j) := by ring
    _ = _ := by rw [hzero, mul_zero, add_zero]

/-- Ordinary coefficient divisibility is equivalent to having a polynomial
in the scaled indeterminate. No division in the localized ring is assumed. -/
theorem scaled_representation {S : Type*} [CommRing S] (P : S[X]) :
    (∀ j, (2 : S) ^ j ∣ P.coeff j) ↔ ∃ U : S[X], P = U.comp (C 2 * X) := by
  classical
  constructor
  · intro h
    choose a ha using h
    let U : S[X] := ∑ i ∈ P.support, monomial i (a i)
    refine ⟨U, ?_⟩
    ext j
    rw [comp_C_mul_X_coeff, show U.coeff j =
      (if j ∈ P.support then a j else 0) by
        simp [U, finset_sum_coeff, coeff_monomial]]
    by_cases hj : j ∈ P.support
    · rw [if_pos hj, ha j, mul_comm]
    · rw [if_neg hj, zero_mul]
      exact notMem_support_iff.mp hj
  · rintro ⟨U, rfl⟩ j
    exact ⟨U.coeff j, by rw [comp_C_mul_X_coeff, mul_comm]⟩

/-- A finite sum over assignments of finite products of admissible local
factors has the same coefficient divisibility, including empty sums/products. -/
theorem contraction_divisibility {S I J : Type*} [CommRing S] [Fintype I] [Fintype J]
    (localFactor : I → J → S[X])
    (hlocal : ∀ i k j, (2 : S) ^ j ∣ (localFactor i k).coeff j) :
    ∀ j, (2 : S) ^ j ∣ (∑ i, ∏ k, localFactor i k).coeff j := by
  classical
  have hrepr (i : I) (k : J) := (scaled_representation (localFactor i k)).1 (hlocal i k)
  choose q hq using hrepr
  apply (scaled_representation _).2
  refine ⟨∑ i, ∏ k, q i k, ?_⟩
  simp only [sum_comp, prod_comp, hq]

abbrev NodeMessage (p : ℕ) := (j : Fin p) → ZMod (2 ^ (p - j.val))

noncomputable def encode (p : ℕ) (U : Base[X]) : NodeMessage p :=
  fun j => reduce (p - j.val) (U.coeff j.val)

def reconstruct {p : ℕ} (m : NodeMessage p) (z : R) : R :=
  ∑ j : Fin p, ((m j).val : R) * (2 * z) ^ j.val

private theorem eval_truncated {p : ℕ} (h₂ : (2 : R) ^ p = 0)
    (f : Base →+* R) (U : Base[X]) (z : R) :
    U.eval₂ f (2 * z) = ∑ j ∈ Finset.range p, f (U.coeff j) * (2 * z) ^ j := by
  let n := max p (U.natDegree + 1)
  have hdeg : U.natDegree < n := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right ..)
  rw [eval₂_eq_sum_range' f hdeg]
  symm
  apply Finset.sum_subset (Finset.range_mono (le_max_left ..))
  intro j _ hj
  have hpj : p ≤ j := Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))
  rw [mul_pow, pow_vanish_of_le h₂ hpj, zero_mul, mul_zero]

/-- A *single* digit array recovers all extension-valued evaluations. -/
theorem reconstruct_eq_eval {p : ℕ} (h₂ : (2 : R) ^ p = 0)
    (f : Base →+* R) (U : Base[X]) (z : R) :
    reconstruct (encode p U) z = U.eval₂ f (2 * z) := by
  rw [eval_truncated h₂, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [encode, mul_pow, ← mul_assoc]
  rw [weighted_coefficient j.isLt.le h₂]

/-- Normalizing a polynomial only uses its base coefficients. -/
noncomputable def encodeDivisible (p : ℕ) (P : Base[X])
    (hP : ∀ j, (2 : Base) ^ j ∣ P.coeff j) : NodeMessage p :=
  encode p (((scaled_representation P).1 hP).choose)

theorem reconstruct_divisible {p : ℕ} (h₂ : (2 : R) ^ p = 0)
    (f : Base →+* R) (P : Base[X]) (hP : ∀ j, (2 : Base) ^ j ∣ P.coeff j) (z : R) :
    reconstruct (encodeDivisible p P hP) z = P.eval₂ f z := by
  let h := (scaled_representation P).1 hP
  change reconstruct (encode p h.choose) z = _
  calc
    reconstruct (encode p h.choose) z = h.choose.eval₂ f (2 * z) :=
      reconstruct_eq_eval h₂ f _ z
    _ = (h.choose.comp (C 2 * X)).eval₂ f z := by
      rw [eval₂_comp]
      simp [show f 2 = 2 from map_ofNat f 2]
    _ = P.eval₂ f z := congrArg (eval₂ f z) h.choose_spec.symm

/-- Choose the finite message before the receiving algebra and all of its
evaluation points. Every commutative ring annihilated by the modulus has
the displayed canonical map from the localized coefficient ring. -/
theorem simultaneous_reconstruction (p : ℕ) (P : Base[X])
    (hP : ∀ j, (2 : Base) ^ j ∣ P.coeff j) :
    ∃ m : NodeMessage p, ∀ (S : Type*) [CommRing S] (h₂ : (2 : S) ^ p = 0) (z : S),
      reconstruct m z = P.eval₂ ((residueCast h₂).comp (reduce p)) z := by
  exact ⟨encodeDivisible p P hP,
    fun _ _ h₂ z => reconstruct_divisible h₂ _ P hP z⟩

private theorem triangular_sum (p : ℕ) :
    ∑ j : Fin p, (p - j.val) = p * (p + 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range]
  calc
    ∑ j ∈ Finset.range p, (p - j) =
        ∑ j ∈ Finset.range (p + 1), (p + 1 - 1 - j) := by simp [Finset.sum_range_succ]
    _ = ∑ j ∈ Finset.range (p + 1), j := Finset.sum_range_reflect (fun j => j) _
    _ = _ := by rw [Finset.sum_range_id, Nat.add_sub_cancel, Nat.mul_comm]

theorem node_message_card (p : ℕ) :
    Fintype.card (NodeMessage p) = 2 ^ (p * (p + 1) / 2) := by
  rw [Fintype.card_pi]
  simp_rw [ZMod.card]
  rw [Finset.prod_pow_eq_pow_sum, triangular_sum]

theorem shell_message_card (T : Type*) [Fintype T] (p : ℕ) :
    Nat.card (T → NodeMessage p) = 2 ^ (Fintype.card T * (p * (p + 1) / 2)) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, node_message_card, ← pow_mul, Nat.mul_comm]

/-- Each complete register address has a node, a probe point, and a mode.
After reduction the zero-mode slot is the indicated row/column product.
Every other complete slot is zero. The address and input types can be
infinite; only the number of nodes will enter the entropy bound. -/
structure Shell (X Y T A R : Type*) [CommRing R] where
  baseMap : Base →+* R
  row : X → T → Base[X]
  row_divisible : ∀ x t j, (2 : Base) ^ j ∣ (row x t).coeff j
  node : A → T
  point : A → R
  zeroMode : A → Bool
  column : Y → A → R

namespace Shell

variable {X Y T A O : Type*}

def slots (s : Shell X Y T A R) (x : X) (y : Y) (a : A) : R :=
  if s.zeroMode a then (s.row x (s.node a)).eval₂ s.baseMap (s.point a) * s.column y a else 0

noncomputable def message (s : Shell X Y T A R) (p : ℕ) (x : X) (t : T) : NodeMessage p :=
  encodeDivisible p (s.row x t) (s.row_divisible x t)

def receive (s : Shell X Y T A R) {p : ℕ} (m : T → NodeMessage p) (y : Y) (a : A) : R :=
  if s.zeroMode a then reconstruct (m (s.node a)) (s.point a) * s.column y a else 0

/-- One array per node reconstructs the entire addressed shell jointly. -/
theorem slots_from_message (s : Shell X Y T A R) {p : ℕ} (h₂ : (2 : R) ^ p = 0)
    (x : X) (y : Y) : s.slots x y = s.receive (s.message p x) y := by
  funext a
  simp only [slots, receive, message, reconstruct_divisible h₂ s.baseMap]

/-- Count distinct output rows after arbitrary processing of the complete
residue menu. The sender may also supply any finite auxiliary symbol. -/
theorem decoded_row_count_with_aux [Fintype T] {V : Type*} [Fintype V]
    (s : Shell X Y T A R) {p : ℕ} (h₂ : (2 : R) ^ p = 0)
    (aux : X → V) (decode : Y → V → (A → R) → O) :
    (Set.range (fun x : X => fun y : Y => decode y (aux x) (s.slots x y))).Finite ∧
    Nat.card (Set.range (fun x : X => fun y : Y => decode y (aux x) (s.slots x y))) ≤
      Fintype.card V * 2 ^ (Fintype.card T * (p * (p + 1) / 2)) := by
  classical
  let decoderRows (m : V × (T → NodeMessage p)) (y : Y) : O := decode y m.1 (s.receive m.2 y)
  have hsub : Set.range (fun x : X => fun y : Y => decode y (aux x) (s.slots x y)) ⊆
      Set.range decoderRows := by
    rintro _ ⟨x, rfl⟩
    refine ⟨(aux x, s.message p x), ?_⟩
    funext y
    simp only [decoderRows, s.slots_from_message h₂]
  refine ⟨(Set.finite_range decoderRows).subset hsub, ?_⟩
  calc
    _ ≤ Nat.card (Set.range decoderRows) :=
      Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
    _ ≤ Nat.card (V × (T → NodeMessage p)) := Finite.card_range_le decoderRows
    _ = _ := by rw [Nat.card_prod, Nat.card_eq_fintype_card (α := V), shell_message_card]

theorem decoded_row_count [Fintype T] (s : Shell X Y T A R) {p : ℕ} (h₂ : (2 : R) ^ p = 0)
    (decode : Y → (A → R) → O) :
    (Set.range (fun x : X => fun y : Y => decode y (s.slots x y))).Finite ∧
    Nat.card (Set.range (fun x : X => fun y : Y => decode y (s.slots x y))) ≤
      2 ^ (Fintype.card T * (p * (p + 1) / 2)) := by
  simpa using s.decoded_row_count_with_aux h₂ (fun _ => Unit.unit) (fun y _ => decode y)

end Shell

def matchingOR {m : ℕ} (x y : Fin m → Bool) : Bool := decide (∀ i, x i = true ∨ y i = true)

/-- Setting all column bits except one to true reads exactly that row bit. -/
theorem matching_rows_injective (m : ℕ) : Function.Injective (@matchingOR m) := by
  intro x x' h
  funext i
  let y : Fin m → Bool := fun j => decide (j ≠ i)
  have isolate (v : Fin m → Bool) : matchingOR v y = true ↔ v i = true := by
    rw [matchingOR, decide_eq_true_eq]
    constructor
    · intro hv
      simpa [y] using hv i
    · intro hi j
      by_cases hji : j = i
      · exact Or.inl (hji ▸ hi)
      · exact Or.inr (by simp [y, hji])
  apply Bool.eq_iff_iff.mpr
  exact (isolate x).symm.trans ((Iff.of_eq (congrArg (· = true) (congrFun h y))).trans (isolate x'))

/-- The target is the Boolean product of the actual two-input ORs. Any
correct decoder of the residue shell and b additional row bits must pay
at least one bit per independent matched pair. -/
theorem matching_forces_bits {T A : Type*} [Fintype T] {m b p : ℕ}
    (s : Shell (Fin m → Bool) (Fin m → Bool) T A R) (h₂ : (2 : R) ^ p = 0)
    (aux : (Fin m → Bool) → Fin b → Bool)
    (decode : (Fin m → Bool) → (Fin b → Bool) → (A → R) → Bool)
    (correct : ∀ x y, decode y (aux x) (s.slots x y) = matchingOR x y) :
    m ≤ b + Fintype.card T * (p * (p + 1) / 2) := by
  have hrows := (s.decoded_row_count_with_aux h₂ aux decode).2
  have hf : (fun x y => decode y (aux x) (s.slots x y)) = @matchingOR m := by
    funext x y
    exact correct x y
  rw [hf, ← Nat.card_congr (Equiv.ofInjective _ (matching_rows_injective m)),
    Nat.card_eq_fintype_card] at hrows
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  simpa [pow_add] using hrows

/-- The parity target of the shortened pin-free count family on a matching. -/
def matchingEquality {m : ℕ} (x y : Fin m → Bool) : Bool := decide (x = y)

theorem equality_rows_injective (m : ℕ) : Function.Injective (@matchingEquality m) := by
  intro x x' h
  have hx := congrFun h x
  have he : x' = x := by simpa [matchingEquality] using hx.symm
  exact he.symm

theorem equality_forces_bits {T A : Type*} [Fintype T] {m b p : ℕ}
    (s : Shell (Fin m → Bool) (Fin m → Bool) T A R) (h₂ : (2 : R) ^ p = 0)
    (aux : (Fin m → Bool) → Fin b → Bool)
    (decode : (Fin m → Bool) → (Fin b → Bool) → (A → R) → Bool)
    (correct : ∀ x y, decode y (aux x) (s.slots x y) = matchingEquality x y) :
    m ≤ b + Fintype.card T * (p * (p + 1) / 2) := by
  have hrows := (s.decoded_row_count_with_aux h₂ aux decode).2
  have hf : (fun x y => decode y (aux x) (s.slots x y)) = @matchingEquality m := by
    funext x y
    exact correct x y
  rw [hf, ← Nat.card_congr (Equiv.ofInjective _ (equality_rows_injective m)),
    Nat.card_eq_fintype_card] at hrows
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  simpa [pow_add] using hrows

#print axioms equality_rows_injective
#print axioms equality_forces_bits
#print axioms odd_denominator_unit
#print axioms cast_representative
#print axioms weighted_coefficient
#print axioms scaled_representation
#print axioms contraction_divisibility
#print axioms reconstruct_eq_eval
#print axioms reconstruct_divisible
#print axioms simultaneous_reconstruction
#print axioms node_message_card
#print axioms shell_message_card
#print axioms Shell.slots_from_message
#print axioms Shell.decoded_row_count_with_aux
#print axioms Shell.decoded_row_count
#print axioms matching_rows_injective
#print axioms matching_forces_bits

end TruncatedProbeMenu
