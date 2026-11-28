import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic

/-!
# Finite zero-probe contraction and mixed moments

The theorems concern an already supplied partial wiring. Matched bits are
addressed by a finite type; row and column truth tables have disjoint local
arguments. Feature states use finite-support convolution and coefficients in
the original ring, so the table identity also holds at finite residue
precision. No complexity or source-packing premise is built into the model.
-/

open scoped BigOperators Classical

namespace JointContraction

noncomputable section

section Convolution

variable {R I V : Type*} [CommSemiring R] [AddCommMonoid I]
variable {U : V → Type*} [∀ v, Fintype (U v)]

/-- State after processing a set of vertices: local weights are recorded in the
coefficient ring, while exponents record their actual additive feature labels. -/
noncomputable def distribution (s : Finset V) (w : ∀ v, U v → R)
    (c : ∀ v, U v → I) : AddMonoidAlgebra R I :=
  ∏ v ∈ s, ∑ z : U v, AddMonoidAlgebra.single (c v z) (w v z)

theorem distribution_empty (w : ∀ v, U v → R) (c : ∀ v, U v → I) :
    distribution ∅ w c = 1 := by simp [distribution]

/-- One actual convolution step: process each local assignment once. -/
theorem distribution_insert [DecidableEq V] (v : V) (s : Finset V) (hv : v ∉ s)
    (w : ∀ v, U v → R) (c : ∀ v, U v → I) :
    distribution (insert v s) w c =
      ∑ z : U v, AddMonoidAlgebra.single (c v z) (w v z) * distribution s w c := by
  rw [distribution, Finset.prod_insert hv, Finset.sum_mul]
  rfl

private theorem prod_single (s : Finset V) (a : V → I) (b : V → R) :
    (∏ v ∈ s, AddMonoidAlgebra.single (a v) (b v)) =
      AddMonoidAlgebra.single (∑ v ∈ s, a v) (∏ v ∈ s, b v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddMonoidAlgebra.one_def]
  | insert v s hv ih => simp [Finset.prod_insert hv, Finset.sum_insert hv, ih]

/-- The table's multiplicative expression equals the full distribution of all
simultaneous local choices, even for dependent local assignment types. -/
theorem distribution_exact [Fintype V] (w : ∀ v, U v → R) (c : ∀ v, U v → I) :
    distribution Finset.univ w c =
      ∑ x : (∀ v, U v), AddMonoidAlgebra.single (∑ v, c v (x v)) (∏ v, w v (x v)) := by
  classical
  unfold distribution
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun x _ => prod_single Finset.univ _ _

/-- An individual entry is the sum over precisely the requested statistic
fiber. The entry lookup does not require a finite type of all possible indices. -/
theorem distribution_entry [Fintype V] [DecidableEq I]
    (w : ∀ v, U v → R) (c : ∀ v, U v → I) (j : I) :
    distribution Finset.univ w c j =
      ∑ x : (∀ v, U v), if (∑ v, c v (x v)) = j then (∏ v, w v (x v)) else 0 := by
  classical
  rw [distribution_exact]
  change (Finsupp.lapply j : (I →₀ R) →ₗ[R] R)
    (∑ x : (∀ v, U v), Finsupp.single (∑ v, c v (x v)) (∏ v, w v (x v))) = _
  rw [map_sum]
  simp only [Finsupp.lapply_apply, Finsupp.single_apply]

/-- Several moment queries may reuse the same table. The readout may be any
function on the state, in particular a product of arbitrary moment powers. -/
noncomputable def readout (f : I → R) : AddMonoidAlgebra R I →ₗ[R] R :=
  Finsupp.linearCombination R f

theorem readout_distribution [Fintype V] (f : I → R)
    (w : ∀ v, U v → R) (c : ∀ v, U v → I) :
    readout f (distribution Finset.univ w c) =
      ∑ x : (∀ v, U v), (∏ v, w v (x v)) * f (∑ v, c v (x v)) := by
  classical
  rw [distribution_exact, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  change Finsupp.linearCombination R f (Finsupp.single _ _) = _
  simp

end Convolution

section FeatureBox

variable {R V D : Type*} [CommSemiring R] [Fintype V] [Fintype D]
variable {U : V → Type*} [∀ v, Fintype (U v)]

/-- The exact distribution lives inside the product of the integer feature
ranges. It is the actual state count, not the number of possible moment
queries or the number of all assignments. -/
theorem feature_support_card (w : ∀ v, U v → R) (c : ∀ v, U v → D → ℕ)
    (limit : D → ℕ)
    (bound : ∀ x : (∀ v, U v), ∀ d, (∑ v, c v (x v)) d ≤ limit d) :
    (distribution Finset.univ w c).support.card ≤ ∏ d, (limit d + 1) := by
  classical
  let box := Fintype.piFinset fun d => Finset.range (limit d + 1)
  have hsub : (distribution Finset.univ w c).support ⊆ box := by
    intro j hj
    by_contra hn
    apply (Finsupp.mem_support_iff.mp hj)
    rw [distribution_entry]
    refine Finset.sum_eq_zero fun x _ => ?_
    have hne : (∑ v, c v (x v)) ≠ j := by
      intro he
      apply hn
      rw [← he]
      exact Fintype.mem_piFinset.mpr fun d => Finset.mem_range.mpr (Nat.lt_succ_of_le (bound x d))
    simp [hne]
  simpa [box] using Finset.card_le_card hsub

end FeatureBox

section IndexShift

variable {R I V : Type*} [CommSemiring R] [AddCommGroup I] [DecidableEq V]
variable {U : V → Type*} [∀ v, Fintype (U v)]

/-- Coefficient form of the streaming update. In the integer-vector version,
indices outside the feasible range are automatically zero by finite support. -/
theorem distribution_insert_entry (v : V) (s : Finset V) (hv : v ∉ s)
    (w : ∀ v, U v → R) (c : ∀ v, U v → I) (j : I) :
    distribution (insert v s) w c j =
      ∑ z : U v, w v z * distribution s w c (j - c v z) := by
  rw [distribution_insert v s hv]
  change (Finsupp.lapply j : (I →₀ R) →ₗ[R] R)
    (∑ z : U v, AddMonoidAlgebra.single (c v z) (w v z) * distribution s w c) = _
  rw [map_sum]
  simp only [Finsupp.lapply_apply, AddMonoidAlgebra.single_mul_apply, neg_add_eq_sub]

end IndexShift

section KernelAtCenter

variable {K : Type*} [Field K]

/-- The polynomial form of the packet kernel, with its single linear factor
already canceled. The normalizing denominator is independent of the slot. -/
def canceledKernel (grid : Finset K) (norm t shift : K) : K :=
  (∏ q ∈ grid.erase shift, (t - q)) / norm

/-- At a grid center only columns whose slot difference equals that center
survive. This is an exact characteristic-zero identity before reduction. -/
theorem canceledKernel_at_center (grid : Finset K) (norm t shift : K) (ht : t ∈ grid) :
    canceledKernel grid norm t shift =
      if shift = t then (∏ q ∈ grid.erase t, (t - q)) / norm else 0 := by
  by_cases he : shift = t
  · simp [canceledKernel, he]
  · have hmem : t ∈ grid.erase shift := Finset.mem_erase.mpr ⟨Ne.symm he, ht⟩
    have hprod : (∏ q ∈ grid.erase shift, (t - q)) = 0 :=
      Finset.prod_eq_zero hmem (sub_self t)
    simp [canceledKernel, he, hprod]

end KernelAtCenter

section PartialWiring

variable {R A B M : Type*} [CommRing R] [Fintype A] [Fintype B] [Fintype M]
variable {P : A → Type*} {Q : B → Type*}
variable [∀ a, Fintype (P a)] [∀ b, Fintype (Q b)]

/-- The Boolean affine literal used by the actual tensor deformation. -/
def literal (y : Bool) (z : R) : R := if y then z else 1 - z

/-- Evaluating a partial row wire at the already enumerated matched bits. -/
def wiredInput (c : R) (w : M → Bool) (j : Option M) : R :=
  match j with
  | none => 0
  | some m => if w m then c else 0

/-- Restrict an entire column assignment to the supplied matched addresses. -/
def matchedBits (ports : M → Sigma Q) (x : ∀ b, Q b → Bool) (m : M) : Bool :=
  x (ports m).1 (ports m).2

/-- Local check for consistency with a fixed matched assignment. -/
def agrees (ports : M → Sigma Q) (w : M → Bool) (b : B) (x : Q b → Bool) : Prop :=
  ∀ q : Q b, ∀ m : M, ports m = ⟨b, q⟩ → x q = w m

omit [Fintype B] [Fintype M] [∀ b, Fintype (Q b)] in
theorem all_agree_iff (ports : M → Sigma Q) (w : M → Bool) (x : ∀ b, Q b → Bool) :
    (∀ b, agrees ports w b (x b)) ↔ matchedBits ports x = w := by
  constructor
  · intro h
    funext m
    exact h (ports m).1 (ports m).2 m (Sigma.eta (ports m)).symm
  · intro h b q m he
    have hpoint := congrFun h m
    unfold matchedBits at hpoint
    rw [he] at hpoint
    exact hpoint

/-- Disintegrate a finite sum over a set of observed values. -/
private theorem sum_over_fibers {X W : Type*} [Fintype X] [Fintype W]
    (q : X → W) (f : W → R) (g : X → R) :
    (∑ x, f (q x) * g x) =
      ∑ w, f w * ∑ x, if q x = w then g x else 0 := by
  classical
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp

/-- Sum over the original row truth table one vertex at a time. -/
noncomputable def rowValue (wire : ∀ a, P a → Option M) (c : R)
    (tableA : ∀ a, (P a → Bool) → R) (w : M → Bool) : R :=
  ∏ a, ∑ y : P a → Bool, tableA a y * ∏ p, literal (y p) (wiredInput c w (wire a p))

omit [Fintype M] in
private theorem row_sum (wire : ∀ a, P a → Option M) (c : R)
    (tableA : ∀ a, (P a → Bool) → R) (w : M → Bool) :
    (∑ y : (∀ a, P a → Bool),
      (∏ a, tableA a (y a)) * ∏ a, ∏ p, literal (y a p) (wiredInput c w (wire a p))) =
      rowValue wire c tableA w := by
  classical
  simp only [rowValue, Fintype.prod_sum, Finset.prod_mul_distrib]

theorem product_column_marginals (ports : M → Sigma Q)
    (tableB : ∀ b, (Q b → Bool) → R) (w : M → Bool) :
    (∏ b, ∑ z : Q b → Bool, if agrees ports w b z then tableB b z else 0) =
      ∑ x : (∀ b, Q b → Bool),
        if matchedBits ports x = w then (∏ b, tableB b (x b)) else 0 := by
  classical
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : matchedBits ports x = w
  · simp [hx, (all_agree_iff ports w x).2 hx]
  · have hn : ¬ ∀ b, agrees ports w b (x b) := fun h =>
      hx ((all_agree_iff ports w x).1 h)
    obtain ⟨b, hb⟩ := not_forall.mp hn
    rw [if_neg hx]
    exact Finset.prod_eq_zero (Finset.mem_univ b) (if_neg hb)

/-- J4. The original independent row/column sum collapses to matched bits and
local marginals, without an explicit list of complete original assignments.
An isolated vertex is still included, as a truth table on an empty port set. -/
theorem zero_probe_contraction (ports : M → Sigma Q) (wire : ∀ a, P a → Option M)
    (c : R) (tableA : ∀ a, (P a → Bool) → R) (tableB : ∀ b, (Q b → Bool) → R) :
    (∑ x : (∀ b, Q b → Bool), ∑ y : (∀ a, P a → Bool),
      ((∏ a, tableA a (y a)) * ∏ a, ∏ p,
        literal (y a p) (wiredInput c (matchedBits ports x) (wire a p))) *
      (∏ b, tableB b (x b))) =
    ∑ w : M → Bool, rowValue wire c tableA w *
      ∏ b, ∑ z : Q b → Bool, if agrees ports w b z then tableB b z else 0 := by
  classical
  simp_rw [← Finset.sum_mul, row_sum]
  rw [sum_over_fibers (matchedBits ports) (rowValue wire c tableA)]
  refine Finset.sum_congr rfl fun w _ => congrArg (rowValue wire c tableA w * ·) ?_
  rw [product_column_marginals]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : matchedBits ports x = w <;> simp [hx]

theorem matched_assignment_card : Fintype.card (M → Bool) = 2 ^ Fintype.card M := by
  classical
  simp

variable {I : Type*} [AddCommMonoid I]

/-- J5. For each matched assignment, the same native table answers every
function of an additive vector of tile statistics. Unmatched column bits
are summed by local weighted convolutions. -/
theorem joint_moment_contraction (ports : M → Sigma Q) (wire : ∀ a, P a → Option M)
    (c : R) (tableA : ∀ a, (P a → Bool) → R) (tableB : ∀ b, (Q b → Bool) → R)
    (stat : ∀ b, (Q b → Bool) → I) (moment : I → R) :
    (∑ x : (∀ b, Q b → Bool), ∑ y : (∀ a, P a → Bool),
      ((∏ a, tableA a (y a)) * ∏ a, ∏ p,
        literal (y a p) (wiredInput c (matchedBits ports x) (wire a p))) *
      ((∏ b, tableB b (x b)) * moment (∑ b, stat b (x b)))) =
    ∑ w : M → Bool, rowValue wire c tableA w *
      readout moment (distribution Finset.univ
        (fun b z => if agrees ports w b z then tableB b z else 0) stat) := by
  classical
  simp_rw [← Finset.sum_mul, row_sum]
  rw [sum_over_fibers (matchedBits ports) (rowValue wire c tableA)]
  refine Finset.sum_congr rfl fun w _ => congrArg (rowValue wire c tableA w * ·) ?_
  rw [readout_distribution]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : matchedBits ports x = w
  · simp [hx, (all_agree_iff ports w x).2 hx]
  · have hn : ¬ ∀ b, agrees ports w b (x b) := fun h =>
      hx ((all_agree_iff ports w x).1 h)
    obtain ⟨b, hb⟩ := not_forall.mp hn
    rw [if_neg hx, Finset.prod_eq_zero (Finset.mem_univ b) (if_neg hb), zero_mul]

end PartialWiring

/-- In the parity quotient all positive powers are the input bit. -/
theorem parity_pos_pow (x : ZMod 2) {n : ℕ} (hn : 0 < n) : x ^ n = x := by
  fin_cases x <;> simp [Nat.ne_of_gt hn]

/-- At parity, a tile moment of positive index is just its odd-index
feature, while index zero is the total-bit feature, including at index 0. -/
theorem parity_tile (s : Finset ℕ) (x : ℕ → ZMod 2) (n : ℕ) :
    (∑ j ∈ s, (j : ZMod 2) ^ n * x j) =
      if n = 0 then (∑ j ∈ s, x j) else ∑ j ∈ s, (j : ZMod 2) * x j := by
  by_cases h : n = 0
  · simp [h]
  · simp [h, parity_pos_pow _ (Nat.pos_of_ne_zero h)]

section RationalRecovery

variable {K V T : Type*} [Field K]

/-- The product rule expressed solely through the zeroth and first coefficients,
so all higher Taylor coefficients may be discarded. -/
theorem normalized_product_first (s : Finset V) (f : V → Polynomial K)
    (h : ∀ i ∈ s, (f i).coeff 0 ≠ 0) :
    (∏ i ∈ s, f i).coeff 1 / (∏ i ∈ s, f i).coeff 0 =
      ∑ i ∈ s, (f i).coeff 1 / (f i).coeff 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Polynomial.coeff_one]
  | insert i s hi ih =>
    have h0 : (f i).coeff 0 ≠ 0 := h i (Finset.mem_insert_self i s)
    have hs : ∀ j ∈ s, (f j).coeff 0 ≠ 0 := fun j hj =>
      h j (Finset.mem_insert_of_mem hj)
    have hprod : (∏ j ∈ s, f j).coeff 0 ≠ 0 := by
      rw [Polynomial.coeff_zero_prod]
      exact Finset.prod_ne_zero_iff.mpr hs
    simp only [Finset.prod_insert hi, Finset.sum_insert hi, Polynomial.mul_coeff_one,
      Polynomial.mul_coeff_zero]
    rw [← ih hs]
    field_simp [h0, hprod]
    ring

def bitScalar (K : Type*) [Zero K] [One K] (b : Bool) : K :=
  if b then 1 else 0

def pinPolynomial (b : Bool) (p : Polynomial K) : Polynomial K :=
  if b then p else 1 - p

private theorem pin_constant_ne_zero (b : Bool) (p : Polynomial K)
    (h0 : p.coeff 0 ≠ 0) (h1 : p.coeff 0 ≠ 1) : (pinPolynomial b p).coeff 0 ≠ 0 := by
  cases b
  · simpa [pinPolynomial, sub_ne_zero] using Ne.symm h1
  · simpa [pinPolynomial] using h0

theorem pin_normalized_first (b : Bool) (p : Polynomial K)
    (h0 : p.coeff 0 ≠ 0) (h1 : p.coeff 0 ≠ 1) :
    (pinPolynomial b p).coeff 1 / (pinPolynomial b p).coeff 0 +
        p.coeff 1 / (1 - p.coeff 0) =
      (p.coeff 1 / (p.coeff 0 * (1 - p.coeff 0))) * bitScalar K b := by
  cases b
  · simp [pinPolynomial, bitScalar, Polynomial.coeff_one, neg_div]
  · have hs : 1 - p.coeff 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    simp [pinPolynomial, bitScalar]
    field_simp [h0, hs]
    ring

/-- J3: on a singleton assignment fiber, a first Taylor coefficient gives
the stated affine-linear equation in the true signs. The public polynomial
includes all other factors. This is conditional on nonzero denominators. -/
theorem singleton_pin_first [Fintype V] (other : Polynomial K)
    (p : V → Polynomial K) (sign : V → Bool) (hB : other.coeff 0 ≠ 0)
    (h0 : ∀ v, (p v).coeff 0 ≠ 0) (h1 : ∀ v, (p v).coeff 0 ≠ 1) :
    let H := other * ∏ v, pinPolynomial (sign v) (p v)
    H.coeff 1 / H.coeff 0 - other.coeff 1 / other.coeff 0 +
      (∑ v, (p v).coeff 1 / (1 - (p v).coeff 0)) =
        ∑ v, ((p v).coeff 1 / ((p v).coeff 0 * (1 - (p v).coeff 0))) *
          bitScalar K (sign v) := by
  dsimp
  let F := ∏ v, pinPolynomial (sign v) (p v)
  have hlocal : ∀ v, (pinPolynomial (sign v) (p v)).coeff 0 ≠ 0 := fun v =>
    pin_constant_ne_zero (sign v) (p v) (h0 v) (h1 v)
  have hF : F.coeff 0 ≠ 0 := by
    dsimp [F]
    rw [Polynomial.coeff_zero_prod]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => hlocal v
  have hpart : (other * F).coeff 1 / (other * F).coeff 0 =
      other.coeff 1 / other.coeff 0 + F.coeff 1 / F.coeff 0 := by
    rw [Polynomial.mul_coeff_one, Polynomial.mul_coeff_zero]
    field_simp [hB, hF]
    ring
  change (other * F).coeff 1 / (other * F).coeff 0 - other.coeff 1 / other.coeff 0 +
    (∑ v, (p v).coeff 1 / (1 - (p v).coeff 0)) = _
  rw [hpart, add_sub_cancel_left]
  dsimp only [F]
  rw [normalized_product_first _ _ (fun v _ => hlocal v), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => pin_normalized_first (sign v) (p v) (h0 v) (h1 v)

/-- An already checked left inverse of the stacked coefficient matrix
recovers each sign scalar from the actual normalized observations. -/
theorem recover_with_left_inverse [Fintype V] [Fintype T] (coef : T → V → K)
    (inv : V → T → K) (left : ∀ i j, (∑ t, inv i t * coef t j) = if i = j then 1 else 0)
    (sign : V → Bool) (i : V) :
    (∑ t, inv i t * (∑ j, coef t j * bitScalar K (sign j))) = bitScalar K (sign i) := by
  calc
    _ = ∑ j, (∑ t, inv i t * coef t j) * bitScalar K (sign j) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    _ = _ := by simp [left, ite_mul]

theorem sign_recovery_unique [Fintype V] (coef : T → V → K)
    (inj : Function.Injective (fun x : V → K => fun t => ∑ v, coef t v * x v))
    {sign sign' : V → Bool}
    (observations : ∀ t, (∑ v, coef t v * bitScalar K (sign v)) =
        ∑ v, coef t v * bitScalar K (sign' v)) : sign = sign' := by
  have h := inj (funext observations)
  funext v
  have hv := congrFun h v
  cases hsign : sign v <;> cases hsign' : sign' v <;> simp_all [bitScalar]

end RationalRecovery

#print axioms distribution_insert
#print axioms distribution_exact
#print axioms distribution_entry
#print axioms feature_support_card
#print axioms distribution_insert_entry
#print axioms readout_distribution
#print axioms canceledKernel_at_center
#print axioms zero_probe_contraction
#print axioms matched_assignment_card
#print axioms joint_moment_contraction
#print axioms parity_tile
#print axioms singleton_pin_first
#print axioms recover_with_left_inverse
#print axioms sign_recovery_unique

end

end JointContraction
