import HermiteLossReceive
import HermiteLossSchedule
import J6ActiveSchedule
import Mathlib.Algebra.Module.BigOperators

/-! R9 finite Hermite recomposition. The signed mesh, child exponents,
and denominator losses are the previously verified printed formulas. -/
namespace J6R9Hermite

open P1DyadicGrid DenominatorBudget HermiteLoss
open J6ActiveSchedule
open scoped BigOperators

theorem active_retained (a M u : ℕ) :
    active a M u = retained a u (sourceH M u) := rfl

theorem order_taper (M u : ℕ) (t : ℤ) :
    order M u t = taper u (sourceH M u) (level t) := rfl

/-- D_t=L/2^i agrees with the shortened power in the loss proof. -/
theorem child_precision_loss (p a M u : ℕ) {t : ℤ}
    (ht : t∈grid a) (hn : t≠0) :
    childPrecision p a M u t =
      J9PrintedSchedule.precision p (sourceH M u) (2^(a-level t)) M a := by
  have hi : level t≤a := level_grid_le ht hn
  let i := level t
  have hpow : (2:ℕ)^a = 2^(a-i)*2^i := by
    rw [←pow_add,Nat.sub_add_cancel hi]
  change J9PrintedSchedule.precision p (sourceH M u) (2^a/2^i) M a = _
  rw [hpow,Nat.mul_div_cancel _ (by positivity)]

noncomputable def recompose (a M u : ℕ) (jet : ℤ → ℕ → ℚ) : ℚ :=
  ∑ t ∈ active a M u,
    ∑ j ∈ Finset.range (order M u t), weight a u (sourceH M u) j t * jet t j

theorem integral_pow_two (p : ℕ) : (2:ℚ)^p∈twoLocalSubalgebra :=
  (mem_twoLocal_iff _).mpr ⟨(2:ℤ)^p,1,by norm_num,by simp⟩

theorem congr_zero (p : ℕ) : congruence p 0 0 :=
  ⟨0,twoLocalSubalgebra.zero_mem,by simp⟩

theorem congr_add (p : ℕ) {x y a b : ℚ}
    (h : congruence p x y) (k : congruence p a b) :
    congruence p (x+a) (y+b) := by
  obtain ⟨r,hr,he⟩ := h
  obtain ⟨s,hs,hf⟩ := k
  refine ⟨r+s,twoLocalSubalgebra.add_mem hr hs,?_⟩
  linarith only [he,hf,mul_add ((2:ℚ)^p) r s]

theorem congr_sum {ι : Type*} (s : Finset ι) (p : ℕ) (f g : ι→ℚ)
    (h : ∀ j∈s, congruence p (f j) (g j)) :
    congruence p (∑ j∈s, f j) (∑ j∈s, g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using congr_zero p
  | insert j s hs ih =>
    rw [Finset.sum_insert hs,Finset.sum_insert hs]
    exact congr_add p (h j (Finset.mem_insert_self j s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Summing the actual local quotient-coefficient errors retains p
bits. This step has no assumption of cancellation between nodes. -/
theorem weighted_sum_receive (a M u p : ℕ) (hM : u≤M)
    (approx exactJet : ℤ → ℕ → ℚ)
    (h : ∀ t∈active a M u, ∀ j<order M u t,
      congruence (childPrecision p a M u t) (approx t j) (exactJet t j)) :
    congruence p (recompose a M u approx) (recompose a M u exactJet) := by
  unfold recompose
  apply congr_sum
  intro t ht
  apply congr_sum
  intro j hj
  have hmem : t ∈ retained a u (sourceH M u) := (active_retained a M u) ▸ ht
  obtain ⟨ht',hn,_⟩ := retained_mem.mp hmem
  have hd := h t ht j (Finset.mem_range.mp hj)
  rw [child_precision_loss p a M u ht' hn] at hd
  exact printed_weight_precision ht' hn hM (Finset.mem_range.mp hj) hd

/-- A reconstruction sum congruent to an integral exact origin is
itself integral, before it is reduced. -/
theorem witness_integral {p : ℕ} {x y : ℚ}
    (hy : y∈twoLocalSubalgebra) (h : congruence p x y) :
    x∈twoLocalSubalgebra := by
  obtain ⟨r,hr,he⟩ := h
  have e : x=y+(2:ℚ)^p*r := by linarith [he]
  rw [e]
  exact twoLocalSubalgebra.add_mem hy
    (twoLocalSubalgebra.mul_mem (integral_pow_two p) hr)

theorem integral_origin (a M u p : ℕ) (hM : u≤M)
    (approx exactJet : ℤ → ℕ → ℚ) {origin : ℚ}
    (correct : recompose a M u exactJet=origin)
    (originMem : origin∈twoLocalSubalgebra)
    (h : ∀ t∈active a M u, ∀ j<order M u t,
      congruence (childPrecision p a M u t) (approx t j) (exactJet t j)) :
    ∃ z : TwoLocal, twoLocalRat z = recompose a M u approx ∧
      congruence p (twoLocalRat z) origin := by
  have hh := weighted_sum_receive a M u p hM approx exactJet h
  rw [correct] at hh
  exact ⟨⟨_,witness_integral originMem hh⟩,rfl,hh⟩

section Coordinates
variable {K : Type*} [AddCommGroup K] [Module ℚ K]

noncomputable def linearRecompose (a M u : ℕ) (jet : ℤ→ℕ→K) : K :=
  ∑ t ∈ active a M u,
    ∑ j ∈ Finset.range (order M u t), weight a u (sourceH M u) j t • jet t j

theorem recompose_coordinate (a M u : ℕ) (jet : ℤ→ℕ→K) (read : K→ₗ[ℚ]ℚ) :
    read (linearRecompose a M u jet) =
      recompose a M u (fun t j => read (jet t j)) := by
  simp only [linearRecompose,recompose,map_sum,map_smul,smul_eq_mul]

/-- Any linear coefficient in the characteristic-zero extension can be
recovered independently; its normalized lift is certified two-local. -/
theorem coordinate_receive (a M u p : ℕ) (hM : u≤M)
    (exactJet : ℤ→ℕ→K) (origin : K) (read : K→ₗ[ℚ]ℚ) (approx : ℤ→ℕ→ℚ)
    (correct : linearRecompose a M u exactJet=origin)
    (originMem : read origin∈twoLocalSubalgebra)
    (h : ∀ t∈active a M u, ∀ j<order M u t,
      congruence (childPrecision p a M u t) (approx t j) (read (exactJet t j))) :
    ∃ z : TwoLocal, twoLocalRat z=recompose a M u approx ∧
      congruence p (twoLocalRat z) (read origin) := by
  have he := congrArg read correct
  rw [recompose_coordinate] at he
  exact integral_origin a M u p hM approx _ he originMem h

end Coordinates

#print axioms child_precision_loss
#print axioms weighted_sum_receive
#print axioms witness_integral
#print axioms integral_origin
#print axioms coordinate_receive
end J6R9Hermite

