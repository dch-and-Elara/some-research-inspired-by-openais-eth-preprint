import J6ActiveUniqueness
import Mathlib.Algebra.Ring.GeomSum

/-! Literal finite Hermite recovery formula of Appendix D, lines 274–291.
The jet reciprocal is a finite geometric polynomial and only the first
specified Taylor orders are used. All exact assembly is done in the
rational coefficient algebra, not by inverting even elements of a residue ring. -/
namespace J6ActiveHermite
open scoped BigOperators Polynomial
open Polynomial J6ActiveUniqueness
variable {R I : Type*} [CommRing R] [DecidableEq I]

noncomputable def trim (k : ℕ) (f : R[X]) : R[X] := f %ₘ X^k

theorem prefix_dvd (k : ℕ) (f : R[X]) : (X:R[X])^k ∣ f - trim k f := by
  rw [trim, modByMonic_eq_sub_mul_div f (monic_X.pow k), sub_sub_cancel]
  exact dvd_mul_right _ _

theorem prefix_eq_of_coeff (k : ℕ) {f g : R[X]}
    (h : ∀ j < k, f.coeff j = g.coeff j) : trim k f = trim k g := by
  have hd : (X:R[X])^k ∣ f-g := (X_pow_dvd_iff).mpr (fun j hj => by simp [h j hj])
  apply sub_eq_zero.mp
  unfold trim
  rw [← sub_modByMonic, modByMonic_eq_zero_iff_dvd (monic_X.pow k)]
  exact hd

noncomputable def geomInverse (k : ℕ) (g : R[X]) : R[X] :=
  ∑ i ∈ Finset.range k, (1-g)^i

theorem geom_inverse_mod (k : ℕ) (g : R[X]) (hg : g.coeff 0 = 1) :
    (X:R[X])^k ∣ g * geomInverse k g - 1 := by
  have hX : X ∣ 1-g := by rw [X_dvd_iff]; simp [hg]
  have hgeo : geomInverse k g * g = 1-(1-g)^k := by
    simpa [geomInverse, sub_sub_cancel] using geom_sum_mul_neg (1-g) k
  rw [mul_comm, hgeo, sub_right_comm, sub_self, zero_sub]
  exact dvd_neg.mpr (pow_dvd_pow_of_dvd hX k)

noncomputable def normalizer (s : Finset I) (node : I → R) (k : I → ℕ)
    (inv : I → I → R) (i : I) : R[X] :=
  ∏ j ∈ s.erase i, (C (inv i j) * (X - C (node j)))^k j

theorem normalizer_at_own (s : Finset I) (node : I → R) (k : I → ℕ)
    (inv : I → I → R) (i : I) (a : Rˣ)
    (hinv : ∀ j ∈ s.erase i, inv i j * (node i - node j) = 1) :
    (atNode a (node i) (normalizer s node k inv i)).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, atNode_apply, eval_comp]
  simp only [coord, eval_add, eval_mul, eval_C, eval_X, mul_zero, zero_add]
  unfold normalizer
  simp only [eval_prod, eval_pow, eval_mul, eval_sub, eval_C, eval_X]
  exact Finset.prod_eq_one (fun j hj => by rw [hinv j hj, one_pow])

theorem normalizer_dvd_other (s : Finset I) (node : I → R) (k : I → ℕ)
    (inv : I → I → R) {i j : I} (hij : j ≠ i) (hj : j ∈ s) :
    (X - C (node j))^k j ∣ normalizer s node k inv i := by
  unfold normalizer
  refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hij,hj⟩))
  rw [mul_pow]
  exact dvd_mul_left _ _

theorem normalizer_degree (s : Finset I) (node : I → R) (k : I → ℕ)
    (inv : I → I → R) (i : I) :
    (normalizer s node k inv i).natDegree ≤ ∑ j ∈ s.erase i, k j := by
  unfold normalizer
  apply (natDegree_prod_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply natDegree_pow_le.trans
  have hd : (C (inv i j) * (X - C (node j))).natDegree ≤ 1 :=
    natDegree_mul_le.trans (by simpa using natDegree_X_sub_C_le (node j))
  simpa using Nat.mul_le_mul_left (k j) hd

noncomputable def dividedJet (k : ℕ) (e jet : R[X]) : R[X] :=
  trim k (jet * geomInverse k e)

theorem dividedJet_degree [Nontrivial R] (k : ℕ) (hk : 0 < k) (e f : R[X]) :
    (dividedJet k e f).natDegree < k := by
  unfold dividedJet trim
  have hn : (X:R[X])^k ≠ 1 := by
    intro h
    have hc := congrArg Polynomial.natDegree h
    simp at hc
    omega
  simpa using natDegree_modByMonic_lt (f * geomInverse k e) (monic_X.pow k) hn

theorem dividedJet_congr (k : ℕ) (e f g : R[X])
    (h : ∀ j < k, f.coeff j = g.coeff j) :
    dividedJet k e f = dividedJet k e g := by
  apply prefix_eq_of_coeff
  have hd : (X:R[X])^k ∣ f-g := X_pow_dvd_iff.mpr (fun j hj => by simp [h j hj])
  have he : (X:R[X])^k ∣ f * geomInverse k e - g * geomInverse k e := by
    rw [← sub_mul]
    exact hd.mul_right _
  intro j hj
  have h0 := X_pow_dvd_iff.mp he j hj
  simpa only [coeff_sub,sub_eq_zero] using h0

theorem dividedJet_correct (k : ℕ) (e f : R[X]) (he : e.coeff 0 = 1) :
    (X:R[X])^k ∣ e * dividedJet k e f - f := by
  have hA := dvd_sub_comm.mpr (prefix_dvd k (f * geomInverse k e))
  have hB := geom_inverse_mod k e he
  have hh := (hA.mul_left e).add (hB.mul_left f)
  convert hh using 1
  simp only [dividedJet]
  ring

noncomputable def term (s : Finset I) (node : I → R) (k : I → ℕ) (inv : I → I → R)
    (a : Rˣ) (jet : I → R[X]) (i : I) : R[X] :=
  let e := normalizer s node k inv i
  e * (dividedJet (k i) (atNode a (node i) e) (jet i)).comp (back a (node i))

/-- The own term reproduces its supplied jet; other terms have the
necessary individual zero. -/
theorem term_own_dvd (s : Finset I) (node : I → R) (k : I → ℕ) (inv : I → I → R)
    (a : Rˣ) (f : R[X]) (i : I)
    (hinv : ∀ j ∈ s.erase i, inv i j * (node i - node j) = 1) :
    (X-C (node i))^k i ∣ term s node k inv a (fun j => atNode a (node j) f) i - f := by
  rw [factor_dvd_iff a, map_sub]
  unfold term
  dsimp only
  rw [map_mul]
  change (X:R[X])^k i ∣ (atNode a (node i) (normalizer s node k inv i)) *
    (((dividedJet (k i) (atNode a (node i) (normalizer s node k inv i))
       (atNode a (node i) f)).comp (back a (node i))).comp (coord a (node i))) -
     atNode a (node i) f
  rw [comp_assoc, back_comp, comp_X]
  exact dividedJet_correct _ _ _ (normalizer_at_own s node k inv i a hinv)

theorem term_other_dvd (s : Finset I) (node : I → R) (k : I → ℕ) (inv : I → I → R)
    (a : Rˣ) (jet : I → R[X]) {i j : I} (hij : j ≠ i) (hj : j ∈ s) :
    (X - C (node j))^k j ∣ term s node k inv a jet i :=
  (normalizer_dvd_other s node k inv hij hj).mul_right _

theorem term_degree [Nontrivial R] (s : Finset I) (node : I → R) (k : I → ℕ) (inv : I → I → R)
    (a : Rˣ) (jet : I → R[X]) (i : I) (hi : i ∈ s) (hk : 0 < k i) :
    (term s node k inv a jet i).natDegree < ∑ j ∈ s, k j := by
  unfold term
  dsimp only
  let e := atNode a (node i) (normalizer s node k inv i)
  have hlow := (back_degree a (node i) (dividedJet (k i) e (jet i))).trans_lt
    (dividedJet_degree (k i) hk e (jet i))
  rw [← Finset.sum_erase_add s k hi]
  exact lt_of_le_of_lt natDegree_mul_le (add_lt_add_of_le_of_lt
    (normalizer_degree s node k inv i) hlow)

noncomputable def reconstruct (s : Finset I) (node : I → R) (k : I → ℕ)
    (inv : I → I → R) (a : Rˣ) (jet : I → R[X]) : R[X] :=
  ∑ i ∈ s, term s node k inv a jet i

theorem reconstruct_exact [Nontrivial R] (s : Finset I) (node : I → R) (k : I → ℕ)
    (inv : I → I → R) (a : Rˣ) (f : R[X]) (hk : ∀ i ∈ s, 0 < k i)
    (hinv : ∀ i ∈ s, ∀ j ∈ s.erase i, inv i j * (node i - node j) = 1)
    (hdeg : f.natDegree < ∑ i ∈ s, k i) :
    reconstruct s node k inv a (fun i => atNode a (node i) f) = f := by
  let jet := fun i => atNode a (node i) f
  have hsep (i) (hi : i ∈ s) (j) (hj : j ∈ s) (hij : i ≠ j) :
      IsUnit (node i - node j) := by
    apply isUnit_iff_dvd_one.mpr
    exact ⟨inv i j, (hinv i hi j (Finset.mem_erase.mpr ⟨Ne.symm hij,hj⟩)).symm.trans (mul_comm _ _)⟩
  refine jets_determine s node k a hsep _ f ?_ hdeg ?_
  · have hp : (reconstruct s node k inv a jet).natDegree ≤ (∑ i ∈ s, k i)-1 := by
      unfold reconstruct
      apply natDegree_sum_le_of_forall_le
      intro i hi
      exact Nat.le_sub_one_of_lt (term_degree s node k inv a jet i hi (hk i hi))
    exact lt_of_le_of_lt hp (Nat.sub_lt (Nat.zero_lt_of_lt hdeg) (by decide))
  · intro i hi j hj
    unfold reconstruct
    rw [map_sum, finset_sum_coeff, Finset.sum_eq_single_of_mem i hi]
    · exact (factor_dvd_sub_iff a (node i) (k i) _ f).mp
        (term_own_dvd s node k inv a f i (hinv i hi)) j hj
    · intro u hu hui
      have hd := term_other_dvd s node k inv a jet (Ne.symm hui) hi
      exact X_pow_dvd_iff.mp ((factor_dvd_iff a (node i) _ _).mp hd) j hj

/-- Actual tapered recovery's evaluation formula before precision reduction.
The inputs can have arbitrary higher coefficients, since only their prescribed jets are read. -/
theorem recover_at [Nontrivial R] (s : Finset I) (node : I → R) (k : I → ℕ)
    (inv : I → I → R) (a : Rˣ) (f : R[X]) (sample : I → R[X]) (x : R)
    (hk : ∀ i ∈ s, 0 < k i)
    (hinv : ∀ i ∈ s, ∀ j ∈ s.erase i, inv i j * (node i - node j) = 1)
    (hdeg : f.natDegree < ∑ i ∈ s, k i)
    (hsample : ∀ i ∈ s, ∀ j < k i, (sample i).coeff j = (atNode a (node i) f).coeff j) :
    (∑ i ∈ s, (normalizer s node k inv i).eval x *
      (dividedJet (k i) (atNode a (node i) (normalizer s node k inv i)) (sample i)).eval
        ((↑a⁻¹ : R) * (x-node i))) = f.eval x := by
  rw [← reconstruct_exact s node k inv a f hk hinv hdeg]
  unfold reconstruct
  rw [eval_finset_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  unfold term
  rw [dividedJet_congr _ _ _ _ (hsample i hi)]
  simp [back,eval_comp]

#print axioms prefix_dvd
#print axioms geom_inverse_mod
#print axioms normalizer_at_own
#print axioms dividedJet_congr
#print axioms dividedJet_correct
#print axioms term_degree
#print axioms reconstruct_exact
#print axioms recover_at
end J6ActiveHermite