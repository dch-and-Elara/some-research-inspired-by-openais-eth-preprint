import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Exact Hermite reconstruction and the nonuniform field jet budget. -/

noncomputable section
open Polynomial Matrix
open scoped BigOperators

namespace HermiteJetTransport

variable {K I : Type*} [Field K]

def nodePower (t : K) (k : ℕ) : K[X] := (X - C t) ^ k

def nodeIdeal (t : K) (k : ℕ) : Ideal K[X] := Ideal.span {nodePower t k}

abbrev Jet (t : K) (k : ℕ) := K[X] ⧸ nodeIdeal t k

abbrev jet (t : K) (k : ℕ) : K[X] →+* Jet t k := Ideal.Quotient.mk _

lemma node_monic (t : K) (k : ℕ) : (nodePower t k).Monic := (monic_X_sub_C t).pow k

@[simp] lemma node_natDegree (t : K) (k : ℕ) : (nodePower t k).natDegree = k := by
  simp [nodePower, natDegree_pow]

lemma jet_zero_iff (t : K) (k : ℕ) (p : K[X]) : jet t k p = 0 ↔ nodePower t k ∣ p := by
  exact Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton

variable [Fintype I]

lemma total_monic (t : I → K) (k : I → ℕ) : (∏ i, nodePower (t i) (k i)).Monic :=
  monic_prod_of_monic _ _ (fun i _ => node_monic (t i) (k i))

lemma total_natDegree (t : I → K) (k : I → ℕ) :
    (∏ i, nodePower (t i) (k i)).natDegree = ∑ i, k i := by
  rw [natDegree_prod_of_monic Finset.univ _ (fun i _ => node_monic (t i) (k i))]
  simp

lemma total_degree (t : I → K) (k : I → ℕ) :
    (∏ i, nodePower (t i) (k i)).degree = ↑(∑ i, k i) := by
  rw [degree_eq_natDegree (total_monic t k).ne_zero, total_natDegree]

lemma zero_of_all_jets (t : I → K) (ht : Function.Injective t) (k : I → ℕ)
    {p : K[X]} (hp : p.degree < ↑(∑ i, k i)) (hz : ∀ i, jet (t i) (k i) p = 0) : p = 0 := by
  have hd : (∏ i, nodePower (t i) (k i)) ∣ p := Fintype.prod_dvd_of_coprime
    (fun i j hij => (pairwise_coprime_X_sub_C ht hij).pow) (fun i => (jet_zero_iff ..).1 (hz i))
  by_contra h
  exact (not_lt_of_ge (natDegree_le_of_dvd hd h)) <| by
    rw [total_natDegree]
    exact (natDegree_lt_iff_degree_lt h).2 hp

/-- The actual componentwise quotient map on the degree window. -/
def simultaneousJet (t : I → K) (k : I → ℕ) :
    degreeLT K (∑ i, k i) →ₗ[K] ((i : I) → Jet (t i) (k i)) :=
  LinearMap.pi fun i => (Ideal.Quotient.mkₐ K (nodeIdeal (t i) (k i))).toLinearMap.comp
    (degreeLT K (∑ i, k i)).subtype

/-- Full, nonuniform Hermite CRT with its canonical bounded degree representative. -/
def hermiteEquiv (t : I → K) (ht : Function.Injective t) (k : I → ℕ) :
    degreeLT K (∑ i, k i) ≃ₗ[K] ((i : I) → Jet (t i) (k i)) := by
  apply LinearEquiv.ofBijective (simultaneousJet t k)
  constructor
  · intro x y h
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply zero_of_all_jets t ht k (mem_degreeLT.1 (x-y).property)
    intro i
    change jet (t i) (k i) ((x : K[X]) - y) = 0
    rw [map_sub, sub_eq_zero]
    exact congrFun h i
  · intro z
    have hi : Pairwise fun i j => IsCoprime (nodeIdeal (t i) (k i)) (nodeIdeal (t j) (k j)) := by
      intro i j hij
      apply (Ideal.isCoprime_span_singleton_iff _ _).2
      exact (pairwise_coprime_X_sub_C ht hij).pow
    obtain ⟨p, hp⟩ := Ideal.pi_quotient_surjective hi z
    let Q := ∏ i, nodePower (t i) (k i)
    have hm : Q.Monic := total_monic t k
    refine ⟨⟨p %ₘ Q, mem_degreeLT.2 ?_⟩, ?_⟩
    · rw [← total_degree t k]
      exact degree_modByMonic_lt p hm
    · funext i
      change jet (t i) (k i) (p %ₘ Q) = z i
      have hQ : jet (t i) (k i) Q = 0 := (jet_zero_iff ..).2
        (Finset.dvd_prod_of_mem (fun j => nodePower (t j) (k j)) (Finset.mem_univ i))
      rw [modByMonic_eq_sub_mul_div p hm, map_sub, map_mul, hQ, zero_mul, sub_zero]
      exact hp i

/-- A single jet has exactly its declared number of scalar coordinates. -/
def localCoeffEquiv (t : K) (k : ℕ) : (Fin k → K) ≃ₗ[K] Jet t k := by
  let L : degreeLT K k →ₗ[K] Jet t k := (Ideal.Quotient.mkₐ K (nodeIdeal t k)).toLinearMap.comp
    (degreeLT K k).subtype
  refine (degreeLTEquiv K k).symm.trans (LinearEquiv.ofBijective L ⟨?_, ?_⟩)
  · intro x y h
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hd : nodePower t k ∣ ((x - y : degreeLT K k) : K[X]) :=
      (jet_zero_iff ..).1 (show jet t k ((x : K[X]) - y) = 0 by rw [map_sub]; exact sub_eq_zero.2 h)
    by_contra hn
    have hh := natDegree_le_of_dvd hd hn
    rw [node_natDegree] at hh
    exact (not_lt_of_ge hh) ((natDegree_lt_iff_degree_lt hn).2 (mem_degreeLT.1 (x-y).property))
  · intro z
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective z
    have hm := node_monic t k
    refine ⟨⟨p %ₘ nodePower t k, mem_degreeLT.2 ?_⟩, ?_⟩
    · simpa [degree_eq_natDegree hm.ne_zero] using degree_modByMonic_lt p hm
    · change jet t k (p %ₘ nodePower t k) = z
      rw [modByMonic_eq_sub_mul_div p hm, map_sub, map_mul, (jet_zero_iff ..).2 (dvd_refl _),
        zero_mul, sub_zero]
      exact hp

lemma local_finrank (t : K) (k : ℕ) : Module.finrank K (Jet t k) = k := by
  rw [← (localCoeffEquiv t k).finrank_eq, Module.finrank_pi, Fintype.card_fin]

/-- Evaluate a coefficient vector as a polynomial in the finite test window. -/
def testPolynomial (K : Type*) [Field K] (b : ℕ) : (Fin b → K) →ₗ[K] K[X] :=
  (degreeLT K b).subtype.comp (degreeLTEquiv K b).symm.toLinearMap

lemma test_mem (b : ℕ) (x : Fin b → K) : testPolynomial K b x ∈ degreeLT K b :=
  ((degreeLTEquiv K b).symm x).property

lemma product_degree {N d b : ℕ} (A : Matrix (Fin N) (Fin N) K[X])
    (hdeg : ∀ i j, (A i j).natDegree ≤ d) (hb : 0 < b) (x : Fin N → Fin b → K) (i : Fin N) :
    ((A *ᵥ fun j => testPolynomial K b (x j)) i).degree < ↑(d+b) := by
  let v := fun j => testPolynomial K b (x j)
  have htest (j : Fin N) : (v j).natDegree < b := by
    by_cases h : v j = 0
    · simpa [h] using hb
    · exact (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 (test_mem b (x j)))
  have hbound : ((A *ᵥ v) i).natDegree ≤ d+b-1 := by
    apply natDegree_sum_le_of_forall_le Finset.univ (fun j => A i j * v j)
    intro j _
    have := htest j
    have hh := hdeg i j
    exact (natDegree_mul_le).trans (by omega)
  change ((A *ᵥ v) i).degree < _
  by_cases h : (A *ᵥ v) i = 0
  · rw [h, degree_zero]
    exact WithBot.bot_lt_coe _
  · apply (natDegree_lt_iff_degree_lt h).1
    omega

/-- Reconstruct a matrix-vector polynomial product from its multiplied local jets. -/
theorem decode_jet_product {N d b : ℕ} (t : I → K) (ht : Function.Injective t) (k : I → ℕ)
    (A : Matrix (Fin N) (Fin N) K[X]) (hdeg : ∀ i j, (A i j).natDegree ≤ d)
    (hb : 0 < b) (hwindow : d+b ≤ ∑ i, k i) (x : Fin N → Fin b → K) (j : Fin N) :
    (((hermiteEquiv t ht k).symm (fun i =>
      (A.map (jet (t i) (k i)) *ᵥ fun c => jet (t i) (k i) (testPolynomial K b (x c))) j)) : K[X]) =
      (A *ᵥ fun c => testPolynomial K b (x c)) j := by
  let v := fun c => testPolynomial K b (x c)
  have hd : ((A *ᵥ v) j).degree < ↑(∑ i, k i) :=
    (product_degree A hdeg hb x j).trans_le (WithBot.coe_le_coe.2 hwindow)
  let y : degreeLT K (∑ i, k i) := ⟨(A *ᵥ v) j, mem_degreeLT.2 hd⟩
  have hy : (hermiteEquiv t ht k) y = fun i =>
      (A.map (jet (t i) (k i)) *ᵥ fun c => jet (t i) (k i) (v c)) j := by
    funext i
    exact (jet (t i) (k i)).map_mulVec A v j
  exact congrArg Subtype.val ((hermiteEquiv t ht k).symm_apply_eq.mpr hy.symm)

/-- A regular polynomial matrix separates all degree-window tests through its local jets. -/
theorem test_eq_zero_of_zero_local_images {N d b : ℕ} (t : I → K) (ht : Function.Injective t)
    (k : I → ℕ) (A : Matrix (Fin N) (Fin N) K[X]) (hregular : A.det ≠ 0)
    (hdeg : ∀ i j, (A i j).natDegree ≤ d) (hb : 0 < b) (hwindow : d+b ≤ ∑ i, k i)
    (x : Fin N → Fin b → K) (hz : ∀ i, A.map (jet (t i) (k i)) *ᵥ
      (fun c => jet (t i) (k i) (testPolynomial K b (x c))) = 0) : x = 0 := by
  classical
  let v := fun c => testPolynomial K b (x c)
  have hzero : A *ᵥ v = 0 := by
    funext j
    apply zero_of_all_jets t ht k ((product_degree A hdeg hb x j).trans_le
      (WithBot.coe_le_coe.2 hwindow))
    intro i
    rw [RingHom.map_mulVec]
    exact congrFun (hz i) j
  have hv : v = 0 := by
    by_contra hn
    exact hregular (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hn, hzero⟩)
  funext j
  apply (degreeLTEquiv K b).symm.injective
  apply Subtype.ext
  change (((degreeLTEquiv K b).symm (x j)) : K[X]) = (((degreeLTEquiv K b).symm 0) : K[X])
  rw [map_zero]
  exact congrFun hv j

/-- Send the independent polynomial test coefficients to their local input jet vector. -/
def testAtNode (N b : ℕ) (t : K) (k : ℕ) :
    (Fin N → Fin b → K) →ₗ[K] (Fin N → Jet t k) :=
  LinearMap.pi fun j => (Ideal.Quotient.mkₐ K (nodeIdeal t k)).toLinearMap.comp
    ((testPolynomial K b).comp (LinearMap.proj j))

/-- Write each jet-vector entry in ordinary polynomial remainder coordinates. -/
def outputCoordinates (N : ℕ) (t : K) (k : ℕ) :
    (Fin N → Jet t k) ≃ₗ[K] (Fin N → Fin k → K) :=
  LinearEquiv.piCongrRight fun _ => (localCoeffEquiv t k).symm

/-- Multiplication by the genuine local jet, with output in field coordinates.
Changing the basis of the jet algebra preserves its image dimension. -/
def localMultiplication {N : ℕ} (t : K) (k : ℕ) (A : Matrix (Fin N) (Fin N) K[X]) :
    (Fin N → Jet t k) →ₗ[K] (Fin N → Fin k → K) :=
  (outputCoordinates N t k).toLinearMap.comp ((A.map (jet t k)).mulVecLin.restrictScalars K)

/-- Actual local image dimensions, prior to bounding them by the supplied channel widths. -/
theorem jet_image_capacity {N d b : ℕ} (t : I → K) (ht : Function.Injective t) (k : I → ℕ)
    (A : Matrix (Fin N) (Fin N) K[X]) (hregular : A.det ≠ 0)
    (hdeg : ∀ i j, (A i j).natDegree ≤ d) (hwindow : d+b ≤ ∑ i, k i) :
    N*b ≤ ∑ i, Module.finrank K (LinearMap.range (localMultiplication (t i) (k i) A)) := by
  classical
  by_cases hb : b = 0
  · simp [hb]
  let channel : (Fin N → Fin b → K) →ₗ[K]
      ((i : I) → LinearMap.range (localMultiplication (t i) (k i) A)) :=
    LinearMap.pi fun i => (localMultiplication (t i) (k i) A).rangeRestrict.comp
      (testAtNode N b (t i) (k i))
  have hinj : Function.Injective channel := by
    apply (LinearMap.ker_eq_bot (f := channel)).mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    apply test_eq_zero_of_zero_local_images t ht k A hregular hdeg (Nat.pos_of_ne_zero hb) hwindow
    intro i
    apply (outputCoordinates N (t i) (k i)).injective
    rw [map_zero]
    exact congrArg Subtype.val (congrFun hx i)
  letI (i : I) : Module.Finite K (Jet (t i) (k i)) :=
    Module.Finite.of_surjective (localCoeffEquiv (t i) (k i)).toLinearMap
      (localCoeffEquiv (t i) (k i)).surjective
  letI (i : I) : Module.Finite K (LinearMap.range (localMultiplication (t i) (k i) A)) :=
    Module.Finite.range (localMultiplication (t i) (k i) A)
  letI (i : I) : Module.Free K (LinearMap.range (localMultiplication (t i) (k i) A)) :=
    Module.Free.of_divisionRing K _
  have hh := LinearMap.finrank_le_finrank_of_injective (f := channel) hinj
  rw [Module.finrank_pi_fintype K (M := fun i : I =>
    ↥(LinearMap.range (localMultiplication (t i) (k i) A)))] at hh
  simpa [Module.finrank_pi_fintype, Module.finrank_pi] using hh

/-- Total deficiency in the actual field-linear images of multiplication on all jets. -/
theorem actual_image_defect {N d : ℕ} (t : I → K) (ht : Function.Injective t) (k : I → ℕ)
    (A : Matrix (Fin N) (Fin N) K[X]) (hregular : A.det ≠ 0)
    (hdeg : ∀ i j, (A i j).natDegree ≤ d) :
    (∑ i, (N * k i - Module.finrank K (LinearMap.range (localMultiplication (t i) (k i) A)))) ≤ N*d := by
  let cap := fun i => Module.finrank K (LinearMap.range (localMultiplication (t i) (k i) A))
  have hcap (i : I) : cap i ≤ N * k i := by
    have hh := (LinearMap.range (localMultiplication (t i) (k i) A)).finrank_le
    simpa [cap, Module.finrank_pi_fintype, Module.finrank_pi] using hh
  have he : (∑ i, (N*k i-cap i)) + ∑ i, cap i = N*(∑ i, k i) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hcap i)
  change (∑ i, (N*k i-cap i)) ≤ N*d
  by_cases h : d ≤ ∑ i, k i
  · have hw : d+((∑ i, k i)-d) = ∑ i, k i := by omega
    have hb : N*((∑ i, k i)-d) ≤ ∑ i, cap i := jet_image_capacity t ht k A hregular hdeg hw.le
    have htotal : N*(∑ i, k i) = N*d + N*((∑ i, k i)-d) := by rw [← Nat.mul_add, hw]
    omega
  · have hs : N*(∑ i, k i) ≤ N*d := Nat.mul_le_mul_left N (by omega)
    omega

/-- The degree window injects into the declared local factor channels. The factors
are genuine matrices over the nonreduced local quotient, with independent widths. -/
theorem jet_factor_capacity {N d b : ℕ} (t : I → K) (ht : Function.Injective t) (k r : I → ℕ)
    (A : Matrix (Fin N) (Fin N) K[X]) (hregular : A.det ≠ 0)
    (hdeg : ∀ i j, (A i j).natDegree ≤ d) (hwindow : d+b ≤ ∑ i, k i)
    (U : (i : I) → Matrix (Fin N) (Fin (r i)) (Jet (t i) (k i)))
    (V : (i : I) → Matrix (Fin (r i)) (Fin N) (Jet (t i) (k i)))
    (hfac : ∀ i, A.map (jet (t i) (k i)) = U i * V i) : N*b ≤ ∑ i, r i * k i := by
  classical
  by_cases hb : b = 0
  · simp [hb]
  have hb' : 0 < b := Nat.pos_of_ne_zero hb
  let channel : (Fin N → Fin b → K) →ₗ[K] ((i : I) → Fin (r i) → Jet (t i) (k i)) :=
    LinearMap.pi fun i => ((V i).mulVecLin.restrictScalars K).comp (testAtNode N b (t i) (k i))
  have hinj : Function.Injective channel := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    apply test_eq_zero_of_zero_local_images t ht k A hregular hdeg hb' hwindow
    intro i
    have hlocal : V i *ᵥ (fun c => jet (t i) (k i) (testPolynomial K b (x c))) = 0 := congrFun hx i
    rw [hfac i, ← Matrix.mulVec_mulVec, hlocal, Matrix.mulVec_zero]
  letI (i : I) : Module.Finite K (Jet (t i) (k i)) :=
    Module.Finite.of_surjective (localCoeffEquiv (t i) (k i)).toLinearMap
      (localCoeffEquiv (t i) (k i)).surjective
  have hd := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_pi_fintype, Module.finrank_pi, local_finrank] using hd

/-- Field degree budget without a reconstruction-surplus hypothesis. -/
theorem nonuniform_degree_budget {N d : ℕ} (t : I → K) (ht : Function.Injective t) (k r : I → ℕ)
    (A : Matrix (Fin N) (Fin N) K[X]) (hregular : A.det ≠ 0)
    (hdeg : ∀ i j, (A i j).natDegree ≤ d)
    (U : (i : I) → Matrix (Fin N) (Fin (r i)) (Jet (t i) (k i)))
    (V : (i : I) → Matrix (Fin (r i)) (Fin N) (Jet (t i) (k i)))
    (hfac : ∀ i, A.map (jet (t i) (k i)) = U i * V i) :
    N * (∑ i, k i) ≤ N*d + ∑ i, r i * k i := by
  by_cases h : d ≤ ∑ i, k i
  · have he : d + ((∑ i, k i) - d) = ∑ i, k i := by omega
    have hs := jet_factor_capacity t ht k r A hregular hdeg he.le U V hfac
    calc N * (∑ i, k i) = N*d + N*((∑ i, k i) - d) := by rw [← Nat.mul_add, he]
         _ ≤ _ := Nat.add_le_add_left hs _
  · exact (Nat.mul_le_mul_left N (by omega : (∑ i, k i) ≤ d)).trans (Nat.le_add_right _ _)

/-- A nonsingular specialization is an easy certificate that the polynomial determinant is nonzero. -/
theorem regular_of_anchor {N : ℕ} (A : Matrix (Fin N) (Fin N) K[X]) (a : K)
    (h : ((evalRingHom a).mapMatrix A).det ≠ 0) : A.det ≠ 0 := by
  intro hz
  apply h
  rw [← RingHom.map_det, hz, map_zero]

/-- The literal weighted-corank inequality for whole-jet factor widths in the dimension range. -/
theorem weighted_jet_defect {N d : ℕ} (t : I → K) (ht : Function.Injective t) (k r : I → ℕ)
    (A : Matrix (Fin N) (Fin N) K[X]) (hregular : A.det ≠ 0)
    (hdeg : ∀ i j, (A i j).natDegree ≤ d) (hr : ∀ i, r i ≤ N)
    (U : (i : I) → Matrix (Fin N) (Fin (r i)) (Jet (t i) (k i)))
    (V : (i : I) → Matrix (Fin (r i)) (Fin N) (Jet (t i) (k i)))
    (hfac : ∀ i, A.map (jet (t i) (k i)) = U i * V i) :
    (∑ i, (N-r i)*k i) ≤ N*d := by
  have he : (∑ i, (N-r i)*k i) + ∑ i, r i*k i = N*(∑ i, k i) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← Nat.add_mul, Nat.sub_add_cancel (hr i)]
  have hh := nonuniform_degree_budget t ht k r A hregular hdeg U V hfac
  omega

#print axioms zero_of_all_jets
#print axioms hermiteEquiv
#print axioms localCoeffEquiv
#print axioms decode_jet_product
#print axioms jet_image_capacity
#print axioms actual_image_defect
#print axioms jet_factor_capacity
#print axioms nonuniform_degree_budget
#print axioms regular_of_anchor
#print axioms weighted_jet_defect

end HermiteJetTransport
