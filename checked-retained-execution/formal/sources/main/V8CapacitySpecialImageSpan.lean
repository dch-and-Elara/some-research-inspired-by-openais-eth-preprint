import V8CapacitySpecialImageNull
import V8CapacityMatrixImage

/-! Exact finite column span on any nonempty prescribed sender image.
This is a source equivalence, not just a bound on its number of formal
monomials. Local polynomial remainders use the exact constants. -/
namespace V8CapacitySpecialImageSpan
open scoped Polynomial Classical BigOperators
open Polynomial V8CapacityCRTJet V8CapacityFeatures V8CapacitySpecialImageNull
open V8CapacitySmith

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {O H Z : Type*} [CommRing O] [Fintype H] [Fintype Z] [Nonempty Z] {k : ℕ}
variable [Nontrivial (Jet O k)]

def degreeBox (U : Z → H → Jet O k) (i : H) : ℕ :=
  (exactConstants (fun z => U z i)).card*k

abbrev ExpBox (U : Z → H → Jet O k) := (i : H) → Fin (degreeBox U i)

def jetCol (U : Z → H → Jet O k) (α : ExpBox U) (z : Z) : Jet O k :=
  ∏ i : H, U z i ^ (α i).val

theorem monomial_on_image (U : Z → H → Jet O k) (hk : 0<k) (α : H → ℕ) :
    ∃ b : ExpBox U → Jet O k, ∀ z : Z,
      (∏ i : H, U z i^α i)=∑ r : ExpBox U, b r*jetCol U r z := by
  choose b hb using (fun i : H => bounded_power (fun z => U z i) hk (α i))
  refine ⟨fun a => ∏ i : H, b i (a i),?_⟩
  intro z
  simp_rw [hb]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  exact Finset.prod_mul_distrib

def readJet (U : Z → H → Jet O k) (F : MvPolynomial H (Jet O k)) (z : Z) : Jet O k :=
  MvPolynomial.eval₂Hom (RingHom.id _) (U z) F

theorem arbitrary_decoder_on_image (U : Z → H → Jet O k) (hk : 0<k)
    (F : MvPolynomial H (Jet O k)) :
    ∃ b : ExpBox U → Jet O k, ∀ z, readJet U F z=∑ r : ExpBox U, b r*jetCol U r z := by
  induction F using MvPolynomial.induction_on' with
  | monomial α c =>
    obtain ⟨b,hb⟩ := monomial_on_image U hk α
    refine ⟨fun a => c*b a,fun z => ?_⟩
    unfold readJet
    rw [MvPolynomial.eval₂Hom_monomial,RingHom.id_apply,Finsupp.prod_pow,hb z,Finset.mul_sum]
    simp only [mul_assoc]
  | add f g hf hg =>
    obtain ⟨a,ha⟩ := hf
    obtain ⟨b,hb⟩ := hg
    refine ⟨a+b,fun z => ?_⟩
    change (MvPolynomial.eval₂Hom (RingHom.id _) (U z)) (f+g)=_
    rw [map_add]
    change readJet U f z+readJet U g z=_
    rw [ha,hb]
    simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib]

theorem coeff_product_top (hk : 0<k) (u v : Jet O k) :
    coefficient O k (k-1) (u*v)=
      ∑ j : Fin k, coefficient O k (k-1-j.val) u * coefficient O k j v := by
  obtain ⟨g,rfl⟩ := AdjoinRoot.mk_surjective u
  obtain ⟨p,rfl⟩ := AdjoinRoot.mk_surjective v
  rw [← map_mul,coefficient_mk k (k-1) (by omega),mul_comm g p,coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => p.coeff a*g.coeff b)]
  rw [show (k-1).succ=k by omega]
  rw [← Fin.sum_univ_eq_sum_range (fun j => p.coeff j*g.coeff (k-1-j)) k]
  apply Finset.sum_congr rfl
  intro j _
  have hj := j.isLt
  rw [coefficient_mk k j hj,coefficient_mk k (k-1-j.val) (by omega),mul_comm]

theorem coeff_finset_sum {A : Type*} (s : Finset A) (f : A → Jet O k) (j : ℕ) :
    coefficient O k j (∑ a ∈ s, f a)=∑ a ∈ s, coefficient O k j (f a) := by
  simp only [coefficient,map_sum,finset_sum_coeff]

def sourceColumns (U : Z → H → Jet O k) := ExpBox U × Fin k
noncomputable instance (U : Z → H → Jet O k) : Fintype (sourceColumns U) := by
  unfold sourceColumns
  infer_instance

def finiteRaw (U : Z → H → Jet O k) : Matrix Z (sourceColumns U) O :=
  Matrix.of fun z j => coefficient O k j.2 (jetCol U j.1 z)

theorem in_finite_raw_span [IsDomain O] (U : Z → H → Jet O k) (hk : 0<k)
    (F : MvPolynomial H (Jet O k)) :
    (fun z => coefficient O k (k-1) (readJet U F z))∈matrixImage (finiteRaw U) := by
  obtain ⟨b,hb⟩ := arbitrary_decoder_on_image U hk F
  refine ⟨fun j => coefficient O k (k-1-j.2.val) (b j.1),?_⟩
  funext z
  change (∑ j : sourceColumns U,
    (coefficient O k (j.2.val) (jetCol U j.1 z))*coefficient O k (k-1-j.2.val) (b j.1))=_
  unfold sourceColumns
  rw [Fintype.sum_prod_type,hb z,coeff_finset_sum]
  simp_rw [coeff_product_top hk, mul_comm]

#print axioms monomial_on_image
#print axioms arbitrary_decoder_on_image
#print axioms coeff_product_top
#print axioms in_finite_raw_span
end
end V8CapacitySpecialImageSpan

