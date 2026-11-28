import V8CapacitySpecialImageSpan
import V8CapacitySpecialRankCompare

/-! Exact projected raw image and its saturation on a prescribed finite
set of arbitrary native jets. One actual polynomial realizes each
column even if row coincidences make the fraction-field rank deficient. -/
namespace V8CapacitySpecialImageSpan
open scoped Polynomial Classical BigOperators
open Polynomial V8CapacityCRTJet V8CapacityFeatures V8CapacitySmith

noncomputable section
set_option linter.unusedSectionVars false

variable {O H Z : Type*} [CommRing O] [Fintype H] [Fintype Z] [Nonempty Z] {k : ℕ}
variable [Nontrivial (Jet O k)]

def sourceColumnDecoder (U : Z → H → Jet O k) (j : sourceColumns U) (a : O) :
    MvPolynomial H (Jet O k) :=
  let d : H →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => (j.1 i).val)
  MvPolynomial.monomial d (AdjoinRoot.mk ((X:O[X])^k) (C a*X^(k-1-j.2.val)))

theorem column_read_is_exact (U : Z → H → Jet O k) (hk : 0<k)
    (j : sourceColumns U) (a : O) (z : Z) :
    coefficient O k (k-1) (readJet U (sourceColumnDecoder U j a) z)=
      a*coefficient O k j.2 (jetCol U j.1 z) := by
  unfold sourceColumnDecoder readJet
  rw [MvPolynomial.eval₂Hom_monomial,RingHom.id_apply,Finsupp.prod_pow]
  simp only [Finsupp.equivFunOnFinite_symm_apply_toFun]
  change coefficient O k (k-1)
      (AdjoinRoot.mk ((X:O[X])^k) (C a*X^(k-1-j.2.val))*jetCol U j.1 z)=_
  obtain ⟨g,hg⟩ := AdjoinRoot.mk_surjective (jetCol U j.1 z)
  have hj := j.2.isLt
  rw [← hg,← map_mul,coefficient_mk k (k-1) (by omega),coefficient_mk k j.2 hj]
  rw [mul_assoc,coeff_C_mul,coeff_X_pow_mul',if_pos (by omega),show k-1-(k-1-j.2.val)=j.2.val by omega]

variable [IsDomain O]

theorem exact_projected_image (U : Z → H → Jet O k) (hk : 0<k) (v : Z → O) :
    v∈matrixImage (finiteRaw U) ↔
      ∃ F : MvPolynomial H (Jet O k),
        ∀ z, coefficient O k (k-1) (readJet U F z)=v z := by
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨∑ j : sourceColumns U, sourceColumnDecoder U j (a j),fun z => ?_⟩
    change coefficient O k (k-1)
      (MvPolynomial.eval₂Hom (RingHom.id _) (U z) (∑ j : sourceColumns U,
        sourceColumnDecoder U j (a j)))=_
    rw [map_sum,coeff_finset_sum]
    have hh := congrFun ha z
    change (∑ j : sourceColumns U, coefficient O k j.2 (jetCol U j.1 z)*a j)=v z at hh
    rw [← hh]
    apply Finset.sum_congr rfl
    intro j _
    exact (column_read_is_exact U hk j (a j) z).trans (mul_comm _ _)
  · rintro ⟨F,hF⟩
    rw [← funext hF]
    exact in_finite_raw_span U hk F

variable [IsLocalRing O] [IsPrincipalIdealRing O]

/-- Inherits the A4 module formula with the actual projected proper-image
matrix rather than the universal full-domain Newton matrix. -/
def proper_image_modules (U : Z → H → Jet O k) (π : O)
    (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
    (hπ : π≠0) (L p : ℕ) :=
  matrixA4 π hMax hπ (finiteRaw U) L p

#print axioms column_read_is_exact
#print axioms exact_projected_image
#print axioms proper_image_modules
end
end V8CapacitySpecialImageSpan

