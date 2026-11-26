import P5A2Double

/-! The iterated quotient in A2 is canonically the simultaneous quotient
of the genuine bivariate polynomial ring by the two powers. -/
namespace P5A2
open Polynomial Ideal
open scoped Classical BigOperators

variable {K : Type*} [Field K]

abbrev innerIdeal (K : Type*) [Field K] (k : ℕ) : Ideal K[X] :=
  Ideal.span {(X : K[X])^k}

abbrev outerIdeal (K : Type*) [Field K] (l : ℕ) : Ideal K[X][X] :=
  Ideal.span {(X : K[X][X])^l}

abbrev liftedIdeal (K : Type*) [Field K] (k : ℕ) : Ideal K[X][X] :=
  (innerIdeal K k).map (C : K[X] →+* K[X][X])

abbrev Simultaneous (K : Type*) [Field K] (k l : ℕ) :=
  K[X][X] ⧸ (outerIdeal K l ⊔ liftedIdeal K k)

private theorem inner_image (k l : ℕ) :
    (liftedIdeal K k).map (Ideal.Quotient.mk (outerIdeal K l)) =
      (innerIdeal K k).map (AdjoinRoot.of ((X : K[X][X])^l)) := by
  rw [Ideal.map_map]
  rfl

private theorem outer_map (k l : ℕ) :
    ((X : K[X][X])^l).map (Ideal.Quotient.mk (innerIdeal K k)) =
      (X : (Trunc K k)[X])^l := by simp

noncomputable def twoEquiv (k l : ℕ) : Simultaneous K k l ≃+* Double K k l :=
  (DoubleQuot.quotQuotEquivQuotSup (outerIdeal K l) (liftedIdeal K k)).symm.trans
    ((Ideal.quotEquivOfEq (inner_image (K:=K) k l)).trans
      ((AdjoinRoot.quotEquivQuotMap ((X : K[X][X])^l) (innerIdeal K k)).toRingEquiv.trans
        (Ideal.quotEquivOfEq (congrArg (fun p : (Trunc K k)[X] => Ideal.span {p})
          (outer_map k l)))))

set_option maxHeartbeats 3900000 in
theorem twoEquiv_mk (k l : ℕ) (f : K[X][X]) :
    twoEquiv k l (Ideal.Quotient.mk (outerIdeal K l ⊔ liftedIdeal K k) f) =
      AdjoinRoot.mk ((X : (Trunc K k)[X])^l)
        (f.map (Ideal.Quotient.mk (innerIdeal K k))) := by
  unfold twoEquiv
  simp only [RingEquiv.trans_apply]
  rw [DoubleQuot.quotQuotEquivQuotSup_symm_quotQuotMk]
  unfold DoubleQuot.quotQuotMk
  simp only [RingHom.comp_apply]
  rw [Ideal.quotEquivOfEq_mk]
  change (Ideal.quotEquivOfEq (congrArg (fun p : (Trunc K k)[X] => Ideal.span {p})
      (outer_map k l))) ((AdjoinRoot.quotEquivQuotMap ((X : K[X][X])^l) (innerIdeal K k))
      (Ideal.Quotient.mk _ (AdjoinRoot.mk _ f))) = _
  rw [AdjoinRoot.quotEquivQuotMap_apply_mk]
  exact Ideal.quotEquivOfEq_mk
    (congrArg (fun p : (Trunc K k)[X] => Ideal.span {p}) (outer_map k l))
    (f.map (Ideal.Quotient.mk (innerIdeal K k)))

#print axioms twoEquiv
#print axioms twoEquiv_mk
end P5A2
