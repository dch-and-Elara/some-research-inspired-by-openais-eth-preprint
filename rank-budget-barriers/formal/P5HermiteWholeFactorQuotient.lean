import P5LiteralJets
import P5HermiteTransportGenericShift

/-! The actual double truncation used for local Hermite factors. The
coefficient congruence is read from equality in that same quotient,
not a choice of independent entry errors. -/
namespace Paper5.HermiteWholeFactor
open Polynomial Matrix
open scoped BigOperators Polynomial Classical

variable {R : Type*} [CommRing R]

noncomputable def quotientJet (π : R) (P k : ℕ) : R[X] →+* LocalJet π P k :=
  (AdjoinRoot.mk (X^k : (Cyclic π P)[X])).comp
    (Polynomial.mapRingHom (Ideal.Quotient.mk (PowIdeal π P)))

theorem quotientJet_surjective (π : R) (P k : ℕ) :
    Function.Surjective (quotientJet π P k) := by
  unfold quotientJet
  exact (AdjoinRoot.mk_surjective).comp
    (Polynomial.map_surjective (Ideal.Quotient.mk (PowIdeal π P)) (Ideal.Quotient.mk_surjective (I:=PowIdeal π P)))

theorem quotientJet_coeff_error (π : R) (P k : ℕ) {f g : R[X]}
    (h : quotientJet π P k f = quotientJet π P k g) (j : Fin k) :
    ∃ e : R, f.coeff j.val - g.coeff j.val = π^P * e := by
  change AdjoinRoot.mk (X^k : (Cyclic π P)[X]) (f.map (Ideal.Quotient.mk (PowIdeal π P))) =
    AdjoinRoot.mk (X^k : (Cyclic π P)[X]) (g.map (Ideal.Quotient.mk (PowIdeal π P))) at h
  have hej := (Polynomial.X_pow_dvd_iff.mp (AdjoinRoot.mk_eq_mk.mp h)) j.val j.isLt
  have hm : Ideal.Quotient.mk (PowIdeal π P) (f.coeff j.val-g.coeff j.val)=0 := by
    simpa only [Polynomial.coeff_sub,Polynomial.coeff_map,map_sub] using hej
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hm)

noncomputable def jetPolynomial {k : ℕ} (c : Fin k→R) : R[X] :=
  ∑ i : Fin k,Polynomial.monomial i.val (c i)

theorem jetPolynomial_coeff {k : ℕ} (c : Fin k→R) (j : Fin k) :
    (jetPolynomial c).coeff j.val=c j := by
  classical
  rw [jetPolynomial,Polynomial.finset_sum_coeff,Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    rw [Polynomial.coeff_monomial,if_neg (fun h=>hi (Fin.ext h))]
  · simp

variable {U V : Type*}

noncomputable def jetPolynomialMatrix {k : ℕ} (C : Fin k→Matrix U V R) :
    Matrix U V R[X] :=
  Matrix.of fun u v=>jetPolynomial (fun j=>C j u v)

theorem jetPolynomialMatrix_coeff {k : ℕ} (C : Fin k→Matrix U V R) (j : Fin k) (u : U) (v : V) :
    (jetPolynomialMatrix C u v).coeff j.val=C j u v := jetPolynomial_coeff _ _

/-- Actual coefficient change and truncation at the node, on the given
literal jet coefficients. -/
noncomputable def finiteJetMatrix (π : R) (P : ℕ) {k : ℕ} (C : Fin k→Matrix U V R) :
    Matrix U V (LocalJet π P k) :=
  (jetPolynomialMatrix C).map (quotientJet π P k)

noncomputable def factorLift (π : R) (P k : ℕ)
    (L : Matrix U V (LocalJet π P k)) : Matrix U V R[X] :=
  Matrix.of fun u v=>Classical.choose (quotientJet_surjective π P k (L u v))

theorem factorLift_recovers (π : R) (P k : ℕ)
    (L : Matrix U V (LocalJet π P k)) :
    (factorLift π P k L).map (quotientJet π P k) = L := by
  apply Matrix.ext
  intro u v
  exact Classical.choose_spec (quotientJet_surjective π P k (L u v))

#print axioms quotientJet_surjective
#print axioms quotientJet_coeff_error
#print axioms jetPolynomial_coeff
#print axioms jetPolynomialMatrix_coeff
#print axioms factorLift_recovers
end Paper5.HermiteWholeFactor
