import P5HermiteTransportGenericH1
import P5HermiteTransportGenericValuation
import P5HermiteTransportGenericRegular
import P5HermiteTransportGenericRank

/-! The original fixed Hermite transport with H.2 and H.3 composed.
All inequalities quantify over the very same permissible independent
coefficient replacements. The perturbed output itself is full rank. -/
namespace Paper5.HermiteGeneric
open Polynomial Matrix
open scoped BigOperators Polynomial Kronecker Classical

variable {R K T U V : Type*} [CommRing R] [Field K] [Algebra R K]
  [Fintype T] [DecidableEq T] [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
  [Nonempty U] [Nonempty V]

theorem original_compression_H2 (L : Layout K T) (b d : ℕ)
    (A : Matrix U V K[X]) (hDegree : ∀ u v,(A u v).natDegree≤d)
    (hWindow : d+b≤∑t,L.order t)
    (v : AddValuation K (WithTop ℤ)) (hv : v.toValuation.Integers R)
    (π : R) (hπ : v (algebraMap R K π)=1) (P : Slot L→ℕ) (p : ℕ) :
    (∀ B,Permissible L π P (nativeCoefficients L A) B →
      EntryPrecision π p (anchorMatrix L b A) (compressed L b B)) ↔
      ∀ s : Slot L, ((p:ℤ):WithTop ℤ)≤((P s:ℤ):WithTop ℤ)+minimumTransfer L b v s := by
  rw [(reconstruction_H1 L b d A hDegree hWindow).2]
  simp_rw [compressed_eq_expanded]
  exact all_independent_lifts_H2 L b v hv π hπ P p (nativeCoefficients L A)

variable [IsLocalRing R]

omit [Fintype T] [DecidableEq T] [Fintype U] [Fintype V]
  [DecidableEq U] [DecidableEq V] [Nonempty U] [Nonempty V] in
theorem normalized_uniformizer_in_maximal
    (v : AddValuation K (WithTop ℤ)) (hv : v.toValuation.Integers R)
    (π : R) (hπ : v (algebraMap R K π)=1) : π∈IsLocalRing.maximalIdeal R := by
  apply (IsLocalRing.mem_maximalIdeal π).mpr
  intro hu
  have h := hv.one_of_isUnit hu
  change v (algebraMap R K π)=0 at h
  rw [hπ] at h
  exact one_ne_zero h

set_option maxHeartbeats 14000000 in
theorem original_compression_H3 (L : Layout K T) {b : ℕ} (hb : 0<b) (d : ℕ)
    (A : Matrix U U K[X]) (hDegree : ∀ u w,(A u w).natDegree≤d)
    (hWindow : d+b≤∑t,L.order t)
    (v : AddValuation K (WithTop ℤ)) (hv : v.toValuation.Integers R)
    (π : R) (hπ : v (algebraMap R K π)=1) (P : Slot L→ℕ) (p : ℕ) (hp : 0<p)
    (hA : ∀ j u w,∃ r : R, observedCoefficients A L.anchor L.anchorScale b j u w=algebraMap R K r)
    (hu : ∃ a : Rˣ,(A.map (Polynomial.evalRingHom L.anchor)).det=algebraMap R K (a:R))
    (hMargin : ∀ s : Slot L, ((p:ℤ):WithTop ℤ)≤((P s:ℤ):WithTop ℤ)+minimumTransfer L b v s)
    (B : (t : T)→Fin (L.order t)→Matrix U U K)
    (hB : Permissible L π P (nativeCoefficients L A) B) :
    (compressed L b B).rank=b*Fintype.card U ∧
      b*Fintype.card U≤∑ t,(convolution (B t)).rank ∧
      b*Fintype.card U≤∑t,∑j,(transfer L b t j).rank*(B t j).rank := by
  have hprec := (original_compression_H2 L b d A hDegree hWindow v hv π hπ P p).2 hMargin B hB
  have hr := anchor_integral_correction_H3 L hb hv.hom_inj π
    (normalized_uniformizer_in_maximal v hv π hπ) p hp A hA hu (compressed L b B) hprec
  refine ⟨hr,hr.symm.trans_le (compressed_rank_bound L b B),?_⟩
  rw [compressed_eq_expanded] at hr
  exact hr.symm.trans_le (expanded_rank_bound L b B)

#print axioms original_compression_H2
#print axioms normalized_uniformizer_in_maximal
#print axioms original_compression_H3
end Paper5.HermiteGeneric
