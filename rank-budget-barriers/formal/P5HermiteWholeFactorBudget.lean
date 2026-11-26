import P5HermiteWholeFactorLift
import P5HermiteTransportGenericFinal

/-! The literal conclusion of original TeX 415--419, for the very same
certified Hermite compression. The input is a factorization in the
native double quotient ring; the lifted local entries are constructed
as a truncated product, not assumed permissible or assumed low-rank. -/
namespace Paper5.HermiteWholeFactor
open Matrix Polynomial
open Paper5.HermiteGeneric
open scoped BigOperators Polynomial Classical

variable {R K T U : Type*} [CommRing R] [Field K] [Algebra R K]
  [Fintype T] [DecidableEq T]

noncomputable def factorReplacements (L : Layout K T) (π : R) (P r : T→ℕ)
    (S : (t : T)→Matrix U (Fin (r t)) (LocalJet π (P t) (L.order t)))
    (H : (t : T)→Matrix (Fin (r t)) U (LocalJet π (P t) (L.order t))) :
    (t : T)→Fin (L.order t)→Matrix U U K :=
  fun t j=>(truncatedCoefficients (liftedProduct π (P t) (L.order t) (S t) (H t)) j).map
    (algebraMap R K)

omit [Fintype T] [DecidableEq T] in
theorem factorReplacements_permissible (L : Layout K T) (π : R) (P r : T→ℕ)
    (C : (t : T)→Fin (L.order t)→Matrix U U R)
    (A : (t : T)→Fin (L.order t)→Matrix U U K)
    (hC : ∀t j,(C t j).map (algebraMap R K)=A t j)
    (S : (t : T)→Matrix U (Fin (r t)) (LocalJet π (P t) (L.order t)))
    (H : (t : T)→Matrix (Fin (r t)) U (LocalJet π (P t) (L.order t)))
    (hFact : ∀t,finiteJetMatrix π (P t) (C t)=S t*H t) :
    Permissible L π (fun s=>P s.1) A (factorReplacements L π P r S H) := by
  intro t j u w
  obtain ⟨e,he⟩ := liftedProduct_permissible π (P t) (L.order t) (C t) (S t) (H t)
    (hFact t) j u w
  refine ⟨e,?_⟩
  rw [←hC t j]
  change (algebraMap R K) (truncatedCoefficients
    (liftedProduct π (P t) (L.order t) (S t) (H t)) j u w) -
    (algebraMap R K) (C t j u w) = (algebraMap R K) (π^(P t)*e)
  rw [←map_sub,he]

variable [IsLocalRing R] [Fintype U] [DecidableEq U] [Nonempty U]

set_option maxHeartbeats 17000000 in
theorem original_whole_factor_rank (L : Layout K T) {b : ℕ} (hb : 0<b) (d : ℕ)
    (A : Matrix U U K[X]) (hDegree : ∀ u w,(A u w).natDegree≤d)
    (hWindow : d+b≤∑t,L.order t)
    (v : AddValuation K (WithTop ℤ)) (hv : v.toValuation.Integers R)
    (π : R) (hπ : v (algebraMap R K π)=1) (P r : T→ℕ) (p : ℕ) (hp : 0<p)
    (hA : ∀j u w,∃a : R, observedCoefficients A L.anchor L.anchorScale b j u w=algebraMap R K a)
    (hu : ∃a : Rˣ,(A.map (Polynomial.evalRingHom L.anchor)).det=algebraMap R K (a:R))
    (hMargin : ∀ s : Slot L, ((p:ℤ):WithTop ℤ)≤((P s.1:ℤ):WithTop ℤ)+minimumTransfer L b v s)
    (C : (t : T)→Fin (L.order t)→Matrix U U R)
    (hC : ∀t j,(C t j).map (algebraMap R K)=nativeCoefficients L A t j)
    (S : (t : T)→Matrix U (Fin (r t)) (LocalJet π (P t) (L.order t)))
    (H : (t : T)→Matrix (Fin (r t)) U (LocalJet π (P t) (L.order t)))
    (hFact : ∀t,finiteJetMatrix π (P t) (C t)=S t*H t) :
    (compressed L b (factorReplacements L π P r S H)).rank=b*Fintype.card U ∧
      b*Fintype.card U≤∑ t,L.order t * r t := by
  have hB := factorReplacements_permissible L π P r C (nativeCoefficients L A) hC S H hFact
  have h3 := original_compression_H3 L hb d A hDegree hWindow v hv π hπ (fun s=>P s.1)
    p hp hA hu hMargin (factorReplacements L π P r S H) hB
  refine ⟨h3.1,h3.2.1.trans (Finset.sum_le_sum ?_)⟩
  intro t _
  simpa only [factorReplacements,Fintype.card_fin] using
    (liftedProduct_rank (K:=K) π (P t) (L.order t) (S t) (H t))

#print axioms factorReplacements_permissible
#print axioms original_whole_factor_rank
end Paper5.HermiteWholeFactor
