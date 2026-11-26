import P5HermiteWholeFactorBudget

/-! The printed sum-of-local-factors clause only: concatenate the given
factorizations, so the charged width is the sum of their actual widths. -/
namespace Paper5.HermiteWholeFactor
open Matrix Polynomial
open Paper5.HermiteGeneric
open scoped BigOperators Polynomial Classical

variable {J U V : Type*} [Fintype J]

noncomputable def channelIndex (r : J→ℕ) :
    (Σ j : J,Fin (r j)) ≃ Fin (∑j,r j) :=
  (Fintype.equivFin _).trans (finCongr (by simp [Fintype.card_sigma]))

variable {S : Type*} [CommRing S]

noncomputable def concatLeft (r : J→ℕ) (A : (j : J)→Matrix U (Fin (r j)) S) :
    Matrix U (Fin (∑j,r j)) S :=
  Matrix.of fun u x => A ((channelIndex r).symm x).1 u ((channelIndex r).symm x).2

noncomputable def concatRight (r : J→ℕ) (B : (j : J)→Matrix (Fin (r j)) V S) :
    Matrix (Fin (∑j,r j)) V S :=
  Matrix.of fun x v => B ((channelIndex r).symm x).1 ((channelIndex r).symm x).2 v

theorem concatenate_sum_products (r : J→ℕ) (A : (j : J)→Matrix U (Fin (r j)) S)
    (B : (j : J)→Matrix (Fin (r j)) V S) :
    concatLeft r A * concatRight r B = ∑j,A j*B j := by
  classical
  ext u v
  simp only [Matrix.mul_apply,Matrix.sum_apply,concatLeft,concatRight,Matrix.of_apply]
  let F (x : Σj : J,Fin (r j)) : S := A x.1 u x.2*B x.1 x.2 v
  exact (((channelIndex r).symm.sum_comp F).trans (Fintype.sum_sigma F))

variable {R K T : Type*} [CommRing R] [Field K] [Algebra R K]
  [Fintype T] [DecidableEq T] [IsLocalRing R] [Fintype U] [DecidableEq U] [Nonempty U]

set_option maxHeartbeats 18000000 in
theorem original_whole_factor_sum_rank (L : Layout K T) {b : ℕ} (hb : 0<b) (d : ℕ)
    (A : Matrix U U K[X]) (hDegree : ∀ u w,(A u w).natDegree≤d)
    (hWindow : d+b≤∑t,L.order t)
    (v : AddValuation K (WithTop ℤ)) (hv : v.toValuation.Integers R)
    (π : R) (hπ : v (algebraMap R K π)=1) (P : T→ℕ) (p : ℕ) (hp : 0<p)
    (hA : ∀j u w,∃a : R, observedCoefficients A L.anchor L.anchorScale b j u w=algebraMap R K a)
    (hu : ∃a : Rˣ,(A.map (Polynomial.evalRingHom L.anchor)).det=algebraMap R K (a:R))
    (hMargin : ∀ s : Slot L, ((p:ℤ):WithTop ℤ)≤((P s.1:ℤ):WithTop ℤ)+minimumTransfer L b v s)
    (C : (t : T)→Fin (L.order t)→Matrix U U R)
    (hC : ∀t j,(C t j).map (algebraMap R K)=nativeCoefficients L A t j)
    (Q : T→Type*) [∀t,Fintype (Q t)] (r : (t : T)→ Q t→ℕ)
    (S₀ : (t : T)→(j : Q t)→Matrix U (Fin (r t j)) (LocalJet π (P t) (L.order t)))
    (H : (t : T)→(j : Q t)→Matrix (Fin (r t j)) U (LocalJet π (P t) (L.order t)))
    (hFact : ∀t,finiteJetMatrix π (P t) (C t)=∑j,S₀ t j*H t j) :
    b*Fintype.card U≤∑ t,L.order t * (∑ j,r t j) := by
  exact (original_whole_factor_rank L hb d A hDegree hWindow v hv π hπ P
    (fun t=>∑ j,r t j) p hp hA hu hMargin C hC
    (fun t=>concatLeft (r t) (S₀ t)) (fun t=>concatRight (r t) (H t))
    (fun t=>(hFact t).trans (concatenate_sum_products _ _ _).symm)).2

#print axioms channelIndex
#print axioms concatenate_sum_products
#print axioms original_whole_factor_sum_rank
end Paper5.HermiteWholeFactor
