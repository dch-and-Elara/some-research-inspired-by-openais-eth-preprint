import J6R22ActiveNormalizer

/-! A normalizer compiler for the actual retained centres. The raw
roster has signed grid addresses and their integral taper orders,
not numeric slope coefficients. The bound exposes the sum over the
actual stored multiplicities; no input graph or roster/registry
bootstrap is inferred from it. -/
namespace J6R22Active
open scoped BigOperators Polynomial Classical
open Polynomial A1R10 AOracleMachineTime DenominatorBudget P1DyadicGrid
open J6ActiveSchedule J6ActiveLocalFactor

variable {p ell : ℕ} {fw : List (Word p)}

def normalizerM (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) {k : ℕ} (hk : 0<k)
    (a : ℕ) (t : ℤ) (roster : List (ℤ×ℕ)) : Meter (JetTape fw ell k) :=
  let x := paidJetProd hp he hv hk (normalFactorM hp he hv hk a t) roster
  ⟨x.result,x.steps+roster.length*(8*(a+3)^2+4)+6⟩

def normalizerFee (e ell p a k : ℕ) (hp : 0<p) (roster : List (ℤ×ℕ)) : ℕ :=
  (roster.map (fun q=>normalFactorFee e ell p a k q.2 hp)).sum+
    tapeFee e ell p k+roster.length*(jetMulFee e ell p k hp+2)+
    roster.length*(8*(a+3)^2+4)+6

theorem normalizerM_exact (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) {k : ℕ} (hk : 0<k)
    (a M u : ℕ) {t : ℤ} (ht : t∈active a M u)
    (roster : List (ℤ×ℕ))
    (nodup : (roster.map Prod.fst).Nodup)
    (listExact : (roster.map Prod.fst).toFinset=(active a M u).erase t)
    (orderExact : ∀ q∈roster,q.2=order M u q.1) :
    let N := normalizerM hp he hv hk a t roster
    jetRead hp he N.result=AdjoinRoot.mk (X^k)
      ((integralNormalizer a (active a M u) (order M u) t).map (localReduce hp fw ell)) ∧
    N.steps≤normalizerFee fw.length ell p a k hp roster := by
  let T := normalFactorM hp he hv hk a t
  let P := paidJetProd hp he hv hk T roster
  have htp : t∈grid a := (J6R9Recursive.active_grid a M u ht).1
  have hq (q : ℤ×ℕ) (h : q∈roster) : q.1∈(active a M u).erase t := by
    rw [←listExact,List.mem_toFinset]
    exact List.mem_map_of_mem h
  have F (q : ℤ×ℕ) (h : q∈roster) :=
    normalFactorM_exact hp he hv hk q htp (J6R9Recursive.active_grid a M u (Finset.mem_erase.mp (hq q h)).2).1
      (Finset.ne_of_mem_erase (hq q h)).symm
  obtain ⟨rv,rs⟩ := paidJetProd_exact hp he hv hk T roster
  refine ⟨?_,?_⟩
  · let R := Coeff hp fw ell
    let D := localReduce hp fw ell
    let read (q : ℤ) : AdjoinRoot ((X : R[X])^k) :=
      AdjoinRoot.mk (X^k) ((1+C (D (slope a t q))*X)^order M u q)
    change jetRead hp he P.result=_
    rw [rv]
    have h : roster.map (fun q=>jetRead hp he (T q).result)=(roster.map Prod.fst).map read := by
      rw [List.map_map]
      apply List.map_congr_left
      intro q hq
      exact (F q hq).1.trans (by change _=read q.1; rw [orderExact q hq])
    rw [h,←List.prod_toFinset read nodup,listExact,integralNormalizer,Polynomial.map_prod,map_prod]
    apply Finset.prod_congr rfl
    intro q _
    simp only [read, D,Polynomial.map_pow,Polynomial.map_add,Polynomial.map_one,Polynomial.map_C,
      Polynomial.map_mul,Polynomial.map_X]
    rfl
  · let K (q : ℤ×ℕ) : Meter Unit := ⟨(),normalFactorFee fw.length ell p a k q.2 hp⟩
    have hb : bill T roster≤bill K roster := bill_rel T K roster (fun q hq=>(F q hq).2)
    change P.steps+roster.length*(8*(a+3)^2+4)+6≤_
    exact Nat.add_le_add_right (Nat.add_le_add_right
      (rs.trans (Nat.add_le_add_right (Nat.add_le_add_right hb _) _)) _) _

#print axioms normalizerM_exact
end J6R22Active


