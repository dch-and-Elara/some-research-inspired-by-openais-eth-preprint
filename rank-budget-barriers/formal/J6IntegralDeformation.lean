import J6DeformationLocal

namespace J6IntegralDeformation
open scoped Classical BigOperators Polynomial
open Polynomial J6DeformationPoly J6DeformationLocal DenominatorBudget P1DyadicGrid
variable {P K : Type*} [Fintype P] [DecidableEq K]

noncomputable def localEntry (page : P → K) (slot : P → ℤ) (a : ℕ) (t : ℤ) (i j : P) :
    TwoLocal[X] :=
  if page i = page j then J6R9PacketLocal.W a t (slot j-slot i) else 0

noncomputable def localNetwork (page : P → K) (slot : P → ℤ) (a : ℕ) (t : ℤ)
    (A B : (P → Bool) → TwoLocal) : TwoLocal[X] :=
  ∑ Y : P → Bool, ∑ Xb : P → Bool, C (A Y * B Xb) *
    ∏ i, let z := ∑ j, if Xb j then localEntry page slot a t i j else 0
         if Y i then z else 1-z

theorem network_local_integrality (page : P → K) (slot : P → ℤ) (a : ℕ)
    (t : ℤ) (ht : t ∈ grid a) (A B : (P → Bool) → TwoLocal)
    (hslot : ∀ i j, page i = page j → slot j-slot i ∈ grid a) :
    (network page slot a (twoLocalRat ∘ A) (twoLocalRat ∘ B)).comp (coordinate a t) =
      (localNetwork page slot a t A B).map twoLocalRat := by
  classical
  change (compRingHom (coordinate a t)) _ = (mapRingHom twoLocalRat) _
  simp only [network,localNetwork,map_sum,map_mul,map_prod,coe_compRingHom_apply,
    C_comp, coe_mapRingHom, map_C, Function.comp_apply]
  refine Finset.sum_congr rfl (fun Y _ => Finset.sum_congr rfl (fun Xb _ => ?_))
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hrows :
      ((∑ j, if Xb j then matrix page slot a i j else 0) : ℚ[X]).comp (coordinate a t) =
        (∑ j, if Xb j then localEntry page slot a t i j else 0).map twoLocalRat := by
    change (compRingHom (coordinate a t)) _ = (mapRingHom twoLocalRat) _
    simp only [map_sum,coe_compRingHom_apply,coe_mapRingHom]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hx : Xb j = true
    · by_cases h : page i = page j
      · simpa only [hx, if_true, matrix, localEntry, if_pos h] using entry_local_map ht (hslot i j h)
      · simp [hx,matrix,localEntry,h]
    · simp [hx]
  cases hy : Y i
  · simp only [Bool.false_eq_true, if_false]
    exact sub_comp.trans (by rw [one_comp, Polynomial.map_sub, Polynomial.map_one, hrows])
  · simpa only [hy, if_true] using hrows

#print axioms network_local_integrality
end J6IntegralDeformation
