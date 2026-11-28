import J6R23ScheduleWeightRoster
import J6R16ModeCostSite

/-! Polynomial-sized valuation counters. They do not encode the
whole integer numerator or denominator, and all allowed source
taper orders are bounded on the literal grid. This is not a whole
recursion bit-complexity result. -/
namespace J6R23ScheduleWeight
open scoped BigOperators
open P1DyadicGrid HermiteLoss J6ActiveSchedule

variable {a M u : ℕ} {t : ℤ}

theorem Roster.length_le_grid (L : Roster a M u t) :
    L.rows.length≤2^(a+1) := by
  have h : (L.rows.map Prod.fst).toFinset.card=L.rows.length := by
    rw [List.toFinset_card_of_nodup L.distinct,List.length_map]
  rw [←h,L.complete,←J6R16ModeCost.signed_grid_count]
  apply Finset.card_le_card
  intro q hq
  exact (J6R9Recursive.active_grid a M u (Finset.mem_erase.mp hq).2).1

theorem factor_count_cap {k : ℕ} {q : ℤ}
    (b : Side) (ht : t∈grid a) (hq : q∈grid a) (neq : q≠t) (nonzero : q≠0) :
    factorCount t b (q,k)≤k*a := by
  unfold factorCount
  apply Nat.mul_le_mul_left
  cases b
  · change level (-q)≤a
    rw [level_neg]
    exact level_grid_le hq nonzero
  · exact grid_difference_valuation_le ht hq neq.symm

theorem Roster.countParts_bound (L : Roster a M u t) (ht : t∈active a M u)
    (hu : 0<u) (huM : u≤M) (b : Side) :
    countParts t b L.rows≤L.rows.length*(4*M*a) := by
  have hg := (J6R9Recursive.active_grid a M u ht).1
  have v (q : ℤ×ℕ) (hq : q∈L.rows) : factorCount t b q≤4*M*a := by
    have h := (factor_count_cap (k:=q.2) b hg (L.is_grid q hq) (L.in_active q hq).2
      (J6R9Recursive.active_grid _ _ _ (L.in_active q hq).1).2)
    exact h.trans (Nat.mul_le_mul_right _ ((L.exponents q hq).le.trans (order_bound M u q.1 hu huM)))
  unfold countParts
  let f := factorCount t b
  have all (z : List (ℤ×ℕ)) (hz : ∀ q∈z,f q≤4*M*a) : (z.map f).sum≤z.length*(4*M*a) := by
    induction z with
    | nil => simp
    | cons q qs ih =>
      have c := hz q List.mem_cons_self
      have hd := ih (fun r hr=>hz r (List.mem_cons_of_mem _ hr))
      change f q+(qs.map f).sum≤(qs.length+1)*(4*M*a)
      rw [Nat.succ_mul qs.length]
      omega
  exact all L.rows v

#print axioms Roster.length_le_grid
#print axioms factor_count_cap
#print axioms Roster.countParts_bound
end J6R23ScheduleWeight


