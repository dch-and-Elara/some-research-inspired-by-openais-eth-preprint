import V8CapacityDigitNodes
import V8CapacityOrders

/-! The actual monic Newton factor has all-value divisor π^t, and its
diagonal value attains it up to a unit. Here t is the manuscript's exact
sum of base-q floors, not a bound on the full Smith capacity. -/
namespace V8CapacityFactorial
open scoped BigOperators Classical
open V8CapacityDigits V8CapacityResidues V8CapacityOrders

noncomputable section
set_option linter.unusedSectionVars false

variable {O : Type*} [CommRing O] [IsDomain O] {π : O} {q : ℕ}

def debt (q n : ℕ) : ℕ := ∑ u ∈ Finset.range (n+1), n/q^(u+1)

theorem late_term_zero (q n u : ℕ) (hq : 2≤q) (hu : n+1≤u) :
    n/q^(u+1)=0 := by
  apply Nat.div_eq_of_lt
  have h := successor_le_pow q hq (u+1)
  omega

variable (D : Digits π q) (hq : 0<q)

def newton (n : ℕ) (x : O) : O := ∏ j : Fin n, (x-node D hq j.val)

variable (hq₂ : 2≤q) (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0)
include hq₂ h0 hπ

theorem layer_count_lower (n u : ℕ) (x : O) :
    n/q^u ≤ ∑ j : Fin n, if π^u∣x-node D hq j.val then 1 else 0 := by
  obtain ⟨r,hr⟩ := node_class D hq₂ hq h0 hπ u x
  have hEq : (Finset.univ.filter (fun j : Fin n => π^u∣x-node D hq j.val)) =
      Finset.univ.filter (fun j : Fin n => j.val%q^u=r.val) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hr]
  rw [← Finset.card_filter,hEq,← Fintype.card_subtype]
  exact residue_count_at_least n _ _ (pow_pos hq _) r.isLt

theorem layer_count_diag (n u : ℕ) :
    (∑ j : Fin n, if π^u∣node D hq n-node D hq j.val then 1 else 0) = n/q^u := by
  have hEq : (Finset.univ.filter (fun j : Fin n => π^u∣node D hq n-node D hq j.val)) =
      Finset.univ.filter (fun j : Fin n => j.val%q^u=n%q^u) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,node_diff_iff D hq₂ hq h0 hπ]
  rw [← Finset.card_filter,hEq,← Fintype.card_subtype]
  exact residue_count_diagonal n _ (pow_pos hq _)

theorem ord_sum_lower (n : ℕ) (x : O) :
    debt q n≤∑ j : Fin n, ord π (n+1) (x-node D hq j.val) := by
  unfold debt
  simp_rw [ord_as_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun u _ => layer_count_lower D hq hq₂ h0 hπ n (u+1) x)

theorem ord_sum_diag (n : ℕ) :
    (∑ j : Fin n, ord π (n+1) (node D hq n-node D hq j.val))=debt q n := by
  unfold debt
  simp_rw [ord_as_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  exact layer_count_diag D hq hq₂ h0 hπ n (u+1)

theorem newton_divisor (n : ℕ) (x : O) : π^debt q n∣newton D hq n x := by
  refine (pow_dvd_pow π (ord_sum_lower D hq hq₂ h0 hπ n x)).trans ?_
  unfold newton
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_dvd_prod_of_dvd _ _ (fun j _ => ord_dvd π (n+1) (x-node D hq j.val))

theorem no_failed_diagonal_power (n : ℕ) (j : Fin n) :
    ¬π^(n+1)∣node D hq n-node D hq j.val := by
  intro h
  have hN : n<q^(n+1) := (Nat.lt_succ_self n).trans_le
    ((Nat.le_succ (n+1)).trans (successor_le_pow q hq₂ (n+1)))
  have hJ := j.isLt.trans hN
  have hn := (node_diff_iff D hq₂ hq h0 hπ (n+1) n j.val).mp h
  rw [Nat.mod_eq_of_lt hJ,Nat.mod_eq_of_lt hN] at hn
  exact j.isLt.ne hn

variable [IsLocalRing O]
variable (hMax : IsLocalRing.maximalIdeal O = Ideal.span ({π}:Set O))
include hMax

theorem newton_diagonal_unit (n : ℕ) :
    ∃ u : Oˣ, newton D hq n (node D hq n) = π^debt q n*(u:O) := by
  choose u h using (fun j : Fin n =>
    ord_unit_factor π hMax (n+1) (node D hq n-node D hq j.val)
      (no_failed_diagonal_power D hq hq₂ h0 hπ n j))
  refine ⟨∏ j : Fin n,u j,?_⟩
  calc
    _ = ∏ j : Fin n, π^(ord π (n+1) (node D hq n-node D hq j.val))*(u j:O) :=
      Finset.prod_congr rfl (fun j _ => h j)
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,ord_sum_diag D hq hq₂ h0 hπ]
      exact congrArg (fun v : O => π^debt q n*v) (map_prod (Units.coeHom O) u Finset.univ).symm

#print axioms late_term_zero
#print axioms layer_count_lower
#print axioms layer_count_diag
#print axioms ord_sum_lower
#print axioms ord_sum_diag
#print axioms newton_divisor
#print axioms newton_diagonal_unit
end
end V8CapacityFactorial
