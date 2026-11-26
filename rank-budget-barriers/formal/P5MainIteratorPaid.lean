import P5MainIteratorSource
import P5MainIteratorChoose

/-! Paid visits refer to the three concrete sets in §6, on the same
call. The group node and attainable-summary node need not be identical. -/
namespace P5MainIterator
open scoped BigOperators Classical

variable {E V F Copy I B : Type*} [Fintype E] [Fintype V]
  [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B]

structure SourceVisits (keep : ℕ → Prop) (L : SourceLayout E V F Copy I B)
    (tm tg : I) (g : B) (q T : ℕ) where
  taylor : (TaylorList V q) ↪ Fin T
  tuple : (Set.range (sourceTuple keep L tm)) ↪ Fin T
  assignments : ({v : V // L.a v tg=g} → Bool) ↪ Fin T
  largest : ∀ g' : B, Fintype.card {v : V // L.a v tg=g'} ≤
    Fintype.card {v : V // L.a v tg=g}

theorem actual_visits_counts (keep : ℕ → Prop) (L : SourceLayout E V F Copy I B)
    (tm tg : I) (g : B) (q T : ℕ) (P : SourceVisits keep L tm tg g q T) :
    (TaylorList V q).card≤T ∧ (Set.range (sourceTuple keep L tm)).ncard≤T ∧
      2^Fintype.card {v : V // L.a v tg=g}≤T := by
  let S := Set.range (sourceTuple keep L tm)
  letI : Fintype S := (Set.finite_range _).fintype
  have ht := Fintype.card_le_of_injective P.taylor P.taylor.injective
  have hm := Fintype.card_le_of_injective P.tuple P.tuple.injective
  have hg := Fintype.card_le_of_injective P.assignments P.assignments.injective
  simp only [Fintype.card_coe,Fintype.card_fin] at ht
  simp only [Fintype.card_fin] at hm
  simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at hg
  refine ⟨ht,?_,hg⟩
  change S.ncard≤T
  rw [Set.ncard_eq_toFinset_card',Set.toFinset_card]
  exact hm

theorem group_average_cost (keep : ℕ → Prop) (L : SourceLayout E V F Copy I B)
    (tm tg : I) (g : B) (q T : ℕ) (P : SourceVisits keep L tm tg g q T) :
    (Fintype.card V:ℝ)/(Fintype.card B:ℝ) ≤ logTwo T := by
  have hNat : Fintype.card V ≤ Fintype.card B * Fintype.card {v : V // L.a v tg=g} := by
    have htot : (∑ a : B, Fintype.card {v : V // L.a v tg=a}) = Fintype.card V := by
      let e : (Σ a : B, {v : V // L.a v tg=a}) ≃ V :=
        { toFun := fun p => p.2.val
          invFun := fun v => ⟨L.a v tg,⟨v,rfl⟩⟩
          left_inv := by rintro ⟨a,v,h⟩; subst a; rfl
          right_inv := fun _ => rfl }
      rw [←Fintype.card_sigma,Fintype.card_congr e]
    rw [←htot]
    calc
      _ ≤ ∑ a : B, Fintype.card {v : V // L.a v tg=g} := by
        apply Finset.sum_le_sum
        intro a _
        exact P.largest a
      _ = _ := by simp
  haveI : Nonempty B := ⟨g⟩
  have hr : 0 < (Fintype.card B:ℝ) := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card B)
  have hgroup : (Fintype.card V:ℝ)/(Fintype.card B:ℝ) ≤
      (Fintype.card {v : V // L.a v tg=g}:ℝ) := by
    apply (div_le_iff₀ hr).mpr
    rw [mul_comm]
    exact_mod_cast hNat
  exact hgroup.trans (binary_exponent_le _ _ (actual_visits_counts keep L tm tg g q T P).2.2)

theorem taylor_linear_cost {V : Type*} [Fintype V] [DecidableEq V]
    (q T : ℕ) (ht : (TaylorList V q).card≤T) :
    ((min q (Fintype.card V):ℕ):ℝ) ≤ logTwo T := by
  let j := min q (Fintype.card V)
  have h₁ : j≤q := Nat.min_le_left _ _
  have h₂ : j≤Fintype.card V := Nat.min_le_right _ _
  have hc : 1≤(Fintype.card V).choose j := Nat.choose_pos h₂
  have ht' := choose_le_taylorList (V:=V) q j h₁
  apply binary_exponent_le T j
  exact (by simpa using Nat.mul_le_mul_left (2^j) hc : 2^j≤_).trans (ht'.trans ht)

/-- Native direct and supplied-equation Taylor-order expressions, with
an explicit common integer lower constant 1. -/
theorem printed_nominal_orders (n R Q k mTest l : ℕ)
    (hk : 1≤k) (hl : n≤l-1) :
    n*R/Q ≤ (3*n*R)/Q ∧ n*R/Q ≤ k*(mTest+2*(l-1))*R/Q := by
  constructor
  · apply Nat.div_le_div_right
    exact Nat.mul_le_mul_right R (by omega)
  · apply Nat.div_le_div_right
    have hh : n≤mTest+2*(l-1) := by omega
    have hc := Nat.mul_le_mul hk hh
    simp only [one_mul] at hc
    exact Nat.mul_le_mul_right R hc

omit [Fintype V] [Fintype Copy] in
theorem cell_feasibility_logs (L : SourceLayout E V F Copy I B) [Nonempty E]
    (hr : 2≤Fintype.card B)
    (hcap : ∀ u,cellLoad L u * Fintype.card (WordCell I B) ≤ 2*Fintype.card E) :
    2*(Fintype.card I:ℝ)*Real.log (Fintype.card B:ℝ) ≤ Real.log (2*(Fintype.card E:ℝ)) := by
  have hca := cap_forces_label_count L hcap
  have hR : 0<(Fintype.card B:ℝ) := by exact_mod_cast (by omega : 0<Fintype.card B)
  have hD : ((Fintype.card B:ℝ)^(2*Fintype.card I)) ≤ 2*(Fintype.card E:ℝ) := by exact_mod_cast hca
  have h := Real.log_le_log (pow_pos hR _) hD
  rw [Real.log_pow] at h
  exact_mod_cast h

#print axioms actual_visits_counts
#print axioms group_average_cost
#print axioms taylor_linear_cost
#print axioms printed_nominal_orders
#print axioms cell_feasibility_logs
end P5MainIterator
