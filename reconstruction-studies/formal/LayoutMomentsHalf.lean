import LayoutMoments
import LayoutBudget

namespace Reconstruction.LayoutMoments

open Finset LayoutBudget
open scoped BigOperators Classical
noncomputable section

/-- The independent half restriction of the finite variable set. -/
def halfSet {V : Type*} [Fintype V] [DecidableEq V] (b : Bits V) : Finset V :=
  univ.filter (fun v => b v = true)

/-- Projection of the fair product law to any set of coordinates. -/
theorem expect_restrict_bits {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) (f : Bits S → ℝ) :
    (𝔼 b : Bits V, f (fun v : S => b v.val)) = 𝔼 b : Bits S, f b := by
  classical
  calc
    _ = 𝔼 b : Bits S × Bits {v : V // v ∉ S}, f b.1 :=
      Fintype.expect_equiv (Equiv.piEquivPiSubtypeProd (fun v => v ∈ S) (fun _ => Bool)) _ _
        (fun _ => rfl)
    _ = _ := by
      rw [expect_prod (fun (b : Bits S) (_ : Bits {v : V // v ∉ S}) => f b)]
      simp only [Fintype.expect_const]

private theorem expect_bit {V : Type*} [Fintype V] [DecidableEq V] (v : V) :
    (𝔼 b : Bits V, indicator (b v = true)) = 1/2 := by
  classical
  let S : Finset V := {v}
  let u : S := ⟨v, mem_singleton_self v⟩
  let f (b : Bits S) := indicator (b u = true)
  change (𝔼 b : Bits V, f (fun w : S => b w.val)) = _
  rw [expect_restrict_bits S f]
  let e : Bits S ≃ Bool := {
    toFun := fun b => b u
    invFun := fun x _ => x
    left_inv := fun b => by
      funext w
      have hw : w.val ∈ ({v} : Finset V) := w.property
      have he : w = u := Subtype.ext (mem_singleton.mp hw)
      rw [he]
    right_inv := fun _ => rfl }
  rw [Fintype.expect_equiv e f (fun x => indicator (x = true)) (fun _ => rfl), expect_bool]
  norm_num [indicator]

theorem card_halfSet_as_sum {V : Type*} [Fintype V] [DecidableEq V] (b : Bits V) :
    ((halfSet b).card : ℝ) = ∑ v : V, indicator (b v = true) := by
  calc
    _ = ∑ v ∈ halfSet b, (1:ℝ) := by simp
    _ = _ := by
      rw [halfSet, sum_filter]
      apply sum_congr rfl
      intro v _
      by_cases h : b v = true <;> simp [indicator, h]

/-- Exact expectation n/2, without imposing a fixed sample cardinality. -/
theorem expect_card_halfSet {V : Type*} [Fintype V] [DecidableEq V] :
    (𝔼 b : Bits V, ((halfSet b).card : ℝ)) = (Fintype.card V:ℝ)/2 := by
  simp_rw [card_halfSet_as_sum]
  rw [expect_sum_comm]
  simp [expect_bit, div_eq_mul_inv]

def departures {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G] (a b : V → G) (g : G) : Finset V :=
  univ.filter (fun v => a v = g ∧ b v ≠ g)

def arrivals {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G] (a b : V → G) (g : G) : Finset V :=
  univ.filter (fun v => a v ≠ g ∧ b v = g)

private theorem disjoint_departures_arrivals {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G]
    (a b : V → G) (g : G) : Disjoint (departures a b g) (arrivals a b g) := by
  rw [Finset.disjoint_left]
  intro v hv hw
  exact (mem_filter.mp hw).2.1 (mem_filter.mp hv).2.1

private theorem card_fiber_halfSet {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G]
    (a : V → G) (g : G) (s : Bits V) :
    (Fintype.card (GroupFiber (fun u : halfSet s => a u.val) g) : ℝ) =
      ∑ v : V, indicator (s v = true)*indicator (a v = g) := by
  classical
  let T : Finset V := (halfSet s).filter (fun v => a v = g)
  let e : GroupFiber (fun u : halfSet s => a u.val) g ≃ T := {
    toFun := fun u => ⟨u.val.val, mem_filter.mpr ⟨u.val.property, u.property⟩⟩
    invFun := fun v => ⟨⟨v.val, (mem_filter.mp v.property).1⟩, (mem_filter.mp v.property).2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_coe]
  simp_rw [indicator, ite_mul, zero_mul, one_mul]
  rw [← sum_filter]
  calc
    _ = ∑ v ∈ T, (1:ℝ) := by simp
    _ = _ := by
      dsimp only [T, halfSet]
      rw [sum_filter]
      apply sum_congr rfl
      intro v _
      by_cases h : a v = g <;> simp [h]

set_option maxHeartbeats 800000 in
/-- Exact distribution of the source/target deficit. The walk is indexed by
the disjoint union of departing and arriving variables, and has x+y steps. -/
theorem expect_group_difference {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G]
    (a b : V → G) (g : G) (f : ℝ → ℝ) :
    (𝔼 s : Bits V,
      f ((Fintype.card (GroupFiber (fun u : halfSet s => a u.val) g) : ℝ) -
        Fintype.card (GroupFiber (fun u : halfSet s => b u.val) g))) =
      𝔼 s : Bits (Fin ((departures a b g).card+(arrivals a b g).card)),
        f ((((departures a b g).card:ℝ)-(arrivals a b g).card+walk s)/2) := by
  classical
  let A := departures a b g
  let B := arrivals a b g
  let H := A ∪ B
  have hH : H.card = A.card+B.card := Finset.card_union_of_disjoint
    (disjoint_departures_arrivals a b g)
  let orientation (s : Bits H) (v : H) := if a v.val = g then !(s v) else s v
  have hinv : Function.Involutive orientation := by
    intro s
    funext v
    by_cases he : a v.val = g <;> simp [orientation, he]
  have cardLaw (s : Bits V) :
      (Fintype.card (GroupFiber (fun u : halfSet s => a u.val) g) : ℝ) -
        Fintype.card (GroupFiber (fun u : halfSet s => b u.val) g) =
      ((A.card:ℝ)-B.card+walk (orientation (fun v : H => s v.val)))/2 := by
    rw [card_fiber_halfSet, card_fiber_halfSet, ← sum_sub_distrib]
    have hpoint (v : V) :
        indicator (s v = true)*indicator (a v = g) -
          indicator (s v = true)*indicator (b v = g) =
        ((if v ∈ A then (1:ℝ) else 0) - (if v ∈ B then 1 else 0) +
          (if v ∈ H then sign (if a v = g then !(s v) else s v) else 0))/2 := by
      by_cases ha : a v = g <;> by_cases hb : b v = g <;> cases hs : s v <;>
        norm_num [A, B, H, departures, arrivals, sign, indicator, ha, hb, hs]
    simp_rw [hpoint]
    rw [← sum_div, sum_add_distrib, sum_sub_distrib, ← sum_filter, ← sum_filter, ← sum_filter]
    have he (S : Finset V) : ((univ : Finset V).filter (fun v => v ∈ S)) = S := by ext; simp
    rw [he A, he B, he H]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    have hs : (∑ v ∈ H, sign (if a v = g then !(s v) else s v)) =
        walk (orientation (fun v : H => s v.val)) := sum_subtype H (by simp) _
    rw [hs]
  simp_rw [cardLaw]
  let test (s : Bits H) := f (((A.card:ℝ)-B.card+walk s)/2)
  change (𝔼 s : Bits V, test (orientation (fun v : H => s v.val))) = _
  rw [expect_restrict_bits H (fun s => test (orientation s))]
  rw [Fintype.expect_equiv hinv.toPerm (fun s => test (orientation s)) test (fun _ => rfl)]
  unfold test
  let e : H ≃ Fin (A.card+B.card) := Fintype.equivOfCardEq (by simpa using hH)
  exact expect_walk_equiv e (fun z => f (((A.card:ℝ)-B.card+z)/2))

/-- The paper's quantitative lower bound on one summand of the expected imbalance. -/
theorem expect_abs_group_difference {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G]
    (a b : V → G) (g : G) :
    Real.sqrt ((((departures a b g).card+(arrivals a b g).card : ℕ) : ℝ)/2)/24 ≤
      𝔼 s : Bits V, |(Fintype.card (GroupFiber (fun u : halfSet s => a u.val) g) : ℝ) -
        Fintype.card (GroupFiber (fun u : halfSet s => b u.val) g)| := by
  rw [expect_group_difference a b g abs]
  simp_rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [← expect_div]
  have hm := (expect_abs_walk (ι := Fin ((departures a b g).card+(arrivals a b g).card))).trans
    (expect_abs_walk_le_shift ((departures a b g).card-(arrivals a b g).card : ℝ))
  rw [Fintype.card_fin] at hm
  linarith only [hm]

end
end Reconstruction.LayoutMoments
