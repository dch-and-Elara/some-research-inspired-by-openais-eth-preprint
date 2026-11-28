import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Exact finite counts and the paid-event interface for the three
specified printed iterators. A single event can overlap between these
obligations; the lower bound uses their maximum, not their product. -/
namespace P5MainIterator
open scoped BigOperators Classical

variable {V G T : Type*} [Fintype V] [DecidableEq V] [Fintype G]

noncomputable def TaylorAt (V : Type*) [Fintype V] [DecidableEq V] (j : ℕ) :
    Finset (Finset V × Finset V) :=
  (Finset.univ.powersetCard j).biUnion fun E => E.powerset.image (Prod.mk E)

noncomputable def TaylorList (V : Type*) [Fintype V] [DecidableEq V] (q : ℕ) :
    Finset (Finset V × Finset V) :=
  (Finset.range (min q (Fintype.card V)+1)).biUnion (TaylorAt V)

theorem mem_taylorAt (j : ℕ) (E U : Finset V) :
    (E,U) ∈ TaylorAt V j ↔ U⊆E ∧ E.card=j := by
  unfold TaylorAt
  constructor
  · intro h
    obtain ⟨S,hS,hU⟩ := Finset.mem_biUnion.mp h
    obtain ⟨Z,hZ,h⟩ := Finset.mem_image.mp hU
    have h₁ : S=E := congrArg Prod.fst h
    have h₂ : Z=U := congrArg Prod.snd h
    subst S
    subst Z
    exact ⟨Finset.mem_powerset.mp hZ,(Finset.mem_powersetCard.mp hS).2⟩
  · rintro ⟨hU,hE⟩
    refine Finset.mem_biUnion.mpr ⟨E,?_,?_⟩
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hE⟩
    · exact Finset.mem_image.mpr ⟨U,Finset.mem_powerset.mpr hU,rfl⟩

theorem mem_taylorList (q : ℕ) (E U : Finset V) :
    (E,U) ∈ TaylorList V q ↔ U⊆E ∧ E.card≤q := by
  unfold TaylorList
  constructor
  · intro h
    obtain ⟨j,hq,hj⟩ := Finset.mem_biUnion.mp h
    have h := (mem_taylorAt j E U).mp hj
    exact ⟨h.1,by rw [h.2]; have : j < min q (Fintype.card V)+1 := Finset.mem_range.mp hq; omega⟩
  · rintro ⟨hU,hq⟩
    refine Finset.mem_biUnion.mpr ⟨E.card,Finset.mem_range.mpr ?_,(mem_taylorAt _ E U).mpr ⟨hU,rfl⟩⟩
    have hc := Finset.card_le_univ E
    omega

theorem card_taylorAt (j : ℕ) : (TaylorAt V j).card = 2^j * (Fintype.card V).choose j := by
  unfold TaylorAt
  rw [Finset.card_biUnion]
  · have hE (E : Finset V) (h : E ∈ Finset.univ.powersetCard j) :
        (E.powerset.image (Prod.mk E)).card=2^j := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h),
        Finset.card_powerset,(Finset.mem_powersetCard.mp h).2]
    rw [Finset.sum_congr rfl hE]
    simp [Finset.card_powersetCard,Nat.mul_comm]
  · intro E _ F _ h
    change Disjoint (E.powerset.image (Prod.mk E)) (F.powerset.image (Prod.mk F))
    rw [Finset.disjoint_left]
    intro p hp hq
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hp
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hq
    exact h (congrArg Prod.fst (ha.trans hb.symm))

theorem card_taylorList (q : ℕ) :
    (TaylorList V q).card =
      ∑ j ∈ Finset.range (min q (Fintype.card V)+1), 2^j * (Fintype.card V).choose j := by
  unfold TaylorList
  rw [Finset.card_biUnion]
  · exact Finset.sum_congr rfl (fun j _ => card_taylorAt j)
  · intro j _ k _ h
    change Disjoint (TaylorAt V j) (TaylorAt V k)
    rw [Finset.disjoint_left]
    rintro ⟨E,U⟩ h₁ h₂
    exact h (((mem_taylorAt j E U).mp h₁).2.symm.trans ((mem_taylorAt k E U).mp h₂).2)

theorem choose_le_taylorList (q j : ℕ) (h : j≤q) :
    2^j * (Fintype.card V).choose j ≤ (TaylorList V q).card := by
  rw [←card_taylorAt]
  apply Finset.card_le_card
  rintro ⟨E,U⟩ hp
  have ht := (mem_taylorAt j E U).mp hp
  exact (mem_taylorList q E U).mpr ⟨ht.1,ht.2 ▸ h⟩

omit [DecidableEq V] in
theorem card_group_sum (group : V → G) :
    (∑ g, Fintype.card {v : V // group v=g}) = Fintype.card V := by
  let e : (Σ g, {v : V // group v=g}) ≃ V :=
    { toFun := fun p => p.2.1
      invFun := fun v => ⟨group v,⟨v,rfl⟩⟩
      left_inv := by rintro ⟨g,v,hv⟩; subst g; rfl
      right_inv := fun _ => rfl }
  rw [←Fintype.card_sigma,Fintype.card_congr e]

omit [DecidableEq V] in
theorem largest_group_at_least_average (group : V → G) [Nonempty G] :
    ∃ a : G, (∀ g, Fintype.card {v : V // group v=g} ≤ Fintype.card {v : V // group v=a}) ∧
      Fintype.card V ≤ Fintype.card G * Fintype.card {v : V // group v=a} := by
  let f (g : G) := Fintype.card {v : V // group v=g}
  obtain ⟨g,_,hg⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  refine ⟨g,fun a => hg a (Finset.mem_univ _), ?_⟩
  rw [←card_group_sum group]
  calc
    (∑ a, f a) ≤ ∑ a : G, f g := Finset.sum_le_sum hg
    _ = _ := by simp [f]

omit [Fintype G] in
/-- Three separate actual deliveries, allowing overlap among them. -/
theorem three_iterators_lower {S : Type*} [Fintype S] (q T : ℕ)
    (group : V → G) (g : G)
    (taylor : (TaylorList V q) ↪ Fin T)
    (measurement : S ↪ Fin T)
    (localVisit : ({v : V // group v=g} → Bool) ↪ Fin T) :
    max (TaylorList V q).card (max (Fintype.card S) (2 ^ Fintype.card {v : V // group v=g})) ≤ T := by
  have ht := Fintype.card_le_of_injective taylor taylor.injective
  have hm := Fintype.card_le_of_injective measurement measurement.injective
  have hl := Fintype.card_le_of_injective localVisit localVisit.injective
  simp only [Fintype.card_fin,Fintype.card_coe] at ht hm
  simp only [Fintype.card_fin,Fintype.card_fun,Fintype.card_bool] at hl
  exact max_le ht (max_le hm hl)

/-- Counting the literal iterator slots with the separate variable group
balance bound. This is not an upper bound for arbitrary cell-cap layouts. -/
theorem balanced_slots_upper {T : Type*} [Fintype T] (q B Y : ℕ)
    (group : T → V → G) (measureCount : T → ℕ) (hm : ∀ t, measureCount t≤Y)
    (hb : ∀ t g, Fintype.card {v : V // group t v=g} ≤ B) :
    (∑ t, ((TaylorList V q).card * measureCount t *
      ∑ g, 2 ^ Fintype.card {v : V // group t v=g})) ≤
      Fintype.card T * (TaylorList V q).card * Y * Fintype.card G * 2^B := by
  calc
    _ ≤ ∑ _t : T, ((TaylorList V q).card*Y*(Fintype.card G*2^B)) := by
      apply Finset.sum_le_sum
      intro t _
      apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (hm t))
      calc
        _ ≤ ∑ _g : G, 2^B := Finset.sum_le_sum fun g _ => Nat.pow_le_pow_right (by decide) (hb t g)
        _ = _ := by simp
    _ = _ := by simp [Nat.mul_assoc]

#print axioms mem_taylorList
#print axioms card_taylorList
#print axioms choose_le_taylorList
#print axioms largest_group_at_least_average
#print axioms three_iterators_lower
#print axioms balanced_slots_upper
end P5MainIterator
