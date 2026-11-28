import Mathlib.Tactic
set_option warningAsError true

namespace Paper5.OuterCenters
open scoped BigOperators Classical

variable {V I G : Type*} [Fintype V] [Fintype I] [Fintype G]

noncomputable def scarce (robust : V → Prop) (owner : I → V → G) (i : I) (g : G) : Finset V :=
  Finset.univ.filter fun v => robust v ∧ owner i v = g

noncomputable def bad (robust : V → Prop) (owner : I → V → G) : Finset V :=
  Finset.univ.filter fun v => ¬ robust v ∨ ∃ i, (scarce robust owner i (owner i v)).card ≤ 2

theorem bad_card_bound (robust : V → Prop) (owner : I → V → G) :
    (bad robust owner).card ≤ (Finset.univ.filter fun v => ¬ robust v).card +
      2 * Fintype.card I * Fintype.card G := by
  classical
  let B := (Finset.univ : Finset V).filter fun v => ¬ robust v
  let C (ig : I × G) := if (scarce robust owner ig.1 ig.2).card ≤ 2
    then scarce robust owner ig.1 ig.2 else ∅
  have hsub : bad robust owner ⊆ B ∪ (Finset.univ : Finset (I × G)).biUnion C := by
    intro v hv
    have h := (Finset.mem_filter.mp hv).2
    rw [Finset.mem_union]
    by_cases hrv : robust v
    · right
      obtain ⟨i, hi⟩ := h.resolve_left (not_not_intro hrv)
      exact Finset.mem_biUnion.mpr ⟨(i, owner i v), Finset.mem_univ _, by
        change v ∈ (if (scarce robust owner i (owner i v)).card ≤ 2 then scarce robust owner i (owner i v) else ∅)
        rw [if_pos hi]
        simp [scarce, hrv]⟩
    · left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrv⟩
  calc
    _ ≤ (B ∪ (Finset.univ : Finset (I × G)).biUnion C).card := Finset.card_le_card hsub
    _ ≤ B.card + ((Finset.univ : Finset (I × G)).biUnion C).card := Finset.card_union_le _ _
    _ ≤ B.card + ∑ ig : I × G, (C ig).card := Nat.add_le_add_left (Finset.card_biUnion_le) _
    _ ≤ B.card + ∑ _ : I × G, 2 := by
      apply Nat.add_le_add_left
      apply Finset.sum_le_sum
      intro ig _
      by_cases h : (scarce robust owner ig.1 ig.2).card ≤ 2 <;> simp [C, h]
    _ = _ := by simp [B, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem exterior_avoids_bad (Bad : Finset V) (mate : V ≃ V)
    (h : 2 * Bad.card < Fintype.card V) :
    ∃ v, v ∉ Bad ∧ mate v ∉ Bad := by
  classical
  let B := Bad ∪ Bad.map mate.symm.toEmbedding
  have hB : B.card < Fintype.card V := by
    calc
      _ ≤ Bad.card + (Bad.map mate.symm.toEmbedding).card := Finset.card_union_le _ _
      _ < _ := by simpa [two_mul] using h
  have hne : B ≠ Finset.univ := by
    intro he
    rw [he, Finset.card_univ] at hB
    exact (Nat.lt_irrefl _ hB)
  have he : ∃ v, v ∉ B := by
    by_contra! hh
    exact hne (Finset.eq_univ_of_forall hh)
  obtain ⟨v, hv⟩ := he
  have hvB := Finset.notMem_union.mp hv
  refine ⟨v, hvB.1, fun hh => hvB.2 ?_⟩
  exact Finset.mem_map.mpr ⟨mate v, hh, mate.symm_apply_apply v⟩

omit [Fintype G] in
theorem good_has_sentry (robust : V → Prop) (owner : I → V → G) (i : I)
    (v w : V) (hv : v ∉ bad robust owner) :
    ∃ z, robust z ∧ owner i z = owner i v ∧ z ≠ v ∧ z ≠ w := by
  classical
  let C := scarce robust owner i (owner i v)
  have hcard : 2 < C.card := by
    apply Nat.lt_of_not_ge
    intro hh
    exact hv (by simp [bad]; exact Or.inr ⟨i, hh⟩)
  by_contra! h
  have hs : C ⊆ {v,w} := by
    intro z hz
    have hzm := (Finset.mem_filter.mp hz).2
    by_cases e : z = v
    · simp [e]
    · have hh : z = w := h z hzm.1 hzm.2 e
      simp [hh]
  have hle := Finset.card_le_card hs
  have htwo : ({v,w} : Finset V).card ≤ 2 := by
    by_cases hvw : v = w <;> simp [hvw]
  omega

#print axioms bad_card_bound
#print axioms exterior_avoids_bad
#print axioms good_has_sentry
end Paper5.OuterCenters



