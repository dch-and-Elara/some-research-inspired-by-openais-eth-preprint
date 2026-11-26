import S8PlacementSampling
import S8PortDegrees

namespace S8

open scoped BigOperators
open SourceDensity

variable {W X Y LX LY I : Type*} [Fintype W] [DecidableEq W]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I] [DecidableEq LX] [DecidableEq LY]

def neighbors (left : W → X) (right : W → Y) (extra : W → Finset W) (e : W) : Finset W :=
  ((Finset.univ.filter fun f => left f = left e) ∪
    (Finset.univ.filter fun f => right f = right e)) ∪ extra e

def conflictPairs (left : W → X) (right : W → Y) (extra : W → Finset W) : Finset (W × W) :=
  Finset.univ.filter fun p => p.2 ∈ neighbors left right extra p.1

theorem conflict_count (left : W → X) (right : W → Y) (extra : W → Finset W)
    (a b : ℕ) (la : ∀ x, fiberCount left x ≤ a) (rb : ∀ x, fiberCount right x ≤ b) :
    (conflictPairs left right extra).card ≤ Fintype.card W * (a + b - 1) + ∑ e, (extra e).card := by
  have h (e : W) : (neighbors left right extra e).card ≤ (a+b-1) + (extra e).card := by
    let L := Finset.univ.filter fun f => left f = left e
    let R := Finset.univ.filter fun f => right f = right e
    have hi : 1 ≤ (L ∩ R).card := Finset.card_pos.mpr ⟨e, by simp [L,R]⟩
    have hc := Finset.card_union_add_card_inter L R
    have hl := la (left e)
    have hr := rb (right e)
    change L.card ≤ a at hl
    change R.card ≤ b at hr
    change (L ∪ R ∪ extra e).card ≤ _
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right (by omega) _)
  have hsum : (conflictPairs left right extra).card = ∑ e, (neighbors left right extra e).card := by
    conv_lhs => rw [Finset.card_eq_sum_ones, conflictPairs, Finset.sum_filter]
    rw [Fintype.sum_prod_type
      (f := fun p : W × W => if p.2 ∈ neighbors left right extra p.1 then (1 : ℕ) else 0)]
    apply Finset.sum_congr rfl
    intro e _
    simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id]
  rw [hsum]
  calc
    _ ≤ ∑ e, ((a+b-1) + (extra e).card) := Finset.sum_le_sum fun e _ => h e
    _ = _ := by simp [Finset.sum_add_distrib]

omit [DecidableEq X] [DecidableEq LX] in
theorem key_conflict (classify : X → Option LX) (i t : I) {x y : X}
    (eq : key classify t i x = key classify t i y) :
    x = y ∨ ∃ z, classify x = some z ∧ classify y = some z := by
  by_cases h : i = t
  · cases hx : classify x <;> cases hy : classify y <;> simp_all [key]
  · exact .inl (by simpa [key, h] using eq)

omit [DecidableEq LX] [DecidableEq LY] in
theorem separate_sites (left : W → X) (right : W → Y)
    (shareL : X → Option LX) (shareR : Y → Option LY) (extra : W → Finset W) (t : I)
    (extrasL : ∀ e f z, shareL (left e) = some z → shareL (left f) = some z →
      left e ≠ left f → f ∈ extra e)
    (extrasR : ∀ e f z, shareR (right e) = some z → shareR (right f) = some z →
      right e ≠ right f → f ∈ extra e)
    (e f : W) (good : (e,f) ∉ conflictPairs left right extra) :
    Function.Injective (Sum.elim (site left right shareL shareR t e)
      (site left right shareL shareR t f)) := by
  have noL : left e ≠ left f := by
    intro h
    exact good (by simp [conflictPairs, neighbors, h])
  have noR : right e ≠ right f := by
    intro h
    exact good (by simp [conflictPairs, neighbors, h])
  have noE : f ∉ extra e := by
    intro h
    exact good (by simp [conflictPairs, neighbors, h])
  have inj (w : W) : Function.Injective (site left right shareL shareR t w) := by
    rintro ⟨b,i⟩ ⟨c,j⟩ h
    cases b <;> cases c <;> simp_all [site]
  have disj (a b : Bool × I) :
      site left right shareL shareR t e a ≠ site left right shareL shareR t f b := by
    obtain ⟨a,i⟩ := a
    obtain ⟨b,j⟩ := b
    intro h
    cases a <;> cases b
    · simp only [site, Bool.false_eq_true, if_false, Prod.mk.injEq, Sum.inl.injEq] at h
      rcases h with ⟨rfl, hh⟩
      rcases key_conflict _ _ _ hh with he | ⟨z, he, hf⟩
      · exact noL he
      · exact noE (extrasL e f z he hf noL)
    · simp [site] at h
    · simp [site] at h
    · simp only [site, if_true, Prod.mk.injEq, Sum.inr.injEq] at h
      rcases h with ⟨rfl, hh⟩
      rcases key_conflict _ _ _ hh with he | ⟨z, he, hf⟩
      · exact noR he
      · exact noE (extrasR e f z he hf noR)
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (inj e h)
    | inr b => exact False.elim (disj a b h)
  | inr a =>
    cases b with
    | inl b => exact False.elim (disj b a h.symm)
    | inr b => exact congrArg Sum.inr (inj f h)

#print axioms conflict_count
#print axioms separate_sites

end S8

