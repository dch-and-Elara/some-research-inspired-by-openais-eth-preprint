import PinnedCNF
import GraphCutMoments

/-! Deterministic part of local edge thinning. For every pattern of marks and
orientation bits, the retained edges give a genuine induced matching and their
signed cut statistic equals its endpoint-count imbalance. -/

namespace MatchingThinning

open scoped BigOperators

variable {V : Type*}

def vertex {E : Finset (V × V)} (e : E) (s : Bool) : V :=
  if s then e.1.2 else e.1.1

/-- Two edges conflict when their endpoints coincide or an original graph edge
joins their endpoints. This includes both edge incidence and adjacency. -/
def Conflict (E : Finset (V × V)) (e f : E) : Prop :=
  ∃ s t : Bool, vertex e s = vertex f t ∨ PinnedCNF.Adj E (vertex e s) (vertex f t)

noncomputable def block (E : Finset (V × V)) (e : E) : Finset E := by
  classical
  exact Finset.univ.filter fun f => f = e ∨ Conflict E e f

theorem mem_block_iff (E : Finset (V × V)) (e f : E) :
    f ∈ block E e ↔ f = e ∨ Conflict E e f := by
  classical
  simp [block]

theorem self_mem_block (E : Finset (V × V)) (e : E) : e ∈ block E e :=
  (mem_block_iff E e e).2 (Or.inl rfl)

/-- A marked edge survives precisely when every other edge in its block is unmarked. -/
noncomputable def retained (E : Finset (V × V)) (mark : E → Bool) : Finset E := by
  classical
  exact Finset.univ.filter fun e =>
    mark e = true ∧ ∀ f ∈ block E e, f ≠ e → mark f = false

theorem keep_iff (E : Finset (V × V)) (mark : E → Bool) (e : E) :
    e ∈ retained E mark ↔ mark e = true ∧ ∀ f ∈ block E e, f ≠ e → mark f = false := by
  classical
  simp [retained]

open scoped Classical in
theorem keep_pattern_iff (E : Finset (V × V)) (mark : E → Bool) (e : E) :
    e ∈ retained E mark ↔ ∀ f ∈ block E e, mark f = decide (f = e) := by
  classical
  rw [keep_iff]
  constructor
  · rintro ⟨he, hother⟩ f hf
    by_cases hfe : f = e
    · simpa [hfe] using he
    · simpa [hfe] using hother f hf hfe
  · intro h
    refine ⟨by simpa using h e (self_mem_block E e), ?_⟩
    intro f hf hfe
    simpa [hfe] using h f hf

abbrev Kept (E : Finset (V × V)) (mark : E → Bool) := ↥(retained E mark)

theorem retained_endpoints_separate (E : Finset (V × V)) (mark : E → Bool)
    (e f : Kept E mark) (hne : e ≠ f) (s t : Bool) :
    vertex e.1 s ≠ vertex f.1 t ∧ ¬ PinnedCNF.Adj E (vertex e.1 s) (vertex f.1 t) := by
  have hfe : f.1 ≠ e.1 := fun h => hne (Subtype.ext h.symm)
  have hc : ¬ Conflict E e.1 f.1 := by
    intro hconf
    have hf0 := ((keep_iff E mark e.1).1 e.2).2 f.1
      ((mem_block_iff E e.1 f.1).2 (Or.inr hconf)) hfe
    have hf1 := ((keep_iff E mark f.1).1 f.2).1
    exact Bool.false_ne_true (hf0.symm.trans hf1)
  exact ⟨fun h => hc ⟨s, t, Or.inl h⟩, fun h => hc ⟨s, t, Or.inr h⟩⟩

private theorem ends_ne {E : Finset (V × V)} (hloop : ∀ v, (v,v) ∉ E) (e : E) :
    e.1.1 ≠ e.1.2 := by
  rcases e with ⟨⟨u, v⟩, h⟩
  change u ≠ v
  rintro rfl
  exact hloop _ h

private theorem vertex_injective {E : Finset (V × V)} (hloop : ∀ v, (v,v) ∉ E) (e : E) :
    Function.Injective (vertex e) := by
  intro s t h
  have hne := ends_ne hloop e
  cases s <;> cases t <;> simp_all [vertex]

private theorem vertex_adj_iff {E : Finset (V × V)} (hloop : ∀ v, (v,v) ∉ E) (e : E)
    (s t : Bool) : PinnedCNF.Adj E (vertex e s) (vertex e t) ↔ s ≠ t := by
  rcases e with ⟨⟨u, v⟩, he⟩
  cases s <;> cases t <;> simp [vertex, PinnedCNF.Adj, hloop, he]

def turn (orientation side : Bool) : Bool := if orientation then side else !side

private theorem turn_injective (orientation : Bool) : Function.Injective (turn orientation) := by
  intro s t h
  cases orientation <;> simpa [turn] using h

/-- Every outcome of thinning with arbitrary orientation bits induces a matching
in the original loopless graph. Its index type depends on this outcome. -/
noncomputable def matching (E : Finset (V × V)) (hloop : ∀ v, (v,v) ∉ E)
    (mark orientation : E → Bool) : PinnedCNF.InducedMatching E (Kept E mark) where
  endpoint := {
    toFun := fun p => vertex p.1.1 (turn (orientation p.1.1) p.2)
    inj' := by
      rintro ⟨e, s⟩ ⟨f, t⟩ heq
      by_cases hef : e = f
      · subst f
        exact Prod.ext rfl (turn_injective _ (vertex_injective hloop e.1 heq))
      · exact False.elim ((retained_endpoints_separate E mark e f hef _ _).1 heq)
  }
  adj_iff := by
    rintro ⟨e, s⟩ ⟨f, t⟩
    change PinnedCNF.Adj E (vertex e.1 (turn (orientation e.1) s))
      (vertex f.1 (turn (orientation f.1) t)) ↔ e = f ∧ s ≠ t
    by_cases hef : e = f
    · subst f
      simp only [vertex_adj_iff hloop, true_and]
      exact (turn_injective _).ne_iff
    · simp [hef, (retained_endpoints_separate E mark e f hef _ _).2]

open scoped Classical in
noncomputable def signedValue (E : Finset (V × V)) (mark orientation : E → Bool) (e : E) : ℚ :=
  if e ∈ retained E mark then BangCore.bitSign (orientation e) else 0

noncomputable def sideIndices [DecidableEq V] {I : Type*} [Fintype I]
    {E : Finset (V × V)} (M : PinnedCNF.InducedMatching E I) (S : Finset V) (s : Bool) :
    Finset I :=
  Finset.univ.filter fun i => M.endpoint (i, s) ∈ S

private theorem card_sideIndices [DecidableEq V] {I : Type*} [Fintype I]
    {E : Finset (V × V)} (M : PinnedCNF.InducedMatching E I) (S : Finset V) (s : Bool) :
    ((sideIndices M S s).card : ℚ) = ∑ i, GraphCutMoments.cutBit ℚ S (M.endpoint (i,s)) := by
  rw [sideIndices, Finset.natCast_card_filter]
  rfl

private theorem oriented_difference [DecidableEq V] (E : Finset (V × V)) (hloop : ∀ v, (v,v) ∉ E)
    (mark orientation : E → Bool) (S : Finset V) (e : Kept E mark) :
    GraphCutMoments.cutBit ℚ S ((matching E hloop mark orientation).endpoint (e,false)) -
        GraphCutMoments.cutBit ℚ S ((matching E hloop mark orientation).endpoint (e,true)) =
      GraphCutMoments.cutDifference ℚ S e.1.1 * BangCore.bitSign (orientation e.1) := by
  change GraphCutMoments.cutBit ℚ S (vertex e.1 (turn (orientation e.1) false)) -
      GraphCutMoments.cutBit ℚ S (vertex e.1 (turn (orientation e.1) true)) = _
  cases h : orientation e.1 <;> simp [turn, vertex, GraphCutMoments.cutDifference, BangCore.bitSign]

/-- Signed endpoint count on the two transversals equals the cut statistic
computed from the marks and orientations of all stored edges. -/
theorem signed_imbalance [DecidableEq V] (E : Finset (V × V)) (hloop : ∀ v, (v,v) ∉ E)
    (mark orientation : E → Bool) (S : Finset V) :
    let M := matching E hloop mark orientation
    ((sideIndices M S false).card : ℚ) - ((sideIndices M S true).card : ℚ) =
      ∑ e : E, GraphCutMoments.cutDifference ℚ S e.1 * signedValue E mark orientation e := by
  classical
  dsimp only
  rw [card_sideIndices, card_sideIndices, ← Finset.sum_sub_distrib]
  simp_rw [oriented_difference]
  calc
    _ = ∑ e ∈ retained E mark, GraphCutMoments.cutDifference ℚ S e.1 *
        BangCore.bitSign (orientation e) := Finset.sum_coe_sort _ _
    _ = _ := by simp only [signedValue, mul_ite, mul_zero, Fintype.sum_ite_mem]

#print axioms mem_block_iff
#print axioms self_mem_block
#print axioms keep_iff
#print axioms keep_pattern_iff
#print axioms retained_endpoints_separate
#print axioms matching
#print axioms signed_imbalance

end MatchingThinning
