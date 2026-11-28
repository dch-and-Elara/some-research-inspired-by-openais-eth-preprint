import J1PhysicalIndependent

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

/-! A graph-only deterministic maximal set on the actual three-port
triangle host with the source's one reserved triangle and its mates.
The input vertex order is arbitrary but fixed independently of signs. -/
namespace J1R43Literal
open scoped BigOperators
open J1PhysicalHost J1PhysicalIndependent

variable {B : Type*} [Fintype B] [DecidableEq B]

def reserveStep (M : Match B) (b : B) (H : Finset (Vertex B)) (v : Vertex B) :
    Finset (Vertex B) :=
  if v ∈ available M b ∧ v ∉ H.biUnion (closedNbr M) then insert v H else H

def reserveRun (M : Match B) (b : B) :
    List (Vertex B) → Finset (Vertex B) → Finset (Vertex B)
  | [], H => H
  | v::vs, H => reserveRun M b vs (reserveStep M b H v)

theorem step_props (M : Match B) (b : B) (H : Finset (Vertex B)) (v : Vertex B)
    (hs : H ⊆ available M b) (hi : Independent M H) :
    let T := reserveStep M b H v
    H ⊆ T ∧ T ⊆ available M b ∧ Independent M T ∧
      (v ∈ available M b → v ∈ T.biUnion (closedNbr M)) := by
  dsimp only
  unfold reserveStep
  split
  · rename_i hv
    refine ⟨Finset.subset_insert _ _,Finset.insert_subset hv.1 hs,add_uncovered M H hi v hv.2,?_⟩
    intro _
    exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_insert_self _ _,closed_contains M v⟩
  · rename_i h
    exact ⟨Finset.Subset.refl _,hs,hi,fun hv => by
      by_contra hh
      exact h ⟨hv,hh⟩⟩

theorem coverage_mono (M : Match B) {H T : Finset (Vertex B)}
    (h : H ⊆ T) : H.biUnion (closedNbr M) ⊆ T.biUnion (closedNbr M) := by
  intro v hv
  obtain ⟨x,hx,hm⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_biUnion.mpr ⟨x,h hx,hm⟩

theorem reserveRun_invariant (M : Match B) (b : B) (vs : List (Vertex B))
    (H : Finset (Vertex B)) (hs : H ⊆ available M b) (hi : Independent M H) :
    let T := reserveRun M b vs H
    H ⊆ T ∧ T ⊆ available M b ∧ Independent M T ∧
      ∀ v, v ∈ vs → v ∈ available M b → v ∈ T.biUnion (closedNbr M) := by
  induction vs generalizing H with
  | nil =>
    exact ⟨Finset.Subset.refl _,hs,hi,by simp⟩
  | cons v vs ih =>
    obtain ⟨inc,sub,ind,cv⟩ := step_props M b H v hs hi
    obtain ⟨ext,sub',ind',cover⟩ := ih (reserveStep M b H v) sub ind
    refine ⟨inc.trans ext,sub',ind',?_⟩
    intro x hx ha
    rcases List.mem_cons.mp hx with hx|hx
    · subst x
      exact coverage_mono M ext (cv ha)
    · exact cover x hx ha

/-- The original candidate set is generated greedily, not assumed
as part of the format. It covers every unreserved vertex. -/
theorem graph_only_reserve (M : Match B) (b : B) (vs : List (Vertex B))
    (all : ∀ v, v ∈ vs) :
    let H := reserveRun M b vs ∅
    H ⊆ available M b ∧ Independent M H ∧
      Fintype.card (Vertex B) ≤ 4*H.card+6 := by
  let H := reserveRun M b vs ∅
  have h := reserveRun_invariant M b vs ∅ (Finset.empty_subset _) (by simp [Independent])
  obtain ⟨_,hs,hi,hc⟩ := h
  have hcover : available M b ⊆ H.biUnion (closedNbr M) :=
    fun v hv => hc v (all v) hv
  have hsum := (Finset.card_le_card hcover).trans (Finset.card_biUnion_le :
      (H.biUnion (closedNbr M)).card ≤ ∑ v ∈ H,(closedNbr M v).card)
  have bound : (∑ v ∈ H,(closedNbr M v).card) ≤ 4*H.card :=
    (Finset.sum_le_sum (fun v _ => closedNbr_card M v)).trans_eq
      (by simp [Nat.mul_comm])
  exact ⟨hs,hi,(available_card M b).trans (Nat.add_le_add_right (hsum.trans bound) _)⟩

#print axioms step_props
#print axioms coverage_mono
#print axioms reserveRun_invariant
#print axioms graph_only_reserve

end J1R43Literal