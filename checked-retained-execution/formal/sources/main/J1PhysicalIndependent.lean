import J1PhysicalHost
import ClonedWitness
import Mathlib.Tactic

/-! Choose a graph-only maximal independent set after reserving one
triangle and all its exterior mates. The size loss is at most six plus
a factor four, with explicit finite cardinalities. -/
namespace J1PhysicalIndependent
open scoped BigOperators
open J1PhysicalHost J1MainSourceLabels
variable {B : Type*} [Fintype B] [DecidableEq B]

def triangle (b : B) : Finset (Vertex B) :=
  Finset.univ.filter (fun v => v.1=b)

def mateEmbedding (M : Match B) : Vertex B ↪ Vertex B := ⟨M.mate,M.inv.injective⟩

def reserved (M : Match B) (b : B) : Finset (Vertex B) :=
  triangle b ∪ (triangle b).map (mateEmbedding M)

def available (M : Match B) (b : B) : Finset (Vertex B) :=
  Finset.univ \ reserved M b

def closedNbr (M : Match B) (v : Vertex B) : Finset (Vertex B) :=
  {v,next v,prev v,M.mate v}

omit [Fintype B] in
theorem closedNbr_card (M : Match B) (v : Vertex B) :
    (closedNbr M v).card ≤ 4 := by
  unfold closedNbr
  exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ
    ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ
      ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ (by simp))))))

omit [Fintype B] in
theorem mem_closedNbr (M : Match B) (v w : Vertex B) :
    w ∈ closedNbr M v ↔ w.1=v.1 ∨ w=M.mate v := by
  constructor
  · intro h
    rcases (by simpa [closedNbr] using h :
      w=v ∨ w=next v ∨ w=prev v ∨ w=M.mate v) with h | h | h | h
    · exact Or.inl (congrArg Prod.fst h)
    · exact Or.inl (show w.1=(next v).1 from congrArg Prod.fst h)
    · exact Or.inl (show w.1=(prev v).1 from congrArg Prod.fst h)
    · exact Or.inr h
  · rintro (h|h)
    · rcases v with ⟨b,i⟩
      rcases w with ⟨c,j⟩
      change c=b at h
      subst c
      have ht : ∀ i j : Fin 3, j=i ∨ j=i+1 ∨ j=i-1 := by decide
      rcases ht i j with h | h | h <;> simp [closedNbr,next,prev,h]
    · simp [closedNbr,h]

omit [Fintype B] in
theorem closedNbr_symm (M : Match B) (v w : Vertex B) :
    w ∈ closedNbr M v → v ∈ closedNbr M w := by
  rw [mem_closedNbr,mem_closedNbr]
  rintro (h|h)
  · exact Or.inl h.symm
  · exact Or.inr ((M.inv v).symm.trans (congrArg M.mate h).symm)

omit [Fintype B] in
theorem closed_contains (M : Match B) (v : Vertex B) : v ∈ closedNbr M v :=
  (mem_closedNbr M v v).mpr (Or.inl rfl)

def Independent (M : Match B) (H : Finset (Vertex B)) : Prop :=
  ∀ v ∈ H, ∀ w ∈ H, v≠w → w∉closedNbr M v

omit [Fintype B] in
theorem triangle_restriction (M : Match B) (H : Finset (Vertex B)) (hind : Independent M H)
    (v w : H) :
    ¬triangleEdge Prod.fst v.val w.val := by
  intro ht
  exact hind v.val v.property w.val w.property ht.1
    ((mem_closedNbr M _ _).mpr (Or.inl ht.2.symm))

theorem graph_independent (M : Match B) (H : Finset (Vertex B)) (hind : Independent M H) :
    PinnedWitness.independentOn (edges M) H := by
  rintro ⟨v,w⟩ he ⟨hv,hw⟩
  have hn : v≠w := by
    intro h
    subst w
    exact no_loops M v he
  apply hind v hv w hw hn
  rcases Finset.mem_union.mp he with h | h
  · have ht := (interior_same_block v w).mp (Or.inl h)
    exact (mem_closedNbr M v w).mpr (Or.inl ht.2.symm)
  · exact (mem_closedNbr M v w).mpr (Or.inr ((mem_exterior M v w).mp h).1)

theorem reserved_card (M : Match B) (b : B) : (reserved M b).card ≤ 6 := by
  unfold reserved
  calc
    _ ≤ (triangle b).card+((triangle b).map (mateEmbedding M)).card := Finset.card_union_le _ _
    _ = 6 := by simp [triangle,block_card]

theorem available_card (M : Match B) (b : B) :
    Fintype.card (Vertex B) ≤ (available M b).card+6 := by
  have hr := reserved_card M b
  have hc : (available M b).card + (reserved M b).card = Fintype.card (Vertex B) := by
    unfold available
    exact (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)).trans Finset.card_univ
  omega

theorem unavailable_at_reserved (M : Match B) (b : B) (H : Finset (Vertex B))
    (hH : H ⊆ available M b) (v : Vertex B) (hv : v.1=b) :
    v∉H ∧ M.mate v ∉H := by
  have htv : v∈triangle b := by simp [triangle,hv]
  have hv₁ : v∈reserved M b := Finset.mem_union_left _ htv
  have hv₂ : M.mate v ∈ reserved M b := Finset.mem_union_right _
    (Finset.mem_map.mpr ⟨v,htv,rfl⟩)
  exact ⟨fun h => (Finset.mem_sdiff.mp (hH h)).2 hv₁,
    fun h => (Finset.mem_sdiff.mp (hH h)).2 hv₂⟩

omit [Fintype B] in
theorem add_uncovered (M : Match B) (H : Finset (Vertex B)) (hI : Independent M H)
    (x : Vertex B) (hx : x∉H.biUnion (closedNbr M)) : Independent M (insert x H) := by
  intro v hv w hw hn hnbr
  rcases Finset.mem_insert.mp hv with h | hv
  · subst v
    rcases Finset.mem_insert.mp hw with h | hw
    · exact hn h.symm
    · exact hx (Finset.mem_biUnion.mpr ⟨w,hw,closedNbr_symm M x w hnbr⟩)
  · rcases Finset.mem_insert.mp hw with h | hw
    · subst w
      exact hx (Finset.mem_biUnion.mpr ⟨v,hv,hnbr⟩)
    · exact hI v hv w hw hn hnbr

/-- Maximal independent H dominates the remaining vertices. This is the
finite covering proof of N-6 ≤ 4|H| used by the source label construction. -/
theorem reserve_has_large_independent (M : Match B) (b : B) :
    ∃ H : Finset (Vertex B), H ⊆ available M b ∧ Independent M H ∧
      Fintype.card (Vertex B) ≤ 4*H.card+6 := by
  classical
  let pool := (available M b).powerset.filter (Independent M)
  have h0 : ∅∈pool := by simp [pool,Independent]
  obtain ⟨H,hH,hmax⟩ := Finset.exists_max_image pool Finset.card ⟨∅,h0⟩
  have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hH).1
  have hI := (Finset.mem_filter.mp hH).2
  have hcover : available M b ⊆ H.biUnion (closedNbr M) := by
    intro x hx
    by_contra hbad
    have hxH : x ∉ H := fun hh =>
      hbad (Finset.mem_biUnion.mpr ⟨x,hh,closed_contains M x⟩)
    have hnew : insert x H ∈ pool :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.insert_subset hx hsub),add_uncovered M H hI x hbad⟩
    have hle := hmax (insert x H) hnew
    rw [Finset.card_insert_of_notMem hxH] at hle
    omega
  have hsum := (Finset.card_le_card hcover).trans (Finset.card_biUnion_le :
    (H.biUnion (closedNbr M)).card ≤ ∑ v ∈ H, (closedNbr M v).card)
  have hs : (∑ v ∈ H, (closedNbr M v).card) ≤ 4*H.card := by
    calc
      _ ≤ ∑ _v ∈ H, (4:ℕ) := Finset.sum_le_sum fun v _ => closedNbr_card M v
      _ = _ := by simp [Nat.mul_comm]
  have hh := available_card M b
  have he := hsum.trans hs
  exact ⟨H,hsub,hI,by omega⟩

/-- An explicit finite threshold suffices for the J1 normalized-score guard. -/
theorem threshold_for_reserved_set (M : Match B) (b : B) (Q r : ℕ)
    (hSize : 192*Q*r^2*r^Q+6 < Fintype.card (Vertex B)) :
    ∃ H : Finset (Vertex B), H ⊆ available M b ∧ Independent M H ∧
      48*Q*r^2*r^Q < H.card := by
  obtain ⟨H,h1,h2,h3⟩ := reserve_has_large_independent M b
  refine ⟨H,h1,h2,?_⟩
  have hm : 192*Q*r^2*r^Q = 4*(48*Q*r^2*r^Q) := by ring
  rw [hm] at hSize
  omega

#print axioms graph_independent
#print axioms unavailable_at_reserved
#print axioms reserve_has_large_independent
#print axioms threshold_for_reserved_set

end J1PhysicalIndependent
