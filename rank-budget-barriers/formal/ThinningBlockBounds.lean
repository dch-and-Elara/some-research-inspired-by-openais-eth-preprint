import MatchingThinning

/-! Maximum degree bounds the sizes of the actual marks read by an edge and
the number of edges whose blocks meet its block. -/

namespace ThinningBlockBounds

open MatchingThinning
open scoped BigOperators

variable {V : Type*} [DecidableEq V]

/-- The stored edges incident with a particular vertex. -/
def star (E : Finset (V × V)) (v : V) : Finset E :=
  Finset.univ.filter fun e => e.1.1 = v ∨ e.1.2 = v

def touching (E : Finset (V × V)) (e : E) : Finset E :=
  star E e.1.1 ∪ star E e.1.2

omit [DecidableEq V] in
private theorem card_subtype_filter (E : Finset (V × V)) (p : V × V → Prop) [DecidablePred p] :
    (Finset.univ.filter fun e : E => p e.1).card = (E.filter p).card := by
  simpa only [Finset.sum_boole] using
    (Finset.sum_coe_sort E (fun e => if p e then (1 : ℕ) else 0))

theorem star_card_le_degree (E : Finset (V × V)) (v : V) :
    (star E v).card ≤ GraphCutMoments.degree E v := by
  rw [star, Finset.filter_or]
  apply (Finset.card_union_le _ _).trans
  rw [card_subtype_filter E (fun e => e.1 = v), card_subtype_filter E (fun e => e.2 = v)]
  exact le_rfl

theorem touching_card_le (E : Finset (V × V)) (D : ℕ)
    (hdeg : ∀ v, GraphCutMoments.degree E v ≤ D) (e : E) : (touching E e).card ≤ 2 * D := by
  exact (Finset.card_union_le _ _).trans <| (add_le_add
    ((star_card_le_degree E _).trans (hdeg _)) ((star_card_le_degree E _).trans (hdeg _))).trans_eq
    (two_mul D).symm

theorem mem_touching_iff (E : Finset (V × V)) (e f : E) :
    f ∈ touching E e ↔ ∃ s t : Bool, vertex e s = vertex f t := by
  simp only [touching, star, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ((h | h) | (h | h))
    · exact ⟨false, false, h.symm⟩
    · exact ⟨false, true, h.symm⟩
    · exact ⟨true, false, h.symm⟩
    · exact ⟨true, true, h.symm⟩
  · rintro ⟨s, t, h⟩
    cases s <;> cases t <;> simp_all [vertex]

private theorem touching_self (E : Finset (V × V)) (e : E) : e ∈ touching E e :=
  (mem_touching_iff E e e).2 ⟨false, false, rfl⟩

theorem block_subset_two_steps (E : Finset (V × V)) (e : E) :
    block E e ⊆ (touching E e).biUnion (touching E) := by
  intro f hf
  rw [Finset.mem_biUnion]
  rcases (mem_block_iff E e f).1 hf with rfl | ⟨s, t, hEq | hAdj⟩
  · exact ⟨f, touching_self E f, touching_self E f⟩
  · exact ⟨e, touching_self E e, (mem_touching_iff E e f).2 ⟨s, t, hEq⟩⟩
  · rcases hAdj with h | h
    · let g : E := ⟨(vertex e s, vertex f t), h⟩
      exact ⟨g, (mem_touching_iff E e g).2 ⟨s, false, rfl⟩,
        (mem_touching_iff E g f).2 ⟨true, t, rfl⟩⟩
    · let g : E := ⟨(vertex f t, vertex e s), h⟩
      exact ⟨g, (mem_touching_iff E e g).2 ⟨s, true, rfl⟩,
        (mem_touching_iff E g f).2 ⟨false, t, rfl⟩⟩

private theorem biUnion_card_le_square {X : Type*} [DecidableEq X] (neighbors : X → Finset X)
    (B : ℕ) (hB : ∀ x, (neighbors x).card ≤ B) (x : X) :
    ((neighbors x).biUnion neighbors).card ≤ B ^ 2 := by
  calc
    _ ≤ ∑ y ∈ neighbors x, (neighbors y).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ neighbors x, B := Finset.sum_le_sum fun y _ => hB y
    _ = (neighbors x).card * B := by simp
    _ ≤ B ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right B (hB x)

/-- Every block has at most (2D)² edges for graphs of maximum degree D. -/
theorem block_card_le (E : Finset (V × V)) (D : ℕ)
    (hdeg : ∀ v, GraphCutMoments.degree E v ≤ D) (e : E) : (block E e).card ≤ (2 * D) ^ 2 :=
  (Finset.card_le_card (block_subset_two_steps E e)).trans
    (biUnion_card_le_square (touching E) (2 * D) (touching_card_le E D hdeg) e)

omit [DecidableEq V] in
theorem mem_block_symm (E : Finset (V × V)) (e f : E) : f ∈ block E e ↔ e ∈ block E f := by
  have symm (a b : E) (h : b ∈ block E a) : a ∈ block E b := by
    apply (mem_block_iff E b a).2
    rcases (mem_block_iff E a b).1 h with rfl | ⟨s,t,hst | hadj⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨t,s, Or.inl hst.symm⟩
    · exact Or.inr ⟨t,s, Or.inr hadj.symm⟩
  exact ⟨symm e f, symm f e⟩

open scoped Classical in
theorem overlapping_blocks_eq (E : Finset (V × V)) (e : E) :
    (Finset.univ.filter fun f : E => ¬ Disjoint (block E e) (block E f)) =
      (block E e).biUnion (block E) := by
  classical
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.not_disjoint_iff,
    Finset.mem_biUnion]
  exact exists_congr fun g => and_congr_right fun _ => mem_block_symm E f g

open scoped Classical in
/-- At most (2D)⁴ contributions share marks with the contribution of an edge. -/
theorem overlapping_blocks_card_le (E : Finset (V × V)) (D : ℕ)
    (hdeg : ∀ v, GraphCutMoments.degree E v ≤ D) (e : E) :
    (Finset.univ.filter fun f : E => ¬ Disjoint (block E e) (block E f)).card ≤ (2 * D) ^ 4 := by
  rw [overlapping_blocks_eq]
  have h := biUnion_card_le_square (block E) ((2 * D) ^ 2) (block_card_le E D hdeg) e
  simpa only [← pow_mul] using h

#print axioms star_card_le_degree
#print axioms touching_card_le
#print axioms mem_touching_iff
#print axioms block_subset_two_steps
#print axioms block_card_le
#print axioms mem_block_symm
#print axioms overlapping_blocks_eq
#print axioms overlapping_blocks_card_le

end ThinningBlockBounds
