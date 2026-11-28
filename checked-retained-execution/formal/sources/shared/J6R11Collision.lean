import J1MainSourceCollision
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Exact collision variance for the source's active bipartite graph

Edges are a finite index type, so parallel physical edges and
self-pairs in the ordered pair sum are retained. Vertex words are
sampled independently on both sides. This instantiates the already
verified centered-load algebra on precisely those endpoints.
-/

open scoped BigOperators Classical

namespace J6R11Collision
open DiagonalAbundance J1MainSourceCollision
noncomputable section

universe u v w a
variable {E : Type u} {R : Type v} {C : Type w} {A : Type a}
  [Fintype E] [Fintype R] [Fintype C] [Fintype A] [Nonempty A]

abbrev Sample (R : Type v) (C : Type w) (A : Type a) := (R → A) × (C → A)

def edgeCell (row : E → R) (col : E → C) (z : Sample R C A) (e : E) : A×A :=
  (z.1 (row e),z.2 (col e))

omit [Fintype R] [Fintype C] in
/-- The literal ordered pair statistic minus M²/D, including e=e'. -/
theorem squared_load_identity (row : E → R) (col : E → C) (z : Sample R C A) :
    deviation (edgeCell row col z) =
      (∑ q : E×E, indicator (edgeCell row col z q.1=edgeCell row col z q.2)) -
        (Fintype.card E:ℚ)^2/(Fintype.card (A×A):ℚ) := by
  rw [deviation_eq_pairs,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_prod,Nat.cast_mul]
  ring

def sideProb (A : Type a) [Fintype A] {S : Type*} (i j : S) : ℚ :=
  if i=j then 1 else 1/(Fintype.card A:ℚ)

omit [Fintype E] [Fintype R] [Fintype C] in
theorem side_coincidence {S : Type*} [Fintype S] (i j : S) :
    mean (fun z : S→A => indicator (z i=z j))=sideProb A i j := by
  classical
  by_cases h : i=j
  · subst j
    simp [indicator,sideProb,mean_const]
  · rw [independent_coincidence i j (fun he => h he.symm)]
    simp [sideProb,h]

omit [Fintype E] in
/-- The full pair law exposes the shared-endpoint cases too: each
distinct endpoint comparison contributes 1/|A|; a shared endpoint
contributes exactly one on that side. -/
theorem collision_probability (row : E → R) (col : E → C) (e f : E) :
    mean (fun z : Sample R C A => indicator (edgeCell row col z e=edgeCell row col z f)) =
      sideProb A (row e) (row f)*sideProb A (col e) (col f) := by
  have hp (z : Sample R C A) :
      indicator (edgeCell row col z e=edgeCell row col z f) =
        indicator (z.1 (row e)=z.1 (row f))*indicator (z.2 (col e)=z.2 (col f)) := by
    by_cases hr : z.1 (row e)=z.1 (row f) <;> by_cases hc : z.2 (col e)=z.2 (col f) <;>
      simp [indicator,edgeCell,hr,hc]
  simp_rw [hp]
  rw [mean_product (fun z : R→A => indicator (z (row e)=z (row f)))
    (fun z : C→A => indicator (z (col e)=z (col f))),side_coincidence,side_coincidence]

omit [Fintype E] in
theorem disjoint_probability (row : E → R) (col : E → C) (e f : E)
    (hr : row e≠row f) (hc : col e≠col f) :
    mean (fun z : Sample R C A => indicator (edgeCell row col z e=edgeCell row col z f)) =
      1/(Fintype.card (A×A):ℚ) := by
  rw [collision_probability]
  simp only [sideProb,if_neg hr,if_neg hc,Fintype.card_prod,Nat.cast_mul]
  ring

section Counting

variable {S : Type*}

/-- Degree is the number of indexed incident edges, not the number
of distinct opposite-side neighbors. -/
def fibre (ends : E → S) (v : S) : Finset E :=
  Finset.univ.filter (fun e => ends e=v)

omit [Fintype R] [Fintype C] [Fintype A] [Nonempty A] in
theorem sharing_card (row : E → R) (col : E → C) (Δ : ℕ)
    (hr : ∀ v, (fibre row v).card≤Δ) (hc : ∀ v, (fibre col v).card≤Δ) :
    ((Finset.univ : Finset (E×E)).filter (fun p =>
      row p.1=row p.2 ∨ col p.1=col p.2)).card ≤ 2*Fintype.card E*Δ := by
  let N := fun e => (fibre row (row e)) ∪ (fibre col (col e))
  have hn (e : E) : (N e).card≤2*Δ := by
    have hh := (Finset.card_union_le (fibre row (row e)) (fibre col (col e))).trans
      (Nat.add_le_add (hr _) (hc _))
    simpa only [N,two_mul] using hh
  have hcard : ((Finset.univ : Finset (E×E)).filter (fun p =>
      row p.1=row p.2 ∨ col p.1=col p.2)).card = ∑ e : E,(N e).card := by
    simp only [Finset.card_filter,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro e _
    have hN : N e = (Finset.univ : Finset E).filter (fun f =>
        row e=row f ∨ col e=col f) := by
      ext f
      simp [N,fibre,eq_comm]
    rw [hN,Finset.card_filter]
  rw [hcard]
  calc
    _ ≤ ∑ _e : E, 2*Δ := Finset.sum_le_sum (fun e _ => hn e)
    _ = _ := by simp [Nat.mul_comm,Nat.mul_left_comm]

end Counting

/-- Exact application of the collision potential to a reachable
active graph whose original maximum-degree invariant is supplied. -/
theorem expected_squared_loads (row : E → R) (col : E → C) (Δ : ℕ)
    (hr : ∀ v, (fibre row v).card≤Δ) (hc : ∀ v, (fibre col v).card≤Δ) :
    mean (fun z : Sample R C A => deviation (edgeCell row col z)) ≤
      2*(Fintype.card E:ℚ)*Δ := by
  let bad := (Finset.univ : Finset (E×E)).filter (fun p =>
    row p.1=row p.2 ∨ col p.1=col p.2)
  have hbad : (bad.card:ℚ) ≤ 2*(Fintype.card E:ℚ)*Δ := by
    exact_mod_cast sharing_card row col Δ hr hc
  refine (expected_deviation_bad_pairs (edgeCell row col) bad (fun p hp => ?_)).trans hbad
  have hnot : ¬ (row p.1=row p.2 ∨ col p.1=col p.2) := by simpa [bad] using hp
  exact disjoint_probability row col p.1 p.2 (fun h => hnot (Or.inl h)) (fun h => hnot (Or.inr h))

theorem exists_labeling (row : E → R) (col : E → C) (Δ : ℕ)
    (hr : ∀ v, (fibre row v).card≤Δ) (hc : ∀ v, (fibre col v).card≤Δ) :
    ∃ z : Sample R C A, deviation (edgeCell row col z)≤2*(Fintype.card E:ℚ)*Δ := by
  classical
  let f := fun z : Sample R C A => deviation (edgeCell row col z)
  obtain ⟨z,_hz,hmin⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  refine ⟨z,?_⟩
  have h := mean_mono (fun _ => f z) f (fun a => hmin _ (Finset.mem_univ a))
  rw [mean_const] at h
  exact h.trans (expected_squared_loads row col Δ hr hc)

theorem source_word_cells (r a : ℕ) :
    Fintype.card ((Fin a→Fin r)×(Fin a→Fin r))=r^(2*a) := by
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,← pow_add,two_mul]

omit [Fintype A] [Nonempty A] in
/-- Actual source labels are words of length a on the r symbols,
not arbitrary abstract labels whose cardinality is unstated. -/
theorem actual_source_labeling (r a Δ : ℕ) (hrpos : 0<r) (row : E → R) (col : E → C)
    (hr : ∀ v, (fibre row v).card≤Δ) (hc : ∀ v, (fibre col v).card≤Δ) :
    ∃ z : Sample R C (Fin a→Fin r),
      (∑ c, (load (edgeCell row col z) c -
        (Fintype.card E:ℚ)/((r:ℚ)^(2*a)))^2) ≤ 2*(Fintype.card E:ℚ)*Δ := by
  letI : Nonempty (Fin r) := ⟨⟨0,hrpos⟩⟩
  obtain ⟨z,hz⟩ := exists_labeling (A:=Fin a→Fin r) row col Δ hr hc
  refine ⟨z,?_⟩
  simpa only [deviation,source_word_cells,Nat.cast_pow] using hz

#print axioms squared_load_identity
#print axioms collision_probability
#print axioms disjoint_probability
#print axioms sharing_card
#print axioms expected_squared_loads
#print axioms exists_labeling
#print axioms actual_source_labeling

end
end J6R11Collision

