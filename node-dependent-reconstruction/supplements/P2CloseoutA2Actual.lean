import ExpansionGraphCostConformance
import VisitRuntime

namespace Reconstruction.VisitRuntime.PublishedA2

open ExpansionGraph
open scoped BigOperators

noncomputable section

-- Inspect the exact private implementation used by the published `constructFromEdges`.
-- This is a proof-only view, not a replacement emitter.
open private copyOriginal emitPadding emitEdges prependGate edgeSlot from ExpansionGraphCost
open private edgeAt edgeAt_bijective from ExpansionGraphCostConformance

private theorem copy_mem {n m : ℕ} (F : CNF (Fin n)) (tail : CNF (OutputVar n m))
    {C : List (OutputVar n m × Bool)} (h : C ∈ tail) :
    C ∈ (copyOriginal tail F).output := by
  induction F with
  | nil => exact h
  | cons a F ih =>
    rw [copyOriginal]
    exact List.mem_cons_of_mem _ ih

private theorem padding_mem {n m : ℕ} (tail : CNF (OutputVar n m)) (k : ℕ)
    (hk : k ≤ paddingCount n) {C : List (OutputVar n m × Bool)} (h : C ∈ tail) :
    C ∈ (emitPadding tail k hk).output := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [emitPadding]
    exact List.mem_cons_of_mem _ (ih _)

private theorem emitted_gate_mem {n m : ℕ} (E : EdgeInput n) (i : ℕ)
    (hi : i + E.length ≤ m) (j : Fin E.length) :
    [(Sum.inr (edgeSlot E i hi j),true),
      (Sum.inl (E.get j).1,false),(Sum.inl (E.get j).2,false)] ∈
      (emitEdges E i hi).output := by
  induction E generalizing i with
  | nil => exact Fin.elim0 j
  | cons ab E ih =>
    obtain ⟨a,b⟩ := ab
    rw [emitEdges, prependGate]
    refine Fin.cases ?_ (fun k => ?_) j
    · have hz : edgeSlot ((a,b)::E) i hi (0 : Fin (E.length+1)) =
          (⟨i, by simp only [List.length_cons] at hi; omega⟩ : Fin m) := by
        apply Fin.ext
        exact Nat.add_zero i
      rw [hz]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      simpa only [edgeSlot, List.get_cons_succ', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih (i+1) (by simp only [List.length_cons] at hi; omega) k

def emittedCNF {n : ℕ} (F : CNF (Fin n)) (E : EdgeInput n) :=
  (constructFromEdges F E).output

def thirdClause {n : ℕ} (E : EdgeInput n) (j : Fin E.length) :
    List (OutputVar n E.length × Bool) :=
  [(Sum.inr j,true),(Sum.inl (E.get j).1,false),(Sum.inl (E.get j).2,false)]

/-- Each physical ternary gate clause survives in the actually returned formula. -/
theorem thirdClause_mem {n : ℕ} (F : CNF (Fin n)) (E : EdgeInput n) (j : Fin E.length) :
    thirdClause E j ∈ emittedCNF F E := by
  unfold emittedCNF constructFromEdges
  apply copy_mem
  apply padding_mem
  have hz : edgeSlot E 0 (by simp) j = j := Fin.ext (Nat.zero_add _)
  simpa only [thirdClause, hz] using emitted_gate_mem (m := E.length) E 0 (by simp) j

/-- Use actual emitted clause positions. This proof-only witness does not
add a lookup to the execution of the original construction. -/
def actualThirdSlot {n : ℕ} (F : CNF (Fin n)) (E : EdgeInput n) :
    Fin E.length ↪ Fin (emittedCNF F E).length := by
  let pos (j : Fin E.length) := Classical.choose (List.mem_iff_get.mp (thirdClause_mem F E j))
  have hpos (j) : (emittedCNF F E).get (pos j) = thirdClause E j :=
    Classical.choose_spec (List.mem_iff_get.mp (thirdClause_mem F E j))
  refine ⟨pos, ?_⟩
  intro j k he
  have hh : thirdClause E j = thirdClause E k := by rw [← hpos j, ← hpos k,he]
  exact Sum.inr.inj (Prod.mk.inj (List.cons.inj hh).1).1

theorem get_actualThirdSlot {n : ℕ} (F : CNF (Fin n)) (E : EdgeInput n) (j : Fin E.length) :
    (emittedCNF F E).get (actualThirdSlot F E j) = thirdClause E j := by
  exact Classical.choose_spec (List.mem_iff_get.mp (thirdClause_mem F E j))

/-- The original-edge factors are literally clauses of the output, with the
same endpoints even when the legal edge list changes order or orientation. -/
def actualGraphFactors {n Q r R : ℕ} (F : CNF (Fin n)) {E : EdgeInput n}
    {G : SimpleGraph (PaddedVar n)} (report : PresentsGraph E G)
    (L : PhysicalLayout (OutputVar n E.length) (Fin (emittedCNF F E).length) Q r R)
    (hscope : L.scope = formulaScope (emittedCNF F E)) : GraphFactors G L := by
  let ind := (Equiv.ofBijective (edgeAt report) (edgeAt_bijective report)).symm
  refine ⟨⟨Sum.inl, Sum.inl_injective⟩, ind.toEmbedding.trans (actualThirdSlot F E), ?_⟩
  intro e v hv
  let j := ind e
  have hj : (edgeAt report j).val = e.val :=
    congrArg Subtype.val ((Equiv.ofBijective (edgeAt report) (edgeAt_bijective report)).apply_symm_apply e)
  have whereV : v = (E.get j).1 ∨ v = (E.get j).2 := by
    rw [← hj] at hv
    exact Sym2.mem_iff.mp hv
  rw [hscope]
  change ∃ l ∈ (emittedCNF F E).get (actualThirdSlot F E j), l.1 = Sum.inl v
  rw [get_actualThirdSlot]
  rcases whereV with h | h
  · exact ⟨_,List.mem_cons_of_mem _ (List.mem_cons_self ..),congrArg Sum.inl h.symm⟩
  · exact ⟨_,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      congrArg Sum.inl h.symm⟩

/-- Appendix A.2 and its two visit conclusions for one and the same actual
metered edge-list output. The graph is supplied, as in the manuscript; it is
not reconstructed or validated by the program. -/
theorem same_emitted_A2_cost_count_and_visits {A c₀ : ℝ} (hA : 0 < A) (hc₀ : 0 < c₀) :
    ∃ C₃ C₆ : ℝ, 0 < C₃ ∧ 0 < C₆ ∧ ∃ N₀ : ℕ, ∀ {n : ℕ}
      (F : CNF (Fin n)) {E : EdgeInput n} {G : SimpleGraph (PaddedVar n)} [DecidableRel G.Adj],
      PresentsGraph E G → HasBalancedCuts G → (∀ v, 2 ≤ G.degree v ∧ G.degree v ≤ 3) →
      let N := Fintype.card (OutputVar n E.length)
      Nat.card (Models (emittedCNF F E)) = Nat.card (Models F) ∧
      2*N ≤ 5*(n+paddingCount n) ∧
      (emittedCNF F E).length = F.length+paddingCount n+3*E.length ∧
      (constructFromEdges F E).steps ≤ 895+24*(F.length+(F.map List.length).sum+E.length) ∧
      ∀ {Q r R d₀ T : ℕ}
        (L : PhysicalLayout (OutputVar n E.length) (Fin (emittedCNF F E).length) Q r R)
        (_W : Visits L d₀ T), L.scope = formulaScope (emittedCNF F E) →
        N₀ ≤ N → c₀*(N:ℝ) ≤ d₀ → L.balanced →
        (2:ℝ)^(C₃*arbitraryNodeScale N) ≤ T ∧
          ((r:ℝ)^(2*Q) ≤ (N:ℝ)^A → C₆*((N:ℝ)*scheduledRate N) ≤ Real.log T) := by
  have hδ : (0:ℝ) < 1/32768 := by norm_num
  have hΔ : 0 < (3:ℕ) := by decide
  have hρ : (0:ℝ) < 2/5 := by norm_num
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨a,ha,N₃,h3⟩ := balanced_from_candidates hδ hΔ hρ hc₀ 10
  obtain ⟨b,hb,N₆,h6⟩ := scheduled_from_candidates hA hδ hΔ hρ hc₀ 10
  refine ⟨a/Real.log 2,b,div_pos ha hlog,hb,max 1 (max N₃ N₆),?_⟩
  intro n F E G _ present hcuts hd
  let N := Fintype.card (OutputVar n E.length)
  have hNref : N = Fintype.card (GateVar G) := Fintype.card_congr (suppliedVariableEquiv present)
  have hsize : 2*N ≤ 5*Fintype.card (PaddedVar n) := by
    rw [hNref]
    exact (gateExtension_size G (fun v => (hd v).2)).1
  have hsize' : 2*N ≤ 5*(n+paddingCount n) := by
    simpa only [PaddedVar,Fintype.card_sum,Fintype.card_fin] using hsize
  obtain ⟨hp,hcount⟩ := constructFromEdges_linear_parsimonious F present
  refine ⟨hcount,hsize',(constructFromEdges_shape F E).1,hp,?_⟩
  intro Q r R d₀ T L W hscope hN hd₀ hbal
  let B := actualGraphFactors F present L hscope
  have hN1 : 1 ≤ N := (le_max_left ..).trans hN
  have hX : 0 < Fintype.card (PaddedVar n) := by omega
  have hN' : max N₃ N₆ ≤ N := (le_max_right ..).trans hN
  have hco : (2:ℝ)*(N:ℝ) ≤ 5*(Fintype.card (PaddedVar n):ℝ) := by exact_mod_cast hsize
  have hρ' : (2/5:ℝ)*(N:ℝ) ≤ Fintype.card (PaddedVar n) := by linarith only [hco]
  have hsub : (2/5:ℝ)*(N:ℝ) ≤ B.originalSet.card := by
    simpa only [B.card_originalSet] using hρ'
  have hcan := B.balanced_candidates hcuts hX hd hρ' hbal
  refine ⟨?_,fun hs => h6 W B.originalSet ((le_max_right ..).trans hN') hsub hd₀ hs hcan⟩
  have hr := h3 W B.originalSet ((le_max_left ..).trans hN') hsub hd₀ hbal hcan
  have hT : 0 < (T:ℝ) := by exact_mod_cast W.visits_pos
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos (by norm_num) _) hT).mp
  rw [Real.log_rpow (by norm_num)]
  have he : (a/Real.log 2 * arbitraryNodeScale N)*Real.log 2 = a*arbitraryNodeScale N := by
    field_simp
  rwa [he]

end

#print axioms thirdClause_mem
#print axioms get_actualThirdSlot
#print axioms actualGraphFactors
#print axioms same_emitted_A2_cost_count_and_visits

end Reconstruction.VisitRuntime.PublishedA2
