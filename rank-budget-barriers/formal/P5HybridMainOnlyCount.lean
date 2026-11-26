
import P5HybridMainOnlyPrimitives
import P5HybridMainOnlyTopology
import P5HybridDOnlyPairCount

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000
set_option maxSynthPendingDepth 16
set_option linter.unusedSectionVars false

/-! One full-cell variance on the common physical MAIN port list.
The exterior ties add at most N ordered pairs; the unchanged basic
variable/factor sharing and the triangle ties add at most 4M+2N. -/
namespace Paper5.HybridMainOnly
open scoped Classical BigOperators
open Paper5.HybridClosure J1MainSourceCollision J1MainSourceLabels DiagonalAbundance
open Paper5.HybridDOnly (offTiedPairs off_ties_card_le)
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (cubic : ∀ v,GraphCutMoments.degree E v=3)
local notation "F" => (replacedEdges E cubic)
local notation "Port" => (MainClonedCNF.Port F)
variable (loopless : ∀v,(v,v)∉E)
local notation "reg" => (replaced_cubic E cubic loopless)

scoped instance clauseIndexEq (H : Finset (TriVertex V×TriVertex V)) : DecidableEq (ClauseIndex H) :=
  @instDecidableEqSum (TriVertex V) (H⊕Clone (TriVertex V)) inferInstance
    (@instDecidableEqSum H (Clone (TriVertex V)) inferInstance inferInstance)

scoped instance portEq (H : Finset (TriVertex V×TriVertex V)) : DecidableEq (MainClonedCNF.Port H) :=
  @instDecidableEqSum (TriVertex V) ((H×Bool)⊕(TriVertex V×Fin 4×Bool)) inferInstance
    (@instDecidableEqSum (H×Bool) (TriVertex V×Fin 4×Bool) inferInstance inferInstance)


abbrev SourcePrimitive (I : Type*) := Primitive (Clone (TriVertex V)) (ClauseIndex F) (V⊕E) I

scoped instance sourcePrimitiveEq (J : Type*) [DecidableEq J] :
    DecidableEq (SourcePrimitive E cubic J) :=
  @instDecidableEqSum (Clone (TriVertex V)×J) ((ClauseIndex F×J)⊕(V⊕E)) inferInstance
    (@instDecidableEqSum (ClauseIndex F×J) (V⊕E) inferInstance
      (@instDecidableEqSum V E inferInstance inferInstance))


variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [Nonempty S]

theorem literal_disjoint_coordinates (t u : I) :
    DisjointCoordinates (literalTags E cubic t u) := by
  intro j k f f' b hj hk
  by_cases hjt : j=t
  · subst j
    by_cases hkt : k=t
    · exact hkt.symm
    · by_cases hku : k=u
      · subst k
        cases hf : triangleTie f <;> cases hg : mateTag E cubic f'
        all_goals simp [literalTags,hkt,hf,hg] at hj hk
        rw [← hj] at hk
        cases hk
      · simp [literalTags,hkt,hku] at hk
  · by_cases hju : j=u
    · subst j
      by_cases hkt : k=t
      · subst k
        cases hf : mateTag E cubic f <;> cases hg : triangleTie f'
        all_goals simp [literalTags,hjt,hf,hg] at hj hk
        rw [← hj] at hk
        cases hk
      · by_cases hku : k=u
        · exact hku.symm
        · simp [literalTags,hkt,hku] at hk
    · simp [literalTags,hjt,hju] at hj

def basicPairs : Finset (Port×Port) :=
  badPairs (fun _ : ClauseIndex F=> (none : Option V)) (cloneOwner F reg) (cloneFactor F)

def trianglePairs : Finset (Port×Port) := offTiedPairs (triangleTie ∘ cloneFactor F)

def matePairs : Finset (Port×Port) := offTiedPairs (mateTag E cubic ∘ cloneFactor F)

def sourceBad : Finset (Port×Port) :=
  ((basicPairs E cubic loopless) ∪ trianglePairs E cubic) ∪ matePairs E cubic

theorem source_bad_exact_bound :
    (sourceBad E cubic loopless).card≤4*Fintype.card Port+3*Fintype.card (TriVertex V) := by
  have h₀ : (basicPairs E cubic loopless).card≤4*Fintype.card Port := by
    simpa only [basicPairs,Nat.reduceSub,Nat.reduceAdd,Nat.mul_zero,Nat.add_zero] using
      (bad_pairs_with_ties (fun _ : ClauseIndex F=> (none : Option V)) (cloneOwner F reg)
      (cloneFactor F) 3 2 0 0 (fun v=>(every_clone_three F reg v).le)
      (every_clause_at_most_two F) (fun v=>by simp [tagFibre]) (by simp [tiedSlots]))
  have ht : (trianglePairs E cubic).card≤2*Fintype.card (TriVertex V) :=
    off_ties_card_le _ 2 _ (triangle_tied_fibre F) (triangle_tied_slots F).le
  have hu : (matePairs E cubic).card≤1*Fintype.card (TriVertex V) :=
    off_ties_card_le _ 1 _ (fun e=>(mate_tied_fibre E cubic e).le) (mate_tied_slots E cubic).le
  unfold sourceBad
  have h1 := Finset.card_union_le (basicPairs E cubic loopless) (trianglePairs E cubic)
  have h2 := Finset.card_union_le ((basicPairs E cubic loopless) ∪ trianglePairs E cubic) (matePairs E cubic)
  omega

theorem outside_sources_independent (t u : I) (p : Port×Port)
    (hp : p∉sourceBad E cubic loopless) :
    mean (fun cfg : SourcePrimitive E cubic I→S => indicator
      (twoCell (literalTags E cubic t u) (cloneOwner F reg) (cloneFactor F) cfg p.1=
       twoCell (literalTags E cubic t u) (cloneOwner F reg) (cloneFactor F) cfg p.2)) =
      1/(Fintype.card (Draw I S):ℚ) := by
  have hb : p∉basicPairs E cubic loopless := fun h=>
    hp (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have ht : p∉trianglePairs E cubic := fun h=>
    hp (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hu : p∉matePairs E cubic := fun h=>hp (Finset.mem_union_right _ h)
  have hno : ¬(cloneOwner F reg p.1=cloneOwner F reg p.2 ∨ cloneFactor F p.1=cloneFactor F p.2) := by
    intro h
    apply hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.elim Or.inl (fun h' => Or.inr (Or.inl h'))⟩
  have hv := fun h=>hno (Or.inl h)
  have hf := fun h=>hno (Or.inr h)
  have hneq : p.1≠p.2 := fun h=>hv (congrArg (cloneOwner F reg) h)
  refine two_cells_coincide (E:=Port) (V:=Clone (TriVertex V)) («F»:=ClauseIndex F) (B:=V⊕E)
    (literalTags E cubic t u) (literal_disjoint_coordinates E cubic t u)
    (cloneOwner F reg) (cloneFactor F) p.1 p.2 hv hf ?_
  rintro j b ⟨h₁,h₂⟩
  by_cases hj : j=t
  · have h : ∃ v,triangleTie (cloneFactor F p.1)=some v ∧ triangleTie (cloneFactor F p.2)=some v := by
      revert h₁ h₂
      cases hh : triangleTie (cloneFactor F p.1) <;> cases hk : triangleTie (cloneFactor F p.2)
      all_goals simp [literalTags,hj,hh,hk]
      intro h₁ h₂
      rw [←h₁] at h₂
      exact Sum.inl.inj h₂
    exact ht (by simp [trianglePairs,offTiedPairs,hneq,h])
  · by_cases hk : j=u
    · rw [literalTags,if_neg hj,if_pos hk] at h₁ h₂
      have h : ∃ e,mateTag E cubic (cloneFactor F p.1)=some e ∧
          mateTag E cubic (cloneFactor F p.2)=some e := by
        revert h₁ h₂
        cases h₁ : mateTag E cubic (cloneFactor F p.1) <;> cases h₂ : mateTag E cubic (cloneFactor F p.2)
        all_goals simp
        intro h₁ h₂
        rw [←h₁] at h₂
        exact Sum.inr.inj h₂
      exact hu (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hneq,h⟩)
    · simp [literalTags,hj,hk] at h₁

def sourcePhi (t u : I) (cfg : SourcePrimitive E cubic I→S) : ℚ :=
  deviation (twoCell (literalTags E cubic t u) (cloneOwner F reg) (cloneFactor F) cfg)

theorem actual_main_only_expectation (t u : I) :
    mean (sourcePhi (S:=S) E cubic loopless t u)≤
      4*(Fintype.card Port:ℚ)+3*(Fintype.card (TriVertex V):ℚ) := by
  have h := expected_deviation_bad_pairs
    (twoCell (S:=S) (literalTags E cubic t u) (cloneOwner F reg) (cloneFactor F))
    (sourceBad E cubic loopless) (outside_sources_independent E cubic loopless t u)
  refine h.trans ?_
  exact_mod_cast source_bad_exact_bound E cubic loopless

#print axioms literal_disjoint_coordinates
#print axioms source_bad_exact_bound
#print axioms outside_sources_independent
#print axioms actual_main_only_expectation
end
end Paper5.HybridMainOnly
