import P5HybridDOnlyKey
import P5HybridDOnlyPairCount

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000
set_option maxRecDepth 3200

/-! Pick one true D packing after imposing two designated independent
coordinate ties. The exact source collision charge counts the physical
endpoint pairs once and only the off-diagonal ties afterward. -/
namespace Paper5.HybridDOnly
open scoped Classical BigOperators
open J1MainSourceCollision J6R10Repack J6R11CollisionReindex DiagonalAbundance P11FullPacking

section Tags

variable {A U T I : Type*} [DecidableEq I]

def twoTags (exterior triangle : I) (inner : A→Option U) (outer : A→Option T)
    (i : I) (a : A) : Option (U⊕T) :=
  if i=exterior then (outer a).map Sum.inr
  else if i=triangle then (inner a).map Sum.inl
  else none

theorem twoTags_at_exterior (exterior triangle : I) (inner : A→Option U) (outer : A→Option T)
    (a : A) : twoTags exterior triangle inner outer exterior a=(outer a).map Sum.inr := by
  simp [twoTags]

theorem twoTags_at_triangle {exterior triangle : I} (distinct : exterior≠triangle)
    (inner : A→Option U) (outer : A→Option T) (a : A) :
    twoTags exterior triangle inner outer triangle a=(inner a).map Sum.inl := by
  simp [twoTags,Ne.symm distinct]

private theorem same_map_tag {B C : Type*} {x y : Option B} {f : B→C}
    (hi : Function.Injective f) {z : C}
    (hx : x.map f=some z) (hy : y.map f=some z) :
    ∃ b, x=some b ∧ y=some b := by
  cases x with
  | none => simp at hx
  | some b =>
    cases y with
    | none => simp at hy
    | some c =>
      simp only [Option.map_some,Option.some.injEq] at hx hy
      cases hi (hx.trans hy.symm)
      exact ⟨b,rfl,rfl⟩

theorem same_twoTag_either (exterior triangle : I) (inner : A→Option U) (outer : A→Option T)
    (i : I) (a b : A) (t : U⊕T)
    (ha : twoTags exterior triangle inner outer i a=some t)
    (hb : twoTags exterior triangle inner outer i b=some t) :
    (∃ z,inner a=some z ∧ inner b=some z) ∨ (∃ z,outer a=some z ∧ outer b=some z) := by
  by_cases h : i=exterior
  · exact Or.inr (same_map_tag Sum.inr_injective
      (by simpa only [twoTags,if_pos h] using ha)
      (by simpa only [twoTags,if_pos h] using hb))
  · by_cases j : i=triangle
    · exact Or.inl (same_map_tag Sum.inl_injective
        (by simpa only [twoTags,if_neg h,if_pos j] using ha)
        (by simpa only [twoTags,if_neg h,if_pos j] using hb))
    · simp [twoTags,h,j] at ha
end Tags

section Count

variable {E A B U T I : Type*} [Fintype E] [DecidableEq E]
  [DecidableEq A] [DecidableEq B] [DecidableEq U] [DecidableEq T] [DecidableEq I] [Fintype I]

theorem two_tie_dependent_pairs_le (ar : E→A) (bc : E→B)
    (exterior triangle : I) (inner : A→Option U) (outer : A→Option T) (ν : ℕ)
    (hcol : ∀ j,(varFibre bc j).card≤2)
    (hrow : ∀ j,(facFibre ar j).card≤3)
    (innerFib : ∀ j,(tagFibre (inner∘ar) j).card≤3)
    (outerFib : ∀ j,(tagFibre (outer∘ar) j).card≤2)
    (innerN : (tiedSlots (inner∘ar)).card≤ν) (outerN : (tiedSlots (outer∘ar)).card≤ν) :
    (dependentPairs (twoTags exterior triangle inner outer) ar bc).card≤4*Fintype.card E+3*ν := by
  let base := badPairs (fun _ : A => (none:Option Unit)) bc ar
  let ti := offTiedPairs (inner∘ar)
  let tout := offTiedPairs (outer∘ar)
  have inc : dependentPairs (twoTags exterior triangle inner outer) ar bc ⊆ base ∪ (ti ∪ tout) := by
    intro p hp
    by_cases h : ar p.1=ar p.2 ∨ bc p.1=bc p.2
    · exact Finset.mem_union_left _ (by
        simpa [base,badPairs,or_comm] using h)
    · have neq : p.1≠p.2 := fun e=>h (Or.inl (congrArg ar e))
      simp only [dependentPairs,Finset.mem_filter,Finset.mem_univ,true_and] at hp
      obtain hrow|hcol|⟨i,t,ha,hb⟩ := hp
      · exact (h (Or.inl hrow)).elim
      · exact (h (Or.inr hcol)).elim
      · rcases same_twoTag_either exterior triangle inner outer i (ar p.1) (ar p.2) t ha hb with hi|ho
        · exact Finset.mem_union_right _ (Finset.mem_union_left _
            (by simpa only [ti,offTiedPairs,Finset.mem_filter,Finset.mem_univ,true_and,
              Function.comp_apply] using ⟨neq,hi⟩))
        · exact Finset.mem_union_right _ (Finset.mem_union_right _
            (by simpa only [tout,offTiedPairs,Finset.mem_filter,Finset.mem_univ,true_and,
              Function.comp_apply] using ⟨neq,ho⟩))
  have bb : base.card≤4*Fintype.card E := by
    simpa only [base,show 2+(3:ℕ)-1=4 by decide,
      show 2+((3:ℕ)-1)=4 by decide,Nat.zero_mul,add_zero] using
      Paper5.HybridClosure.bad_pairs_with_ties (fun _ : A => (none:Option Unit)) bc ar 2 3 0 0
        hcol hrow (fun j=>by simp [tagFibre]) (by simp [tiedSlots])
  have bi : ti.card≤2*ν := off_ties_card_le (inner∘ar) 2 ν innerFib innerN
  have bo : tout.card≤1*ν := off_ties_card_le (outer∘ar) 1 ν outerFib outerN
  calc
    _ ≤ (base∪(ti∪tout)).card := Finset.card_le_card inc
    _ ≤ base.card+(ti.card+tout.card) :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_union_le _ _) _)
    _ ≤ _ := by omega
end Count

#print axioms twoTags_at_exterior
#print axioms twoTags_at_triangle
#print axioms same_twoTag_either
#print axioms two_tie_dependent_pairs_le
end Paper5.HybridDOnly
