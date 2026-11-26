
import P5HybridMainOnlyCount

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000
set_option maxSynthPendingDepth 16
set_option linter.unusedSectionVars false

/-! Optional exact census of the added distinct nonshared pairs. The variance
uses just their upper bound, hence does not depend on this module. -/
namespace Paper5.HybridMainOnly
open scoped Classical BigOperators
open Paper5.HybridClosure J1MainSourceCollision
open Paper5.HybridDOnly (offTiedPairs tiedMates off_ties_card_eq_mates)
noncomputable section

private theorem exact_off_card {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    (tag : A→Option B) (k : ℕ) (fiber : ∀ b,(tagFibre tag b).card=k+1) :
    (offTiedPairs tag).card=k*(tiedSlots tag).card := by
  have h (p : A) : (tiedMates tag p).card=k*(if p∈tiedSlots tag then 1 else 0) := by
    cases hp : tag p with
    | none => simp [tiedMates,tiedSlots,hp]
    | some b =>
      have hm : p∈tagFibre tag b := by simp [tagFibre,hp]
      have hpin : p∈tiedSlots tag := by simp [tiedSlots,hp]
      rw [tiedMates,hp,Option.elim_some,Finset.card_erase_of_mem hm,if_pos hpin,mul_one,fiber]
      omega
  simp_rw [off_ties_card_eq_mates,h,←Finset.mul_sum]
  have hh := Finset.card_filter (s:=(Finset.univ : Finset A)) (p:=fun x=>x∈tiedSlots tag)
  rw [Finset.filter_univ_mem] at hh
  rw [←hh]

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (cubic : ∀ v,GraphCutMoments.degree E v=3)
local notation "F" => (replacedEdges E cubic)
local notation "Port" => (MainClonedCNF.Port F)
variable (loopless : ∀v,(v,v)∉E)
local notation "reg" => (replaced_cubic E cubic loopless)
local notation "N" => (Fintype.card (TriVertex V))

theorem triangle_tied_fibre_exact (v : V) :
    (tagFibre (triangleTie ∘ cloneFactor F) v).card=3 := by
  let j : Fin 3↪Port :=
    ⟨fun i=>.inl (v,i),fun _ _ h=>congrArg Prod.snd (Sum.inl.inj h)⟩
  have h : tagFibre (triangleTie ∘ cloneFactor F) v=Finset.univ.map j := by
    ext p
    rcases p with p|p
    · constructor
      · intro hp
        have hbase : p.1=v := by simpa [tagFibre,triangleTie,cloneFactor] using hp
        exact Finset.mem_map.mpr ⟨p.2,Finset.mem_univ _,
          congrArg Sum.inl (Prod.ext hbase.symm rfl)⟩
      · intro hp
        obtain ⟨i,_,hi⟩ := Finset.mem_map.mp hp
        have hEq : (v,i)=p := Sum.inl.inj hi
        subst p
        simp [tagFibre,triangleTie,cloneFactor]
    · rcases p with p|p <;> simp [tagFibre,triangleTie,cloneFactor,j]
  rw [h,Finset.card_map,Finset.card_univ,Fintype.card_fin]

private theorem triangle_tag_at_pin (p : Port) (t : V)
    (hp : triangleTie (cloneFactor F p)=some t) :
    ∃ v : TriVertex V,p=.inl v ∧ v.1=t := by
  cases p with
  | inl v => exact ⟨v,rfl,Option.some.inj hp⟩
  | inr x => cases x <;> cases hp

private theorem mate_tag_at_pin (p : Port) (e : E)
    (hp : mateTag E cubic (cloneFactor F p)=some e) :
    ∃ v : TriVertex V,p=.inl v ∧ ((exteriorPort E cubic).symm v).1=e := by
  cases p with
  | inl v => exact ⟨v,rfl,Option.some.inj hp⟩
  | inr x => cases x <;> cases hp

include loopless in
private theorem distinct_mates_different_triangles (a b : TriVertex V) (hne : a≠b)
    (h : ((exteriorPort E cubic).symm a).1=((exteriorPort E cubic).symm b).1) :
    a.1≠b.1 := by
  let A := (exteriorPort E cubic).symm a
  let B := (exteriorPort E cubic).symm b
  have hAB : A.1=B.1 := h
  have hBool : A.2≠B.2 := fun h' => hne ((exteriorPort E cubic).symm.injective (Prod.ext hAB h'))
  have hA : a=exteriorPort E cubic (A.1,A.2) := (Equiv.apply_symm_apply _ _).symm
  have hB : b=exteriorPort E cubic (A.1,B.2) := by
    rw [hAB]
    exact (Equiv.apply_symm_apply _ _).symm
  rw [hA,hB]
  cases ha : A.2 <;> cases hb : B.2
  · exact False.elim (hBool (ha.trans hb.symm))
  · exact literal_tri_mates_separate E cubic loopless A.1
  · exact (literal_tri_mates_separate E cubic loopless A.1).symm
  · exact False.elim (hBool (ha.trans hb.symm))

include loopless in
theorem distinct_source_tie_pairs :
    Disjoint (trianglePairs E cubic) (matePairs E cubic) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  obtain ⟨_,hneq,tag,h₁,h₂⟩ := Finset.mem_filter.mp hp
  obtain ⟨_,_,e,h₃,h₄⟩ := Finset.mem_filter.mp hq
  obtain ⟨a,ha,ha₁⟩ := triangle_tag_at_pin E cubic p.1 tag h₁
  obtain ⟨b,hb,hb₁⟩ := triangle_tag_at_pin E cubic p.2 tag h₂
  obtain ⟨a',ha',he₁⟩ := mate_tag_at_pin E cubic p.1 e h₃
  obtain ⟨b',hb',he₂⟩ := mate_tag_at_pin E cubic p.2 e h₄
  have hEqA := Sum.inl.inj (ha.symm.trans ha')
  have hEqB := Sum.inl.inj (hb.symm.trans hb')
  subst a'
  subst b'
  have hne : a≠b := fun h=>hneq (ha.trans ((congrArg Sum.inl h).trans hb.symm))
  exact distinct_mates_different_triangles E cubic loopless a b hne (he₁.trans he₂.symm)
    (ha₁.trans hb₁.symm)

include loopless in
theorem exact_three_per_pin :
    ((trianglePairs E cubic) ∪ (matePairs E cubic)).card=3*N := by
  have hT : (trianglePairs E cubic).card=2*N := by
    rw [trianglePairs,exact_off_card _ 2 (triangle_tied_fibre_exact E cubic),triangle_tied_slots]
  have hM : (matePairs E cubic).card=1*N := by
    rw [matePairs,exact_off_card _ 1 (mate_tied_fibre E cubic),mate_tied_slots]
  rw [Finset.card_union_of_disjoint (distinct_source_tie_pairs E cubic loopless),hT,hM]
  omega


theorem tied_pairs_share_no_endpoint (p : Port×Port)
    (hp : p ∈ (trianglePairs E cubic) ∪ (matePairs E cubic)) :
    cloneOwner F reg p.1 ≠ cloneOwner F reg p.2 ∧ cloneFactor F p.1 ≠ cloneFactor F p.2 := by
  have hpin : ∃ a b : TriVertex V, p.1=Sum.inl a ∧ p.2=Sum.inl b ∧ a≠b := by
    rcases Finset.mem_union.mp hp with ht|hm
    · obtain ⟨_,hneq,t,h₁,h₂⟩ := Finset.mem_filter.mp ht
      obtain ⟨a,ha,_⟩ := triangle_tag_at_pin E cubic p.1 t h₁
      obtain ⟨b,hb,_⟩ := triangle_tag_at_pin E cubic p.2 t h₂
      exact ⟨a,b,ha,hb,fun h=>hneq (ha.trans ((congrArg Sum.inl h).trans hb.symm))⟩
    · obtain ⟨_,hneq,e,h₁,h₂⟩ := Finset.mem_filter.mp hm
      obtain ⟨a,ha,_⟩ := mate_tag_at_pin E cubic p.1 e h₁
      obtain ⟨b,hb,_⟩ := mate_tag_at_pin E cubic p.2 e h₂
      exact ⟨a,b,ha,hb,fun h=>hneq (ha.trans ((congrArg Sum.inl h).trans hb.symm))⟩
  obtain ⟨a,b,ha,hb,hne⟩ := hpin
  rw [ha,hb]
  constructor
  · change (a,(0:Fin 4)) ≠ (b,0)
    exact fun h=>hne (congrArg Prod.fst h)
  · exact fun h=>hne (Sum.inl.inj h)

#print axioms tied_pairs_share_no_endpoint
#print axioms triangle_tied_fibre_exact
#print axioms distinct_source_tie_pairs
#print axioms exact_three_per_pin
end
end Paper5.HybridMainOnly
