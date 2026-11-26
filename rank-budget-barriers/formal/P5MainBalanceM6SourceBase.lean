import P5MainBalanceM6PointReads
import P5MainBalanceM6Mix

/-! The actual printed operator fixes the kernel of the actual
exceptional reads. Combining with place/read transport discharges the
source group evaluator's base-invariance premise. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator
open scoped BigOperators Classical

private theorem fixed_combination {S T : Type*} [Fintype S] [Fintype T]
    (M : Matrix S S ℚ) (weight : T→ℚ) (row : T→S→ℚ)
    (h : ∀ r,weight r=0 ∨ M.mulVec (row r)=row r) :
    M.mulVec (∑ r,weight r • row r)=∑ r,weight r • row r := by
  rw [Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Matrix.mulVec_smul]
  rcases h r with hr|hr
  · simp [hr]
  · rw [hr]

section Generic
variable {O : Type*} (D : O→Type*) [Fintype O] [∀ o,Fintype (D o)]

theorem spectral_fixes_all_zero_reads (keep : ℕ→Prop) (M : Matrix (OrbitSlots D) (OrbitSlots D) ℚ)
    (h : ∀ r : OrbitSlots D,¬keep (boolWeight r.2) → M.mulVec (qOrbitRow D r)=qOrbitRow D r)
    (ζ : OrbitSlots D→ℚ) (hζ : ∀ r : Exceptional D keep,qRead D ζ r.val=0) :
    M.mulVec ζ=ζ := by
  let α (r : OrbitSlots D) := qRead D ζ r/qNorm D r
  have hζ' : (∑ r,α r • qOrbitRow D r)=ζ := qRead_recover D ζ
  have hName : ∀ r : OrbitSlots D,α r=0 ∨ M.mulVec (qOrbitRow D r)=qOrbitRow D r := by
    intro r
    by_cases k : keep (boolWeight r.2)
    · left
      exact (congrArg (fun y=>y/qNorm D r) (hζ ⟨r,k⟩)).trans (zero_div _)
    · exact Or.inr (h r k)
  exact (congrArg M.mulVec hζ'.symm).trans
    ((fixed_combination M α (qOrbitRow D) hName).trans hζ')

end Generic

variable {E W F Copy I B : Type*} [Fintype E] [Fintype W] [Fintype Copy]
  [Fintype I] [Fintype B] [LinearOrder B]


private theorem mulVec_same_fintype {S : Type*} (F G : Fintype S)
    (M : Matrix S S ℚ) (ζ : S→ℚ) :
    @Matrix.mulVec S S ℚ _ F M ζ=@Matrix.mulVec S S ℚ _ G M ζ := by
  rw [Subsingleton.elim F G]

set_option maxHeartbeats 7400000 in
theorem printedMix_actual_reads (A R : ℕ) :
    FixesExceptionalReads (outsideInterval A R) (printedMix A R : Mix Copy I B) := by
  intro ζ hζ
  let D := CoordFamily (Copy:=Copy) (I:=I) (B:=B)
  let S := OrbitSlots D
  let M : Mix Copy I B := printedMix A R
  let F : Fintype S := inferInstanceAs (Fintype (Slt Copy I B))
  let G : Fintype S :=
    @Sigma.instFintype (CopyOrbit Copy I B) (fun o=>D o→Bool)
      (fun o=>@Pi.instFintype (D o) (fun _=>Bool)
        (fun _ _=>Classical.propDecidable _) (inferInstanceAs (Fintype (CoordFamily o)))
        (fun _=>inferInstance))
      inferInstance
  have h (r : S) (hr : ¬outsideInterval A R (boolWeight r.2)) :
      @Matrix.mulVec S S ℚ _ G M (qOrbitRow D r)=qOrbitRow D r := by
    exact (mulVec_same_fintype G F M (qOrbitRow D r)).trans
      (printedMix_fixed_on_kept A R r (not_not.mp hr))
  have he : @Matrix.mulVec S S ℚ _ G M ζ=ζ :=
    spectral_fixes_all_zero_reads D (outsideInterval A R) M h ζ hζ
  exact (mulVec_same_fintype F G M ζ).trans he

theorem printed_source_base_invariant (L : SourceLayout E W F Copy I B) (A R : ℕ) :
    ActualBaseInvariant (outsideInterval A R) L (printedMix A R) :=
  placed_read_implements_base (outsideInterval A R) L (printedMix A R) (printedMix_actual_reads A R)

#print axioms spectral_fixes_all_zero_reads
#print axioms printedMix_actual_reads
#print axioms printed_source_base_invariant
end P5MainBalance.M6
