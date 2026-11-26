import P5FrontendG1NormalizationSplit
import Mathlib.Data.Finset.Powerset

/-! A finite executable check of the source's root rules. This constructs
the clause subsets and shared degrees, with no unbounded search or test
oracle. It is not a cost analysis or a reproduction of the branching tie break. -/
namespace Paper5.FrontendG1.Normalization
variable {W : Type*} [DecidableEq W]

def complementaryLits (C : ClauseSet W) : ClauseSet W :=
  C.filter fun l => (l.1,!l.2)∈C

theorem complementary_empty_iff (C : ClauseSet W) :
    complementaryLits C=∅ ↔ TautFree C := by
  rw [Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro hh w hT hF
    exact hh (w,true) (Finset.mem_filter.mpr ⟨hT,hF⟩)
  · intro hh l hL
    obtain ⟨ha,hb⟩ := Finset.mem_filter.mp hL
    rcases l with ⟨w,b⟩
    cases b with
    | false => exact hh w hb ha
    | true => exact hh w ha hb

def removeTaut (F : Family W) : Family W :=
  F.filter fun C => complementaryLits C=∅

theorem mem_removeTaut (F : Family W) (C : ClauseSet W) :
    C∈removeTaut F ↔ C∈F ∧ TautFree C := by
  simp [removeTaut,complementary_empty_iff]

def strictSubsets (F : Family W) (C : ClauseSet W) : Family W :=
  F.filter fun D => D ⊂ C

def normalizeExec (F : Family W) : Family W :=
  (removeTaut F).filter fun C => strictSubsets (removeTaut F) C = ∅

theorem normalizeExec_eq (F : Family W) : normalizeExec F=normalize F := by
  ext C
  simp only [normalizeExec,Finset.mem_filter,mem_removeTaut,mem_normalize,
    strictSubsets,Finset.eq_empty_iff_forall_notMem]
  constructor
  · rintro ⟨⟨hC,ht⟩,hm⟩
    refine ⟨hC,ht,?_⟩
    rintro ⟨D,hD,htD,hs⟩
    exact hm D ⟨⟨hD,htD⟩,hs⟩
  · rintro ⟨hC,ht,hn⟩
    refine ⟨⟨hC,ht⟩,?_⟩
    rintro D ⟨⟨hD,htD⟩,hs⟩
    exact hn ⟨D,hD,htD,hs⟩

def degSharedExec (F : Family W) (c : ℕ) (H : ClauseSet W) : ℕ :=
  (F.filter fun C => C.card=c ∧ H ⊆ C).card

theorem degSharedExec_eq (F : Family W) (c : ℕ) (H : ClauseSet W) :
    degSharedExec F c H = degShared F c H := by
  unfold degSharedExec degShared
  apply congrArg Finset.card
  ext C
  simp

-- All candidate H come from the actual current clauses' powersets.
def splitMenu (M : ℕ) (F : Family W) : Finset (ClauseSet W × ClauseSet W) :=
  F.biUnion fun C =>
    ((C.powerset.filter fun H => H≠∅ ∧ H≠C ∧
      M^(C.card-H.card) ≤ degSharedExec F C.card H).image fun H => (C,H))

theorem mem_splitMenu_iff (M : ℕ) (F : Family W) (C H : ClauseSet W) :
    (C,H)∈splitMenu M F ↔ C∈F ∧ H.Nonempty ∧ H ⊂ C ∧
      M^(C.card-H.card) ≤ degShared F C.card H := by
  simp only [splitMenu,Finset.mem_biUnion,Finset.mem_image,Finset.mem_filter,
    Finset.mem_powerset,Prod.mk.injEq,degSharedExec_eq,Finset.ssubset_iff_subset_ne,
    Finset.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨c,hc,h,⟨hle,hn,hh,hbound⟩,rfl,rfl⟩
    exact ⟨hc,hn,⟨hle,hh⟩,hbound⟩
  · rintro ⟨hc,hn,⟨hle,hh⟩,hb⟩
    exact ⟨C,hc,H,⟨hle,hn,hh,hb⟩,rfl,rfl⟩

theorem splitMenu_nonempty_iff (M : ℕ) (F : Family W) :
    (splitMenu M F).Nonempty ↔ SplitEligible M F := by
  constructor
  · rintro ⟨⟨C,H⟩,h⟩
    obtain ⟨hc,hn,hS,hb⟩ := (mem_splitMenu_iff M F C H).mp h
    exact ⟨C,hc,H,hn,hS,hb⟩
  · rintro ⟨C,hc,H,hn,hS,hb⟩
    exact ⟨(C,H),(mem_splitMenu_iff M F C H).mpr ⟨hc,hn,hS,hb⟩⟩

def sourceRootExec (M : ℕ) (F : Family W) : RootAction W :=
  let G := normalizeExec F
  if ∅∈G then .contradiction else if G=∅ then .noClauses
  else if splitMenu M G=∅ then .leaf G else .split

theorem sourceRootExec_eq (M : ℕ) (F : Family W) :
    sourceRootExec M F = sourceRoot M F := by
  classical
  have hne : splitMenu M (normalize F)≠∅ ↔ SplitEligible M (normalize F) :=
    Finset.nonempty_iff_ne_empty.symm.trans (splitMenu_nonempty_iff M (normalize F))
  by_cases hS : SplitEligible M (normalize F)
  · simp [sourceRootExec,sourceRoot,normalizeExec_eq,hS,hne.mpr hS]
  · have he : splitMenu M (normalize F)=∅ := by
      by_contra hm
      exact hS (hne.mp hm)
    simp [sourceRootExec,sourceRoot,normalizeExec_eq,hS,he]

theorem executable_unchanged_guarded [Fintype W] [Nonempty W] (E : Finset (W×W))
    (hS : OrientedSimple E) (sgn : W→Bool)
    (hD : ∀v,GraphCutMoments.degree E v≤3) (M : ℕ) (hM : 4<M) :
    sourceRootExec M (parsed (guardedFormula E sgn)) =
      .leaf (parsed (guardedFormula E sgn)) := by
  rw [sourceRootExec_eq,guarded_single_unchanged_leaf E hS sgn hD hM]

#print axioms complementary_empty_iff
#print axioms mem_removeTaut
#print axioms normalizeExec_eq
#print axioms degSharedExec_eq
#print axioms mem_splitMenu_iff
#print axioms splitMenu_nonempty_iff
#print axioms sourceRootExec_eq
#print axioms executable_unchanged_guarded
end Paper5.FrontendG1.Normalization