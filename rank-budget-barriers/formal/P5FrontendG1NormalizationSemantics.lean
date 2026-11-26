import P5FrontendG1NormalizationCore
import Mathlib.Data.Finset.Max

/-! Normalization is genuine source CNF semantics, not an arbitrary
simplification receipt. In particular the same n declared variables are
used for all assignments before/after the transformation. -/
namespace Paper5.FrontendG1.Normalization
variable {W : Type*} [DecidableEq W]

def Holds (F : Family W) (a : W→Bool) : Prop :=
  ∀ C∈F, ∃ l∈C, a l.1=l.2

theorem source_clause_holds (L : Std.Sat.CNF.Clause W) (a : W→Bool) :
    L.eval a=true ↔ ∃ l∈L.toFinset, a l.1=l.2 := by
  simp [Std.Sat.CNF.Clause.eval,List.any_eq_true]

theorem parsed_holds (f : Std.Sat.CNF W) (a : W→Bool) :
    Holds (parsed f) a ↔ f.Sat a := by
  rw [Std.Sat.CNF.sat_def]
  simp only [Std.Sat.CNF.eval,List.all_eq_true,source_clause_holds]
  constructor
  · intro h L hL
    exact h _ ((mem_parsed f _).mpr ⟨L,hL,rfl⟩)
  · intro h C hC
    obtain ⟨L,hL,rfl⟩ := (mem_parsed f C).mp hC
    exact h L hL

theorem normalize_preserves_holds (F : Family W) (a : W→Bool) :
    Holds (normalize F) a ↔ Holds F a := by
  classical
  constructor
  · intro h C hC
    by_cases hTc : TautFree C
    · let S := F.filter fun D => TautFree D ∧ D ⊆ C
      have hCS : C∈S := Finset.mem_filter.mpr ⟨hC,hTc,Finset.Subset.refl _⟩
      obtain ⟨D,hDS,hmin⟩ := S.exists_min_image Finset.card ⟨C,hCS⟩
      obtain ⟨hDF,hDt,hDC⟩ := Finset.mem_filter.mp hDS
      have hDn : D∈normalize F := by
        refine (mem_normalize F D).mpr ⟨hDF,hDt,?_⟩
        rintro ⟨B,hBF,hBt,hBD⟩
        exact (not_lt_of_ge (hmin B (Finset.mem_filter.mpr
          ⟨hBF,hBt,hBD.subset.trans hDC⟩))) (Finset.card_lt_card hBD)
      obtain ⟨l,hl,he⟩ := h D hDn
      exact ⟨l,hDC hl,he⟩
    · simp only [TautFree,not_forall,not_not] at hTc
      obtain ⟨w,hT,hF⟩ := hTc
      cases ha : a w with
      | false => exact ⟨(w,false),hF,ha⟩
      | true => exact ⟨(w,true),hT,ha⟩
  · intro h C hC
    exact h C ((mem_normalize F C).mp hC).1

noncomputable def familyCount [Fintype W] (F : Family W) : ℕ := by
  classical
  exact (Finset.univ.filter fun a : W→Bool => Holds F a).card

theorem parsed_count [Fintype W] (f : Std.Sat.CNF W) :
    familyCount (parsed f)=PinnedCNF.modelCount f := by
  classical
  unfold familyCount PinnedCNF.modelCount
  apply congrArg Finset.card
  ext a
  simp [parsed_holds,Std.Sat.CNF.sat_def]

theorem normalized_count [Fintype W] (f : Std.Sat.CNF W) :
    familyCount (normalize (parsed f))=PinnedCNF.modelCount f := by
  classical
  rw [←parsed_count]
  unfold familyCount
  apply congrArg Finset.card
  ext a
  simp [normalize_preserves_holds]

#print axioms source_clause_holds
#print axioms parsed_holds
#print axioms normalize_preserves_holds
#print axioms parsed_count
#print axioms normalized_count
end Paper5.FrontendG1.Normalization