import P5FrontendG1NormalizationSplit
import P5FrontendG1NormalizationSemantics
import P5NativeEntrySparsify

/-! The guarded G1 family on the actual width-two source schedule. Both
exhaustive-search guards remain visible. The count is from the literal
unchanged family, not a claim about the subsequent implementation. -/
namespace Paper5.FrontendG1.Normalization
open Paper5.NativeEntry

def sourceM (s : ℕ) (hs : 2≤s) : ℕ := 2^(sparExponent s hs)

theorem actual_source_M_first_success (s : ℕ) (hs : 2≤s) :
    (4≤sourceM s hs ∧ 4*Nat.clog 2 (4*4*sourceM s hs)*s≤sourceM s hs) ∧
    ∀ j<sparExponent s hs, ¬(4≤2^j ∧ 4*Nat.clog 2 (4*4*2^j)*s≤2^j) := by
  have h := spar_first_success s hs
  exact ⟨(spar_exact_guard _ _).mp h.1,fun j hj hG => h.2 j hj ((spar_exact_guard _ _).mpr hG)⟩

theorem actual_source_s_is_printed {n : ℕ} (hn : 20≤n) :
    printedGroups n=⌊Real.sqrt (sourceLambda n:ℝ)/(sourceNu n:ℝ)^2⌋₊ :=
  printedGroups_literal (nu_pos (by omega))

theorem actual_source_M_gt_four (s : ℕ) (hs : 2≤s) :
    4<sourceM s hs := by
  obtain ⟨hj,hm⟩ := (spar_first_success s hs).1
  have hmul : 4*(4+sparExponent s hs)*s≥4*6*2 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 4 (by omega)) hs
  unfold sourceM
  omega

inductive GuardedDispatch (V : Type*)
  | exhaustive
  | sparsifier (outcome : RootAction (GuardVar V))

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def printedGuardedDispatch (E : Finset (V×V)) (sgn : V→Bool) :
    GuardedDispatch V :=
  let n := Fintype.card (GuardVar V)
  if 20≤n then
    if hs : 2≤printedGroups n then
      .sparsifier (sourceRoot (sourceM (printedGroups n) hs) (parsed (guardedFormula E sgn)))
    else .exhaustive
  else .exhaustive

theorem printed_guarded_source_leaf [Nonempty V] (E : Finset (V×V)) (hS : OrientedSimple E)
    (sgn : V→Bool) (hD : ∀v, GraphCutMoments.degree E v≤3)
    (hSmall : 20≤Fintype.card (GuardVar V))
    (hs : 2≤printedGroups (Fintype.card (GuardVar V))) :
    printedGuardedDispatch E sgn = .sparsifier (.leaf (parsed (guardedFormula E sgn))) := by
  simp only [printedGuardedDispatch,hSmall,if_true,dif_pos hs]
  rw [guarded_single_unchanged_leaf E hS sgn hD (actual_source_M_gt_four _ hs)]

/- Both real CNFs have exactly one model precisely on the sign covers.
The guarded leaf preserves every original variable and every clause. -/
omit [DecidableEq V] in
theorem original_guarded_and_raw_same_count (E : Finset (V×V)) (sgn : V→Bool) :
    PinnedCNF.modelCount (guardedFormula E sgn)=PinnedCNF.modelCount (PinnedCNF.formula E sgn) := by
  classical
  rw [guarded_count_indicator,PinnedCNF.count_eq_indicator]

omit [DecidableEq V] in
theorem guarded_count_one_iff_no_raw_edge (E : Finset (V×V)) (sgn : V→Bool) :
    PinnedCNF.modelCount (guardedFormula E sgn)=1 ↔ survivingEdges E sgn=∅ := by
  rw [original_guarded_and_raw_same_count,raw_count_one_iff_no_edge]

theorem normalized_raw_count_one_iff (E : Finset (V×V)) (sgn : V→Bool) :
    familyCount (normalize (parsed (PinnedCNF.formula E sgn)))=1 ↔ survivingEdges E sgn=∅ := by
  rw [normalized_count,raw_count_one_iff_no_edge]

theorem printed_guarded_source_leaf_and_count_one [Nonempty V]
    (E : Finset (V×V)) (hS : OrientedSimple E) (sgn : V→Bool)
    (hD : ∀v,GraphCutMoments.degree E v=3)
    (hSmall : 20≤Fintype.card (GuardVar V))
    (hs : 2≤printedGroups (Fintype.card (GuardVar V)))
    (hCover : PinnedCNF.AllEdges E sgn) :
    printedGuardedDispatch E sgn = .sparsifier (.leaf (parsed (guardedFormula E sgn))) ∧
    Fintype.card (GuardVar V)=2*Fintype.card V ∧
    2*(parsed (guardedFormula E sgn)).card=7*Fintype.card V ∧
    familyCount (parsed (guardedFormula E sgn))=1 := by
  refine ⟨printed_guarded_source_leaf E hS sgn (fun v=>(hD v).le) hSmall hs,
    guarded_variable_card,guarded_cubic_clause_card E hS sgn hD,?_⟩
  rw [parsed_count]
  exact (guarded_count_one_iff_no_raw_edge E sgn).2 ((surviving_empty_iff E sgn).2 hCover)

omit [DecidableEq V] in
theorem source_canonical_oriented_simple [LinearOrder V] (G : V→V→Prop) :
    OrientedSimple (PinnedCNF.edgesOf G) := by
  classical
  intro e hE hS
  have hh : e.1<e.2 := (Finset.mem_filter.mp hE).2.1
  have hhh : e.2<e.1 := (Finset.mem_filter.mp hS).2.1
  exact lt_asymm hh hhh

universe u

/-- A uniform threshold in the original (undoubled) vertex size, valid for
every supplied simple subcubic graph and every sign word thereafter. -/
theorem eventual_printed_guarded_source_leaf :
    ∃ N₀ : ℕ, ∀ {U : Type u} [Fintype U] [DecidableEq U] [Nonempty U]
      (E : Finset (U×U)), OrientedSimple E →
      (∀ v, GraphCutMoments.degree E v≤3) → N₀≤Fintype.card U →
      ∀ sgn : U→Bool, printedGuardedDispatch E sgn =
        .sparsifier (.leaf (parsed (guardedFormula E sgn))) := by
  obtain ⟨n₀,hn₀⟩ := eventual_prelim_guard
  refine ⟨max 20 n₀,?_⟩
  intro U _ _ _ E hs hd hn w
  have h20 := (le_max_left 20 n₀).trans hn
  have hx := (le_max_right 20 n₀).trans hn
  have hCard := guarded_variable_card (V:=U)
  exact printed_guarded_source_leaf E hs w hd (by omega) (hn₀ _ (by omega))

#print axioms actual_source_M_first_success
#print axioms actual_source_s_is_printed
#print axioms actual_source_M_gt_four
#print axioms printed_guarded_source_leaf
#print axioms original_guarded_and_raw_same_count
#print axioms guarded_count_one_iff_no_raw_edge
#print axioms normalized_raw_count_one_iff
#print axioms printed_guarded_source_leaf_and_count_one
#print axioms source_canonical_oriented_simple
#print axioms eventual_printed_guarded_source_leaf
end Paper5.FrontendG1.Normalization