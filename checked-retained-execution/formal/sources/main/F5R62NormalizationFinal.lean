import F5R62NormalizationAntichain
import F5R62PhysicalEmitVolume

/-! Guards for the four deletion rules actually stated in MAIN
3577–3579 and 3647–3653. This is the same emitted signed CNF,
not a differently generated normalized formula or a sorting routine. -/
namespace F5R62.Normalization
open F5R60 F5R61 F5R60.Ambient F5R62.PhysicalEmit
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {V E T : Type}

def HasTautologicalPair (r : Row V E T) : Prop :=
  ∃ x : PhysicalVar V E T, (⟨x,false⟩ : Signed V E T) ∈ r ∧
    (⟨x,true⟩ : Signed V E T) ∈ r

structure PrintedNoDeletion (F : CNF V E T) : Prop where
  rowsNodup : F.Nodup
  slotsNodup : ∀ r∈F, (rowVars r).Nodup
  width : ∀ r∈F, r.length=2 ∨ r.length=3
  supportAntichain : ∀ r∈F, ∀ s∈F, rowVars r ⊆ rowVars s → r=s

theorem PrintedNoDeletion.noRepeatedLiteral {F : CNF V E T} (C : PrintedNoDeletion F)
    (r : Row V E T) (m : r∈F) : r.Nodup :=
  List.Nodup.of_map F5R59.Literal.var (C.slotsNodup r m)

theorem PrintedNoDeletion.noTautology {F : CNF V E T} (C : PrintedNoDeletion F)
    (r : Row V E T) (m : r∈F) : ¬HasTautologicalPair r := by
  rintro ⟨x,neg,pos⟩
  have eq := List.inj_on_of_nodup_map (C.slotsNodup r m) neg pos rfl
  exact Bool.false_ne_true (congrArg F5R59.Literal.positive eq)

theorem PrintedNoDeletion.noSubsumption {F : CNF V E T} (C : PrintedNoDeletion F)
    (r s : Row V E T) (hr : r∈F) (hs : s∈F) (neq : r≠s) : ¬r ⊆ s := by
  intro sub
  exact neq (C.supportAntichain r hr s hs (signed_subset_implies_support_subset r s sub))

theorem printed_cleanup_has_no_trigger {F : CNF V E T} (C : PrintedNoDeletion F) :
    F.Nodup ∧
      (∀ r∈F, r.Nodup ∧ ¬HasTautologicalPair r ∧ (r.length=2 ∨ r.length=3)) ∧
      ∀ r∈F, ∀ s∈F, r≠s → ¬r ⊆ s := by
  exact ⟨C.rowsNodup,fun r h=>⟨C.noRepeatedLiteral r h,C.noTautology r h,C.width r h⟩,
    fun r hr s hs ne => C.noSubsumption r s hr hs ne⟩

section General
variable [DecidableEq V] [DecidableEq T] [Fintype V] [Fintype E] [Fintype T]

theorem actual_F1_source_normalization
    (G : RequestGraph V E T) (v : Listing V) (e : Listing E) (t : Listing T)
    (distinct : DistinctSourceEnds G) (incident : ∀ x, ∃ a, G.left a=x ∨ G.right a=x) :
    PrintedNoDeletion (f1ActualCNF G v e t) := by
  refine ⟨actual_F1_rows_have_no_duplicates G v e t distinct incident,?_,?_,?_⟩
  · intro r m
    exact (actual_F1_row_width_and_distinct G v e t incident r m).2
  · intro r m
    exact (actual_F1_row_width_and_distinct G v e t incident r m).1
  · intro r hr s hs sub
    exact actual_F1_support_antichain G v e t distinct incident r s hr hs sub

theorem actual_F1_normalization_preserves_printed_volume
    (G : RequestGraph V E T) (v : Listing V) (e : Listing E) (t : Listing T)
    (distinct : DistinctSourceEnds G) (incident : ∀ x, ∃ a, G.left a=x ∨ G.right a=x) :
    let K := printedK V E T
    let F := f1ActualCNF G v e t
    PrintedNoDeletion F ∧
      F.length=Fintype.card V+2*Fintype.card E+4*Fintype.card T+K+1 ∧
      literalCount F=3*K+2 :=
  ⟨actual_F1_source_normalization G v e t distinct incident,
    exact_f1_emitted_list_at_printed_sizes G v e t⟩
end General

theorem actual_ambient_F1_no_normalization_deletion
    {C U : Type} {n : ℕ} [DecidableEq C] [Fintype C]
    (S : F5R59.ClauseSystem C U) (k : F5R59.Vertex S ↪ Fin n) (B : SimpleGraph (Fin n))
    (v : Listing (Vertices n)) (e : Listing (Edge (paddedH S k) B)) (t : Listing (TripleClause S)) :
    PrintedNoDeletion (f1ActualCNF (requestGraph S k B) v e t) := by
  letI : Fintype (TripleClause S) := Fintype.ofFinite _
  exact actual_F1_source_normalization (requestGraph S k B) v e t
    (actual_ambient_ends_distinct S k B) (all_ambient_vertices_incident S k B)

#print axioms PrintedNoDeletion.noRepeatedLiteral
#print axioms PrintedNoDeletion.noTautology
#print axioms PrintedNoDeletion.noSubsumption
#print axioms printed_cleanup_has_no_trigger
#print axioms actual_F1_source_normalization
#print axioms actual_F1_normalization_preserves_printed_volume
#print axioms actual_ambient_F1_no_normalization_deletion
end F5R62.Normalization
