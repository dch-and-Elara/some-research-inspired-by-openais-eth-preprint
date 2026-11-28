import F5R63SparsifyBranch
import F5R63SparsifyParameters

/-! Actual F1/F5 dispatch on the same source formula. The MAIN
conclusion is an unchanged root leaf after its true entrance test.
The D conclusion is its separate sparse-versus-parity branch test;
it is not a compiled D execution or a bound on its packing/recursion. -/
namespace F5R63.Sparsify
open F5R60 F5R61 F5R60.Ambient F5R62.PhysicalEmit F5R62.Normalization
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {V E T : Type}
variable [DecidableEq V] [DecidableEq T] [Fintype V] [Fintype E] [Fintype T]

theorem declared_size_is_actual_F1 (V E T : Type) [Fintype V] [Fintype E] [Fintype T] :
    Nat.card (PhysicalVar V E T)=printedK V E T+2 := by
  letI : Fintype (PrivatePos V E T) := privatePositionsFintype
  exact Nat.card_eq_fintype_card.trans (actual_declared_F1_variables V E T)

theorem actual_F1_density_at_most_two
    (G : RequestGraph V E T) (v : Listing V) (e : Listing E) (t : Listing T) :
    (f1ActualCNF G v e t).length ≤ 2*Nat.card (PhysicalVar V E T) := by
  have size := (exact_f1_emitted_list_at_printed_sizes G v e t).1
  change (f1ActualCNF G v e t).length =
    Fintype.card V+2*Fintype.card E+4*Fintype.card T+printedK V E T+1 at size
  rw [size,declared_size_is_actual_F1]
  unfold printedK
  omega

theorem actual_F1_printed_MAIN_unchanged_leaf
    (G : RequestGraph V E T) (v : Listing V) (e : Listing E) (t : Listing T)
    (distinct : DistinctSourceEnds G) (incident : ∀ x,∃ a,G.left a=x ∨ G.right a=x)
    (n20 : 20≤Nat.card (PhysicalVar V E T))
    (useSparse : 2≤sourceS (Nat.card (PhysicalVar V E T))) :
    let n := Nat.card (PhysicalVar V E T)
    let s := sourceS n
    let M := selectedSourceBase s
    validSourceIndex n s ∧
      (∀ a,validSourceIndex n a → a≤s) ∧ 2≤s ∧
      (successfulSourceExponent s (selectedSourceExponent s) ∧
        ∀ a<selectedSourceExponent s,¬successfulSourceExponent s a) ∧
      PrintedUnchangedLeaf (f1ActualCNF G v e t) M := by
  dsimp only
  have idx := sourceS_is_exact_largest_index (Nat.card (PhysicalVar V E T)) n20
  exact ⟨idx.1,idx.2,useSparse,printed_source_selects_first_success _,
    actual_F1_unchanged_leaf_at_threshold G v e t distinct incident _
      ((show (4:ℕ)≤16 by decide).trans (printed_selected_threshold_at_least_sixteen _))⟩

/-- Appendix D 363–369: the actual emitted clause count passes the
printed clause-network test with the actual number of declared variables. -/
theorem actual_F1_printed_D_clause_dispatch
    (G : RequestGraph V E T) (v : Listing V) (e : Listing E) (t : Listing T)
    (nu : 2≤sourceNu (Nat.card (PhysicalVar V E T))) :
    let F := f1ActualCNF G v e t
    let n := Nat.card (PhysicalVar V E T)
    F.length≤n*sourceNu n ∧ n+F.length≤3*n ∧ n+1=printedK V E T+3 := by
  dsimp only
  have m := actual_F1_density_at_most_two G v e t
  constructor
  · apply m.trans
    rw [Nat.mul_comm 2]
    exact Nat.mul_le_mul_left _ nu
  constructor
  · omega
  · rw [declared_size_is_actual_F1]

/-- The only eventual restriction here is MAIN's original s≥2/exhaustive
search gate. Its chosen threshold is already ≥16 once admitted,
independently of the graph size/packing and of all input signs. -/
theorem actual_F1_large_original_source_dispatch
    (G : RequestGraph V E T) (v : Listing V) (e : Listing E) (t : Listing T)
    (distinct : DistinctSourceEnds G) (incident : ∀ x,∃ a,G.left a=x ∨ G.right a=x)
    (large : (2:ℕ)^((2:ℕ)^20)<Nat.card (PhysicalVar V E T)) :
    let F := f1ActualCNF G v e t
    let n := Nat.card (PhysicalVar V E T)
    20≤n ∧ 2≤sourceS n ∧
      PrintedUnchangedLeaf F (selectedSourceBase (sourceS n)) ∧
      F.length≤n*sourceNu n ∧ n+F.length≤3*n ∧ n+1=printedK V E T+3 := by
  dsimp only
  let n := Nat.card (PhysicalVar V E T)
  obtain ⟨h20,hs⟩ := large_source_enters_sparsifier n large
  have nu : 2≤sourceNu n := (show (2:ℕ)≤3 by decide).trans (source_nu_at_least_three n h20)
  exact ⟨h20,hs,(actual_F1_printed_MAIN_unchanged_leaf G v e t distinct incident h20 hs).2.2.2.2,
    actual_F1_printed_D_clause_dispatch G v e t nu⟩

theorem actual_ambient_F5_large_original_source_dispatch
    {C U : Type} {m : ℕ} [DecidableEq C] [Fintype C]
    (S : F5R59.ClauseSystem C U) (k : F5R59.Vertex S ↪ Fin m) (B : SimpleGraph (Fin m))
    (v : Listing (Vertices m)) (e : Listing (Edge (paddedH S k) B)) (t : Listing (TripleClause S))
    (large : (2:ℕ)^((2:ℕ)^20)<m) :
    let F := f1ActualCNF (requestGraph S k B) v e t
    let n := Nat.card (PhysicalVar (Vertices m) (Edge (paddedH S k) B) (TripleClause S))
    20≤n ∧ 2≤sourceS n ∧
      PrintedUnchangedLeaf F (selectedSourceBase (sourceS n)) ∧
      F.length≤n*sourceNu n ∧ n+F.length≤3*n := by
  letI : Fintype (TripleClause S) := Fintype.ofFinite _
  have le : m≤Nat.card (PhysicalVar (Vertices m) (Edge (paddedH S k) B) (TripleClause S)) := by
    rw [declared_size_is_actual_F1,printedK,joined_vertices_card]
    omega
  have h := actual_F1_large_original_source_dispatch (requestGraph S k B) v e t
    (actual_ambient_ends_distinct S k B) (all_ambient_vertices_incident S k B) (large.trans_le le)
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩

#print axioms declared_size_is_actual_F1
#print axioms actual_F1_density_at_most_two
#print axioms actual_F1_printed_MAIN_unchanged_leaf
#print axioms actual_F1_printed_D_clause_dispatch
#print axioms actual_F1_large_original_source_dispatch
#print axioms actual_ambient_F5_large_original_source_dispatch
end F5R63.Sparsify