import J7R9Size

/-!
# Width-four source input obtained from raw 3CNF

An original tautology or repeated literal does not produce duplicate
ports after the literal guard. Empty original clauses are treated
faithfully: their guard is a real unary clause.
-/

open Std.Sat
open scoped BigOperators

namespace J7R9SourceInput
open J7R9Clause J7R9Compiler J7R9Subdivision J7R9Size
variable {V : Type*} [DecidableEq V] [Fintype V]

noncomputable def H (F : CNF V) : CNF (Option V) := J6Guard.guardedFormula (clean F)

theorem no_duplicates (F : CNF V) :
    ∀ c ∈ H F, (c.map Prod.fst).Nodup := by
  intro c hc
  unfold H J6Guard.guardedFormula at hc
  rcases List.mem_append.mp hc with hc|hc
  · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    have hm : (List.map Prod.fst (List.map J6Guard.mapLit d)) =
        (d.map Prod.fst).map some := by
      simp [List.map_map,Function.comp_def,J6Guard.mapLit]
    rw [List.map_cons,hm]
    exact List.nodup_cons.mpr
      ⟨by simp,(clean_no_repeat hd).map (Option.some_injective V)⟩
  · obtain ⟨v,_hv,rfl⟩ := List.mem_map.mp hc
    simp

theorem nonempty_clauses (F : CNF V) :
    ∀ c ∈ H F, 0<c.length := by
  intro c hc
  unfold H J6Guard.guardedFormula at hc
  rcases List.mem_append.mp hc with hc|hc
  · obtain ⟨d,_hd,rfl⟩ := List.mem_map.mp hc
    simp
  · obtain ⟨v,_hv,rfl⟩ := List.mem_map.mp hc
    change 0<2
    decide

theorem width_four (F : CNF V) (h : ∀ c ∈ F, c.length≤3) :
    ∀ c ∈ H F, c.length≤4 :=
  J6Guard.width_le_four _ (clean_width 3 h)

/-- Actual repaired source input: no supplied count, width, or
all-zero raw tensor validity assumptions. This does not choose the
later polynomial packet layout or prove a bit-time construction. -/
theorem source_count_size [Nonempty V] (F : CNF V)
    (h : ∀ c ∈ F, c.length≤3) :
    Nat.card {x : Half (H F) → Bool // bipolarOK (H F) x}=1+PinnedCNF.modelCount F ∧
    J7R9Subdivision.bipolarOK (H F) (fun _ => false) ∧
    Fintype.card (Option V)+(H F).length≤Fintype.card (Half (H F)) ∧
    Fintype.card (Half (H F))≤16*(H F).length := by
  have hs := source_size (H F) 4 (guard_allOccur _) (nonempty_clauses F) (width_four F h)
  refine ⟨guarded_subdivision_count F,?_,hs.1,hs.2⟩
  change bipolarOK (H F) (lift (H F) (encode (H F) (fun _ => false)))
  rw [network_under_lift,encode_ok]
  exact J6Guard.all_zero_model (clean F)

#print axioms no_duplicates
#print axioms nonempty_clauses
#print axioms width_four
#print axioms source_count_size

end J7R9SourceInput

