import P5AlwaysSatOriginalPhysicalCycle
import P5AlwaysSatOriginalCount

/-! The actual source implication-cycle formula and its count-preserving
projection, including the single b₀ copy that has no cycle clauses. -/
namespace Paper5.AlwaysSatOriginal.Physical
variable {V : Type*} [Fintype V]
variable (E : Finset (V×V)) (T : Finset V)

abbrev CloneFactor := Factor E T ⊕ Cycle E T

def originalCopies (s : V→Bool) (i : Factor E T) : Std.Sat.CNF.Clause (Port E T) :=
  List.ofFn (fun j : Fin ((template E T i).length) =>
    (⟨i,j⟩,(realLiteral s (⟨i,j⟩ : Port E T)).2))

noncomputable def cycleClause (p : Cycle E T) : Std.Sat.CNF.Clause (Port E T) :=
  [(p.val,false),(next E T p.val,true)]

noncomputable def clonedClause (s : V→Bool) : CloneFactor E T→Std.Sat.CNF.Clause (Port E T)
  | .inl i => originalCopies E T s i
  | .inr p => cycleClause E T p

noncomputable def cloneCNF (s : V→Bool) : Std.Sat.CNF (Port E T) :=
  (Finset.univ : Finset (CloneFactor E T)).toList.map (clonedClause E T s)

omit [Fintype V] in
@[simp] theorem originalCopies_length (s : V→Bool) (i : Factor E T) :
    (originalCopies E T s i).length=(clause E T s i).length := by
  rw [originalCopies,List.length_ofFn,literal_width_independent]

omit [Fintype V] in
theorem projection_of_original_clauses (s : V→Bool) (i : Factor E T) :
    (originalCopies E T s i).map (fun l=>((owner l.1 : Var T),l.2))=clause E T s i := by
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    have hh : k < (originalCopies E T s i).length := by simpa only [List.length_map] using hk
    rw [List.getElem_map]
    change ((owner ((originalCopies E T s i)[k]'hh).1),((originalCopies E T s i)[k]'hh).2) = _
    simp only [originalCopies,List.getElem_ofFn]
    apply Prod.ext
    · exact (realLiteral_owner s (⟨i,⟨k,by simpa only [List.length_map,
        originalCopies,List.length_ofFn] using hk⟩⟩ : Port E T)).symm
    · rfl

omit [Fintype V] in
theorem originalCopies_eval (s : V→Bool) (a : Var T→Bool) (i : Factor E T) :
    (originalCopies E T s i).eval (a ∘ owner) = (clause E T s i).eval a := by
  rw [← projection_of_original_clauses E T s i]
  simp only [Std.Sat.CNF.Clause.eval,List.any_map]
  rfl

theorem cycle_clause_sat_iff (a : Port E T→Bool) (p : Cycle E T) :
    (cycleClause E T p).eval a=true ↔ a p.val=true → a (next E T p.val)=true := by
  cases h : a p.val <;>
    simp [cycleClause,Std.Sat.CNF.Clause.eval,h]

theorem clone_sat_iff (s : V→Bool) (a : Port E T→Bool) :
    (cloneCNF E T s).Sat a ↔
      (∀ i,(originalCopies E T s i).eval a=true) ∧
      (∀ p : Cycle E T,a p.val=true → a (next E T p.val)=true) := by
  simp only [Std.Sat.CNF.sat_def,cloneCNF,Std.Sat.CNF.eval,List.all_map,Function.comp_def,
    List.all_eq_true,Finset.mem_toList,Finset.mem_univ,true_implies,Sum.forall,clonedClause,
    cycle_clause_sat_iff]

def lifted (a : Var T→Bool) : Port E T→Bool := a ∘ owner

noncomputable def representative (w : Var T) : Port E T :=
  Classical.choose (every_variable_has_port E T w)

omit [Fintype V] in
@[simp] theorem representative_owner (w : Var T) : owner (representative E T w)=w :=
  Classical.choose_spec (every_variable_has_port E T w)

noncomputable def collapsed (a : Port E T→Bool) : Var T→Bool :=
  fun w=>a (representative E T w)

omit [Fintype V] in
@[simp] theorem collapsed_lifted (a : Var T→Bool) :
    collapsed E T (lifted E T a)=a := by
  funext w
  simp [collapsed,lifted]

theorem lifted_collapsed_on_models (s : V→Bool) (a : Port E T→Bool)
    (ha : (cloneCNF E T s).Sat a) : lifted E T (collapsed E T a)=a := by
  funext p
  have h := (clone_sat_iff E T s a).mp ha
  apply rotates_constant_on_fibre E T a h.2
  exact representative_owner E T _

theorem lifted_sat_iff (s : V→Bool) (a : Var T→Bool) :
    (cloneCNF E T s).Sat (lifted E T a) ↔ (formula E T s).Sat a := by
  rw [clone_sat_iff,cnf_sat_all_clauses]
  simp [lifted,originalCopies_eval]

noncomputable def sourceModelEquiv (s : V→Bool) :
    {a : Var T→Bool // (formula E T s).Sat a} ≃
      {a : Port E T→Bool // (cloneCNF E T s).Sat a} where
  toFun a := ⟨lifted E T a.val,(lifted_sat_iff E T s a.val).mpr a.property⟩
  invFun a := ⟨collapsed E T a.val,(lifted_sat_iff E T s (collapsed E T a.val)).mp
    ((lifted_collapsed_on_models E T s a.val a.property).symm ▸ a.property)⟩
  left_inv a := Subtype.ext (collapsed_lifted E T a.val)
  right_inv a := Subtype.ext (lifted_collapsed_on_models E T s a.val a.property)

private theorem count_eq_model_card {W : Type*} [Fintype W] (F : Std.Sat.CNF W) :
    PinnedCNF.modelCount F=Nat.card {a : W→Bool // F.Sat a} := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  unfold PinnedCNF.modelCount
  congr 1
  ext a
  simp [Std.Sat.CNF.sat_def]

theorem cloned_modelCount_eq (s : V→Bool) :
    PinnedCNF.modelCount (cloneCNF E T s)=PinnedCNF.modelCount (formula E T s) := by
  rw [count_eq_model_card,count_eq_model_card]
  exact Nat.card_congr (sourceModelEquiv E T s).symm

theorem cloned_display_M7 (s : V→Bool) :
    PinnedCNF.modelCount (cloneCNF E T s) =
      2^(1+∑ v∈T,if s v then (1:ℕ) else 0)+PinnedCNF.modelCount (PinnedCNF.formula E s) := by
  rw [cloned_modelCount_eq,original_display_M7]

theorem cloned_count_parity (s : V→Bool) :
    PinnedCNF.modelCount (cloneCNF E T s)%2=PinnedCNF.modelCount (PinnedCNF.formula E s) := by
  rw [cloned_modelCount_eq,original_count_parity]

theorem cloned_all_signs_sat (s : V→Bool) :
    (cloneCNF E T s).Sat (lifted E T (assignment T s false false (fun _=>false))) :=
  (lifted_sat_iff E T s _).mpr (all_signs_sat E T s)

#print axioms projection_of_original_clauses
#print axioms originalCopies_eval
#print axioms cycle_clause_sat_iff
#print axioms clone_sat_iff
#print axioms lifted_collapsed_on_models
#print axioms lifted_sat_iff
#print axioms sourceModelEquiv
#print axioms cloned_modelCount_eq
#print axioms cloned_display_M7
#print axioms cloned_count_parity
#print axioms cloned_all_signs_sat
end Paper5.AlwaysSatOriginal.Physical