import P5AlwaysSatOriginalPhysicalSparsePoly

/-! The sparse tests keep all real literal incidences and add exactly one
neutral-factor incidence for each clone, including the single b₀ copy. -/
namespace Paper5.AlwaysSatOriginal.Physical
open scoped BigOperators Classical

variable {V : Type*} [Fintype V]
variable (E : Finset (V×V)) (T : Finset V)

abbrev SparsePort := ClausePort E T ⊕ Port E T
abbrev SparseFactor := CloneFactor E T ⊕ Port E T

noncomputable def sparseOwner : SparsePort E T→Port E T
  | .inl w => portOwner E T w
  | .inr v => v

def sparseFactor : SparsePort E T→SparseFactor E T
  | .inl w => .inl (portFactor E T w)
  | .inr v => .inr v

def sparseMarked : V↪SparsePort E T :=
  ⟨fun v=>.inl (marked E T v),fun _ _ h=>(marked E T).injective (Sum.inl.inj h)⟩

noncomputable def sparse_var_fibre (v : Port E T) :
    {e : SparsePort E T // sparseOwner E T e=v} ≃
      {e : ClausePort E T // portOwner E T e=v} ⊕ Unit := by
  classical
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨w|w,hw⟩
    · exact .inl ⟨w,hw⟩
    · exact .inr ()
  · intro q
    rcases q with q|q
    · exact ⟨.inl q.val,q.property⟩
    · exact ⟨.inr v,rfl⟩
  · rintro ⟨w|w,hw⟩
    · rfl
    · exact Subtype.ext (congrArg Sum.inr hw.symm)
  · rintro (q|q) <;> rfl

theorem sparse_copy_degree (v : Port E T) :
    Nat.card {e : SparsePort E T // sparseOwner E T e=v}=
      if v=bonusZeroPort E T then 2 else 4 := by
  rw [Nat.card_congr (sparse_var_fibre E T v),Nat.card_sum]
  rw [physical_copy_degree,Nat.card_unique]
  split <;> rfl

theorem sparse_copy_degree_le (v : Port E T) :
    Nat.card {e : SparsePort E T // sparseOwner E T e=v}≤4 := by
  rw [sparse_copy_degree]
  split <;> decide

noncomputable def sparseClauseFibre (f : CloneFactor E T) :
    {e : SparsePort E T // sparseFactor E T e=.inl f} ≃ FactorFibre E T f :=
  { toFun := by
      rintro ⟨w|w,h⟩
      · exact ⟨w,Sum.inl.inj h⟩
      · cases h
    invFun := fun w=>⟨.inl w.val,congrArg Sum.inl w.property⟩
    left_inv := by
      rintro ⟨w|w,h⟩
      · rfl
      · cases h
    right_inv _ := rfl }

def sparseNeutralFibre (v : Port E T) :
    {e : SparsePort E T // sparseFactor E T e=.inr v} ≃ Unit :=
  { toFun _ := ()
    invFun _ := ⟨.inr v,rfl⟩
    left_inv := by
      rintro ⟨w|w,h⟩
      · cases h
      · have hv : v=w := (Sum.inr.inj h).symm
        subst w
        rfl
    right_inv _ := rfl }

theorem sparse_factor_degree (v : SparseFactor E T) :
    1≤Nat.card {e : SparsePort E T // sparseFactor E T e=v} ∧
      Nat.card {e : SparsePort E T // sparseFactor E T e=v}≤3 := by
  rcases v with v|v
  · rw [Nat.card_congr (sparseClauseFibre E T v)]
    exact factor_fibre_degree E T v
  · rw [Nat.card_congr (sparseNeutralFibre E T v),Nat.card_unique]
    decide

theorem sparse_owner_surj : Function.Surjective (sparseOwner E T) :=
  fun v=>⟨.inr v,rfl⟩

theorem sparse_port_count [DecidableEq V] (hC : ∀ v,GraphCutMoments.degree E v=3) :
    Fintype.card (SparsePort E T)=22*Fintype.card V+16*T.card+6 := by
  rw [Fintype.card_sum]
  exact (original_physical_sizes E T (fun _=>false) hC).2.2

theorem sparse_no_heavy (v : Port E T) :
    Nat.card {e : SparsePort E T // sparseOwner E T e=v}≤4 :=
  sparse_copy_degree_le E T v

#print axioms sparse_var_fibre
#print axioms sparse_copy_degree
#print axioms sparse_copy_degree_le
#print axioms sparse_factor_degree
#print axioms sparse_owner_surj
#print axioms sparse_port_count
#print axioms sparse_no_heavy
end Paper5.AlwaysSatOriginal.Physical