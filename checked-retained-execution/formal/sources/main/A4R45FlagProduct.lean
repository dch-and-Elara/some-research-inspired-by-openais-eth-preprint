import A4R45LiteralTables

/-! Identify the primitive completed zero-mode sum on the actual A4
sparse host with the literal signed predecessor register in A6. -/
namespace A4R45LiteralValue
open scoped BigOperators Polynomial
open Acquisition A4R45LiteralNetwork A4R45LiteralTables
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3300000
set_option maxRecDepth 1600

noncomputable section
variable {V₂ V₃ U C G : Type} [Fintype V₂] [Fintype V₃] [Fintype U] [Fintype C]
variable [LinearOrder G] [Fintype G] {a : ℕ}
variable {K : Type} [CommRing K]
local notation "W" => Wire V₂ V₃ U
local notation "N" => network (V₂:=V₂) (V₃:=V₃) (U:=U)

omit [Fintype V₂] [Fintype V₃] [Fintype U] [Fintype C] in
theorem eq_column_fibre (cols : Var V₂ V₃ U ≃ C) (X : W→Bool) (v : Var V₂ V₃ U) :
    (∀ i j : W, cols i.1=cols v → cols j.1=cols v → X i=X j) ↔
      X (v,false)=X (v,true) := by
  constructor
  · intro h
    exact h (v,false) (v,true) rfl rfl
  · intro h
    rintro ⟨i,b⟩ ⟨j,c⟩ hi hj
    have iv : i=v := cols.injective hi
    have jv : j=v := cols.injective hj
    subst i
    subst j
    cases b <;> cases c
    · rfl
    · exact h
    · exact h.symm
    · rfl

theorem actual_flags_product (cols : Var V₂ V₃ U ≃ C) (X Y : W→Bool) :
    (∏ v : Row V₂ V₃ U ⊕ Var V₂ V₃ U,
      J6R9PacketTiles.bit K (trueFlags v (fun p => Sum.elim Y X p.val))) =
        rowProduct (coverTables (K:=K)) (fun i => Y (i,true)) *
          equalityTensor (cols ∘ (Prod.fst : W→Var V₂ V₃ U)) X := by
  classical
  let f (v : Row V₂ V₃ U ⊕ Var V₂ V₃ U) : K :=
    J6R9PacketTiles.bit K (trueFlags v fun p => Sum.elim Y X p.val)
  have c (r : CoverRow V₂ V₃ U) : f (.inl (.inl r)) =
      coverTables r (fun j => Y (⟨r,j⟩,true)) :=
    actual_signed_flag_as_ring r _
  have u (v : Var V₂ V₃ U) : f (.inl (.inr v))=1 := rfl
  have col (v : Var V₂ V₃ U) :
      f (.inr v)=@ite K (∀ i j : W, cols i.1=cols v → cols j.1=cols v → X i=X j)
        (Classical.propDecidable _) 1 0 := by
    unfold f J6R9PacketTiles.bit
    change (if (X (v,false)==X (v,true)) then 1 else 0)=_
    by_cases h : X (v,false)=X (v,true)
    · have h' := (eq_column_fibre cols X v).2 h
      rw [if_pos (by simpa only [beq_iff_eq, Bool.coe_true] using h), if_pos h']
    · have h' := fun yes => h ((eq_column_fibre cols X v).1 yes)
      rw [if_neg (by simpa using h), if_neg h']
  change (∏ v,f v)=_
  rw [Fintype.prod_sum_type f,Fintype.prod_sum_type (fun v => f (.inl v))]
  simp only [c,u,Finset.prod_const_one,mul_one,rowProduct,equalityTensor]
  apply congrArg₂ (·*·) rfl
  apply Fintype.prod_equiv cols
  intro v
  exact col v

#print axioms eq_column_fibre
#print axioms actual_flags_product
end
end A4R45LiteralValue
