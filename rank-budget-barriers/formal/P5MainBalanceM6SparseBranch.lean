import P5MainBalanceM6SparseOccurrences

/-! An empty or constant supplied equation cannot short-circuit either
literal sparse witness. Each test has both accepting and rejecting
Boolean assignments. The neutral factors are not equations. -/
namespace P5MainBalance.M6.Sparse
open P5MainBalance P5MainBalance.M6 P5MainIterator
open scoped BigOperators Classical

variable {V : Type*}

theorem uncloned_nonconstant_tests (G : Finset (V×V)) (σ : V→Bool) (i : V⊕G) :
    (∃ x,validTest (unclonedTests G σ (.inl i) x)) ∧
      (∃ x,¬validTest (unclonedTests G σ (.inl i) x)) := by
  rcases i with v|e
  · refine ⟨⟨σ, (source_pin_even _ _).mpr rfl⟩,⟨fun w=> !(σ w),?_⟩⟩
    change ¬validTest (some (integerBit (!(σ v))+integerBit (σ v)))
    rw [source_pin_even]
    cases σ v <;> simp
  · refine ⟨⟨fun _=>true,(source_edge_even _ _).mpr (Or.inl rfl)⟩,⟨fun _=>false,?_⟩⟩
    change ¬validTest (some ((1+integerBit false)*(1+integerBit false)))
    rw [source_edge_even]
    simp

theorem cloned_nonconstant_tests (G : Finset (V×V)) (left right : G→Fin 4)
    (σ : V→Bool) (i : Direct.Factor G) :
    (∃ x,validTest (clonedTests G left right σ (.inl i) x)) ∧
      (∃ x,¬validTest (clonedTests G left right σ (.inl i) x)) := by
  rcases i with v|e|⟨v,j⟩
  · refine ⟨⟨fun w=>σ w.1, (source_pin_even _ _).mpr rfl⟩,⟨fun w=> !(σ w.1),?_⟩⟩
    change ¬validTest (some (integerBit (!(σ v))+integerBit (σ v)))
    rw [source_pin_even]
    cases σ v <;> simp
  · refine ⟨⟨fun _=>true,(source_edge_even _ _).mpr (Or.inl rfl)⟩,⟨fun _=>false,?_⟩⟩
    change ¬validTest (some ((1+integerBit false)*(1+integerBit false)))
    rw [source_edge_even]
    simp
  · let bad : V×Fin 4→Bool := fun w=>decide (w.2=j)
    refine ⟨⟨fun _=>false,(source_implication_even _ _).mpr (Or.inl rfl)⟩,⟨bad,?_⟩⟩
    change ¬validTest (some (integerBit (bad (v,j))*(1+integerBit (bad (v,j+1)))))
    rw [source_implication_even]
    have h : j+1≠j := by
      intro he
      exact (by decide : (1:Fin 4) ≠ 0) (add_left_cancel (he.trans (add_zero j).symm))
    simp [bad,h]

#print axioms uncloned_nonconstant_tests
#print axioms cloned_nonconstant_tests
end P5MainBalance.M6.Sparse
