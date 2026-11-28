import J9LayoutTransferCompiler

/-! Arbitrary source-address alphabets, overlap and caching of other modes
do not change the literal selected singleton. This projects the one real
address; it does not postulate an isolated one-mode implementation. -/

namespace J9LayoutTransfer

open scoped BigOperators Classical
open LiteralPortCompiler
noncomputable section
variable {R K B : Type*} [Fintype R] [DecidableEq R] [CommRing K]
  [Fintype B] [DecidableEq B]

theorem selected_real_address (base : Port R → K) (kernel : Port R → B → K) (m : B) :
    MvPolynomial.coeff (Finsupp.single m 1)
      (completed (allRows (R:=R)) (fun _ p => base p) (fun _ p j => kernel p j)) =
      MvPolynomial.coeff β (rowCompiler base (fun p => kernel p m)) := by
  rw [rowCompiler, β, singleton_coeff, singleton_coeff]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  apply Finset.prod_congr rfl
  intro q _
  by_cases h : q = p <;> simp [portTerm,atPort,h]

/-- The exact physical singleton fact holds when other distinct modes
are present in the same contraction. -/
theorem singleton_overlapping_menu (base : Port R → K) (kernel : Port R → B → K) (m : B) :
    MvPolynomial.coeff (Finsupp.single m 1)
      (completed (allRows (R:=R)) (fun _ p => base p) (fun _ p j => kernel p j)) =
      ∑ p : Port R, kernel p m * (-1 + 2 * base (p.1,!p.2)) *
        ∏ r ∈ (Finset.univ : Finset R).erase p.1,
          TargetDerivative.equality (base (r,false)) (base (r,true)) := by
  rw [selected_real_address, singleton_native_rows]

#print axioms selected_real_address
#print axioms singleton_overlapping_menu
end
end J9LayoutTransfer

