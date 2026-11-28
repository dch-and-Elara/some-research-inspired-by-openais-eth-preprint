import J9EndCoefficient

/-! The finite assignment splitting needed to compare the global
literal sum with the product of child sums. The split is indexed by
actual label fibers, not assumed independent duplicated assignments. -/

namespace J9End

open scoped BigOperators Classical
noncomputable section

variable {A G K : Type*} (label : A → G)

abbrev GroupBit (g : G) := {a : A // label a = g} → Bool

def groupBitsEquiv : (A → Bool) ≃ ((g : G) → GroupBit label g) where
  toFun x g p := x p.1
  invFun x p := x (label p) ⟨p,rfl⟩
  left_inv _ := rfl
  right_inv x := by
    funext g p
    obtain ⟨a,ha⟩ := p
    subst g
    rfl

variable [Fintype A] [Fintype G] [DecidableEq G] [CommSemiring K]

/-- Exact reindexing of the full Boolean cube. A factor can include the
source feature or a marked target; no nonlinear independence assumption
or approximation is used beyond depending only on its own fiber. -/
theorem group_product_as_global (factor : (g : G) → GroupBit label g → K) :
    (∑ x : A → Bool, ∏ g : G, factor g (fun p => x p.1)) =
      ∏ g : G, ∑ x : GroupBit label g, factor g x := by
  classical
  rw [Fintype.prod_sum]
  exact Fintype.sum_equiv (groupBitsEquiv label) _ _ (fun _ => rfl)

theorem product_one_marked (factor : G → K) (g : G) (marked : K) :
    ∏ t : G, (if t = g then marked else factor t) =
      marked * ∏ t ∈ (Finset.univ : Finset G).erase g, factor t := by
  classical
  let f := fun t => if t = g then marked else factor t
  have e := Finset.prod_erase_mul (Finset.univ : Finset G) f (Finset.mem_univ g)
  change _ = marked * _
  calc
    _ = (∏ t ∈ (Finset.univ : Finset G).erase g, f t) * f g := e.symm
    _ = _ := by
      rw [mul_comm, show f g = marked by simp [f]]
      congr 1
      exact Finset.prod_congr rfl fun t ht => if_neg (Finset.mem_erase.mp ht).1

theorem product_two_marked (factor : G → K) (src tgt : G) (hne : src ≠ tgt) (s t : K) :
    ∏ g : G, (if g = src then s else if g = tgt then t else factor g) =
      s * t * ∏ g ∈ ((Finset.univ : Finset G).erase src).erase tgt, factor g := by
  classical
  let f := fun g => if g = tgt then t else factor g
  have hmem : tgt ∈ (Finset.univ : Finset G).erase src :=
    Finset.mem_erase.mpr ⟨hne.symm,Finset.mem_univ _⟩
  rw [product_one_marked (fun g => if g = tgt then t else factor g) src s]
  change _ * (∏ g ∈ (Finset.univ : Finset G).erase src, f g) = _
  rw [← Finset.prod_erase_mul _ f hmem, show f tgt = t by simp [f]]
  have hprod : (∏ g ∈ ((Finset.univ : Finset G).erase src).erase tgt, f g) =
      ∏ g ∈ ((Finset.univ : Finset G).erase src).erase tgt, factor g :=
    Finset.prod_congr rfl fun g hg => if_neg (Finset.mem_erase.mp hg).1
  rw [hprod]
  ac_rfl

#print axioms group_product_as_global
#print axioms product_two_marked

end
end J9End

