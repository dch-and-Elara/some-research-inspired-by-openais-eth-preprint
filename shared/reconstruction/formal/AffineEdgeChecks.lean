import AffineEdgeOrbitResults
import Mathlib.FieldTheory.Finite.GaloisField

open scoped Polynomial
open AffineEdge

section

variable {ι F : Type*} [Fintype ι] [Field F]

example {sites : Fin 2 → F} {C : Matrix ι (Word 2) F} {P : Word 2 → Word 2 → F[X]}
    (hi : Function.Injective sites) (hn : ∀ t, sites t ≠ 0)
    (hp : PairedCondition sites C 0 P) : 5 ≤ C.rank :=
  paired_rank_lower (by decide) hi hn hp

example {sites : Fin 3 → F} {C : Matrix ι (Word 3) F} {P : Word 3 → Word 3 → F[X]}
    (hi : Function.Injective sites) (hn : ∀ t, sites t ≠ 0)
    (hp : PairedCondition sites C 1 P) : 7 ≤ C.rank :=
  paired_rank_lower (by decide) hi hn hp

example {sites : Fin 4 → F} {C : Matrix ι (Word 4) F} {P : Word 4 → Word 4 → F[X]}
    (hi : Function.Injective sites) (hn : ∀ t, sites t ≠ 0)
    (hp : PairedCondition sites C 2 P) : 8 ≤ C.rank :=
  paired_rank_lower (by decide) hi hn hp

end

example (sites : Fin 2 → ℚ) : (Orbit.zeroEncoder (F := ℚ) 2 (Fin 2)).rank = 6 :=
  Orbit.zeroEncoder_rank 2 2 sites

example (sites : Fin 2 → ℚ) (hi : Function.Injective sites) (hn : ∀ t, sites t ≠ 0) :
    (Orbit.boundaryEncoder (F := ℚ) 2).rank = 6 :=
  (Orbit.boundaryEncoder_attains sites (by decide) hi hn).2

section

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

-- A positive-degree instance with all three nonzero sites in characteristic two.
example :
    ∃ sites : Fin 3 → GaloisField 2 2, Function.Injective sites ∧ (∀ t, sites t ≠ 0) ∧
      (∃ P, PairedCondition sites (binaryEncoder 3) 1 P) ∧
      (binaryEncoder (F := GaloisField 2 2) 3).rank = 7 := by
  classical
  let K := GaloisField 2 2
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 2 (by decide)
  letI : Unique {x : K // x = 0} := ⟨⟨0,rfl⟩, fun x => Subtype.ext x.property⟩
  have hz : Fintype.card {x : K // x = 0} = 1 := Fintype.card_unique
  have hn : Fintype.card {x : K // x ≠ 0} = 3 := by
    rw [Fintype.card_subtype_compl (fun x : K => x = 0), hcard, hz]
  let e : {x : K // x ≠ 0} ≃ Fin 3 := (Fintype.equivFin _).trans (finCongr hn)
  let sites (t : Fin 3) := (e.symm t).val
  have hi : Function.Injective sites := Subtype.val_injective.comp e.symm.injective
  have hn (t : Fin 3) : sites t ≠ 0 := (e.symm t).property
  exact ⟨sites, hi, hn, binaryEncoder_attains sites (by decide) hi hn⟩

end

#print axioms affine_test_of_paired
#print axioms centerCondition_of_paired
#print axioms edge_count
#print axioms rank_lower_of_centerCondition
#print axioms paired_rank_lower
#print axioms paired_iff_polynomial_affine
#print axioms rowSystem_of_affine
#print axioms reconstruct_matrix_of_rowSystems
#print axioms binaryEncoder_binary
#print axioms binaryEncoder_attains
#print axioms Orbit.orbitwise_zero_rank_lower
#print axioms Orbit.zeroEncoder_rank
#print axioms Orbit.orbitwise_boundary_rank_lower
#print axioms Orbit.boundaryEncoder_attains
#print axioms Orbit.zero_rank_ratio
#print axioms Orbit.boundary_ratio_limit
