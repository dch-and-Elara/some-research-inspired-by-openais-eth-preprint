import P5A11Full

/-! Stated common-precision consequence of the determinant bound. -/
namespace Paper5
open scoped BigOperators Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
variable {T : Type*} [Fintype T]

theorem a11_common_precision {N : ℕ}
    (π : R) (hπ : π≠0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (t α : T→R) (P : ℕ) (k : T→ℕ)
    (ht : Function.Injective ((IsLocalRing.residue R) ∘ t))
    (hα : ∀ u, IsUnit (α u))
    (A : Matrix (Fin N) (Fin N) R[X])
    (hreg : (A.map (Polynomial.mapRingHom (IsLocalRing.residue R))).det≠0) :
    (∑ u, Module.length R ((Fin N→LocalJet π P (k u)) ⧸
      LinearMap.range (localMul A π (t u) (α u) P (k u)))) ≤
    ((P*(A.map (Polynomial.mapRingHom (IsLocalRing.residue R))).det.natDegree:ℕ) : ENat) := by
  refine (a11_full π hπ hmax t α (fun _ => P) k ht hα A hreg).trans ?_
  apply ENat.coe_le_coe.mpr
  let U := Finset.univ.sup (fun _ : T => P)
  let D := (A.map (Polynomial.mapRingHom (IsLocalRing.residue R))).det.natDegree
  have hU : U≤P := Finset.sup_le (fun _ _ => le_rfl)
  calc
    (∑ j ∈ Finset.range U, min D (N * ∑ u ∈ Finset.univ.filter (fun (_ : T) => j<P),k u))
       ≤ ∑ _j ∈ Finset.range U,D := Finset.sum_le_sum fun _ _ => min_le_left _ _
    _ = U*D := by simp
    _ ≤ P*D := Nat.mul_le_mul_right D hU

#print axioms a11_common_precision
end Paper5
