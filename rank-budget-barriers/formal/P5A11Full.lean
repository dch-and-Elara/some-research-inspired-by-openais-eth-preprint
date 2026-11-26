import P5A11Layer
import P5A11FieldTransport

/-! The full stated sum-by-precision-layer determinant bound (A.11).
Distinct residual centers and invertible residual scales are necessary
for this transport, unlike the more general lower bound (A.10). -/
namespace Paper5
open scoped BigOperators Polynomial
open Polynomial Matrix

theorem field_determinant_budget_indexed {K I T : Type*} [Field K] [Fintype I]
    [DecidableEq I] [Fintype T] (A : Matrix I I K[X]) (t : T→K)
    (ht : Function.Injective t) (k : T→ℕ) (hreg : A.det≠0) :
    (∑ u, (Fintype.card I*k u - RankBudget.jetLength A (t u) (k u))) ≤ A.det.natDegree := by
  classical
  let s := Finset.univ.image t
  let e : T ≃ s := Equiv.ofBijective (fun u => ⟨t u,Finset.mem_image.mpr ⟨u,Finset.mem_univ u,rfl⟩⟩)
    ⟨fun u v h => ht (congrArg Subtype.val h),fun a => by
      obtain ⟨u,_,hu⟩ := Finset.mem_image.mp a.property
      exact ⟨u,Subtype.ext hu⟩⟩
  let k' : K→ℕ := fun x => if h : x∈s then k (e.symm ⟨x,h⟩) else 0
  have hke (u : T) : k' (t u)=k u := by
    dsimp only [k']
    have h : t u ∈ s := (e u).property
    rw [dif_pos h]
    exact congrArg k (e.symm_apply_apply u)
  have h := RankBudget.jetDefectLeDetDegree A s k' hreg
  rw [←Finset.sum_coe_sort s (fun x => Fintype.card I*k' x-RankBudget.jetLength A x (k' x))] at h
  have he := Fintype.sum_equiv e
    (fun u => (Fintype.card I*k u - RankBudget.jetLength A (t u) (k u)))
    (fun a : s => (Fintype.card I*k' a.val - RankBudget.jetLength A a.val (k' a.val))) (fun u => by
      change Fintype.card I*k u - RankBudget.jetLength A (t u) (k u) =
        Fintype.card I*k' (t u) - RankBudget.jetLength A (t u) (k' (t u))
      rw [hke])
  exact he.trans_le h

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
variable {T : Type*} [Fintype T]

theorem a11_full {N : ℕ}
    (π : R) (hπ : π≠0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (t α : T→R) (P k : T→ℕ)
    (ht : Function.Injective ((IsLocalRing.residue R) ∘ t))
    (hα : ∀ u, IsUnit (α u))
    (A : Matrix (Fin N) (Fin N) R[X])
    (hreg : (A.map (Polynomial.mapRingHom (IsLocalRing.residue R))).det≠0) :
    (∑ u, Module.length R ((Fin N→LocalJet π (P u) (k u)) ⧸
      LinearMap.range (localMul A π (t u) (α u) (P u) (k u)))) ≤
    (↑(∑ j ∈ Finset.range (Finset.univ.sup P),
      min (A.map (Polynomial.mapRingHom (IsLocalRing.residue R))).det.natDegree
        (N * ∑ u ∈ Finset.univ.filter (fun u => j<P u),k u)) : ENat) := by
  let ρ := IsLocalRing.residue R
  let B := A.map (Polynomial.mapRingHom ρ)
  let d : T→ℕ := fun u => N*k u-RankBudget.jetLength B (ρ (t u)) (k u)
  have htotal : (∑ u,d u)≤B.det.natDegree := by
    simpa only [Fintype.card_fin] using field_determinant_budget_indexed B (ρ ∘ t) ht k hreg
  have hd (u : T) : ((localCoefficientMatrix A (t u) (α u) (k u)).map ρ).rank =
      RankBudget.jetLength B (ρ (t u)) (k u) := by
    rw [localCoefficientMatrix_map]
    exact local_coeff_rank_eq_field_jet B (ρ (t u)) (ρ (α u))
      ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (hα u)) (k u)
  refine precision_layer_budget P k d N B.det.natDegree (fun u => Nat.sub_le _ _) htotal _ ?_
  intro u
  have hu := real_jet_coker_le A π (t u) (α u) (P u) (k u) hπ hmax
  rw [Fintype.card_fin,hd] at hu
  exact hu

#print axioms field_determinant_budget_indexed
#print axioms a11_full
end Paper5
