import P5A11SharpAllocation
import P5A11SharpDegree
import P5A11Layer

/-! Realized sharp examples on every original distinct-residue
precision list, including zero precision and zero degree. The
top-d slots are genuinely selected for all layers at once. -/
namespace Paper5
open Polynomial Matrix
open scoped BigOperators Polynomial Classical

variable {R T : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [Fintype T]

private theorem nat_mul_min (N d c : ℕ) : N*min d c=min (N*d) (N*c) := by
  by_cases h : d≤c
  · rw [min_eq_left h,min_eq_left (Nat.mul_le_mul_left N h)]
  · have h' : c≤d := (lt_of_not_ge h).le
    rw [min_eq_right h',min_eq_right (Nat.mul_le_mul_left N h')]

set_option maxHeartbeats 13000000 in
theorem a11_distinct_residue_grade_sharp (N : ℕ) (π : R) (hπ : π≠0)
    (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (t α : T→R) (P k : T→ℕ)
    (ht : Function.Injective ((IsLocalRing.residue R)∘t))
    (hα : ∀ u,IsUnit (α u)) (d : ℕ) (hd : d≤∑u,k u) :
    ∃ l : T→ℕ, (∀ u,l u≤k u) ∧ (∑u,l u)=d ∧
      ∃ A : Matrix (Fin N) (Fin N) R[X],
        A=sharpMatrix t l ∧ (∀ i j,(A i j).natDegree≤d) ∧
        (A.map (Polynomial.mapRingHom (IsLocalRing.residue R))).det≠0 ∧
        (A.map (Polynomial.mapRingHom (IsLocalRing.residue R))).det.natDegree=N*d ∧
        (∑ u,Module.length R ((Fin N→LocalJet π (P u) (k u)) ⧸
          LinearMap.range (localMul A π (t u) (α u) (P u) (k u)))) =
          (↑(∑ j∈Finset.range (Finset.univ.sup P),
            min (N*d) (N*(∑ u∈Finset.univ.filter (fun u=>j<P u),k u))) : ENat) := by
  letI : LinearOrder T := LinearOrder.lift' (Fintype.equivFin T) (Fintype.equivFin T).injective
  obtain ⟨l,hL,hSum,hLayer⟩ := also_exists_sharp_slots P k d hd
  let A : Matrix (Fin N) (Fin N) R[X] := sharpMatrix t l
  refine ⟨l,hL,hSum,A,rfl,?_,?_,?_,?_⟩
  · intro i j
    by_cases h : i=j
    · subst j
      simp [A,sharpMatrix,sharpScalar_degree,hSum]
    · simp [A,sharpMatrix,h]
  · exact (sharp_residue_det_monic (I:=Fin N) t l).ne_zero
  · have he := sharp_residue_det_degree (I:=Fin N) t l
    rw [Fintype.card_fin,hSum] at he
    exact he
  · calc
      _ = ∑ u, ((N*l u*P u:ℕ):ENat) := by
        apply Finset.sum_congr rfl
        intro u _
        have he := sharp_local_cokernel_exact (I:=Fin N) π hπ hmax t α P k l ht hα u (hL u)
        rw [Fintype.card_fin] at he
        exact he
      _ = ((N*(∑u,l u*P u):ℕ):ENat) := by
        simp_rw [Nat.mul_assoc]
        rw [←Nat.cast_sum,←Finset.mul_sum]
      _ = _ := by
        apply congrArg (fun a : ℕ=>(a:ENat))
        rw [precision_layer_sum,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [hLayer,nat_mul_min]

#print axioms a11_distinct_residue_grade_sharp
end Paper5
