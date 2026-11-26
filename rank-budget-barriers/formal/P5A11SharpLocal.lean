import P5A11SharpUnit
import P5A11SharpProjection
import P5LiteralCapacity

/-! Exact local deficiency of the actual distinct-residue witness.
The structural global allocation of the top precision entries is
separate from this quotient-length equality. -/
namespace Paper5
open Polynomial Matrix
open scoped BigOperators Polynomial Classical

variable {R I T : Type*} [CommRing R] [Fintype I] [DecidableEq I]

noncomputable def sharpMatrix (t : T→R) (l : T→ℕ) [Fintype T] : Matrix I I R[X] :=
  Matrix.diagonal (fun _ => sharpScalar t l)

theorem local_mul_diagonal_scalar (p : R[X]) (π t α : R) (P k : ℕ)
    (x : I→LocalJet π P k) (i : I) :
    localMul (Matrix.diagonal (fun _ : I=>p)) π t α P k x i =
      (nativeObs π t α P k p)*x i := by
  let g := (nativeObs π t α P k).toRingHom
  have hg : (Matrix.diagonal (fun _ : I=>p)).map g=
      Matrix.diagonal (fun _ : I=>g p) := by
    ext a b
    by_cases h : a=b
    · subst b; simp
    · simp [h]
  change (((Matrix.diagonal (fun _ : I=>p)).map g) *ᵥ x) i=_
  rw [hg]
  change (∑ j,Matrix.diagonal (fun _ : I=>g p) i j*x j)=_
  rw [Finset.sum_eq_single i]
  · simp [g]
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

variable [Fintype T] [IsDomain R] [IsLocalRing R]

set_option maxHeartbeats 13000000 in
theorem sharp_local_cokernel_exact (π : R) (hπ : π≠0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (t α : T→R) (P k l : T→ℕ)
    (ht : Function.Injective ((IsLocalRing.residue R)∘t))
    (ha : ∀ u,IsUnit (α u)) (u : T) (hl : l u≤k u) :
    Module.length R ((I→LocalJet π (P u) (k u)) ⧸
      LinearMap.range (localMul (sharpMatrix (I:=I) t l) π (t u) (α u) (P u) (k u))) =
      (Fintype.card I*l u*P u:ℕ) := by
  let K := LocalJet π (P u) (k u)
  let J := LocalJet π (P u) (l u)
  let fs := sharpJetProjection (S:=Cyclic π (P u)) (k u) (l u) hl
  let proj : (I→K) →ₗ[R] (I→J) :=
    LinearMap.pi (fun i=> (fs.toLinearMap.restrictScalars R).comp (LinearMap.proj i))
  let F := localMul (sharpMatrix (I:=I) t l) π (t u) (α u) (P u) (k u)
  obtain ⟨v,hv⟩ := sharp_scalar_native_shape π t α P k l ht ha u
  have hp (x : I→K) (i : I) :
      F x i=((v:K)*(AdjoinRoot.root (X^(k u) : (Cyclic π (P u))[X]))^(l u))*x i := by
    unfold F sharpMatrix
    rw [local_mul_diagonal_scalar,hv]
  have hproj (x : I→K) (i : I) : proj x i=fs (x i) := rfl
  have hsurj : Function.Surjective proj := by
    intro y
    choose z hz using fun i => sharpJetProjection_surjective (S:=Cyclic π (P u)) (k u) (l u) hl (y i)
    exact ⟨z,funext hz⟩
  have hk : LinearMap.ker proj=LinearMap.range F := by
    ext x
    rw [LinearMap.mem_ker,LinearMap.mem_range]
    constructor
    · intro h
      have hh (i : I) : fs (x i)=0 := by
        rw [←hproj,h]
        rfl
      choose y hy using fun i => (sharpJetProjection_scaled_range (k u) (l u) hl v (x i)).mp (hh i)
      exact ⟨y,funext (fun i=>(hp y i).trans (hy i))⟩
    · rintro ⟨y,rfl⟩
      funext i
      rw [hproj]
      exact (sharpJetProjection_scaled_range (k u) (l u) hl v (F y i)).mpr ⟨y i,(hp y i).symm⟩
  let e := LinearMap.quotKerEquivOfSurjective proj hsurj
  change Module.length R ((I→K) ⧸ LinearMap.range F)=_
  rw [←hk,e.length_eq,Module.length_pi_of_fintype]
  simp [J,actual_jet_length π hπ hmax,Nat.mul_assoc]

#print axioms local_mul_diagonal_scalar
#print axioms sharp_local_cokernel_exact
end Paper5
