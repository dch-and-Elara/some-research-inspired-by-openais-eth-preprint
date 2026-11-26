import P5RepeatedObservation
import P5LiteralJets

/-! Paper 5 (A.10) for literal integral polynomial matrix jets.
The only structural receipt is the Smith identification of the actual
observation image. The primitive free split, multiplication, quotient
compatibility, and local-image injection are derived below. -/
namespace Paper5
open scoped BigOperators Polynomial
open Matrix

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
variable {T : Type*} [Fintype T]

theorem native_observation_length {N m d : ℕ}
    (π : R) (hπ : π≠0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (t α : T→R) (P k : T→ℕ) (hs : m+d = ∑ u,k u)
    (A : Matrix (Fin N) (Fin N) R[X])
    (hdegree : ∀ i j, (A i j).natDegree≤d)
    (hregular : (A.map (Polynomial.mapRingHom (IsLocalRing.residue R))).det≠0)
    (lo : Fin m→ℕ) (hi : Fin d→ℕ) (hsep : ∀ a b,lo a≤hi b)
    (smith : LinearMap.range (observeGrid (I:=Fin N) π t α P k (∑ u,k u)) ≃ₗ[R]
      CyclicGrid π (repExponent lo hi : RepIndex N m d → ℕ)) :
    (N * ∑ a,lo a : ℕ) ≤
      ∑ u, Module.length R (LinearMap.range (localMul A π (t u) (α u) (P u) (k u))) := by
  let S := ∑ u,k u
  let O := observeGrid (I:=Fin N) π t α P k S
  have hd : ∀ i j, ((A i j).map (IsLocalRing.residue R)).natDegree≤d :=
    fun i j => (Polynomial.natDegree_map_le ..).trans (hdegree i j)
  have split := polynomial_split_from_regular_residue A m S d hd hs.le hregular
  have hdim : Fintype.card (Fin N × Fin S) - Fintype.card (Fin N × Fin m) = d*N := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    change m+d=S at hs
    rw [←hs,Nat.mul_add,Nat.add_sub_cancel_left,Nat.mul_comm]
  rw [hdim] at split
  obtain ⟨e,he⟩ := split
  let obs := smith.toLinearMap.comp (O.rangeRestrict.comp e.toLinearMap)
  let embed := (LinearMap.range O).subtype.comp smith.symm.toLinearMap
  have hoR : Function.Surjective O.rangeRestrict := by
    intro x
    obtain ⟨v,hv⟩ := x.property
    exact ⟨v,Subtype.ext hv⟩
  have hob : Function.Surjective obs :=
    smith.surjective.comp (hoR.comp e.surjective)
  have hem : Function.Injective embed :=
    Subtype.val_injective.comp smith.symm.injective
  have hcomp (x : (Fin N × Fin m→R) × (Fin (d*N)→R)) : embed (obs x) = O (e x) := by
    exact congrArg Subtype.val (smith.symm_apply_apply (O.rangeRestrict (e x)))
  refine observation_length_lower π lo hi obs hπ hmax hob hsep embed hem
    (fun u => LinearMap.range (localMul A π (t u) (α u) (P u) (k u))) ?_
  intro x u
  rw [hcomp,he]
  change O ((coefficientMatrix A m S) *ᵥ x) u ∈ _
  have hmul := observed_mul A π t α P k m S d hdegree hs.le x u
  rw [show O ((coefficientMatrix A m S) *ᵥ x) u =
    localMul A π (t u) (α u) (P u) (k u) (observeGrid π t α P k m x u) from hmul]
  exact ⟨observeGrid π t α P k m x u,rfl⟩

#print axioms native_observation_length
end Paper5
