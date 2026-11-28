import J6R10IntegralFinite

/-! Reindex the literal contraction by a true bijection of real edges.
Both independently summed Boolean cubes, the row product and the inner
column sums are transported; padded slots are never made extra bits. -/
namespace J6R12Integral
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive J6R10Integral

variable {I J K : Type*} [Fintype I] [Fintype J] {a : ℕ}

def indexedAtlas (e : I ≃ J) (W : Atlas J K a) : Atlas I K a where
  page := W.page ∘ e
  slot := W.slot ∘ e
  injective := fun _ _ h => e.injective (W.injective h)

def edgeBits (e : I ≃ J) : (I → Bool) ≃ (J → Bool) :=
  e.arrowCongr (Equiv.refl Bool)

omit [Fintype I] [Fintype J] in
theorem edgeBits_apply (e : I ≃ J) (x : I → Bool) (j : J) :
    edgeBits e x j = x (e.symm j) := rfl

omit [Fintype I] [Fintype J] in
theorem edgeBits_at_index (e : I ≃ J) (x : I → Bool) (i : I) : edgeBits e x (e i) = x i := by
  rw [edgeBits_apply,Equiv.symm_apply_apply]

theorem contract_reindex {R : Type*} [CommRing R] (e : I ≃ J) (M : J → J → R)
    (U V : (J → Bool) → R) :
    contract (fun i j => M (e i) (e j)) (U ∘ edgeBits e) (V ∘ edgeBits e) =
      contract M U V := by
  classical
  unfold J6R10Integral.contract
  refine Fintype.sum_equiv (edgeBits e) _ _ (fun Y => ?_)
  refine Fintype.sum_equiv (edgeBits e) _ _ (fun X => ?_)
  change U (edgeBits e Y) * V (edgeBits e X) * _ = _
  congr 1
  refine Fintype.prod_equiv e _ _ (fun i => ?_)
  have hr :
      (∑ j : I, if X j then M (e i) (e j) else 0) =
        ∑ j : J, if edgeBits e X j then M (e i) j else 0 :=
    Fintype.sum_equiv e _ _ (fun j => by rw [edgeBits_at_index])
  simp only [hr,edgeBits_at_index]

variable [DecidableEq K]

theorem integralNetwork_reindex (e : I ≃ J) (W : Atlas J K a) (f : ℤ[X]) (ell : ℕ) (t : ℤ)
    (U V : (J → Bool) → IntRing f ell) :
    integralNetwork f ell (indexedAtlas e W) t (U ∘ edgeBits e) (V ∘ edgeBits e) =
      integralNetwork f ell W t U V := by
  unfold integralNetwork
  exact contract_reindex e (integralEntry f ell W t) (C ∘ U) (C ∘ V)

theorem globalNetwork_reindex (e : I ≃ J) (W : Atlas J K a) (f : ℤ[X]) (ell : ℕ)
    (U V : (J → Bool) → IntRing f ell) :
    globalNetwork f ell (indexedAtlas e W) (U ∘ edgeBits e) (V ∘ edgeBits e) =
      globalNetwork f ell W U V := by
  unfold globalNetwork
  rw [network_eq_contract,network_eq_contract]
  exact contract_reindex e (J6DeformationPoly.matrix W.page W.index a)
    (C ∘ embed f ell ∘ U) (C ∘ embed f ell ∘ V)

#print axioms edgeBits_at_index
#print axioms contract_reindex
#print axioms integralNetwork_reindex
#print axioms globalNetwork_reindex
end J6R12Integral
