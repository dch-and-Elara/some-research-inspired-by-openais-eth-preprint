import J6R10IntegralOwner

/-! Reconcile the canonical list of retained entries in the recursive
interface with the actual products indexed by vertices. -/
namespace J6R10Integral
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive

variable {A V : Type*} [Fintype V] {f : ℤ[X]} {ell p : ℕ}

noncomputable def vertexList (owner : A → V)
    (entry : ∀ v, ({r : A // owner r = v} → Bool) → Box f ell p) (x : A → Bool) :
    List (Box f ell p) :=
  List.ofFn fun i : Fin (Fintype.card V) =>
    entry ((Fintype.equivFin V).symm i) (fun r => x r.val)

theorem liftedProduct_vertexList (hf : f.Monic) (owner : A → V)
    (entry : ∀ v, ({r : A // owner r = v} → Bool) → Box f ell p) (x : A → Bool) :
    liftedProduct p f hf ell (vertexList owner entry x) = liftedVertexProduct hf owner entry x := by
  classical
  unfold liftedProduct vertexList liftedVertexProduct vertexProduct
  rw [List.map_ofFn,List.prod_ofFn]
  symm
  refine Fintype.prod_equiv (Fintype.equivFin V) _ _ (fun v => ?_)
  exact (congrArg (fun w => canonicalLift p f hf ell (entry w (fun r => x r.val)))
    ((Fintype.equivFin V).symm_apply_apply v)).symm

#print axioms liftedProduct_vertexList
end J6R10Integral
