import J6R10IntegralAssignments

/-! The old local tables are the actual retained tensor entries, lifted
individually from the precision of the parent before reduction to the
probe register. This identifies the grouped-old premise pointwise, not
merely on the final scalar. -/
namespace J6R10Integral
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive

variable {A Q G V W : Type*} [Fintype G] [Fintype V] [Fintype W]
variable {f : ℤ[X]} {ell p q : ℕ}

noncomputable def liftedVertexProduct {A V : Type*} [Fintype V]
    (hf : f.Monic) (owner : A → V)
    (entry : ∀ v, ({r : A // owner r = v} → Bool) → Box f ell p) (x : A → Bool) :
    IntRing f ell :=
  vertexProduct owner (fun v u => canonicalLift p f hf ell (entry v u)) x

noncomputable def groupedOldLifts (hf : f.Monic) (rg : A → G) (cg : Q → G)
    (rowOwner : A → V) (colOwner : Q → W) (rowBucket : V → G) (colBucket : W → G)
    (hr : ∀ r, rg r = rowBucket (rowOwner r)) (hc : ∀ c, cg c = colBucket (colOwner c))
    (rowVal : ∀ v, ({r : A // rowOwner r = v} → Bool) → Box f ell p)
    (colVal : ∀ w, ({c : Q // colOwner c = w} → Bool) → Box f ell p) (g : G)
    (u : AssignmentState rg cg g) : Box f ell q :=
  groupedTable rg cg rowOwner colOwner rowBucket colBucket hr hc
    (fun v x => reduce q f ell (canonicalLift p f hf ell (rowVal v x)))
    (fun w x => reduce q f ell (canonicalLift p f hf ell (colVal w x))) g u

theorem groupedOldLifts_exact (hf : f.Monic) (e : A ≃ Q) (rg : A → G) (cg : Q → G)
    (rowOwner : A → V) (colOwner : Q → W) (rowBucket : V → G) (colBucket : W → G)
    (hr : ∀ r, rg r = rowBucket (rowOwner r)) (hc : ∀ c, cg c = colBucket (colOwner c))
    (rowVal : ∀ v, ({r : A // rowOwner r = v} → Bool) → Box f ell p)
    (colVal : ∀ w, ({c : Q // colOwner c = w} → Bool) → Box f ell p) (Y X : A → Bool) :
    reduce q f ell (liftedVertexProduct hf rowOwner rowVal Y) *
      reduce q f ell (liftedVertexProduct hf colOwner colVal (X ∘ e.symm)) =
      ∏ g, groupedOldLifts hf rg cg rowOwner colOwner rowBucket colBucket hr hc rowVal colVal g
        (pairedGroups e rg cg (Y,X) g) := by
  classical
  let R' (v : V) (y : {r : A // rowOwner r = v} → Bool) :=
    reduce q f ell (canonicalLift p f hf ell (rowVal v y))
  let C' (w : W) (x : {c : Q // colOwner c = w} → Bool) :=
    reduce q f ell (canonicalLift p f hf ell (colVal w x))
  have h : (∏ g, groupedTable rg cg rowOwner colOwner rowBucket colBucket hr hc R' C' g
      (groupAssignments rg cg (Y,X ∘ e.symm) g)) =
      vertexProduct rowOwner R' Y * vertexProduct colOwner C' (X ∘ e.symm) :=
    groupedTable_exact rg cg rowOwner colOwner rowBucket colBucket hr hc R' C' Y (X ∘ e.symm)
  change _ = ∏ g, groupedTable rg cg rowOwner colOwner rowBucket colBucket hr hc R' C' g
    (groupAssignments rg cg (Y,X ∘ e.symm) g)
  rw [h]
  simp only [liftedVertexProduct,vertexProduct,R',C',map_prod]

#print axioms groupedOldLifts_exact
end J6R10Integral
