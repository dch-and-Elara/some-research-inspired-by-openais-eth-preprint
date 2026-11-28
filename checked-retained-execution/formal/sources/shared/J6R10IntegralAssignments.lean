import J6R10IntegralFinite
import J6OldEntries

/-! The two independent physical Boolean assignment cubes can be
partitioned by the *same* actual 64-symbol grouping used by the
source. No copying of incidence bits or locality assumption about
the final contraction is made. -/
namespace J6R10Integral
open scoped Classical BigOperators Polynomial

variable {A Q G : Type*}

abbrev AssignmentState (rg : A → G) (cg : Q → G) (g : G) :=
  ({r : A // rg r = g} → Bool) × ({q : Q // cg q = g} → Bool)

def groupAssignments (rg : A → G) (cg : Q → G) :
    ((A → Bool) × (Q → Bool)) ≃ (∀ g, AssignmentState rg cg g) where
  toFun x _ := (fun r => x.1 r.val, fun q => x.2 q.val)
  invFun x := (fun r => (x (rg r)).1 ⟨r,rfl⟩, fun q => (x (cg q)).2 ⟨q,rfl⟩)
  left_inv _ := rfl
  right_inv x := by
    funext g
    apply Prod.ext
    · funext r
      obtain ⟨r,hr⟩ := r
      subst g
      rfl
    · funext q
      obtain ⟨q,hq⟩ := q
      subst g
      rfl

/-- The two endpoint sets index the same real edges, although the vertex
groups at the two ends may differ. -/
def pairedGroups (e : A ≃ Q) (rg : A → G) (cg : Q → G) :
    ((A → Bool) × (A → Bool)) ≃ (∀ g, AssignmentState rg cg g) :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.arrowCongr e (Equiv.refl Bool))).trans
    (groupAssignments rg cg)

theorem pairedGroups_row (e : A ≃ Q) (rg : A → G) (cg : Q → G)
    (Y X : A → Bool) (r : A) :
    ((pairedGroups e rg cg (Y,X)) (rg r)).1 ⟨r,rfl⟩ = Y r := rfl

theorem pairedGroups_col (e : A ≃ Q) (rg : A → G) (cg : Q → G)
    (Y X : A → Bool) (q : Q) :
    ((pairedGroups e rg cg (Y,X)) (cg q)).2 ⟨q,rfl⟩ = X (e.symm q) := rfl

section Tables

variable {V W R : Type*} [CommRing R] [Fintype V] [Fintype W]

noncomputable def vertexProduct (own : A → V)
    (val : ∀ v, ({r : A // own r = v} → Bool) → R) (x : A → Bool) : R :=
  ∏ v, val v (fun r => x r.val)

/-- Product of the original retained vertex tables at one group. A
vertex contributes once even if it has no incidence in its fiber. -/
noncomputable def groupedTable (rg : A → G) (cg : Q → G)
    (rowOwner : A → V) (colOwner : Q → W) (rowBucket : V → G) (colBucket : W → G)
    (hr : ∀ r, rg r = rowBucket (rowOwner r)) (hc : ∀ q, cg q = colBucket (colOwner q))
    (rowVal : ∀ v, ({r : A // rowOwner r = v} → Bool) → R)
    (colVal : ∀ w, ({q : Q // colOwner q = w} → Bool) → R)
    (g : G) (x : AssignmentState rg cg g) : R :=
  (∏ v : {v : V // rowBucket v = g}, rowVal v.val (fun r =>
      x.1 ⟨r.val, (hr r.val).trans ((congrArg rowBucket r.property).trans v.property)⟩)) *
  (∏ w : {w : W // colBucket w = g}, colVal w.val (fun q =>
      x.2 ⟨q.val, (hc q.val).trans ((congrArg colBucket q.property).trans w.property)⟩))

variable [Fintype G]

theorem groupedTable_exact (rg : A → G) (cg : Q → G)
    (rowOwner : A → V) (colOwner : Q → W) (rowBucket : V → G) (colBucket : W → G)
    (hr : ∀ r, rg r = rowBucket (rowOwner r)) (hc : ∀ q, cg q = colBucket (colOwner q))
    (rowVal : ∀ v, ({r : A // rowOwner r = v} → Bool) → R)
    (colVal : ∀ w, ({q : Q // colOwner q = w} → Bool) → R)
    (Y : A → Bool) (X : Q → Bool) :
    (∏ g, groupedTable rg cg rowOwner colOwner rowBucket colBucket hr hc rowVal colVal g
      (groupAssignments rg cg (Y,X) g)) =
      vertexProduct rowOwner rowVal Y * vertexProduct colOwner colVal X := by
  classical
  unfold groupedTable
  rw [Finset.prod_mul_distrib]
  congr 1
  · exact (J6BlockFactor.prod_rows rowBucket (fun v => rowVal v (fun r => Y r.val))).symm
  · exact (J6BlockFactor.prod_rows colBucket (fun w => colVal w (fun q => X q.val))).symm

end Tables

variable {R : Type*} [AddCommMonoid R] [Fintype A] [Fintype Q] [Fintype G]

theorem sum_over_grouped_pairs (e : A ≃ Q) (rg : A → G) (cg : Q → G)
    (h : (A → Bool) → (A → Bool) → R) :
    (∑ Y, ∑ X, h Y X) =
      ∑ x, h ((pairedGroups e rg cg).symm x).1 ((pairedGroups e rg cg).symm x).2 := by
  classical
  rw [← Fintype.sum_prod_type (fun y : (A → Bool) × (A → Bool) => h y.1 y.2)]
  exact Fintype.sum_equiv (pairedGroups e rg cg) _ _ (fun y => by
    rw [Equiv.symm_apply_apply])

#print axioms groupAssignments
#print axioms pairedGroups_row
#print axioms pairedGroups_col
#print axioms groupedTable_exact
#print axioms sum_over_grouped_pairs
end J6R10Integral
