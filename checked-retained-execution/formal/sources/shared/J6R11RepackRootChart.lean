import J6R10RepackPhysical
import J6RepairedCapacity
import J6OrientedHost
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Equiv.Prod

/-! The concrete planted/padded J6 root is an instance of the same
bipartite network and real packet placement used by every child.
The old topology here is not replaced by a list of arbitrary tables. -/
namespace J6R11Repack
open scoped Classical BigOperators
open P11FullPacking J6OrientedHost J6RecursiveOrientation J6RepairedCapacity
open J6R10Repack
variable {S V : Type*} [LinearOrder S] {a b m q l : ℕ}

abbrev Left (V : Type*) (w : Fin a → S) (m b l : ℕ) := J6OrientedHost.Old V w m b l
abbrev Right (w : Fin a → S) (m b l q : ℕ) := J6OrientedHost.New w m b l q

private def unitTail (X : Type*) : (Σ _ : X, Unit) ≃ X where
  toFun x := x.1
  invFun x := ⟨x,()⟩
  left_inv
    | ⟨_,()⟩ => rfl
  right_inv _ := rfl

private def layerSigma {X L : Type*} (D : X → Type*) :
    (Σ p : X × L, D p.1) ≃ (Σ x, D x) × L where
  toFun p := (⟨p.1.1,p.2⟩,p.1.2)
  invFun p := ⟨(p.1.1,p.2),p.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def rotatePair (X Y Z : Type*) : (X × Y) × Z ≃ (X × Z) × Y where
  toFun x := ((x.1.1,x.2),x.1.2)
  invFun x := ((x.1.1,x.2),x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The old row ports enumerate each physical root wire exactly once. -/
def rootRowChart (T : Plant V m q) (w : Fin a → S) :
    (Σ v : Left V w m b l, oldScope T w v) ≃ Wire w m b l :=
  (Equiv.sumSigmaDistrib (oldScope T w)).trans (Equiv.sumCongr
    ((layerSigma (L:=Fin (2*l)) (fun v : V => Fin (T.degree v))).trans
      (T.rowPort.prodCongr (Equiv.refl _)))
    (unitTail _))

/-- Both incidences of a subdivision vertex name their actual distinct
wires, including on off-diagonal padding cells. -/
def rootColChart (T : Plant V m q) (w : Fin a → S) :
    (Σ _ : Right w m b l q, Bool) ≃ Wire w m b l :=
  (Equiv.sumSigmaDistrib (fun _ : Right w m b l q => Bool)).trans (Equiv.sumCongr
    ((Equiv.sigmaEquivProd _ _).trans ((rotatePair (Fin q) (Fin (2*l)) Bool).trans
      (T.colPort.prodCongr (Equiv.refl _))))
    (Equiv.sigmaEquivProd _ _))

theorem rootRowChart_apply (T : Plant V m q) (w : Fin a → S)
    (v : Left V w m b l) (j : oldScope T w v) :
    rootRowChart T w ⟨v,j⟩ = rowPort T w v j := by
  rcases v with ⟨v,d⟩|⟨s,b⟩ <;> rfl

theorem rootColChart_apply (T : Plant V m q) (w : Fin a → S)
    (v : Right w m b l q) (j : Bool) :
    rootColChart T w ⟨v,j⟩ = colPort T w v j := by
  cases v <;> rfl

def rootNetwork (T : Plant V m q) (w : Fin a → S) :
    Network (Wire w m b l) (Left V w m b l) (Right w m b l q) where
  row e := ((rootRowChart T w).symm e).1
  col e := ((rootColChart T w).symm e).1

theorem root_row_owner (T : Plant V m q) (w : Fin a → S)
    (v : Left V w m b l) (j : oldScope T w v) :
    (rootNetwork T w).row (rowPort T w v j) = v := by
  rw [← rootRowChart_apply]
  exact congrArg Sigma.fst ((rootRowChart T w).symm_apply_apply ⟨v,j⟩)

theorem root_col_owner (T : Plant V m q) (w : Fin a → S)
    (v : Right w m b l q) (j : Bool) :
    (rootNetwork T w).col (colPort T w v j) = v := by
  rw [← rootColChart_apply T]
  exact congrArg Sigma.fst ((rootColChart T w).symm_apply_apply ⟨v,j⟩)

/-- An original vertex chart and the port subnet of the graph are
equivalent even when the original vertex happens to have no incidences. -/
def chartFiber {X E : Type*} {D : X → Type*} (h : (Σ x, D x) ≃ E) (v : X) :
    D v ≃ {e : E // (h.symm e).1 = v} :=
  (Equiv.sigmaSubtype v).symm.trans (Equiv.subtypeEquiv h (fun a => by
    change a.1=v ↔ (h.symm (h a)).1=v
    rw [h.symm_apply_apply]))

/-- The repaired orientation map provides the source's actual root
layout, with the original slot map and labels in every coordinate. -/
noncomputable def rootPacking [Fintype S] (m l q : ℕ) (T : Plant V m q)
    (w : Fin (J6Mesh.a m) → S) (mask : MaskFamily (J6Mesh.a m) (J6Mesh.K m) S)
    (h : m≤J6Mesh.K m) (hL : 2*l=J6Mesh.L m) (hS : Fintype.card S=64) :
    PhysicalPacking (rootNetwork (b:=J6Mesh.K m) (l:=l) T w) (J6Mesh.a m) S where
  copies := J6Mesh.K m
  mask := mask
  seat := ⟨oriented mask w m l h hL,orientation_injective mask w m l h hL⟩
  rowLabel := fun v i => J6OrientedHost.owner w i (.inl v)
  colLabel := fun v i => J6OrientedHost.owner w i (.inr v)
  exactCell e := by
    funext i
    apply Prod.ext
    · let u := (rootRowChart (b:=J6Mesh.K m) (l:=l) T w).symm e
      have he : rowPort T w u.1 u.2 = e := by
        rw [← rootRowChart_apply]
        exact (rootRowChart (b:=J6Mesh.K m) (l:=l) T w).apply_symm_apply e
      simpa only [J6OrientedHost.group, J6RecursivePortCube.ports, Sum.elim_inl, he] using
        owner_exact T mask w h hL i (.inl u.1) u.2
    · let u := (rootColChart (b:=J6Mesh.K m) (l:=l) T w).symm e
      have he : colPort T w u.1 u.2 = e := by
        rw [← rootColChart_apply T]
        exact (rootColChart (b:=J6Mesh.K m) (l:=l) T w).apply_symm_apply e
      simpa only [J6OrientedHost.group, J6RecursivePortCube.ports, Sum.elim_inr, he] using
        owner_exact T mask w h hL i (.inr u.1) u.2
  paddedBudget := by
    rw [Nat.card_eq_fintype_card,ordered_cells_exact m hS]
    change J6Mesh.D m * (J6Mesh.K m * J6Mesh.L m) ≤
      3*Nat.card (J6RepairedCentered.Ports m l w)
    rw [J6Mesh.mesh_product,Nat.card_eq_fintype_card,actual_wire_count m l w h hL hS]
    omega

#print axioms rootRowChart_apply
#print axioms rootColChart_apply
#print axioms root_row_owner
#print axioms root_col_owner
#print axioms chartFiber
#print axioms rootPacking
end J6R11Repack
