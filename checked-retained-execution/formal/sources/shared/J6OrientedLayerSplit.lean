import J6OrientedShift
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-! Explicit Boolean-cube reindexing by matched and unmatched layers.
The matched row occupies j, its matched column j+t, and the two
boundary sets have exactly t layers each. -/
namespace J6OrientedLayerSplit
open scoped BigOperators

def row (L t : ℕ) (ht : t ≤ L) : (Fin (L-t) ⊕ Fin t) ≃ Fin L :=
  finSumFinEquiv.trans (finCongr (Nat.sub_add_cancel ht))

def col (L t : ℕ) (ht : t ≤ L) : (Fin t ⊕ Fin (L-t)) ≃ Fin L :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le ht))

theorem row_matched (L t : ℕ) (ht : t ≤ L) (i : Fin (L-t)) :
    (row L t ht (.inl i)).val=i.val := rfl

theorem row_unmatched (L t : ℕ) (ht : t ≤ L) (i : Fin t) :
    (row L t ht (.inr i)).val=L-t+i.val := by
  simp [row,finSumFinEquiv_apply_right,Nat.add_comm]

theorem col_unmatched (L t : ℕ) (ht : t ≤ L) (i : Fin t) :
    (col L t ht (.inl i)).val=i.val := rfl

theorem col_matched (L t : ℕ) (ht : t ≤ L) (i : Fin (L-t)) :
    (col L t ht (.inr i)).val=t+i.val := by
  simp [col,finSumFinEquiv_apply_right]

abbrev Blocks (Y X : Type*) (L t : ℕ) :=
  (Fin (L-t) → Y×X) × (Fin t → Y) × (Fin t → X)

def assignments (Y X : Type*) (L t : ℕ) (ht : t ≤ L) :
    Blocks Y X L t ≃ ((Fin L → Y) × (Fin L → X)) where
  toFun d :=
    (fun j => Sum.elim (fun i => (d.1 i).1) d.2.1 ((row L t ht).symm j),
     fun j => Sum.elim d.2.2 (fun i => (d.1 i).2) ((col L t ht).symm j))
  invFun a := (fun i => (a.1 (row L t ht (.inl i)),a.2 (col L t ht (.inr i))),
    (fun i => a.1 (row L t ht (.inr i)),fun i => a.2 (col L t ht (.inl i))))
  left_inv d := by
    rcases d with ⟨d,yr,xc⟩
    apply Prod.ext
    · funext i
      simp
    · apply Prod.ext
      · funext i
        simp
      · funext i
        simp
  right_inv d := by
    apply Prod.ext
    · funext i
      change (Sum.elim (fun j => d.1 (row L t ht (.inl j)))
        (fun j => d.1 (row L t ht (.inr j))) ((row L t ht).symm i))=d.1 i
      obtain ⟨j,rfl⟩ := (row L t ht).surjective i
      cases j <;> simp
    · funext i
      change (Sum.elim (fun j => d.2 (col L t ht (.inl j)))
        (fun j => d.2 (col L t ht (.inr j))) ((col L t ht).symm i))=d.2 i
      obtain ⟨j,rfl⟩ := (col L t ht).surjective i
      cases j <;> simp

theorem rows_interior (Y X : Type*) (L t : ℕ) (ht : t ≤ L)
    (d : Blocks Y X L t) (i : Fin (L-t)) :
    (assignments Y X L t ht d).1 (row L t ht (.inl i)) = (d.1 i).1 := by
  change Sum.elim (fun j => (d.1 j).1) d.2.1 ((row L t ht).symm (row L t ht (.inl i))) = _
  simp

theorem cols_interior (Y X : Type*) (L t : ℕ) (ht : t ≤ L)
    (d : Blocks Y X L t) (i : Fin (L-t)) :
    (assignments Y X L t ht d).2 (col L t ht (.inr i)) = (d.1 i).2 := by
  change Sum.elim d.2.2 (fun j => (d.1 j).2) ((col L t ht).symm (col L t ht (.inr i))) = _
  simp

#print axioms row_matched
#print axioms row_unmatched
#print axioms col_matched
#print axioms assignments
#print axioms rows_interior
#print axioms cols_interior
end J6OrientedLayerSplit
