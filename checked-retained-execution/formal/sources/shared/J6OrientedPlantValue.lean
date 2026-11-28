import J6OrientedLayerProduct
import J6OrientedSplitSides
import J6RecursivePortCube
import J6BoundaryFactors
import Mathlib.Tactic

/-! Actual planted port product and its J6 layer identity. The read
here is the one proved on corrected physical diagonal seats by
J6OrientedShift.plant_shift, not a supplied contraction value. -/
namespace J6OrientedPlantValue
open scoped BigOperators Polynomial
open J6OrientedLayerSplit J6OrientedLayerProduct J6NativeHeightClearing
open J6RecursivePortCube
variable {m L : ℕ}

abbrev W (m L : ℕ) := Fin m × Fin L
abbrev Vec (m : ℕ) := Fin m → Bool

def flatten : (Fin L → Vec m) ≃ (W m L → Bool) where
  toFun y p := y p.2 p.1
  invFun a j i := a (i,j)
  left_inv _ := rfl
  right_inv a := funext (fun p => by cases p; rfl)

def read (t : ℕ) (p : W m L) (x : W m L → Bool) : Bool :=
  if h : p.2.val+t<L then x (p.1,⟨p.2.val+t,h⟩) else false

noncomputable def ok (F : Vec m → Bool) (x : W m L → Bool) : Bool :=
  good (fun j : Fin L => F (fun p => x (p,j)))

noncomputable def wt (F : Vec m → Bool) (x : Vec m) : ℚ := if F x then 1 else 0

noncomputable def factor (c : ℚ) (y : Vec m) (x : Option (Vec m)) : ℚ :=
  ∏ p, (LayerRecovery.wireFactor (y p) (x.elim false fun a => a p)).eval c

private theorem read_interior (t : ℕ) (ht : t ≤ L) (p : Fin m)
    (i : Fin (L-t)) (x : Fin L→Vec m) :
    read t (p,row L t ht (.inl i)) (flatten x) = x (col L t ht (.inr i)) p := by
  have hi := i.isLt
  have hL : (row L t ht (.inl i)).val+t < L := by
    rw [row_matched]
    omega
  unfold read
  rw [dif_pos hL]
  have he : (⟨(row L t ht (.inl i)).val+t,hL⟩ : Fin L)=col L t ht (.inr i) := by
    apply Fin.ext
    change (row L t ht (.inl i)).val+t=(col L t ht (.inr i)).val
    rw [row_matched,col_matched]
    omega
  change x ⟨(row L t ht (.inl i)).val+t,hL⟩ p = _
  rw [he]

private theorem read_boundary (t : ℕ) (ht : t ≤ L) (p : Fin m) (i : Fin t)
    (x : Fin L→Vec m) :
    read t (p,row L t ht (.inr i)) (flatten x) = false := by
  have hL : ¬ (row L t ht (.inr i)).val+t < L := by
    rw [row_unmatched]
    omega
  exact dif_neg hL

theorem planted_port_value (A B : Vec m → Bool) (c : ℚ)
    (t : ℕ) (ht : t ≤ L) (y x : Fin L→Vec m) :
    J6OrientedSplitSides.term (ok A) (ok B) (read t) c (flatten y,flatten x) =
      value (wt A) (wt B) (factor c) L t ht (y,x) := by
  classical
  have hProd :
    (∏ p : W m L, (LayerRecovery.wireFactor (flatten y p) (read t p (flatten x))).eval c) =
      (∏ j : Fin (L-t), factor c (y (row L t ht (.inl j))) (some (x (col L t ht (.inr j))))) *
        ∏ j : Fin t, factor c (y (row L t ht (.inr j))) none := by
    rw [← Equiv.prod_comp (Equiv.prodComm (Fin L) (Fin m))
      (fun p : W m L => (LayerRecovery.wireFactor (flatten y p) (read t p (flatten x))).eval c),
      Fintype.prod_prod_type]
    change (∏ j : Fin L, ∏ p : Fin m,
      (LayerRecovery.wireFactor (y j p) (read t (p,j) (flatten x))).eval c) = _
    rw [← Equiv.prod_comp (row L t ht) (fun j => ∏ p : Fin m,
      (LayerRecovery.wireFactor (y j p) (read t (p,j) (flatten x))).eval c),Fintype.prod_sum_type]
    simp only [read_interior,read_boundary,factor,Option.elim_some,Option.elim_none]
  have hA : (∏ j, wt A (y j)) = if ok A (flatten y) then 1 else 0 :=
    prod_flags (fun j : Fin L => A (y j))
  have hB : (∏ j, wt B (x j)) = if ok B (flatten x) then 1 else 0 :=
    prod_flags (fun j : Fin L => B (x j))
  unfold J6OrientedSplitSides.term value
  simp only [hProd,hA,hB]
  cases ok A (flatten y) <;> cases ok B (flatten x) <;> simp

theorem planted_factors (A B : Vec m → Bool) (c : ℚ) (t : ℕ) (ht : t ≤ L) :
    rationalSlot (ok (L:=L) A) (ok B) (read t) c =
      ((LayerRecovery.layerPolynomial (wt A) (wt B)).eval c)^(L-t) *
        (wt A (fun _ => false))^t * (∑ x : Vec m, wt B x)^t := by
  classical
  let T := J6OrientedSplitSides.term (ok (L:=L) A) (ok B) (read t) c
  change (∑ y : W m L→Bool, ∑ x : W m L→Bool, T (y,x)) = _
  rw [← Fintype.sum_prod_type T]
  rw [← Equiv.sum_comp (flatten.prodCongr flatten) T]
  change (∑ d : (Fin L → Vec m) × (Fin L → Vec m), T (flatten d.1,flatten d.2)) = _
  simp only [T,planted_port_value A B c t ht]
  rw [layer_partition]
  congr 2
  · rw [Fintype.sum_prod_type]
    unfold LayerRecovery.layerPolynomial
    simp [factor,Polynomial.eval_finset_sum,Polynomial.eval_mul,Polynomial.eval_prod]
  · have h := J6BoundaryFactors.no_read_singleton (wt A) c
    exact congrArg (fun z : ℚ => z^t) h

#print axioms planted_port_value
#print axioms planted_factors
end J6OrientedPlantValue
