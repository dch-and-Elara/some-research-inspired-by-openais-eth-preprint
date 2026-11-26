import J6R10IntegralPhysical
import J6R10IntegralOwner
import J6R10RowPrinted

/-! Connect the exact finite source sum to the printed children. -/
namespace J6R10Integral
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking P1DyadicGrid J6R9Recursive
open J6R9PacketScopes J6R9PacketChild J6R10RowAffine J6R10RowPrinted

variable {A Q S : Type*} [LinearOrder S] {a b : ℕ}
  [Fintype A] [Fintype Q] [Fintype S] {f : ℤ[X]} {ell : ℕ}
variable [Fintype (Page a b S)]

/-- Literal nonzero child sum equals the finite evaluation of the actual
integral polynomial. There is no substituted compact rank surrogate. -/
theorem finite_from_printed_children
    (ρ : A → Physical a b S) (κ : Q → Physical a b S)
    (inj : Function.Injective ρ) (e : A ≃ Q) (paired : ∀ r, κ (e r) = ρ r)
    (mask : MaskFamily a b S) (i : Fin a) {t : ℤ}
    (htM : t ∈ grid a) (ht : t ≠ 0) (hv : padicValInt 2 t = i.val)
    (p : ℕ) (hp : 0 < p) (z : Box f ell p)
    (U V : (A → Bool) → IntRing f ell) (old : ∀ g, State ρ κ mask i g → Box f ell p)
    (hOld : ∀ Y X, reduce p f ell (U Y) * reduce p f ell (V X) =
      ∏ g, old g
        (pairedGroups e (fun r => rowGroup mask i (ρ r)) (fun q => colGroup mask i (κ q)) (Y,X) g)) :
    ((integralNetwork f ell (physicalAtlas ρ inj) t U V).map (reduce p f ell)).eval z =
      ∑ β ∈ J6RecursiveMenu.menu p (weight i p mask),
        ∏ g, reconstructedChild ρ κ mask i ht hv p (box_two_nil p f ell) z old β g := by
  rw [finite_grouped_reference ρ κ inj e paired mask i t p z U V old hOld]
  exact actual_source_step ρ κ mask i htM ht hv p hp (box_two_nil p f ell) z old

/-- Specialize the comparison to the original retained vertex tables,
each supplied at the parent precision and lifted individually. -/
theorem finite_from_owned_children {V W : Type*} [Fintype V] [Fintype W]
    {p₀ : ℕ} (hf : f.Monic)
    (ρ : A → Physical a b S) (κ : Q → Physical a b S)
    (inj : Function.Injective ρ) (e : A ≃ Q) (paired : ∀ r, κ (e r) = ρ r)
    (mask : MaskFamily a b S) (i : Fin a) {t : ℤ}
    (htM : t ∈ grid a) (ht : t ≠ 0) (hv : padicValInt 2 t = i.val)
    (p : ℕ) (hp : 0 < p) (z : Box f ell p)
    (rowOwner : A → V) (colOwner : Q → W) (rowBucket : V → S) (colBucket : W → S)
    (hr : ∀ r, rowGroup mask i (ρ r) = rowBucket (rowOwner r))
    (hc : ∀ c, colGroup mask i (κ c) = colBucket (colOwner c))
    (rowVal : ∀ v, ({r : A // rowOwner r = v} → Bool) → Box f ell p₀)
    (colVal : ∀ w, ({c : Q // colOwner c = w} → Bool) → Box f ell p₀) :
    let U := liftedVertexProduct hf rowOwner rowVal
    let V' := fun X : A → Bool => liftedVertexProduct hf colOwner colVal (X ∘ e.symm)
    let old := groupedOldLifts (q:=p) hf (fun r => rowGroup mask i (ρ r))
      (fun c => colGroup mask i (κ c)) rowOwner colOwner rowBucket colBucket hr hc rowVal colVal
    ((integralNetwork f ell (physicalAtlas ρ inj) t U V').map (reduce p f ell)).eval z =
      ∑ β ∈ J6RecursiveMenu.menu p (weight i p mask),
        ∏ g, reconstructedChild ρ κ mask i ht hv p (box_two_nil p f ell) z old β g := by
  dsimp only
  apply finite_from_printed_children ρ κ inj e paired mask i htM ht hv p hp z
  exact groupedOldLifts_exact hf e _ _ rowOwner colOwner rowBucket colBucket hr hc rowVal colVal

#print axioms finite_from_printed_children
#print axioms finite_from_owned_children
end J6R10Integral
