import J6R10IntegralAssignments
import J6R10RowLocal

/-! The finite polynomial evaluation is the very physical source sum
used by the nonzero-child construction. Separate row and column
endpoint sets are paired by the original edge identification. -/
namespace J6R10Integral
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P11FullPacking P1DyadicGrid
open J6R9Recursive J6R9PacketScopes J6R9PacketChild
open J6R10RowLocal

variable {A Q S : Type*} [LinearOrder S] {a b : ℕ}

def physicalAtlas (ρ : A → Physical a b S) (inj : Function.Injective ρ) :
    Atlas A (Page a b S) a where
  page := fun r => (ρ r).1
  slot := fun r => (ρ r).2
  injective := inj

variable [Fintype A] [Fintype Q] {f : ℤ[X]} {ell : ℕ}

theorem physical_row (ρ : A → Physical a b S) (κ : Q → Physical a b S)
    (inj : Function.Injective ρ) (e : A ≃ Q) (paired : ∀ r, κ (e r) = ρ r)
    (t : ℤ) (p : ℕ) (z : Box f ell p) (r : A) (X : A → Bool) :
    (∑ j, if X j then finiteEntry p f ell (physicalAtlas ρ inj) t z r j else 0) =
      originalRow κ t p (box_two_nil p f ell) z (ρ r) (X ∘ e.symm) := by
  classical
  unfold originalRow
  refine Fintype.sum_equiv e _ _ (fun j => ?_)
  unfold finiteEntry columnEntry
  simp only [physicalAtlas,Atlas.index,paired j,Function.comp_apply,Equiv.symm_apply_apply]
  by_cases hp : (ρ r).1 = (ρ j).1
  · rw [if_pos hp,if_pos hp.symm]
    cases X j
    · simp only [Bool.false_eq_true,if_false,J6R9PacketTiles.bit,mul_zero]
    · simp only [if_true,J6R9PacketTiles.bit,mul_one]
  · rw [if_neg hp,if_neg (Ne.symm hp)]
    split <;> rfl
def physicalRows (ρ : A → Physical a b S) (κ : Q → Physical a b S)
    (mask : MaskFamily a b S) (i : Fin a) (x : ∀ g, State ρ κ mask i g) (r : A) : Bool :=
  (x (rowGroup mask i (ρ r))).1 ⟨r,rfl⟩

def physicalCols (ρ : A → Physical a b S) (κ : Q → Physical a b S)
    (mask : MaskFamily a b S) (i : Fin a) (x : ∀ g, State ρ κ mask i g) (q : Q) : Bool :=
  (x (colGroup mask i (κ q))).2 ⟨q,rfl⟩

variable [Fintype S]

theorem finite_grouped_reference
    (ρ : A → Physical a b S) (κ : Q → Physical a b S)
    (inj : Function.Injective ρ) (e : A ≃ Q) (paired : ∀ r, κ (e r) = ρ r)
    (mask : MaskFamily a b S) (i : Fin a) (t : ℤ) (p : ℕ) (z : Box f ell p)
    (U V : (A → Bool) → IntRing f ell) (old : ∀ g, State ρ κ mask i g → Box f ell p)
    (hOld : ∀ Y X, reduce p f ell (U Y) * reduce p f ell (V X) =
      ∏ g, old g
        (pairedGroups e (fun r => rowGroup mask i (ρ r)) (fun q => colGroup mask i (κ q)) (Y,X) g)) :
    ((integralNetwork f ell (physicalAtlas ρ inj) t U V).map (reduce p f ell)).eval z =
      ∑ x : ∀ g, State ρ κ mask i g, (∏ g, old g (x g)) *
        ∏ r : A, LiteralPortCompiler.affine (physicalRows ρ κ mask i x r)
          (originalRow κ t p (box_two_nil p f ell) z (ρ r) (physicalCols ρ κ mask i x)) := by
  classical
  rw [network_finite,contract]
  let A' : (A → Bool) × (A → Bool) → Box f ell p := fun y =>
    reduce p f ell (U y.1) * reduce p f ell (V y.2) *
      ∏ r : A, let z := ∑ j, if y.2 j then finiteEntry p f ell (physicalAtlas ρ inj) t z r j else 0
               if y.1 r then z else 1-z
  change (∑ Y, ∑ X, A' (Y,X)) = _
  rw [← Fintype.sum_prod_type A']
  let rg := fun r => rowGroup mask i (ρ r)
  let cg := fun q => colGroup mask i (κ q)
  let E := pairedGroups e rg cg
  refine Fintype.sum_equiv E _ _ (fun xy => ?_)
  rcases xy with ⟨Y,X⟩
  change reduce p f ell (U Y) * reduce p f ell (V X) * _ = _
  rw [hOld Y X]
  congr 1
  refine Finset.prod_congr rfl (fun r _ => ?_)
  have hy : physicalRows ρ κ mask i (E (Y,X)) r = Y r := pairedGroups_row e rg cg Y X r
  have hx : physicalCols ρ κ mask i (E (Y,X)) = X ∘ e.symm :=
    funext (pairedGroups_col e rg cg Y X)
  rw [hy,hx,physical_row ρ κ inj e paired]
  cases h : Y r <;> simp [h,LiteralPortCompiler.affine]


#print axioms physical_row
#print axioms finite_grouped_reference
end J6R10Integral
