import MainProbe
import J1R14QueryTape

/-! Numerical MAIN addresses and the expanded selection in the printed
group scan. In contrast to the support-only NativeJ2 address, the prescribed
word here is recovered from the actual row values, and the fibre is an
explicit finite filter of the local Boolean cube. The public basis file
is supplied once, with a certificate that its selected rows are the actual
copied diagonal-orbit rows. -/
namespace J1R14Query
open scoped BigOperators Polynomial
open MainProbe

universe u v w c p b
variable {I : Type u} {S : Type v} {X : Type w} {Copy : Type c} {Pin : Type p}
  {Basis : Type b}
variable [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
variable (D : DiagonalLayout I S X Copy Pin)

structure BasisFile where
  entry : Basis → Cell I S → ℤ
  diagonalIndex : Pin → Basis
  exactDiagonal : ∀ p u, entry (diagonalIndex p) u = if u = D.slot p then 1 else 0

variable (B : BasisFile (Basis:=Basis) D)

abbrev own (t : I) (g : S) := {v : X // D.variableWord v t = g}

def groupBit (t : I) (g : S) (x : X → Bool) (j : X) : ℤ :=
  if D.variableWord j t = g ∧ x j = true then 1 else 0

/-- The printed row of the block-diagonal matrix after inserting the occupied
coordinates and zeroing the columns outside the group. Its two projections
are the copy index and the exceptional basis-row index. -/
def rowRead (t : I) (g : S) (h : Copy × Basis) (x : X → Bool) : ℤ :=
  ∑ u : Cell I S, B.entry h.2 u * (D.occupied h.1 u).elim 0 (groupBit D t g x)

theorem rowRead_diagonal (t : I) (g : S) (p : Pin) (h : (D.slot p).2 t = g)
    (x : X → Bool) :
    rowRead D B t g (D.copy p,B.diagonalIndex p) x = if x (D.pinVar p) then 1 else 0 := by
  have hm : D.variableWord (D.pinVar p) t = g :=
    (congrFun (D.variableLabel p) t).trans ((congrFun (D.diagonal p) t).trans h)
  simp [rowRead,B.exactDiagonal,ite_mul,D.localSlot,groupBit,hm]

theorem rowRead_matches_weight_zero (interval : Finset ℕ) (hOutside : 0 ∉ interval)
    (t : I) (g : S) (p : Pin) (h : (D.slot p).2 t = g) (x : X → Bool) :
    (rowRead D B t g (D.copy p,B.diagonalIndex p) x : ℚ) =
      groupMeasurement D interval t g p x := by
  rw [rowRead_diagonal D B t g p h,groupMeasurement_pin D interval hOutside t g p h]
  cases x (D.pinVar p) <;> norm_num [boolRat]

variable [Fintype X] [DecidableEq X] [Fintype Copy] [Fintype Basis]

/-- All rows are retained, including a row that restricts to zero. -/
abbrev RowValues (S : Type v) (Copy : Type c) (Basis : Type b) :=
  S → Copy × Basis → ℤ

def extendGroup (t : I) (g : S) (x : own D t g → Bool) (v : X) : Bool :=
  if h : D.variableWord v t = g then x ⟨v,h⟩ else false

omit [Fintype I] [DecidableEq I] [Fintype S] [Fintype X] [DecidableEq X] [Fintype Copy] in
theorem extendGroup_injective (t : I) (g : S) :
    Function.Injective (extendGroup D t g) := by
  intro x y he
  funext v
  simpa [extendGroup,v.property] using congrFun he v.val

noncomputable def groupSize (t : I) (g : S) : ℕ :=
  Fintype.card (own D t g)

noncomputable def privateCube (t : I) (g : S) : Finset (X → Bool) := by
  classical
  exact Finset.univ.map ⟨extendGroup D t g,extendGroup_injective D t g⟩

omit [Fintype I] [DecidableEq I] [Fintype S] [Fintype Copy] in
theorem privateCube_card (t : I) (g : S) :
    (privateCube D t g).card = 2^groupSize D t g := by
  classical
  simp [privateCube,groupSize]

noncomputable def firstScan (t : I) (g : S) (y : RowValues S Copy Basis) :
    Finset (X → Bool) := by
  classical
  exact (privateCube D t g).filter fun x => ∀ h, rowRead D B t g h x = y g h

noncomputable def secondScan (t : I) (g : S) (E : Finset X) (y : RowValues S Copy Basis) :
    Finset (X → Bool) := by
  classical
  exact (firstScan D B t g y).filter fun x =>
    ∀ v ∈ E, D.variableWord v t = g → x v = true

theorem secondScan_membership (t : I) (g : S) (E : Finset X) (y : RowValues S Copy Basis)
    (x : X → Bool) :
    x ∈ secondScan D B t g E y ↔ x ∈ privateCube D t g ∧
      (∀ h, rowRead D B t g h x = y g h) ∧
      (∀ v ∈ E, D.variableWord v t = g → x v = true) := by
  classical
  simp only [secondScan,firstScan,Finset.mem_filter,and_assoc]

/-- Read the bit from the node's actual row register. On a malformed
non-Boolean pin coordinate the group fibre is empty; no representative
or actual pin value is postulated. -/
def prescribed (t : I) (y : RowValues S Copy Basis) (p : Pin) : Bool :=
  decide (y ((D.slot p).2 t) (D.copy p,B.diagonalIndex p) = 1)

theorem prescribed_of_fibre (t : I) (g : S) (E : Finset X) (y : RowValues S Copy Basis)
    (x : X → Bool) (hx : x ∈ secondScan D B t g E y) (p : Pin) (h : (D.slot p).2 t = g) :
    x (D.pinVar p) = prescribed D B t y p := by
  have he := (secondScan_membership D B t g E y x).mp hx
  have hr := he.2.1 (D.copy p,B.diagonalIndex p)
  rw [rowRead_diagonal D B t g p h] at hr
  unfold prescribed
  rw [h,← hr]
  cases x (D.pinVar p) <;> decide

variable [DecidableEq Pin]

/-- Adding the diagonal filter of the previous support-only wrapper does
not alter the actual numerical fibre. Hence it is safe to instantiate the
older J1/J2 support theorem with this computed fibre. -/
theorem redundant_diagonal_filter (interval : Finset ℕ) (hOutside : 0 ∉ interval)
    (t : I) (g : S) (E : Finset X) (y : RowValues S Copy Basis) (tracked : Finset Pin) :
    (secondScan D B t g E y).filter (fun x => ∀ p ∈ ownedPins D t g tracked,
      groupMeasurement D interval t g p x = boolRat (prescribed D B t y p)) =
    secondScan D B t g E y := by
  classical
  ext x
  simp only [Finset.mem_filter,and_iff_left_iff_imp]
  intro hx p hp
  have h := (Finset.mem_filter.mp hp).2
  rw [groupMeasurement_pin D interval hOutside t g p h, prescribed_of_fibre D B t g E y x hx p h]

theorem original_group_sum (interval : Finset ℕ) (hOutside : 0 ∉ interval)
    (f : ℚ[X]) (node : I → ℚ) (t : I) (g : S) (E : Finset X) (y : RowValues S Copy Basis)
    (tracked : Finset Pin) (U : X → Bool) (sigma : Pin → Bool) (other : (X → Bool) → ℚ[X]) :
    sourceGroupProbe D interval f node t g tracked (secondScan D B t g E y)
      U (prescribed D B t y) sigma other =
      ∑ x ∈ secondScan D B t g E y,
        other x * ∏ p ∈ ownedPins D t g tracked,
          pinFactor (sigma p) (correctedArgument (sourceRow f node (D.slot p)) (node t)
            (embedded D (D.copy p) (fun j => boolRat (x j)))
            (embedded D (D.copy p) (fun j => boolRat (U j)))) := by
  classical
  unfold sourceGroupProbe
  rw [redundant_diagonal_filter D B interval hOutside]

/-- The two sweeps in the original loop, before any early termination.
The number of *tested vectors* is counted here, not the bit cost of each
matrix test or each evaluated factor. -/
noncomputable def scanVisits (t : I) (g : S) : ℕ :=
  (privateCube D t g).card + (privateCube D t g).card

omit [Fintype I] [DecidableEq I] [Fintype S] [Fintype Copy] [DecidableEq Pin] in
theorem scanVisits_exact (t : I) (g : S) :
    scanVisits D t g = 2*2^groupSize D t g := by
  unfold scanVisits
  rw [privateCube_card,two_mul]

#print axioms rowRead_diagonal
#print axioms rowRead_matches_weight_zero
#print axioms extendGroup_injective
#print axioms privateCube_card
#print axioms secondScan_membership
#print axioms prescribed_of_fibre
#print axioms redundant_diagonal_filter
#print axioms original_group_sum
#print axioms scanVisits_exact
end J1R14Query
