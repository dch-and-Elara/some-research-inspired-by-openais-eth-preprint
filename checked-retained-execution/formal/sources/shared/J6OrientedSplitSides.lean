import J6NativeHeightClearing
import Mathlib.Tactic

/-! Disjoint planted/padding sectors of the *actual* finite rational
contraction, valid whenever the two physical sectors do not share a
shift edge. This step uses both Boolean port cubes separately. -/
namespace J6OrientedSplitSides
open scoped BigOperators Polynomial
open J6NativeHeightClearing
variable {P D : Type*} [Fintype P] [DecidableEq P] [Fintype D] [DecidableEq D]

def joined (f : (P → Bool) → Bool) (g : (D → Bool) → Bool)
    (a : P ⊕ D → Bool) : Bool := f (fun p => a (.inl p)) && g (fun d => a (.inr d))

def joinedRead (left : P → (P→Bool) → Bool) (right : D → (D→Bool) → Bool)
    (p : P ⊕ D) (x : P ⊕ D → Bool) : Bool :=
  match p with
  | .inl q => left q (fun q' => x (.inl q'))
  | .inr q => right q (fun q' => x (.inr q'))

def sectorCube :
  (((P→Bool) × (P→Bool)) × ((D→Bool) × (D→Bool))) ≃
    (((P⊕D)→Bool) × ((P⊕D)→Bool)) where
  toFun u := (Sum.elim u.1.1 u.2.1,Sum.elim u.1.2 u.2.2)
  invFun u := ((u.1 ∘ Sum.inl,u.2 ∘ Sum.inl),(u.1 ∘ Sum.inr,u.2 ∘ Sum.inr))
  left_inv _ := rfl
  right_inv u := Prod.ext (funext (fun p => by cases p <;> rfl))
    (funext (fun p => by cases p <;> rfl))

noncomputable def term {W : Type*} [Fintype W]
    (A B : (W→Bool)→Bool) (read : W → (W→Bool)→Bool) (c : ℚ)
    (u : (W→Bool)×(W→Bool)) : ℚ :=
  if A u.1 && B u.2 then ∏ p, (LayerRecovery.wireFactor (u.1 p) (read p u.2)).eval c else 0

theorem split_rationalSlot (A B : (P→Bool)→Bool) (C E : (D→Bool)→Bool)
    (f : P → (P→Bool)→Bool) (g : D → (D→Bool)→Bool) (c : ℚ) :
    rationalSlot (joined A C) (joined B E) (joinedRead f g) c =
      rationalSlot A B f c * rationalSlot C E g c := by
  classical
  change (∑ y : P⊕D→Bool, ∑ x, term (joined A C) (joined B E) (joinedRead f g) c (y,x)) =
    (∑ y : P→Bool, ∑ x, term A B f c (y,x)) * (∑ y : D→Bool, ∑ x, term C E g c (y,x))
  rw [← Fintype.sum_prod_type (term (joined A C) (joined B E) (joinedRead f g) c),
    ← Fintype.sum_prod_type (term A B f c),← Fintype.sum_prod_type (term C E g c)]
  rw [← Equiv.sum_comp sectorCube (term (joined A C) (joined B E) (joinedRead f g) c)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  unfold term
  rw [Fintype.prod_sum_type]
  change (if (A u.1 && C v.1) && (B u.2 && E v.2) then
    ((∏ p, (LayerRecovery.wireFactor (u.1 p) (f p u.2)).eval c) *
      ∏ q, (LayerRecovery.wireFactor (v.1 q) (g q v.2)).eval c) else 0) = _
  cases A u.1 <;> cases B u.2 <;> cases C v.1 <;> cases E v.2 <;> simp

#print axioms split_rationalSlot
end J6OrientedSplitSides
