import J6OrientedHost
import J6OrientedShift
import J6OrientedPadding
import J6BoundaryFactors
import Mathlib.Tactic

/-! Physical cardinalities and the exact free-copy subdivision count.
The all-zero old-row condition remains a condition on the actual gates
of the guarded planted network, not an assumption of equal contractions. -/
namespace J6OrientedHostEval
open P11FullPacking J6RecursiveOrientation
open J6OrientedHost J6RecursivePortCube
open scoped BigOperators
variable {S V : Type*} [LinearOrder S] [Fintype S] [Fintype V] {a b m q l : ℕ}

noncomputable def coreA (T : Plant V m q) (y : Fin m → Bool) : Bool :=
  good (fun v => (T.old v).eval (fun i => y (T.rowPort ⟨v,i⟩)))

noncomputable def coreB (T : Plant V m q) (x : Fin m → Bool) : Bool :=
  good (fun v : Fin q => decide (x (T.colPort (v,false)) = x (T.colPort (v,true))))

omit [Fintype V] in
theorem coreB_count (T : Plant V m q) :
    (∑ x : Fin m→Bool, if coreB T x then (1:ℚ) else 0) = (2:ℚ)^q := by
  classical
  let e : ((Fin q×Bool)→Bool) ≃ (Fin m→Bool) :=
    { toFun := fun f p => f (T.colPort.symm p)
      invFun := fun x p => x (T.colPort p)
      left_inv := fun f => by funext p; simp
      right_inv := fun f => by funext p; simp }
  have h := Fintype.sum_equiv e
    (fun x : Fin q×Bool→Bool => if ∀ d, x (d,false)=x (d,true) then (1:ℚ) else 0)
    (fun x => if coreB T x then (1:ℚ) else 0)
    (fun x => by simp [coreB,good,e])
  apply h.symm.trans
  convert (J6BoundaryFactors.free_subdivisions (Q:=Fin q)) using 1
  · apply Finset.sum_congr rfl
    intro x _
    by_cases hx : ∀ d : Fin q, x (d,false)=x (d,true) <;> simp [hx]
  · simp

theorem coreA_zero (T : Plant V m q)
    (h : ∀ v, (T.old v).eval (fun _ => false)=true) :
    coreA T (fun _ => false)=true := by
  simp [coreA,good,h]

noncomputable def padShift (mask : MaskFamily a b S) (w : Fin a → S)
    (h : m ≤ b) (hL : 2*l=2^a) (t : ℕ) (p : Pad w m b l×Bool) :
    Option (Pad w m b l×Bool) :=
  (J6RecursiveOrientationLocal.shifted mask w m l h hL t (.inr p)).bind fun
   | .inl _ => none
   | .inr d => some d

omit [Fintype S] in
theorem padShift_apply (mask : MaskFamily a b S) (w : Fin a → S)
    (h : m ≤ b) (hL : 2*l=2^a) (t : ℕ) (p r : Pad w m b l×Bool)
    (hs : padShift mask w h hL t p=some r) :
    J6RecursiveOrientationLocal.shifted mask w m l h hL t (.inr p)=some (.inr r) := by
  cases he : J6RecursiveOrientationLocal.shifted mask w m l h hL t (.inr p) with
  | none => simp [padShift,he] at hs
  | some x =>
    rcases x with g | g
    · simp [padShift,he] at hs
    · have hg : g=r := by simpa [padShift,he] using hs
      rw [hg]

theorem padShift_count_le_two (mask : MaskFamily a b S) (w : Fin a → S)
    (h : m ≤ b) (hL : 2*l=2^a) (t : ℕ) (d : Pad w m b l) :
    J6OrientedPadding.count (padShift mask w h hL t) d ≤ 2 := by
  classical
  apply J6OrientedPadding.count_le_two
  intro p r q hp hr
  exact Sum.inr_injective
    (J6OrientedShift.successor_injective mask w h hL t _ _ _
      (padShift_apply mask w h hL t p q hp) (padShift_apply mask w h hL t r q hr))

theorem wire_cardinality (w : Fin a → S) :
    Fintype.card (Wire w m b l) = m*(2*l)+2*Fintype.card (Pad w m b l) := by
  simp only [Wire,J6PhysicalPacking.Wire,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_bool]
  rw [Nat.mul_comm (Fintype.card (Pad w m b l))]

#print axioms coreB_count
#print axioms coreA_zero
#print axioms padShift_count_le_two
#print axioms wire_cardinality
end J6OrientedHostEval
