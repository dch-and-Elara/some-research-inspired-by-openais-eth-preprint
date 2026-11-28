import J6OrientedHostCounts
import J6OrientedHost
import J6OrientedShift
import J6OrientedSplitSides
import J6OrientedPadding
import J6OrientedPlantValue
import Mathlib.Tactic

/-! Full physical J6 host evaluates to the polynomial of the
planted network times the exact padding factor computed on the
corrected printed packet geometry. -/
namespace J6OrientedHostEval
open P11FullPacking J6RecursiveOrientation
open J6OrientedHost J6RecursivePortCube J6NativeHeightClearing J6OrientedSplitSides
open scoped BigOperators Polynomial

variable {S V : Type*} [LinearOrder S] [Fintype S] [Fintype V] {a b m q l : ℕ}

noncomputable def padA {D : Type*} [Fintype D] (y : D×Bool → Bool) : Bool :=
  good (fun p : D×Bool => if p.2 then true else !y p)

noncomputable def padB {D : Type*} [Fintype D] (x : D×Bool → Bool) : Bool :=
  good (fun p : D => decide (x (p,false)=x (p,true)))

noncomputable def oldOK (T : Plant V m q) (w : Fin a → S)
    (y : Wire w m b l → Bool) : Bool :=
  good (fun v => rowTable T w v (fun i => y (rowPort T w v i)))

noncomputable def newOK (T : Plant V m q) (w : Fin a → S)
    (x : Wire w m b l → Bool) : Bool :=
  good (fun v => colTable w v (fun i => x (colPort T w v i)))

theorem oldOK_split (T : Plant V m q) (w : Fin a → S) :
    (oldOK (b:=b) (l:=l) T w) = joined (J6OrientedPlantValue.ok (coreA T)) padA := by
  classical
  funext y
  apply Bool.eq_iff_iff.mpr
  simp [oldOK,good,joined,J6OrientedPlantValue.ok,coreA,padA,Sum.forall,Prod.forall,
    rowTable,rowPort]
  tauto

omit [Fintype V] in
theorem newOK_split (T : Plant V m q) (w : Fin a → S) :
    (newOK (b:=b) (l:=l) T w) = joined (J6OrientedPlantValue.ok (coreB T)) padB := by
  classical
  funext x
  apply Bool.eq_iff_iff.mpr
  simp [newOK,good,joined,J6OrientedPlantValue.ok,coreB,padB,Sum.forall,Prod.forall,
    colTable,colPort]
  tauto

omit [Fintype S] in
theorem actual_read_split (mask : MaskFamily a b S) (w : Fin a → S)
    (h : m ≤ b) (hL : 2*l=2^a) (t : ℕ) :
    (fun p (x : Wire w m b l→Bool) =>
        ((J6RecursiveOrientationLocal.shifted mask w m l h hL t p).map x).getD false) =
      joinedRead (J6OrientedPlantValue.read t)
        (fun p (x : Pad w m b l×Bool→Bool) => ((padShift mask w h hL t p).map x).getD false) := by
  funext p x
  rcases p with ⟨u,j⟩|⟨d,side⟩
  · rw [J6OrientedShift.plant_shift]
    by_cases hj : j.val+t<2*l <;> simp [joinedRead,J6OrientedPlantValue.read,hj]
  · cases hs : J6RecursiveOrientationLocal.shifted mask w m l h hL t (.inr (d,side)) with
    | none => simp [joinedRead,padShift,hs]
    | some z =>
      rcases z with ⟨u,j⟩|p
      · exact (J6OrientedShift.no_pad_to_plant mask w h hL t d side u j hs).elim
      · simp [joinedRead,padShift,hs]

theorem padding_table_factor {D : Type*} [Fintype D] [DecidableEq D]
    (shift : D×Bool → Option (D×Bool)) (c : ℚ) :
    rationalSlot padA padB (fun p x => ((shift p).map x).getD false) c =
      ∏ d, (1+(1-c)^J6OrientedPadding.count shift d) := by
  classical
  rw [← J6OrientedPadding.factor_actual_padding]
  unfold rationalSlot J6OrientedPadding.contract
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_mul_distrib]
  have hy :
      (∏ p : D×Bool, if p.2 ∨ ¬y p then (1:ℚ) else 0) =
        if padA y then 1 else 0 := by
    calc
      _ = ∏ p : D×Bool, (if (if p.2 then true else !y p) then (1:ℚ) else 0) :=
        Finset.prod_congr rfl (fun p _ => by cases p.2 <;> cases y p <;> simp)
      _ = _ := prod_flags (fun p : D×Bool => if p.2 then true else !y p)
  rw [hy]
  cases hp : padA y <;> by_cases hq : ∀ d : D, x (d,false)=x (d,true) <;>
    simp [padB,good,hq]

theorem actual_layer_factorization (T : Plant V m q) (mask : MaskFamily a b S) (w : Fin a → S)
    (h : m ≤ b) (hL : 2*l=2^a) (t : ℕ) (ht : t ≤ 2*l) (c : ℚ) :
    letI : DecidableEq (Pad w m b l) := Classical.decEq _
    rationalSlot (oldOK T w) (newOK T w)
      (fun p x => ((J6RecursiveOrientationLocal.shifted mask w m l h hL t p).map x).getD false) c =
        ((LayerRecovery.layerPolynomial (J6OrientedPlantValue.wt (coreA T))
          (J6OrientedPlantValue.wt (coreB T))).eval c)^(2*l-t) *
        (J6OrientedPlantValue.wt (coreA T) (fun _ => false))^t *
        (∑ x : Fin m→Bool, J6OrientedPlantValue.wt (coreB T) x)^t *
        ∏ d, (1+(1-c)^J6OrientedPadding.count (padShift mask w h hL t) d) := by
  letI : DecidableEq (Pad w m b l) := Classical.decEq _
  rw [oldOK_split,newOK_split,actual_read_split,split_rationalSlot,
    J6OrientedPlantValue.planted_factors _ _ _ _ ht,padding_table_factor]

#print axioms oldOK_split
#print axioms newOK_split
#print axioms actual_read_split
#print axioms padding_table_factor
#print axioms actual_layer_factorization
end J6OrientedHostEval
