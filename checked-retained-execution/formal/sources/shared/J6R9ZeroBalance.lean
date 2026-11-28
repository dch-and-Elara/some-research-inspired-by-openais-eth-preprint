import J6R9ZeroCutoff
import J6RepairedCapacity
import Mathlib.Logic.Equiv.Prod

/-! The guarded, fully padded J6 physical placement has the same number
of child wires in all 64 source groups. The equivalence used to count
these wires does not claim the different group subnetworks have equal
contractions. -/

namespace J6R9ZeroBalance
open scoped BigOperators Classical
open J6Mesh P11FullPacking J6RepairedCentered J6RecursiveOrientation

noncomputable section
set_option maxHeartbeats 2000000

private theorem uniform_card {X S : Type*} [Fintype X] [Fintype S] (label : X → S) (s : S)
    (move : ∀ t : S, {x // label x = t} ≃ {x // label x = s}) :
    Fintype.card S * Nat.card {x // label x = s} = Fintype.card X := by
  classical
  have he (t : S) : Fintype.card {x // label x = t} = Fintype.card {x // label x = s} :=
    Fintype.card_congr (move t)
  rw [Nat.card_eq_fintype_card]
  symm
  calc
    Fintype.card X = Fintype.card (Σ t : S, {x // label x = t}) :=
      Fintype.card_congr (Equiv.sigmaFiberEquiv label).symm
    _ = Fintype.card S * Fintype.card {x // label x = s} := by
      rw [Fintype.card_sigma]
      simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rfl

private def wordSwap {I S : Type*} [DecidableEq S] (g h : S) : Equiv.Perm (Cell I S) :=
  Equiv.piCongrRight (fun _ => Equiv.prodCongr (Equiv.swap g h) (Equiv.swap g h))

variable {S : Type*} [LinearOrder S] [Fintype S]

/-- Raw child incidence cardinal, before choosing an enumeration. Each
group gets both the row and the column ports, not just one side. -/
theorem actual_group_card
    (m l : ℕ) (mask : MaskFamily (a m) (K m) S)
    (w : Fin (a m) → S) (h : m≤K m) (hL : 2*l=L m) (hS : Fintype.card S = 64)
    (g : S) :
    32 * Nat.card {q : Sum (Ports m l w) (Ports m l w) // groupOf m l mask w h hL q = g} = M m := by
  classical
  let α := Ports m l w
  let β := Sum α α
  let group : β → S := groupOf m l mask w h hL
  let addr := J6PhysicalPacking.placement (diagonal w) m (K m) l h
  have swapFibers (k : S) : {p : β // group p = k} ≃ {p : β // group p = g} := by
    let swap := Equiv.swap k g
    let changeAddr := Equiv.prodCongr (wordSwap (I:=Fin (a m)) k g)
      (Equiv.refl (Fin (K m) × Fin (2*l)))
    let e : Equiv.Perm α := (addr.trans changeAddr).trans addr.symm
    let f : Equiv.Perm β := Equiv.sumCongr e e
    have hAddr (p : α) : addr (e p) = changeAddr (addr p) := addr.apply_symm_apply _
    have hLeft (p : α) : group (.inl (e p)) = swap (group (.inl p)) := by
      change groupOf m l mask w h hL (.inl (e p)) = swap (groupOf m l mask w h hL (.inl p))
      rw [(groupOf_cell m l mask w h hL (e p)).1,(groupOf_cell m l mask w h hL p).1]
      change ((addr (e p)).1 (coord m)).1 = swap (((addr p).1 (coord m)).1)
      rw [hAddr]
      rfl
    have hRight (p : α) : group (.inr (e p)) = swap (group (.inr p)) := by
      change groupOf m l mask w h hL (.inr (e p)) = swap (groupOf m l mask w h hL (.inr p))
      rw [(groupOf_cell m l mask w h hL (e p)).2,(groupOf_cell m l mask w h hL p).2]
      change ((addr (e p)).1 (coord m)).2 = swap (((addr p).1 (coord m)).2)
      rw [hAddr]
      rfl
    have hf (p : β) : group (f p) = swap (group p) := by
      cases p with
      | inl q => exact hLeft q
      | inr q => exact hRight q
    exact
      { toFun := fun p => ⟨f p.val,by rw [hf,p.prop]; exact Equiv.swap_apply_left k g⟩
        invFun := fun p => ⟨f.symm p.val,by
          apply swap.injective
          rw [← hf,f.apply_symm_apply,p.prop]
          exact (Equiv.swap_apply_left k g).symm⟩
        left_inv := fun p => Subtype.ext (f.symm_apply_apply p.val)
        right_inv := fun p => Subtype.ext (f.apply_symm_apply p.val) }
  have hb := uniform_card group g swapFibers
  have hcard : Fintype.card β = M m + M m := by
    change Fintype.card (Sum (Ports m l w) (Ports m l w)) = _
    rw [Fintype.card_sum,J6RepairedCapacity.actual_wire_count m l w h hL hS]
  rw [hS,hcard] at hb
  change 64 * Nat.card {q : Sum (Ports m l w) (Ports m l w) // groupOf m l mask w h hL q = g} =
    M m + M m at hb
  omega

/-- On the repaired physical host the next group call is active at the
original exact ceiling cutoff. This rejects using the direct leaf
execution theorem as a theorem about the large J6 root. -/
theorem actual_group_above_printed_cutoff
    (m l native : ℕ) (mask : MaskFamily (a m) (K m) S)
    (w : Fin (a m) → S) (h : m≤K m) (hL : 2*l=L m) (hS : Fintype.card S = 64)
    (hs : native ≤ m) (g : S) (n : ℕ)
    (order : Fin n ≃ {q : Sum (Ports m l w) (Ports m l w) // groupOf m l mask w h hL q = g}) :
    J6R9ZeroCutoff.cutoff (physicalSize m native) (Nat.clog 2 (physicalSize m native)) < n := by
  have hn : n = Nat.card {q : Sum (Ports m l w) (Ports m l w) // groupOf m l mask w h hL q = g} := by
    simpa only [Nat.card_fin] using Nat.card_congr order
  apply J6R9ZeroCutoff.actual_J6_balanced_above_cutoff m native n hs
  rw [hn]
  exact actual_group_card m l mask w h hL hS g

#print axioms actual_group_card
#print axioms actual_group_above_printed_cutoff

end
end J6R9ZeroBalance
