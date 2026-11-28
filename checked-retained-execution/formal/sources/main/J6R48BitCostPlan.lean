import J6R48BitCostActive
import J6R24MeteredRecursionWhole

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10500000
set_option maxRecDepth 2400

/-! Eliminate the opaque local active arithmetic term in the R24 prepared
occurrence ledger. This tariff is a proof-side expression on the real prepared
descriptors, independent of the returned child values; it is not
another paid walk. Leaf and chronological writer costs stay separate. -/
namespace J6R48BitCost
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R10
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R22Active J6R24MeteredRecursion


variable {f : ℤ[X]} {ell s C : ℕ}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
attribute [local irreducible] J6R12Blueprint.printedParams

section Active
def structuralFee {sel : @Selector f ell S (sourceDelta s)}
    {c : Call (PhysicalHost f ell)} {d : @Ready f ell S (sourceDelta s) c}
    {bank : Bank f} (D : @ActiveDesc f ell s sel c d bank) (hp : 0<c.prec) (hv : 0<ell) : ℕ :=
  binaryActiveTariff (sel:=sel) (d:=d) D hp hv (fun t _ _ _ =>
    let fr := bank (@J6ActiveRun.registerPrecision (PhysicalHost f ell) Unit S c t) (@register_positive f ell S (sourceDelta s) c d t)
    ⟨(zeroM fr.hp).result,0⟩)

theorem tariff_ignores_child_words {sel : @Selector f ell S (sourceDelta s)}
    {c : Call (PhysicalHost f ell)} {d : @Ready f ell S (sourceDelta s) c}
    {bank : Bank f} (D : @ActiveDesc f ell s sel c d bank) (hp : 0<c.prec) (hv : 0<ell)
    (x : @ActiveChild f ell s sel c d bank) :
    binaryActiveTariff (sel:=sel) (d:=d) D hp hv x=structuralFee D hp hv := rfl

theorem bare_child_bill_zero {sel : @Selector f ell S (sourceDelta s)}
    {c : Call (PhysicalHost f ell)} {d : @Ready f ell S (sourceDelta s) c}
    {bank : Bank f} (D : @ActiveDesc f ell s sel c d bank) (hv : 0<ell)
    (x : @ActiveChild f ell s sel c d bank) :
    D.children hv (fun t z β g => bare (x t z β g))=0 := by
  have h := child_sum_exact d D hv (fun t z β g => bare (x t z β g))
    (fun _ => 0) (fun _ _ _ _ => rfl)
  exact h.trans (by simp)
end Active

noncomputable def preparedActiveAt {cfg : RootBounds s C f}
    {sel : @Selector f ell S (sourceDelta s)} {r : Call (PhysicalHost f ell)} {hf : f.Monic}
    (T : @Prepared f ell s C cfg sel r hf)
    (c : Call (PhysicalHost f ell)) : ℕ :=
  if c.edges≤(S).cutoff then 0 else T.localAt c

noncomputable def structuralAt {cfg : RootBounds s C f}
    {sel : @Selector f ell S (sourceDelta s)} {r : Call (PhysicalHost f ell)} {hf : f.Monic}
    (T : @Prepared f ell s C cfg sel r hf)
    (c : Call (PhysicalHost f ell)) : ℕ :=
  if reach : NativeReach (Plan sel) r c then
    if act : (S).cutoff<c.edges then
      structuralFee (T.active c reach act) (reachable_positive T reach) T.vPositive
    else 0
  else 0

variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem actual_prepared_charge {cfg : RootBounds s C f}
    {sel : @Selector f ell S (sourceDelta s)} {r : Call (PhysicalHost f ell)} {hf : f.Monic}
    (T : @Prepared f ell s C cfg sel r hf)
    (c : Call (PhysicalHost f ell)) :
    preparedActiveAt T c ≤ structuralAt T c := by
  by_cases h : NativeReach (Plan sel) r c
  · by_cases stop : c.edges≤(S).cutoff
    · rw [preparedActiveAt,if_pos stop,structuralAt,dif_pos h,dif_neg (Nat.not_lt_of_ge stop)]
    · let act := Nat.lt_of_not_ge stop
      let d := ready_reachable cfg sel h T.rootStable act
      let A := T.active c h act
      let x := T.childRuns h d
      let leaf := reachable_positive T h
      let y := fun t z β g => bare (x t z β g)
      have scale := (J6R12Integral.printedGuards cfg sel r T.rootStable).taper c h act
      have hA := active_arithmetic_measured A leaf T.vPositive hf scale.1 scale.2 y
      have h0 : A.children T.vPositive y=0 := bare_child_bill_zero A T.vPositive x
      rw [h0,zero_add,tariff_ignores_child_words] at hA
      rw [preparedActiveAt,if_neg stop,Prepared.localAt,dif_pos h,dif_neg stop,
        structuralAt,dif_pos h,dif_pos act]
      exact hA
  · simp only [structuralAt,preparedActiveAt,Prepared.localAt,dif_neg h,ite_self,le_refl]

theorem list_sum_le_charges {A : Type*} (xs : List A) {p q : A→ℕ}
    (h : ∀ x,p x≤q x) : (xs.map p).sum≤(xs.map q).sum := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih => simpa only [List.map_cons,List.sum_cons] using Nat.add_le_add (h x) ih

theorem structural_depth_charge {cfg : RootBounds s C f}
    {sel : @Selector f ell S (sourceDelta s)} {r : Call (PhysicalHost f ell)} {hf : f.Monic}
    (T : @Prepared f ell s C cfg sel r hf) :
    (∑ j∈Finset.range (pathLimit s C+1),levelBill (Plan sel) r (preparedActiveAt T) j)≤
      ∑ j∈Finset.range (pathLimit s C+1),levelBill (Plan sel) r (structuralAt T) j := by
  apply Finset.sum_le_sum
  intro j _
  unfold levelBill
  exact list_sum_le_charges _ (actual_prepared_charge T)

#print axioms structuralFee
#print axioms tariff_ignores_child_words
#print axioms bare_child_bill_zero
#print axioms actual_prepared_charge
#print axioms structural_depth_charge
end J6R48BitCost

