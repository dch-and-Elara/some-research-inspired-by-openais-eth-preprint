import J6R48BitCostPlan
import J6R25PreparedSupplyWhole

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 2400

/-! Compose the same internal arithmetic tariff with the real R25
producer run. Its mode preparation is executed, not an estimated
external term. This is separate from the R33 paged ledger: no page
creation, routing or leaf implementation has been identified by default. -/
namespace J6R48BitCost
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R10
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R22Active J6R24MeteredRecursion J6R25PreparedSupply

variable {f : ℤ[X]} {ell s C : ℕ}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
attribute [local irreducible] J6R12Blueprint.printedParams

noncomputable def preparedLeafAt {cfg : RootBounds s C f} {sel : @Selector f ell S (sourceDelta s)}
    {r : Call (PhysicalHost f ell)} {hf : f.Monic}
    (T : @Prepared f ell s C cfg sel r hf)
    (c : Call (PhysicalHost f ell)) : ℕ :=
  if c.edges≤(S).cutoff then T.localAt c else 0

theorem native_leaf_active_split {cfg : RootBounds s C f} {sel : @Selector f ell S (sourceDelta s)}
    {r : Call (PhysicalHost f ell)} {hf : f.Monic}
    (T : @Prepared f ell s C cfg sel r hf)
    (c : Call (PhysicalHost f ell)) :
    T.localAt c=preparedActiveAt T c+preparedLeafAt T c := by
  by_cases stop : c.edges≤(S).cutoff <;> simp [preparedActiveAt,preparedLeafAt,stop]

theorem prepared_run_explicit_meter {cfg : RootBounds s C f} {sel : @Selector f ell S (sourceDelta s)}
    {r : Call (PhysicalHost f ell)} {hf : f.Monic}
    (T : @Prepared f ell s C cfg sel r hf)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] (depth : r.depth=0) :
    (T.run r (.reflexive r)).steps≤
      ∑ j∈Finset.range (pathLimit s C+1),
        (levelBill (Plan sel) r (structuralAt T) j+levelBill (Plan sel) r (preparedLeafAt T) j) := by
  rw [T.paid_exact depth]
  apply Finset.sum_le_sum
  intro j _
  let order := occurrences (Plan sel) r j
  have hs := list_charge order T.localAt (preparedActiveAt T) (preparedLeafAt T)
    (fun c _ => native_leaf_active_split T c)
  have hb := list_sum_le_charges order (actual_prepared_charge T)
  unfold levelBill
  exact hs.le.trans (Nat.add_le_add_right hb _)

theorem actual_mode_produced_internal_meter {cfg : RootBounds s C f} {sel : @Selector f ell S (sourceDelta s)}
    {r : Call (PhysicalHost f ell)} {hf : f.Monic}
    (P : @J6R25PreparedSupply.Input f ell s C cfg sel r hf)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r)] :
    let out := P.run r (.reflexive r)
    (P.prepared.frame (.reflexive r)).decode out.result=reduce r.prec f ell (r.host.contract hf) ∧
      out.steps≤
        (∑ j∈Finset.range (pathLimit s C+1),
          (levelBill (Plan sel) r (structuralAt P.prepared) j+
            levelBill (Plan sel) r (preparedLeafAt P.prepared) j))+
        ∑ j∈Finset.range (pathLimit s C+1),levelBill (Plan sel) r P.modeAt j := by
  obtain ⟨value,cost⟩ := whole_produced_modes P
  exact ⟨value,cost.le.trans (Nat.add_le_add_right (prepared_run_explicit_meter P.prepared P.dZero) _)⟩

#print axioms preparedLeafAt
#print axioms native_leaf_active_split
#print axioms prepared_run_explicit_meter
#print axioms actual_mode_produced_internal_meter
end J6R48BitCost

