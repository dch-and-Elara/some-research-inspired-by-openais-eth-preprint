import J6R24MeteredRecursionNativeLedger
import J6R48BitCostProbe

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6800000
set_option maxRecDepth 1800

/-! Count the arithmetic iteration roster on the genuine dependent
Plan slots, with multiplicity. This proof-side unit receipt is never
used as an evaluator; it only counts actual centre/probe/mode/group
addresses, including two addresses that create equal Call records. -/
namespace J6R48BitCost
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R10 A1R12
open J6R22Active J6R24MeteredRecursion J6R9Recursive
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted

variable {f : ℤ[X]} {ell s : ℕ}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

def realProbeCount (c : Call (PhysicalHost f ell)) : ℕ := J9PrintedSchedule.probeCount c.edges (2^((S).levelBits c.depth))

attribute [local irreducible] J6R12Blueprint.printedParams

theorem actual_group_visit_count {sel : @Selector f ell S (sourceDelta s)}
    {c : Call (PhysicalHost f ell)} {d : @Ready f ell S (sourceDelta s) c} {bank : Bank f}
    (D : @ActiveDesc f ell s sel c d bank) :
    (D.centres.map (fun t=>@realProbeCount f ell s c*(D.tape t).modes.length*64)).sum =
      Nat.card ((Plan sel).Slot c) := by
  letI : ∀ t : @J6ActiveRun.Center (PhysicalHost f ell) Unit S c, Fintype (NativeMenu (N sel) c t) :=
    fun t=>Finset.fintypeCoeSort (@J6RecursiveMenu.menu ((N sel).Mode c t) ((N sel).finiteMode c t)
      ((N sel).decideMode c t) (registerPrecision S c t) ((N sel).weight c t))
  letI : Fintype (NativeAddress (N sel) c) := Sigma.instFintype
  rw [←Nat.card_congr (liveEquiv (sel:=sel) d),Nat.card_eq_fintype_card,Fintype.card_sigma,
    complete_list_sum D.centres D.centreUnique D.centreComplete]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hset : (D.tape t).modes.toFinset=Finset.univ := by
    ext β
    simp [(D.tape t).modeComplete β]
  have hcard : (D.tape t).modes.length = Fintype.card (NativeMenu (N sel) c t) := by
    rw [←List.toFinset_card_of_nodup (D.tape t).modeUnique,hset,Finset.card_univ]
  change @realProbeCount f ell s c*(D.tape t).modes.length*64 =
    Fintype.card (Probe S c × NativeMenu (N sel) c t × Fin 64)
  rw [Fintype.card_prod,Fintype.card_prod,Fintype.card_fin,hcard]
  simp only [Fintype.card_fin,realProbeCount,Nat.mul_assoc]

#print axioms actual_group_visit_count
end J6R48BitCost

