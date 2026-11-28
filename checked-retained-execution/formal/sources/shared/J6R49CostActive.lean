import J6R49CostCentreWord
import J6R49DFSActive
import J6R48BitCostActive

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 20000000
set_option maxRecDepth 2700

/-! Source R49 active machine's checked strip and sum of its actual
streamed centres. This is the running-meter inequality, not an
equality of results transplanted from another cost model. -/
namespace J6R49Cost
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 A1R11 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R23ScheduleWeight J6R19Retained HermiteLoss J6R48BitCost J6R49DFS
attribute [local irreducible] J6R12Blueprint.printedParams

variable {f : ℤ[X]} {ell s : ℕ}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

noncomputable def streamActiveChildBill {sel : @Selector f ell S (sourceDelta s)}
    {c : Call (PhysicalHost f ell)} {d : @Ready f ell S (sourceDelta s) c} {bank : Bank f}
    {q : ℕ} (D : @ActiveMachine f ell s sel c d bank q)
    (child : @ActiveChild f ell s sel c d bank) : ℕ :=
  (D.centres.map (fun t=>centreChildBill (D.tape t).low (child t))).sum

noncomputable def streamActiveTariff {sel : @Selector f ell S (sourceDelta s)}
    {c : Call (PhysicalHost f ell)} {d : @Ready f ell S (sourceDelta s) c} {bank : Bank f}
    {q : ℕ} (D : @ActiveMachine f ell s sel c d bank q)
    (hp : 0<c.prec) (hv : 0<ell) : ℕ :=
  let H := D.high hp
  let L := bank c.prec hp
  let B := D.extraPrecision
  (D.centres.map (fun t=>streamCentreTariff (sel:=sel) (d:=d) (t:=t) (D.tape t) hv H B)).sum+
    uvWidth H.words.length ell (c.prec+B)+D.centres.length*(addCap H.words.length ell (c.prec+B) H.hp+2)+
    stripFee H.words.length ell c.prec B+4+uvWidth L.words.length ell c.prec+2

theorem actual_stream_active_word_meter {sel : @Selector f ell S (sourceDelta s)}
    {c : Call (PhysicalHost f ell)} {d : @Ready f ell S (sourceDelta s) c} {bank : Bank f}
    {q : ℕ} (D : @ActiveMachine f ell s sel c d bank q)
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (hu : 0<(@centreU f ell s c)) (huM : (@centreU f ell s c) ≤ c.edges)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (child : @ActiveChild f ell s sel c d bank) :
    (D.eval hq hp hv hf child).steps  ≤ 
      streamActiveChildBill (sel:=sel) (d:=d) D child+streamActiveTariff (sel:=sel) (d:=d) D hp hv := by
  let H := D.high hp
  let L := bank c.prec hp
  let B := D.extraPrecision
  let run := fun t=>(D.tape t).runCentre hq hv hf H B (child t)
  let own := fun t=>streamCentreTariff (sel:=sel) (d:=d) (t:=t) (D.tape t) hv H B
  let input := fun t=>centreChildBill (D.tape t).low (child t)
  let cap := fun t => (⟨(),input t+own t⟩ : Meter Unit)
  have b := bill_rel run cap D.centres
    (fun t _ => actual_stream_centre_all_arithmetic (sel:=sel) (d:=d) (t:=t) (D.tape t) hq hv hf H B hu huM D.enough (child t))
  have hb : bill cap D.centres=streamActiveChildBill D child+(D.centres.map own).sum :=
    list_charge D.centres (fun t=>input t+own t) input own (fun _ _=>rfl)
  rw [hb] at b
  have hm := (sumM_steps H.hp run D.centres).2
  have hstrip := strip_loop_measured ((H.natDegree hf).trans (L.natDegree hf).symm) (D.highRun hq hp hv hf child).result
  have hcheck := checked_choice_bound (zeroM L.hp) (D.finish hq hp hv hf child)
  change (D.eval hq hp hv hf child).steps  ≤  (D.highRun hq hp hv hf child).steps+
    (stripUVLoop ((H.natDegree hf).trans (L.natDegree hf).symm) (D.highRun hq hp hv hf child).result).steps+
    4+uvWidth L.words.length ell c.prec+2 at hcheck
  change (D.highRun hq hp hv hf child).steps  ≤  _ at hm
  have highBound := hm.trans (Nat.add_le_add_right (Nat.add_le_add_right b _) _)
  have all := Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add highBound hstrip) 4) (uvWidth L.words.length ell c.prec)) 2
  calc
    _  ≤  _ := hcheck
    _  ≤  _ := all
    _ = _ := by unfold streamActiveTariff; dsimp only; ac_rfl

#print axioms streamActiveChildBill
#print axioms streamActiveTariff
#print axioms actual_stream_active_word_meter
end J6R49Cost

