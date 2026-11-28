import J6R48BitCostCentre
import J6R24MeteredRecursionNativeLedger

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4200000
set_option maxRecDepth 2000

/-! The genuine active-node itinerary accumulates one charged receipt per
centre. Its dependent beta/g child occurrences have an independent bill.
The final checked strip never carries the price of a fictitious oracle. -/
namespace J6R48BitCost
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleCoordinates A1R10 A1R11 A1R12
open J6R22Active J6R23ScheduleWeight J6R24MeteredRecursion J6R9Recursive
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R19Retained HermiteLoss
attribute [local irreducible] J6R12Blueprint.printedParams

variable {f : ℤ[X]} {ell s : ℕ}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
def binaryActiveTariff {sel : @Selector f ell S (sourceDelta s)}
    {c : Call (PhysicalHost f ell)} {d : @Ready f ell S (sourceDelta s) c} {bank : Bank f}
    (D : @ActiveDesc f ell s sel c d bank) (hp : 0<c.prec) (hv : 0<ell)
    (child : @ActiveChild f ell s sel c d bank) : ℕ :=
  let H := D.high hp
  let L := bank c.prec hp
  let B := D.extraPrecision
  (D.centres.map (fun t=>centreTariff (sel:=sel) (s:=s) (d:=d) (t:=t) (D.tape t) hv H B (child t))).sum +
    uvWidth H.words.length ell (c.prec+B) + D.centres.length * (addCap H.words.length ell (c.prec+B) H.hp+2) +
    stripFee H.words.length ell c.prec B + 4 + uvWidth L.words.length ell c.prec + 2

theorem checked_choice_bound {A : Type*} (nil : Meter A) (x : Meter (Option A)) :
    (checkedWord nil x).steps≤x.steps+nil.steps+2 := by
  unfold checkedWord
  split <;> simp only <;> omega

theorem active_arithmetic_measured {sel : @Selector f ell S (sourceDelta s)}
    {c : Call (PhysicalHost f ell)} {d : @Ready f ell S (sourceDelta s) c} {bank : Bank f}
    (D : @ActiveDesc f ell s sel c d bank) (hp : 0<c.prec) (hv : 0<ell)
    (hf : f.Monic) (hu : 0<(@centreU f ell s c)) (huM : (@centreU f ell s c)≤c.edges)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (child : @ActiveChild f ell s sel c d bank) :
    (D.eval hp hv hf child).steps ≤ D.children hv child + binaryActiveTariff (sel:=sel) (d:=d) D hp hv child := by
  let H := D.high hp
  let L := bank c.prec hp
  let B := D.extraPrecision
  let run := fun t => (D.tape t).centre hv hf H B (child t)
  let fee := fun t => centreTariff (sel:=sel) (s:=s) (d:=d) (t:=t) (D.tape t) hv H B (child t)
  let childFee := fun t => ((D.tape t).site hv (child t)).childBill
  let cap := fun t => (⟨(),childFee t+fee t⟩ : Meter Unit)
  have h0 := bill_rel run cap D.centres
    (fun t _ => centre_arithmetic_measured (sel:=sel) (s:=s) (d:=d) (t:=t) (D.tape t) hv hf H B hu huM D.enough (child t))
  have hsplit : bill cap D.centres=D.children hv child+(D.centres.map fee).sum := by
    change (D.centres.map (fun t=>childFee t+fee t)).sum=(D.centres.map childFee).sum+(D.centres.map fee).sum
    exact list_charge D.centres (fun t=>childFee t+fee t) childFee fee (fun _ _=>rfl)
  rw [hsplit] at h0
  have hm := (sumM_steps H.hp run D.centres).2
  have hstrip := strip_loop_measured ((H.natDegree hf).trans (L.natDegree hf).symm)
    (D.highRun hp hv hf child).result
  have hcheck := checked_choice_bound (zeroM L.hp) (D.finish hp hv hf child)
  change (D.eval hp hv hf child).steps≤_ at hcheck
  change _≤(D.highRun hp hv hf child).steps+
    (stripUVLoop ((H.natDegree hf).trans (L.natDegree hf).symm) (D.highRun hp hv hf child).result).steps+
    4+uvWidth L.words.length ell c.prec+2 at hcheck
  change (D.highRun hp hv hf child).steps≤_ at hm
  have highBound := hm.trans (Nat.add_le_add_right (Nat.add_le_add_right h0 _) _)
  have all := Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add highBound hstrip) 4) (uvWidth L.words.length ell c.prec)) 2
  calc
    _ ≤ _ := hcheck
    _ ≤ _ := all
    _ = D.children hv child + binaryActiveTariff (sel:=sel) (d:=d) D hp hv child := by
      unfold binaryActiveTariff
      dsimp only
      ac_rfl

#print axioms binaryActiveTariff
#print axioms checked_choice_bound
#print axioms active_arithmetic_measured
end J6R48BitCost

